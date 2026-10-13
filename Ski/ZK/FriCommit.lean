import Ski.ZK.FSMultiOpenRd

/-!
# A commit phase of FRI's shape as an opening that reads the tables

FRI commits to its layers in turn: layer `i` is the codeword folded by the
challenges so far, its Merkle root `Rᵢ` is observed, and the next folding
challenge `βᵢ` is sampled from the challenger.  Here a strategy of that
shape is an opening that reads the fourth table: `βᵢ = H₄(φ M (Rᵢ, i))` at
the third message `M`, the root `Rᵢ = layer c4 d σ β<ᵢ` any function of
the query challenge, the opening's data and salt and the earlier
challenges (`friBetas`; `layer` may return the whole root history).  It is
`FSMultiOpen`'s `pfRd` (`friCommit_run`, `friCommitPf_eq`), `k` reads for
`k` layers (`friCommit_reads`), so it fits a slot of the data-reading
composites (`sud_interleaveD` and its kin), all slots making `kr` reads.

Not shown, and needed before this is Plonky3's FRI:
- the roots read one commitment's data and `c4`, not the out-of-domain
  point, the other challenges or the other commitments' data, which
  FRI's batched DEEP codeword reads;
- the hash point is `(M, Rᵢ, i)`, not the full transcript;
- the query indices `c4` are drawn before the commit phase, where Plonky3
  samples them after it;
- the proof's view keeps its own FRI (`fri c4`, `Rb c4` in `sudFS4T`);
  nothing here replaces it;
- the opening's hiding given the opened values (`hp`) is a hypothesis,
  not derived from `MaskFri`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The commit phase's strategy: layer `i`'s challenge is read from the
    fourth table at `φ M (Rᵢ, i)`, `Rᵢ` the root of the layer folded by the
    challenges read so far (newest first, so reversed). -/
def friCommitNxt {D R : Type} (n1 : Nat) (layer : Nat → D → Nat → List Nat → R) :
    Nat → Nat → D → Nat → List Nat → Nat × Nat × (R × Nat) :=
  fun c4 M d σ prev => (3, M / n1, (layer c4 d σ prev.reverse, prev.length))

/-- **FRI's folding challenges**, newest first: `βᵢ` the fourth table's
    answer at `φ M (Rᵢ, i)`. -/
def friBetas {D R : Type} (K4 : Nat) (φ : Nat → R × Nat → Nat) (layer : Nat → D → Nat → List Nat → R)
    (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => rget K4 (φ M (layer c4 d σ (friBetas K4 φ layer H c4 M d σ k).reverse, k)) H.2.2.2 ::
      friBetas K4 φ layer H c4 M d σ k

theorem friBetas_length {D R : Type} (K4 : Nat) (φ : Nat → R × Nat → Nat) (layer : Nat → D → Nat → List Nat → R)
    (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) : ∀ k, (friBetas K4 φ layer H c4 M d σ k).length = k
  | 0 => rfl
  | k + 1 => by show (friBetas K4 φ layer H c4 M d σ k).length + 1 = k + 1; rw [friBetas_length K4 φ layer H c4 M d σ k]

/-- **The commit phase is a read strategy**: `runR4` with `friCommitNxt`
    reads exactly FRI's folding challenges. -/
theorem friCommit_run {D R : Type} (K1 K2 K3 K4 n1 : Nat) (φ : Nat → R × Nat → Nat) (layer : Nat → D → Nat → List Nat → R)
    (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    ∀ k, runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxt n1 layer c4 M d σ) H k = friBetas K4 φ layer H c4 M d σ k
  | 0 => rfl
  | k + 1 => by
    have ih := friCommit_run K1 K2 K3 K4 n1 φ layer H c4 M d σ k
    show rget4 K1 K2 K3 K4 H 3 (pt4 n1 φ (M % n1) (friCommitNxt n1 layer c4 M d σ
        (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxt n1 layer c4 M d σ) H k))) ::
        runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxt n1 layer c4 M d σ) H k = _
    rw [ih]
    show rget K4 (φ (M % n1 + n1 * (M / n1)) (layer c4 d σ (friBetas K4 φ layer H c4 M d σ k).reverse,
      (friBetas K4 φ layer H c4 M d σ k).length)) H.2.2.2 :: friBetas K4 φ layer H c4 M d σ k = _
    rw [Nat.mod_add_div, friBetas_length]
    rfl

/-- **FRI's commit phase as an opening** (`pfRd`): `k` layers, the output
    `out` any function of the challenges, the data and the salt. -/
def friCommitPf {D R P : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat) (layer : Nat → D → Nat → List Nat → R)
    (out : Nat → Nat → D → Nat → List Nat → P) : Nat → Nat → Nat → Nat → Nat → Nat → D → Nat → P :=
  pfRd K1 K2 K3 K4 n1 k φ (friCommitNxt n1 layer) out

theorem friCommitPf_eq {D R P : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat)
    (layer : Nat → D → Nat → List Nat → R) (out : Nat → Nat → D → Nat → List Nat → P)
    (c4 T1 T2 T3 T4 M : Nat) (d : D) (σ : Nat) :
    friCommitPf K1 K2 K3 K4 n1 k φ layer out c4 T1 T2 T3 T4 M d σ =
      out c4 M d σ (friBetas K4 φ layer (T1, T2, T3, T4) c4 M d σ k) := by
  unfold friCommitPf pfRd
  rw [friCommit_run]

/-- **Its reads**: `k` of them, in the fourth table (their points follow from
    `friCommit_run` and `pfRdReads`). -/
theorem friCommit_reads {D R : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat)
    (layer : Nat → D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    (pfRdReads K1 K2 K3 K4 n1 k φ (friCommitNxt n1 layer) H c4 M d σ).length = k :=
  pfRdReads_length _ _ _ _ _ _ _ _ _ _ _ _ _

end Circuit
