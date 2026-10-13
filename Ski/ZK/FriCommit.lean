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

A strategy may first read the earlier challenges (`friCommitNxtC`): the
first three tables at points that are the first, second and third messages
when the commitments lie in their digits' ranges (`Com1 < n1`, `Com2 < n2`:
`friCommitC_first3`, `msg_nest`, `friCommitC_msgs`), so its roots also read
`c1`, `c2`, `c3`, the out-of-domain point `ζ = efOf c3` among them; layer
`i` reads at `φ M (Rᵢ, i)` (`friCommitNxtC_layer`).  It costs `3 + k`
reads for `k` layers, so the slots' common `kr` is at least that.  The
link of these reads to `sudFS4T`'s challenges is by the messages' layout,
not stated as one theorem.

Not shown, and needed before this is Plonky3's FRI:
- the roots read one commitment's data, not the other commitments', which
  FRI's batched DEEP codeword reads (and, with `friCommitNxt`, not the
  earlier challenges either);
- the hash point is `(M, Rᵢ, i)`, not the full transcript.  This
  commitment's values opened at `ζ` (Plonky3 observes every commitment's
  before FRI's batching challenge and folding challenges) enter only where
  a layer returns them beside its root, as arguments of `φ`: `friCommitQCPf` reads the three earlier challenges, then the `k`
  layers, then the query seed, its layers given those challenges, the
  data and the salt, nothing reading `c4` (`runR4_dropA`, `friCommitQC_c4`,
  `friCommitQC_seed`, `friCommitQC_reads`; there the seed's point holds
  whatever the last layer returns, and the batching challenge is a first
  folding read whose layer returns no root);
- the proof's query indices `c4` are drawn before the commit phase, where
  Plonky3 samples them after it.  A strategy may draw its own after
  (`friCommitQPf`: `k` layers, then a query seed read at `φ M (R_k, k)`,
  nothing reading `c4`; `friBetas_c4`, `friCommitQ_eq`, `friCommitQ_c4`,
  `friCommitQ_seed`, `friCommitQ_reads`), but the proof's view still reads
  `c4`.  That strategy derives every query index from one value below `K4`,
  read at a point that holds the final root alone, where Plonky3 samples
  each index after observing the final polynomial and the proof of work;
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

/-- **The commit phase reading the earlier challenges first**: reads `0`,
    `1`, `2` take the first three tables at the first, second and third
    messages (the digit `M % n1`, then `M % n1 + n1 ((M / n1) % n2)`, then
    `M`), so they are the challenges `c1`, `c2`, `c3` where the messages
    nest as the protocol's do; layer `i` then reads the fourth table at
    `φ M (Rᵢ, i)`, its root a function of `c4`, those three challenges,
    the data and salt, and the folding challenges so far. -/
def friCommitNxtC {D R : Type} (n1 n2 : Nat) (layer : Nat → List Nat → D → Nat → List Nat → R) :
    Nat → Nat → D → Nat → List Nat → Nat × Nat × (Option R × Nat) :=
  fun c4 M d σ prev =>
    match prev.length with
    | 0 => (0, 0, (none, 0))
    | 1 => (1, (M / n1) % n2, (none, 1))
    | 2 => (2, M / n1, (none, 2))
    | i + 3 => (3, M / n1, (some (layer c4 (prev.reverse.take 3) d σ (prev.reverse.drop 3)), i))

theorem runR4_length {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) : ∀ k, (runR4 K1 K2 K3 K4 n1 m φ nxt H k).length = k
  | 0 => rfl
  | k + 1 => by
    show (runR4 K1 K2 K3 K4 n1 m φ nxt H k).length + 1 = k + 1
    rw [runR4_length K1 K2 K3 K4 n1 m φ nxt H k]

/-- **Its first three reads are the earlier challenges**: the first
    table at the digit, the second at `M % n1 + n1 ((M / n1) % n2)`, the
    third at `M`. -/
theorem friCommitC_first3 {D R : Type} (K1 K2 K3 K4 n1 n2 : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer : Nat → List Nat → D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 3 =
      [rget K3 M H.2.2.1, rget K2 (M % n1 + n1 * ((M / n1) % n2)) H.2.1, rget K1 (M % n1) H.1] := by
  have e0 : runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 0 = [] := rfl
  have e1 : runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 1 = [rget K1 (M % n1) H.1] := by
    show rget4 K1 K2 K3 K4 H 0 (pt4 n1 φ (M % n1) (0, 0, (none, 0))) :: [] = _
    show [rget K1 (M % n1 + n1 * 0) H.1] = _
    rw [Nat.mul_zero, Nat.add_zero]
  have e2 : runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 2 =
      [rget K2 (M % n1 + n1 * ((M / n1) % n2)) H.2.1, rget K1 (M % n1) H.1] := by
    show rget4 K1 K2 K3 K4 H (friCommitNxtC n1 n2 layer c4 M d σ (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 1)).1
      (pt4 n1 φ (M % n1) (friCommitNxtC n1 n2 layer c4 M d σ (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 1))) ::
      runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 1 = _
    rw [e1]; rfl
  show rget4 K1 K2 K3 K4 H (friCommitNxtC n1 n2 layer c4 M d σ (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 2)).1
    (pt4 n1 φ (M % n1) (friCommitNxtC n1 n2 layer c4 M d σ (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 2))) ::
    runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 layer c4 M d σ) H 2 = _
  rw [e2]
  show [rget K3 (M % n1 + n1 * (M / n1)) H.2.2.1, _, _] = _
  rw [Nat.mod_add_div]

/-- **The messages nest**: with the third message `M = m1 + n1 (a + n2 b)`
    (`m1 < n1`, `a < n2`), as `comPair` builds it, the reads' points are
    the first message `m1` and the second `m1 + n1 a`. -/
theorem msg_nest {n1 n2 m1 a b : Nat} (hm1 : m1 < n1) (ha : a < n2) :
    (m1 + n1 * (a + n2 * b)) % n1 = m1 ∧
      (m1 + n1 * (a + n2 * b)) % n1 + n1 * ((m1 + n1 * (a + n2 * b)) / n1 % n2) = m1 + n1 * a := by
  have hp : 0 < n1 := Nat.lt_of_le_of_lt (Nat.zero_le _) hm1
  have e1 : (m1 + n1 * (a + n2 * b)) % n1 = m1 := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm1]
  have e2 : (m1 + n1 * (a + n2 * b)) / n1 = a + n2 * b := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hm1, Nat.zero_add]
  refine ⟨e1, ?_⟩
  rw [e1, e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

/-- **The first three reads at the protocol's messages**: with
    `M = m1 + n1 (a + n2 b)`, `m1 < n1` and `a < n2` (the commitments in
    range, `hr1`, `hr2`), they read the first table at the first message,
    the second at the second, the third at the third. -/
theorem friCommitC_msgs {D R : Type} (K1 K2 K3 K4 n1 n2 : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer : Nat → List Nat → D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 : Nat) (d : D) (σ : Nat)
    {m1 a b : Nat} (hm1 : m1 < n1) (ha : a < n2) :
    runR4 K1 K2 K3 K4 n1 ((m1 + n1 * (a + n2 * b)) % n1) φ
        (friCommitNxtC n1 n2 layer c4 (m1 + n1 * (a + n2 * b)) d σ) H 3 =
      [rget K3 (m1 + n1 * (a + n2 * b)) H.2.2.1, rget K2 (m1 + n1 * a) H.2.1, rget K1 m1 H.1] := by
  rw [friCommitC_first3, (msg_nest (b := b) hm1 ha).2, (msg_nest (b := b) hm1 ha).1]

/-- **A layer's read**: after the three challenges and `i` layers, the
    fourth table at `φ M (Rᵢ, i)`. -/
theorem friCommitNxtC_layer {D R : Type} (n1 n2 : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer : Nat → List Nat → D → Nat → List Nat → R) (c4 M : Nat) (d : D) (σ : Nat) (prev : List Nat) (i : Nat)
    (hl : prev.length = i + 3) :
    (friCommitNxtC n1 n2 layer c4 M d σ prev).1 = 3 ∧
      pt4 n1 φ (M % n1) (friCommitNxtC n1 n2 layer c4 M d σ prev) =
        φ M (some (layer c4 (prev.reverse.take 3) d σ (prev.reverse.drop 3)), i) := by
  unfold friCommitNxtC
  rw [hl]
  refine ⟨rfl, ?_⟩
  show φ (M % n1 + n1 * (M / n1)) _ = _
  rw [Nat.mod_add_div]

/-! ### Queries drawn after the commit phase -/

/-- **A layer function blind to `c4` reads challenges blind to it.** -/
theorem friBetas_c4 {D R : Type} (K4 : Nat) (φ : Nat → R × Nat → Nat) (layer0 : D → Nat → List Nat → R)
    (H : Nat × Nat × Nat × Nat) (c4 c4' M : Nat) (d : D) (σ : Nat) :
    ∀ k, friBetas K4 φ (fun _ => layer0) H c4 M d σ k = friBetas K4 φ (fun _ => layer0) H c4' M d σ k
  | 0 => rfl
  | k + 1 => by
    show rget K4 (φ M (layer0 d σ (friBetas K4 φ (fun _ => layer0) H c4 M d σ k).reverse, k)) H.2.2.2 :: _ =
      rget K4 (φ M (layer0 d σ (friBetas K4 φ (fun _ => layer0) H c4' M d σ k).reverse, k)) H.2.2.2 :: _
    rw [friBetas_c4 K4 φ layer0 H c4 c4' M d σ k]

/-- **FRI with its queries drawn after the commit phase**: `k` layers, then
    one more read of the fourth table at `φ M (R_k, k)`, `R_k` the root
    after all `k` folding challenges, as the query seed; the layers and the
    output never read the proof's fourth challenge `c4`. -/
def friCommitQPf {D R P : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat) (layer0 : D → Nat → List Nat → R)
    (out : Nat → D → Nat → List Nat → Nat → P) : Nat → Nat → Nat → Nat → Nat → Nat → D → Nat → P :=
  friCommitPf K1 K2 K3 K4 n1 (k + 1) φ (fun _ => layer0) (fun _ M d σ l => out M d σ l.tail (l.headD 0))

/-- **Its folding challenges and query seed**: the challenges are
    `friBetas` over `k` layers; the seed is the fourth table's answer at
    `φ M (R_k, k)`, read after every root; none depends on `c4`. -/
theorem friCommitQ_eq {D R P : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat)
    (layer0 : D → Nat → List Nat → R) (out : Nat → D → Nat → List Nat → Nat → P)
    (c4 T1 T2 T3 T4 M : Nat) (d : D) (σ : Nat) :
    friCommitQPf K1 K2 K3 K4 n1 k φ layer0 out c4 T1 T2 T3 T4 M d σ =
      out M d σ (friBetas K4 φ (fun _ => layer0) (T1, T2, T3, T4) 0 M d σ k)
        (rget K4 (φ M (layer0 d σ (friBetas K4 φ (fun _ => layer0) (T1, T2, T3, T4) 0 M d σ k).reverse, k)) T4) := by
  unfold friCommitQPf
  rw [friCommitPf_eq, friBetas_c4 K4 φ layer0 _ c4 0 M d σ (k + 1)]
  rfl

/-- **Its reads**: `k + 1` of them. -/
theorem friCommitQ_reads {D R : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat)
    (layer0 : D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    (pfRdReads K1 K2 K3 K4 n1 (k + 1) φ (friCommitNxt n1 (fun _ => layer0)) H c4 M d σ).length = k + 1 :=
  pfRdReads_length _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The strategy does not read `c4`.** -/
theorem friCommitQ_c4 {D R P : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat) (layer0 : D → Nat → List Nat → R)
    (out : Nat → D → Nat → List Nat → Nat → P) (c4 c4' : Nat) :
    friCommitQPf K1 K2 K3 K4 n1 k φ layer0 out c4 = friCommitQPf K1 K2 K3 K4 n1 k φ layer0 out c4' := rfl

/-- **The newest read is the query seed**: the fourth table at
    `φ M (R_k, k)`, `R_k` the root after all `k` folding challenges. -/
theorem friCommitQ_seed {D R : Type} (K1 K2 K3 K4 n1 k : Nat) (φ : Nat → R × Nat → Nat)
    (layer0 : D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    (pfRdReads K1 K2 K3 K4 n1 (k + 1) φ (friCommitNxt n1 (fun _ => layer0)) H c4 M d σ).head? =
      some (3, φ M (layer0 d σ (friBetas K4 φ (fun _ => layer0) H 0 M d σ k).reverse, k)) := by
  unfold pfRdReads
  show some (3, pt4 n1 φ (M % n1) (friCommitNxt n1 (fun _ => layer0) c4 M d σ
      (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxt n1 (fun _ => layer0) c4 M d σ) H k))) = _
  rw [friCommit_run]
  show some (3, φ (M % n1 + n1 * (M / n1)) _) = _
  rw [Nat.mod_add_div]
  show some (3, φ M (layer0 d σ (friBetas K4 φ (fun _ => layer0) H c4 M d σ k).reverse,
    (friBetas K4 φ (fun _ => layer0) H c4 M d σ k).length)) = _
  rw [friBetas_length, friBetas_c4 K4 φ layer0 H c4 0 M d σ k]

/-! ### The earlier challenges and the opened values hashed, queries last -/

/-- A run keeps its older reads: after `a` more reads, dropping the newest
    `a` gives the run of `b`. -/
theorem runR4_dropA {W : Type} (K1 K2 K3 K4 n1 m : Nat) (φ : Nat → W → Nat) (nxt : List Nat → Nat × Nat × W)
    (H : Nat × Nat × Nat × Nat) (b : Nat) : ∀ a, (runR4 K1 K2 K3 K4 n1 m φ nxt H (b + a)).drop a = runR4 K1 K2 K3 K4 n1 m φ nxt H b
  | 0 => rfl
  | a + 1 => by
    show (_ :: runR4 K1 K2 K3 K4 n1 m φ nxt H (b + a)).drop (a + 1) = _
    rw [List.drop_succ_cons]; exact runR4_dropA K1 K2 K3 K4 n1 m φ nxt H b a

/-- **FRI in Plonky3's order, as a read strategy**: read the three earlier
    challenges, then `k` folding challenges, layer `i` hashed at
    `φ M (Rᵢ, i)`, then the query seed at `φ M (R_k, k)`, after every root;
    nothing reads `c4`.  `R` is any type, so a layer may return the values
    opened at `ζ` (a function of the earlier challenges, the data and the
    salt) beside its root, and the hash points then hold them. -/
def friCommitQCPf {D R P : Type} (K1 K2 K3 K4 n1 n2 k : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer0 : List Nat → D → Nat → List Nat → R) (out : Nat → D → Nat → List Nat → P) :
    Nat → Nat → Nat → Nat → Nat → Nat → D → Nat → P :=
  pfRd K1 K2 K3 K4 n1 (k + 4) φ (friCommitNxtC n1 n2 (fun _ => layer0)) (fun _ M d σ l => out M d σ l)

theorem friCommitQC_c4 {D R P : Type} (K1 K2 K3 K4 n1 n2 k : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer0 : List Nat → D → Nat → List Nat → R) (out : Nat → D → Nat → List Nat → P) (c4 c4' : Nat) :
    friCommitQCPf K1 K2 K3 K4 n1 n2 k φ layer0 out c4 = friCommitQCPf K1 K2 K3 K4 n1 n2 k φ layer0 out c4' := rfl

/-- **Its newest read is the query seed**: the fourth table at
    `φ M (R_k, k)`, `R_k` the layer of the three earlier challenges (the
    first table at `M % n1`, the second at `M % n1 + n1 ((M / n1) % n2)`,
    the third at `M`: the three messages when the commitments lie in range,
    `friCommitC_msgs`) and all `k` folding challenges, oldest first. -/
theorem friCommitQC_seed {D R : Type} (K1 K2 K3 K4 n1 n2 k : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer0 : List Nat → D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    let run := runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 (fun _ => layer0) c4 M d σ) H (k + 3)
    (friCommitNxtC n1 n2 (fun _ => layer0) c4 M d σ run).1 = 3 ∧
      pt4 n1 φ (M % n1) (friCommitNxtC n1 n2 (fun _ => layer0) c4 M d σ run) =
        φ M (some (layer0 [rget K1 (M % n1) H.1, rget K2 (M % n1 + n1 * ((M / n1) % n2)) H.2.1, rget K3 M H.2.2.1] d σ
          (run.reverse.drop 3)), k) := by
  intro run
  have hl : run.length = k + 3 := runR4_length _ _ _ _ _ _ _ _ _ _
  obtain ⟨h1, h2⟩ := friCommitNxtC_layer n1 n2 φ (fun _ => layer0) c4 M d σ run k hl
  refine ⟨h1, ?_⟩
  rw [h2]
  have hd : run.drop k = runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 (fun _ => layer0) c4 M d σ) H 3 := by
    show (runR4 K1 K2 K3 K4 n1 (M % n1) φ (friCommitNxtC n1 n2 (fun _ => layer0) c4 M d σ) H (k + 3)).drop k = _
    rw [Nat.add_comm k 3]; exact runR4_dropA _ _ _ _ _ _ _ _ _ 3 k
  have ht : run.reverse.take 3 =
      [rget K1 (M % n1) H.1, rget K2 (M % n1 + n1 * ((M / n1) % n2)) H.2.1, rget K3 M H.2.2.1] := by
    have hB : (run.drop k).reverse.length = 3 := by rw [List.length_reverse, List.length_drop, hl]; omega
    have this : run.reverse.take 3 = (run.drop k).reverse := by
      calc run.reverse.take 3 = ((run.take k ++ run.drop k).reverse).take 3 := by rw [List.take_append_drop]
        _ = ((run.drop k).reverse ++ (run.take k).reverse).take 3 := by rw [List.reverse_append]
        _ = (run.drop k).reverse := List.take_left' hB
    rw [this, hd, friCommitC_first3]; rfl
  rw [ht]

theorem friCommitQC_reads {D R : Type} (K1 K2 K3 K4 n1 n2 k : Nat) (φ : Nat → Option R × Nat → Nat)
    (layer0 : List Nat → D → Nat → List Nat → R) (H : Nat × Nat × Nat × Nat) (c4 M : Nat) (d : D) (σ : Nat) :
    (pfRdReads K1 K2 K3 K4 n1 (k + 4) φ (friCommitNxtC n1 n2 (fun _ => layer0)) H c4 M d σ).length = k + 4 :=
  pfRdReads_length _ _ _ _ _ _ _ _ _ _ _ _ _

end Circuit
