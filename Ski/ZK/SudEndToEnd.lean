import Ski.ZK.ROMMerkleIdxC
import Ski.ZK.SudDraws

/-!
# Every hypothesis of a Merkle-committed Sudoku bound, met at once

`sud_fs_open4ROMMC_fri` bounds one Sudoku proof whose first commitment is
a salted Merkle tree over the oracle, its leaves opened at FRI's query
indices.  Its hypotheses fall in two kinds: the run's (`hc`, `hA`, `hacc`,
`hlen`, `hk`), which say the statement is true, and the rest.  Here every
hypothesis of the second kind is met together, at Plonky3's heights, so
the bound applies to every accepted Sudoku run.

- **The heights and indices.** The program table has `tP = 14`
  (`sud_progTp`); the groups' log heights are `sudBl 14 1` (log blowup `1`),
  and the `q = 100` query indices are drawn from the fourth challenge in
  `bl 0 + 1 = 17`-bit blocks (`qIdx`).  `qIdx_fri_conds` meets the index
  and size conditions, `sudBl` stays below `26`, and
  `L = 2 ^ 17` leaves.
- **The second and third commitments.** A salt modulo `n` hides any data
  (`comSalt_hides`); an opening whose output is the opened values meets
  `ComPfHides` beside it (`comSalt_pf`); the commitment stays below `n`
  (`comSalt_lt`).
- **The composite.** `sud_fs_open4ROMMC_fri_sat` applies
  `sud_fs_open4ROMMC_fri` with all of these, the leaf table's answers and
  the leaf hash's values `8`-element digests (`KA = Mh = p ^ 8`), and the
  leaf hash and distinguisher strategy left free; the event is fixed, as
  it is no hypothesis.  It elaborates, so the hypotheses are jointly
  satisfiable.
- **The Merkle term.** At `L = 2 ^ 17`, one salt of four field elements
  (`NSl = p ^ 4`), `sQ = 1` and `kQ = 2 ^ 64` leaf-hash queries, the
  hiding term `L sQ (kQ + L) + 2 L² sQ` stays below `NSl / 2 ^ 42`
  (`sudStd_merkle`).

Limits.  The second and third commitments are salts: they hide and bind
nothing, where Plonky3 commits by Merkle trees; their openings output the
opened values alone, where Plonky3's carry Merkle paths and FRI's layers
(`FriProof` states why Plonky3's FRI does not meet the hiding premise).
One salt of four field elements per leaf stands in for Plonky3's
per-matrix salts.  So this shows the hypotheses consistent, not that
Plonky3 meets them.  The
bound's other terms, the non-generic count `B4` and the PCS error at the
run, are left as the theorem states them; no accepted run is built here,
since the kernel cannot replay `2 ^ 16` rows without `native_decide`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- **A commitment that is its salt modulo `n` hides any data.** -/
theorem comSalt_hides {D : Type} (n : Nat) : ComHides n (fun (_ : D) σ => σ % n) :=
  fun _ _ _ => rfl

/-- **An opening that outputs the opened values hides the rest** beside
    the salt commitment. -/
theorem comSalt_pf {D O : Type} (n : Nat) (op : D → O) :
    ComPfHides n (fun (_ : D) σ => σ % n) (fun d _ => op d) op := by
  intro d d' hop E
  exact sumTo_congr _ (fun σ _ => by show indB (E (σ % n) (op d)) = indB (E (σ % n) (op d')); rw [hop])

/-- The salt commitment stays below `n`. -/
theorem comSalt_lt {D : Type} {n : Nat} (hn : 0 < n) : ∀ (_ : D) σ, σ % n < n :=
  fun _ σ => Nat.mod_lt σ hn

/-- `sudBl 14 1` stays below `26`. -/
theorem sudBl_std : ∀ k, sudBl 14 1 k ≤ 26 := fun k => by
  unfold sudBl; split
  · decide
  · split <;> decide

/-- **The Merkle hiding term at Plonky3's sizes**: `L = 2 ^ 17` leaves, one
    salt of four BabyBear elements, `2 ^ 64` leaf-hash queries. -/
theorem sudStd_merkle :
    2 ^ 42 * (2 ^ 17 * 1 * (2 ^ 64 + 2 ^ 17) + 2 * (2 ^ 17) ^ 2 * 1) < 2013265921 ^ 4 := by decide

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
/-- **`sud_fs_open4ROMMC_fri` applies to every accepted Sudoku run**: its
    hypotheses beyond the run's met together at log blowup `1`, `100`
    queries, `8`-element leaf digests and salt commitments in the second
    and third slots. -/
theorem sud_fs_open4ROMMC_fri_sat {V Wv Pq : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : Nat}
    (hlwm : ∀ c, (wm c).length = Lwm) (hlwc : ∀ c, (wc c).length = Lwc)
    (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat)
    {N4 : Nat} (hφ : ∀ m w, φ m w < N4) (αd : Nat → EF)
    (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat)
    (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv)
    {n2 n3 : Nat} (hn2 : 0 < n2) (hn3 : 0 < n3)
    (h : List (List F) → Nat) (kQ : Nat)
    (g : List (List (List F)) → List Nat → Pq) (nxt : Pq → Nat → List Nat → Nat)
    (d1 : List (List (List F))) (d2 : List (List (List F)))
    (d3 : List (List (List (List F))) × List (List (List F))) :
    True := by
  have htp := (sud_progTp hc).symm
  let bl := sudBl 14 1
  let sh := fun k => sudBl 14 1 0 - sudBl 14 1 k
  let idx := fun c => qIdx (bl 0 + 1) 100 c
  have c10 := qIdx_fri_conds (bl := bl) (sh := sh) (L := 2 ^ (bl 0 + 1)) (q := 100) (H := 2 ^ 10) rfl (by decide)
  have cP := qIdx_fri_conds (bl := bl) (sh := sh) (L := 2 ^ (bl 0 + 1)) (q := 100) (H := 2 ^ (14 + 1)) rfl (by decide)
  have c16 := qIdx_fri_conds (bl := bl) (sh := sh) (L := 2 ^ (bl 0 + 1)) (q := 100) (H := 2 ^ 16) rfl (by decide)
  have _ := sud_fs_open4ROMMC_fri off hc hA hacc hlen hk htp (bl := bl) (sh := sh) (idx := idx) qv wm wc ww wp
    hlwm hlwc hlww hlwp hK2 hK4 φ hφ (fun c4 => c16.2 0 c4) (fun c4 => c10.2 4 c4) (fun c4 => cP.2 6 c4)
    αd (Nat.le_refl _) fri (Nat.le_refl 4) NR2 Rb Ro
    (NSl := 2013265921 ^ 4) (L := 2 ^ (bl 0 + 1)) (KA := 2013265921 ^ 8) (sQ := 1) (kQ := kQ)
    (nQ := 2 ^ (bl 0 + 1) * (2013265921 ^ 4 * 2013265921 ^ 8)) (KQ := (2013265921 ^ 8) ^ 2 ^ (bl 0 + 1))
    (NS2 := n2) (NS3 := n3)
    (n2 := n2) (n3 := n3)
    (Nat.pow_pos (by decide)) (by decide) rfl sudBl_std rfl rfl (Nat.sub_self _) c10.1 rfl (h := h)
    (Mh := 2013265921 ^ 8) (Nat.pow_pos (by decide))
    (Nat.le_refl _) (Nat.le_refl 1) g nxt d1
    (fun _ σ => σ % n2)
    (fun c4 d _ => opF ((sudGroups 14 ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)
      EF.zero qv).map (·.base.S)) [1, 3, 5, 7] d)
    (comSalt_hides n2) (fun _ => comSalt_pf n2 _) (comSalt_lt hn2) d2
    (fun _ σ => σ % n3)
    (fun c4 d _ => (opQ (sudSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.1,
      opCw (sudSsC 14 ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.2))
    (comSalt_hides n3) (fun _ => comSalt_pf n3 _) (comSalt_lt hn3) d3 (fun _ _ _ _ _ _ _ _ => true)
  trivial

end

end Circuit
