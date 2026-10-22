import Ski.ZK.SudEndToEnd

/-!
# Every hypothesis of the hidden-term and composed Merkle-committed bounds, met at once

`SudEndToEnd` meets every hypothesis of `sud_fs_open4ROMMC_fri` beyond the
run's.  Here the same is done for `wit_fs_open4ROMMC_fri` and
`comp_fs_open4ROMMC_fri`, so both bounds apply to every accepted run of
their circuits.

- **The heights.** At log blowup `1`, a group of height `2 ^ (t + 1)` has
  `bl = t + 1`.  The hidden-term circuit's traces are `2 ^ 10` rows, its
  fixed group `2 ^ 9`, its program table `2 ^ (tP + 1)` (`witBl tP`).  The
  composed circuit's memory and CPU traces are `2 ^ Lm` and `2 ^ R`, its
  fixed group `2 ^ 9`, its program and segment tables `2 ^ (tp + 1)`
  (`compBl (Lm - 1) (R - 1) tpP tpS`).
- **The public tables are no taller than the traces.** Each is padded
  from `2 ^ 9` and holds at most what the run holds: the hidden-term
  program table the heap, `2 ^ 10` cells (`wit_prog_tight`); the composed
  program table the heap, `2 ^ Lm` cells, and the segment table one row
  per root, at most `2 ^ R` (`comp_pub_tight`).  So the hidden-term
  witness's tallest group is a trace, `bl = 10`, and the composed one's at
  most `bl = 20`: each `_sat` theorem concludes this, and the Merkle term
  has `L = 2 ^ 11` and `L ≤ 2 ^ 21` leaves.
- **The indices.** `q = 100` indices in `bl k0 + 1`-bit blocks of the
  fourth challenge (`qIdx`), drawn over the tallest opened group `k0`
  (`topK`, which is in the list and at least as tall as each member:
  `topK_mem`, `topK_max`), each group's shift its height's difference from
  it, as Plonky3's mixed-height Merkle tree reads a shorter matrix.  Each
  group's query set has `100` points, which every height meets
  (`2 · 100 + 8 ≤ 2 ^ 9`).
- **The composed statement's heights.** `comp_fs_open4ROMMC_fri` takes the
  memory and CPU heights `2 ^ Lm` and `2 ^ R` as the statement gives them;
  the witness asks `9 ≤ Lm` and `9 ≤ R`, the floor the statement check
  sets (`logOK`).
- **The second and third commitments** are salts, as in `SudEndToEnd`
  (`comSalt_hides`, `comSalt_pf`, `comSalt_lt`).
- **The Merkle term**, one salt of four field elements, `2 ^ 64` leaf-hash
  queries: below `NSl / 2 ^ 48` at the hidden-term `2 ^ 11` leaves
  (`witStd_merkle`), below `NSl / 2 ^ 38` at every composed `L ≤ 2 ^ 21`
  (`compStd_merkle`), against `SudEndToEnd`'s `2 ^ 42` at `2 ^ 17`.

Limits, as `SudEndToEnd`'s: the salt commitments hide and bind nothing,
and one salt of four field elements stands in for Plonky3's per-matrix
salts, so these show the hypotheses consistent, not that Plonky3 meets
them.  Lean ties `R` and `Lm` to the statement text's heights by name
only.
-/

set_option autoImplicit false

namespace Circuit
open ZKF

/-- The first of the opened groups with the greatest height. -/
def topK (bl : Nat → Nat) : List Nat → Nat
  | [] => 0
  | [k] => k
  | k :: j :: ks => if bl (topK bl (j :: ks)) ≤ bl k then k else topK bl (j :: ks)

/-- **The tallest group is one of the groups.** -/
theorem topK_mem (bl : Nat → Nat) : ∀ (k : Nat) (ks : List Nat), topK bl (k :: ks) ∈ k :: ks
  | k, [] => List.mem_singleton.2 rfl
  | k, j :: ks => by
    have ih := topK_mem bl j ks
    show (if bl (topK bl (j :: ks)) ≤ bl k then k else topK bl (j :: ks)) ∈ k :: j :: ks
    split
    · exact List.mem_cons.2 (Or.inl rfl)
    · exact List.mem_cons.2 (Or.inr ih)

/-- **The tallest group is at least as tall as each group**, so every
    shift `bl (topK bl ks) - bl k` is the height difference, untruncated. -/
theorem topK_max (bl : Nat → Nat) : ∀ (ks : List Nat), ∀ i ∈ ks, bl i ≤ bl (topK bl ks)
  | [], _, h => absurd h List.not_mem_nil
  | [k], i, h => by
    have e : i = k := List.mem_singleton.1 h
    subst e; exact Nat.le_refl _
  | k :: j :: ks, i, h => by
    have ih := topK_max bl (j :: ks)
    show bl i ≤ bl (if bl (topK bl (j :: ks)) ≤ bl k then k else topK bl (j :: ks))
    rcases List.mem_cons.1 h with e | hi
    · subst e
      split
      · exact Nat.le_refl _
      · next hn => exact Nat.le_of_lt (Nat.lt_of_not_le hn)
    · split
      · next hle => exact Nat.le_trans (ih i hi) hle
      · exact ih i hi

/-- The query sets at `100` drawn indices fit every group of height at
    least `2 ^ 9`. -/
theorem friS_qIdx100_fits (bl sh : Nat → Nat) (B k c4 : Nat) {H : Nat} (hH : 2 ^ 9 ≤ H) :
    2 * (friS bl sh (fun c => qIdx B 100 c) k c4).length + 8 ≤ H := by
  rw [friS_qIdx_length]; exact Nat.le_trans (by decide) hH

theorem pow9_le {t : Nat} (ht : 8 ≤ t) : 2 ^ 9 ≤ 2 ^ (t + 1) :=
  Nat.pow_le_pow_right (by decide) (Nat.succ_le_succ ht)

/-- The hidden-term circuit's group heights at log blowup `1`: traces `2 ^ 10`,
    the fixed group `2 ^ 9`, the program table `2 ^ (tP + 1)`. -/
def witBl (tP k : Nat) : Nat :=
  if k < 4 then 10 else if k < 6 then 9 else tP + 1

theorem witBl_le {tP : Nat} (htP : tP ≤ 23) : ∀ k, witBl tP k ≤ 26 := fun k => by
  unfold witBl; split
  · decide
  · split
    · decide
    · exact Nat.le_trans (Nat.succ_le_succ htP) (by decide)

/-- The composed circuit's group heights at log blowup `1`: memory
    `2 ^ (tbM + 1)`, CPU `2 ^ (tbC + 1)`, the fixed group `2 ^ 9`, program
    `2 ^ (tpP + 1)`, segments `2 ^ (tpS + 1)`. -/
def compBl (tbM tbC tpP tpS k : Nat) : Nat :=
  if k < 2 then tbM + 1 else if k < 4 then tbC + 1 else if k < 6 then 9 else if k < 8 then tpP + 1 else tpS + 1

theorem compBl_le {tbM tbC tpP tpS : Nat} (hM : tbM ≤ 23) (hC : tbC ≤ 23) (hP : tpP ≤ 23) (hS : tpS ≤ 23) :
    ∀ k, compBl tbM tbC tpP tpS k ≤ 26 := fun k => by
  have h : ∀ a, a ≤ 23 → a + 1 ≤ 26 := fun a ha => Nat.le_trans (Nat.succ_le_succ ha) (by decide)
  unfold compBl; split
  · exact h _ hM
  · split
    · exact h _ hC
    · split
      · decide
      · split
        · exact h _ hP
        · exact h _ hS

/-- **The hidden-term Merkle hiding term**: `L = 2 ^ 11` leaves (traces of
    `2 ^ 10` rows, the tallest, at log blowup `1`), one salt of four
    BabyBear elements, `2 ^ 64` leaf-hash queries. -/
theorem witStd_merkle :
    2 ^ 48 * (2 ^ 11 * 1 * (2 ^ 64 + 2 ^ 11) + 2 * (2 ^ 11) ^ 2 * 1) < 2013265921 ^ 4 := by decide

/-- **The composed Merkle hiding term**, for every `L ≤ 2 ^ 21` leaves (the
    tallest trace `2 ^ 20` rows at log blowup `1`), one salt of four
    BabyBear elements, `2 ^ 64` leaf-hash queries; the term grows with `L`. -/
theorem compStd_merkle {L : Nat} (hL : L ≤ 2 ^ 21) :
    2 ^ 38 * (L * 1 * (2 ^ 64 + L) + 2 * L ^ 2 * 1) < 2013265921 ^ 4 :=
  Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_left _ (Nat.add_le_add
      (Nat.mul_le_mul (Nat.mul_le_mul_right 1 hL) (Nat.add_le_add_left hL _))
      (Nat.mul_le_mul_right 1 (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hL 2)))))
    (by decide)

/-- Rows padded from the floor `2 ^ 9` fit any power of two `2 ^ K ≥ 2 ^ 9`
    that holds them. -/
theorem pad9_le {α : Type} (rows : List α) (z : α) {K : Nat} (h9 : 9 ≤ K) (h24 : K ≤ 24)
    (hn : rows.length ≤ 2 ^ K) :
    (rows ++ List.replicate (pow2From 64 (2 ^ 9) rows.length - rows.length) z).length ≤ 2 ^ K := by
  have hge := pow2From_ge_n 64 (2 ^ 9) rows.length (by
    calc rows.length ≤ 2 ^ K := hn
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.le_trans h24 (by decide))
      _ ≤ 2 ^ 9 * 2 ^ 64 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos 9))
  rw [List.length_append, List.length_replicate, Nat.add_sub_of_le hge]
  exact pow2From_leK hn 64 9 h9

theorem tp_le_of_h {T : Table} {tp K : Nat} (hh : T.h = 2 ^ (tp + 1)) (hK : T.h ≤ 2 ^ K) : tp + 1 ≤ K := by
  rcases Nat.lt_or_ge K (tp + 1) with h | h
  · have h2 : 2 ^ (K + 1) ≤ 2 ^ (tp + 1) := Nat.pow_le_pow_right (by decide) h
    have h3 : 2 ^ (K + 1) = 2 ^ K + 2 ^ K := by rw [Nat.pow_succ, Nat.mul_two]
    have h4 : 0 < 2 ^ K := Nat.two_pow_pos K
    rw [hh] at hK
    exact absurd (Nat.le_trans h2 hK) (by rw [h3]; exact Nat.not_le_of_gt (Nat.lt_add_of_pos_right h4))
  · exact h

theorem witBl_le10 {tP : Nat} (h : tP + 1 ≤ 10) : ∀ k, witBl tP k ≤ 10 := fun k => by
  unfold witBl; split
  · exact Nat.le_refl _
  · split
    · decide
    · exact h

theorem compBl_le20 {tbM tbC tpP tpS : Nat} (hM : tbM + 1 ≤ 20) (hC : tbC + 1 ≤ 20) (hP : tpP + 1 ≤ 20)
    (hS : tpS + 1 ≤ 20) : ∀ k, compBl tbM tbC tpP tpS k ≤ 20 := fun k => by
  unfold compBl; split
  · exact hM
  · split
    · exact hC
    · split
      · decide
      · split
        · exact hP
        · exact hS

theorem progC_tp_ge {heap : List Cell} {N W : Nat} (hh : heap.length ≤ 2 ^ 24) : 8 ≤ progTpC heap N W := by
  obtain ⟨d, h9, _, hd⟩ := padPow ((heap.zipIdx.filter fun (_, i) => !(3 ≤ i && i < 3 + N + W)).map
    fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1])
    [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] (e := 9) (by decide)
    (by rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_zipIdx]; exact hh))
  have hh' : (progTableC heap N W).h = 2 ^ d := hd
  have ht : progTpC heap N W = d - 1 := by unfold progTpC; rw [hh', lgF_pow 64 d (by omega)]
  rw [ht]; exact Nat.le_sub_of_add_le h9

theorem segsC_tp_ge {roots : List Nat} (hr : roots.length ≤ 2 ^ 24) : 8 ≤ segTp roots := by
  obtain ⟨d, h9, _, hd⟩ := padPow (roots.zipIdx.map fun (r, j) => [ofN j, ofN r])
    ((roots.zipIdx.map fun (r, j) => [ofN j, ofN r]).headD []) (e := 9) (by decide)
    (by rw [List.length_map, List.length_zipIdx]; exact hr)
  have hh' : (segsPub roots).h = 2 ^ d := hd
  have ht : segTp roots = d - 1 := by unfold segTp; rw [hh', lgF_pow 64 d (by omega)]
  rw [ht]; exact Nat.le_sub_of_add_le h9

section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

/-- **The composed run's public tables are at least `2 ^ 9` rows**, the
    floor `padPow` pads to; `comp_pub_heights` gives the ceiling. -/
theorem comp_pub_heights_ge {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term} {W : Nat}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R) :
    8 ≤ progTpC (blankM shp W Ps).heap (BT.nleaves shp) W ∧ 8 ≤ segTp (blankRoots shp W Ps) := by
  have hRb : 2 ^ R ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
  have hLb : 2 ^ Lm ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots, hlenm, _, _⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
  have hn : 0 < Ps.length := hA.npos
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have h0 : A.take (cMachine ρ shp region Ps).heap.length = (cMachine ρ shp region Ps).heap := by
    rw [← hA.ctr0]; exact hA.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (cMachine ρ shp region Ps).heap.length = (blankM shp W Ps).heap.length := hlenm
  exact ⟨progC_tp_ge (by omega), segsC_tp_ge (by omega)⟩

/-- **The composed run's public tables are no taller than its traces**: the
    program table holds at most the heap, `2 ^ Lm` cells, and the segment
    table one row per root, at most `2 ^ R`, each padded from `2 ^ 9`. -/
theorem comp_pub_tight {R Lm : Nat} (hR : R ≤ 20) (h9R : 9 ≤ R) (h9M : 9 ≤ Lm) {shp : BT} {Ps : List Term} {W : Nat}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R) :
    progTpC (blankM shp W Ps).heap (BT.nleaves shp) W + 1 ≤ Lm ∧ segTp (blankRoots shp W Ps) + 1 ≤ R := by
  have hph := comp_pub_heights hR hrl hA hlen hLm hK
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots, hlenm, _, _⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
  have hn : 0 < Ps.length := hA.npos
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have h0 : A.take (cMachine ρ shp region Ps).heap.length = (cMachine ρ shp region Ps).heap := by
    rw [← hA.ctr0]; exact hA.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (cMachine ρ shp region Ps).heap.length = (blankM shp W Ps).heap.length := hlenm
  have hheap : (blankM shp W Ps).heap.length ≤ 2 ^ Lm := by omega
  let heap := (blankM shp W Ps).heap
  let N := BT.nleaves shp
  let roots := blankRoots shp W Ps
  have hP0 := pad9_le ((heap.zipIdx.filter fun (_, i) => !(3 ≤ i && i < 3 + N + W)).map
      fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1])
      [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] h9M (Nat.le_trans hLm (by decide))
      (by rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_zipIdx]; exact hheap))
  have hP : (progTableC heap N W).h ≤ 2 ^ Lm := hP0
  have hS0 := pad9_le (roots.zipIdx.map fun (r, j) => [ofN j, ofN r])
      ((roots.zipIdx.map fun (r, j) => [ofN j, ofN r]).headD []) h9R (Nat.le_trans hR (by decide))
      (by rw [List.length_map, List.length_zipIdx]; exact hnR ▸ hnK)
  have hS : (segsPub roots).h ≤ 2 ^ R := hS0
  exact ⟨tp_le_of_h hph.2.1 hP, tp_le_of_h hph.2.2.2 hS⟩

/-- **The hidden-term program table is no taller than the traces**: the
    statement heap fits the run's `2 ^ 10` cells, padded from `2 ^ 9`. -/
theorem wit_prog_tight {Vt x : Term} {W : Nat} {ws : List Cell} (hwl : ws.length = W) {A : List Cell} {k : Nat}
    {row : Nat → Air.Row} (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row) (hlen : A.length = 2 ^ 10) :
    progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W + 1 ≤ 10 := by
  let heap := (wMachine (List.replicate W .S) (Vt ⬝ x)).heap
  have hl : ws.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hwl]
  obtain ⟨_, _, hlenm, _, _⟩ := wMachine_public ws (List.replicate W .S) (Vt ⬝ x) hl
  have h0 : A.take (wMachine ws (Vt ⬝ x)).heap.length = (wMachine ws (Vt ⬝ x)).heap := by
    rw [← hA.ctr0]; exact hA.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (wMachine ws (Vt ⬝ x)).heap.length = heap.length := hlenm
  have hle : heap.length ≤ 2 ^ 10 := by rw [← e1, ← hlen]; omega
  have hP : (progTableW heap W).h ≤ 2 ^ 10 :=
    pad9_le ((heap.zipIdx.filter fun (_, i) => !(i < W)).map
      fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1])
      [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] (by decide) (by decide)
      (by rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_zipIdx]; exact hle))
  exact tp_le_of_h (wit_prog_height hwl hA hlen).2.2 hP

set_option maxRecDepth 100000 in
/-- **`wit_fs_open4ROMMC_fri` applies to every accepted hidden-term run**:
    its hypotheses beyond the run's met together at log blowup `1`, `100`
    queries over the tallest group, `8`-element leaf digests and salt
    commitments in the second and third slots.  The tallest group is a
    trace, `bl = 10`, so the Merkle tree has `2 ^ 11` leaves. -/
theorem wit_fs_open4ROMMC_fri_sat {V Wv Pq : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell}
    (hwf : WF ws) (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
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
    witBl (progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
      (topK (witBl (progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)) [0, 2, 4, 6]) = 10 := by
  have hph := wit_prog_height hwl hA hlen
  let tP := progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W
  have htP8 : 8 ≤ tP := hph.1
  have htP23 : tP ≤ 23 := hph.2.1
  let bl := witBl tP
  let k0 := topK bl [0, 2, 4, 6]
  let sh := fun k => bl k0 - bl k
  let idx := fun c => qIdx (bl k0 + 1) 100 c
  have _ := wit_fs_open4ROMMC_fri off hwf hwl hW8 hA hK hlen hk (tP := tP) rfl (bl := bl) (sh := sh) (idx := idx)
    qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ
    (fun c4 => friS_qIdx100_fits bl sh _ 0 c4 (Nat.pow_le_pow_right (by decide) (by decide)))
    (fun c4 => friS_qIdx100_fits bl sh _ 4 c4 (Nat.le_refl _))
    (fun c4 => friS_qIdx100_fits bl sh _ 6 c4 (pow9_le htP8))
    αd (Nat.le_refl _) fri (Nat.le_refl 4) NR2 Rb Ro
    (NSl := 2013265921 ^ 4) (L := 2 ^ (bl k0 + 1)) (KA := 2013265921 ^ 8) (sQ := 1) (kQ := kQ)
    (nQ := 2 ^ (bl k0 + 1) * (2013265921 ^ 4 * 2013265921 ^ 8)) (KQ := (2013265921 ^ 8) ^ 2 ^ (bl k0 + 1))
    (NS2 := n2) (NS3 := n3) (n2 := n2) (n3 := n3)
    (Nat.pow_pos (by decide)) (by decide) rfl (witBl_le htP23) rfl rfl
    (topK_mem bl 0 [2, 4, 6]) (Nat.sub_self _) (fun c4 => qIdx_lt _ 100 c4) rfl (h := h)
    (Mh := 2013265921 ^ 8) (Nat.pow_pos (by decide))
    (Nat.le_refl _) (Nat.le_refl 1) g nxt d1
    (fun _ σ => σ % n2)
    (fun c4 d _ => opF ((wGroups tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)
      EF.zero qv).map (·.base.S)) [1, 3, 5, 7] d)
    (comSalt_hides n2) (fun _ => comSalt_pf n2 _) (comSalt_lt hn2) d2
    (fun _ σ => σ % n3)
    (fun c4 d _ => (opQ (wSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.1,
      opCw (wSsC tP ((friS bl sh idx 0) c4) ((friS bl sh idx 4) c4) ((friS bl sh idx 6) c4)) d.2))
    (comSalt_hides n3) (fun _ => comSalt_pf n3 _) (comSalt_lt hn3) d3 (fun _ _ _ _ _ _ _ _ => true)
  exact Nat.le_antisymm (witBl_le10 (wit_prog_tight hwl hA hlen) _)
    (topK_max bl [0, 2, 4, 6] 0 (List.mem_cons.2 (Or.inl rfl)))

set_option maxRecDepth 100000 in
/-- **`comp_fs_open4ROMMC_fri` applies to every accepted composed run** whose
    statement's heights meet the statement check's floor `2 ^ 9`: its
    hypotheses beyond the run's met together at log blowup `1`, `100`
    queries over the tallest group, `8`-element leaf digests and salt
    commitments in the second and third slots.  The tallest group has
    `bl ≤ 20`, so the Merkle tree has at most `2 ^ 21` leaves. -/
theorem comp_fs_open4ROMMC_fri_sat {V Wv Pq : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20)
    (h9R : 9 ≤ R) (h9M : 9 ≤ Lm) {shp : BT} {Ps : List Term}
    {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : Nat}
    (hlwm : ∀ c, (wm c).length = Lwm) (hlwc : ∀ c, (wc c).length = Lwc)
    (hlww : ∀ c, (ww c).length = Lww) (hlwp : ∀ c, (wp c).length = Lwp)
    (hlwsg : ∀ c, (wsg c).length = Lwsg)
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
    compBl (Lm - 1) (R - 1) (progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (segTp (blankRoots shp W Ps))
      (topK (compBl (Lm - 1) (R - 1) (progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (segTp (blankRoots shp W Ps)))
        [0, 2, 4, 6, 8]) ≤ 20 := by
  have hph := comp_pub_heights hR hrl hA hlen hLm hK
  have hge := comp_pub_heights_ge hR hrl hA hlen hLm hK
  let tpP := progTpC (blankM shp W Ps).heap (BT.nleaves shp) W
  let tpS := segTp (blankRoots shp W Ps)
  let tbM := Lm - 1
  let tbC := R - 1
  have htM : tbM + 1 = Lm := Nat.sub_add_cancel (Nat.le_trans (by decide) h9M)
  have htC : tbC + 1 = R := Nat.sub_add_cancel (Nat.le_trans (by decide) h9R)
  have hM23 : tbM ≤ 23 := Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans hLm (by decide))
  have hC23 : tbC ≤ 23 := Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans hR (by decide))
  let bl := compBl tbM tbC tpP tpS
  let k0 := topK bl [0, 2, 4, 6, 8]
  let sh := fun k => bl k0 - bl k
  let idx := fun c => qIdx (bl k0 + 1) 100 c
  have _ := comp_fs_open4ROMMC_fri off hR hrl hr hA hlen hLm hK hNW htM htC (tpP := tpP) (tpS := tpS) rfl rfl
    (bl := bl) (sh := sh) (idx := idx)
    qv wm wc ww wp wsg hlwm hlwc hlww hlwp hlwsg hK2 hK4 φ hφ
    (fun c4 => friS_qIdx100_fits bl sh _ 0 c4 (by rw [htM]; exact Nat.pow_le_pow_right (by decide) h9M))
    (fun c4 => friS_qIdx100_fits bl sh _ 2 c4 (by rw [htC]; exact Nat.pow_le_pow_right (by decide) h9R))
    (fun c4 => friS_qIdx100_fits bl sh _ 4 c4 (Nat.le_refl _))
    (fun c4 => friS_qIdx100_fits bl sh _ 6 c4 (pow9_le hge.1))
    (fun c4 => friS_qIdx100_fits bl sh _ 8 c4 (pow9_le hge.2))
    αd (Nat.le_refl _) fri (Nat.le_refl 4) NR2 Rb Ro
    (NSl := 2013265921 ^ 4) (L := 2 ^ (bl k0 + 1)) (KA := 2013265921 ^ 8) (sQ := 1) (kQ := kQ)
    (nQ := 2 ^ (bl k0 + 1) * (2013265921 ^ 4 * 2013265921 ^ 8)) (KQ := (2013265921 ^ 8) ^ 2 ^ (bl k0 + 1))
    (NS2 := n2) (NS3 := n3) (n2 := n2) (n3 := n3)
    (Nat.pow_pos (by decide)) (by decide) rfl (compBl_le hM23 hC23 hph.1 hph.2.2.1)
    (topK_mem bl 0 [2, 4, 6, 8]) (Nat.sub_self _) (fun c4 => qIdx_lt _ 100 c4) rfl (h := h)
    (Mh := 2013265921 ^ 8) (Nat.pow_pos (by decide))
    (Nat.le_refl _) (Nat.le_refl 1) g nxt d1
    (fun _ σ => σ % n2)
    (fun c4 d _ => opF ((cGroups tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4)
      ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4) EF.zero qv).map (·.base.S)) [1, 3, 5, 7, 9] d)
    (comSalt_hides n2) (fun _ => comSalt_pf n2 _) (comSalt_lt hn2) d2
    (fun _ σ => σ % n3)
    (fun c4 d _ => (opQ (cSsT ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4)
        ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4)) d.1,
      opCw (cSsC tbM tbC tpP tpS ((friS bl sh idx 0) c4) ((friS bl sh idx 2) c4) ((friS bl sh idx 4) c4)
        ((friS bl sh idx 6) c4) ((friS bl sh idx 8) c4)) d.2))
    (comSalt_hides n3) (fun _ => comSalt_pf n3 _) (comSalt_lt hn3) d3 (fun _ _ _ _ _ _ _ _ => true)
  have ht := comp_pub_tight hR h9R h9M hrl hA hlen hLm hK
  exact compBl_le20 (by rw [htM]; exact hLm) (by rw [htC]; exact hR) (Nat.le_trans ht.1 hLm)
    (Nat.le_trans ht.2 hR) _

end

end Circuit
