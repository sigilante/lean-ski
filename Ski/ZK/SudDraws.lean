import Ski.ZK.FSQueryPowT
import Ski.ZK.ROMMerkleIdx

/-!
# Sudoku statements share their draws

The adaptive theorems (`FSMultiAdapt`) need the `S` statements a
distinguisher picks among to share their draws.  A Sudoku proof's draws
number `NS1 · NS · NR` salts and randomness, each with `m` table coins, `NR = sudNR · NR2`, and `sudNR`
reads the quotient tables' shapes and the AIRs' widths and lookup counts.
These are the same for every puzzle (`sudNR_eq`): the CPU and program AIRs
have constant columns and interactions, and the quotient tables' chunks,
heights and generator counts depend on the heights alone.  The program
table's height `2^(tP+1)` is the one input that follows the puzzle, and it
is the same for every puzzle too: the statement heap holds `24063 + 2c`
cells for `c` clues (`sudHeap_length`; `pbuild` allocates a cell for every
node but the slot variables, and each clue adds one conjunction), at most
`24225` for `81` clues, so the program table's `24063 + 2c - 729` public
rows pad to `2^15` (`sud_progTp`, `tP = 14`).  Two Sudoku proofs with the
same parameters, whatever their puzzles, witnesses and runs, therefore
count the same draws (`sudFS4T_sm`, `sud_sm_eq`).  A family's draws
`smPowD (fun i => (sudD … i).sm 2) n` then agree across families by
`funext` over `i`, with these hypotheses at every `i`.  `SudAdapt` rewrites
each family's `ZKBT` into the shared draws and applies `zkbT_adaptive`.
-/

set_option autoImplicit false

namespace Circuit
open ZKF Stmt Sudoku BExpr SudokuText

/-- The cells `pbuild` allocates for a term: one for every node but a
    variable below the bound. -/
def osz (b : Nat) : OTerm → Nat
  | .S => 1
  | .K => 1
  | .I => 1
  | .var x => if x < b then 0 else 1
  | .app f a => osz b f + osz b a + 1

theorem pbuild_length (b : Nat) : ∀ (h : List Cell) (t : OTerm), (pbuild b h t).1.length = h.length + osz b t
  | h, .S => by simp [pbuild, Mach.alloc, osz]
  | h, .K => by simp [pbuild, Mach.alloc, osz]
  | h, .I => by simp [pbuild, Mach.alloc, osz]
  | h, .var x => by
    unfold pbuild osz
    by_cases hx : x < b
    · simp [hx]
    · simp [hx, Mach.alloc]
  | h, .app f a => by
    show (Mach.alloc (pbuild b (pbuild b h f).1 a).1 _).1.length = _
    simp only [Mach.alloc, List.length_append, List.length_singleton]
    rw [pbuild_length b _ a, pbuild_length b h f]
    show h.length + osz b f + osz b a + 1 = h.length + (osz b f + osz b a + 1)
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]

/-- A conjunction's cells: its conjuncts' cells plus two per conjunction. -/
theorem osz_all {b : Nat} (hb : 1 < b) : ∀ (l : List BExpr), l ≠ [] →
    osz b (compile (all l)) = (l.map fun e => osz b (compile e)).sum + 2 * (l.length - 1)
  | [], h => absurd rfl h
  | [a], _ => by simp [all]
  | a :: c :: l, _ => by
    have ih := osz_all hb (c :: l) (List.cons_ne_nil _ _)
    show osz b (compile a) + osz b (compile (all (c :: l))) + 1 + osz b (.var FF) + 1 = _
    rw [ih]
    simp only [osz, FF, if_pos hb, List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- A clue's conjunct is a slot variable, allocating nothing. -/
theorem osz_clues {clues : List Clue} (hc : CluesOK clues) :
    ((clues.map fun cl => bit (cl.1, cl.2.1) (cl.2.2 - 1)).map fun e => osz 731 (compile e)).sum = 0 := by
  induction clues with
  | nil => rfl
  | cons cl cs ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, ih (fun c hc' => hc c (List.mem_cons_of_mem _ hc'))]
    obtain ⟨h1, h2, h3, h4⟩ := hc cl List.mem_cons_self
    have hlt : idx cl.1 cl.2.1 (cl.2.2 - 1) + 2 < 731 := by unfold idx; omega
    simp only [bit, compile, inSlot, osz, if_pos hlt]

set_option maxRecDepth 100000 in
/-- The fixed conjuncts' cells: `22680` in `324` conjuncts. -/
theorem osz_fixed : ((cells.map cellOne ++ (groups.flatMap fun g => nine.map (groupHas g))).map
    fun e => osz 731 (compile e)).sum = 22680 ∧
    (cells.map cellOne ++ (groups.flatMap fun g => nine.map (groupHas g))).length = 324 := by
  constructor <;> decide

theorem stmtMachine_heap (ρ : Nat → Bool) (N : Nat) (e : BExpr) (acc rej : Nat) :
    (stmtMachine ρ N e acc rej).heap = (pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1 ++ [Cell.nil] := rfl

/-- **The Sudoku statement heap's size**: `24063 + 2c` cells for `c`
    clues, whatever their digits and the inputs. -/
theorem sudHeap_length {clues : List Clue} (hc : CluesOK clues) (ρ : Nat → Bool) :
    (stmtMachine ρ 729 (sudokuExpr clues) ACC REJ).heap.length = 24063 + 2 * clues.length := by
  have hne : (cells.map cellOne ++ (groups.flatMap fun g => nine.map (groupHas g)) ++
      clues.map fun cl => bit (cl.1, cl.2.1) (cl.2.2 - 1)) ≠ [] := by
    intro e
    have := congrArg List.length e
    rw [List.length_append, osz_fixed.2] at this
    exact absurd this (by simp)
  have he := osz_all (b := 731) (by decide) _ hne
  rw [List.map_append, List.sum_append, osz_clues hc, osz_fixed.1, List.length_append, osz_fixed.2,
    List.length_map] at he
  rw [stmtMachine_heap, List.length_append, pbuild_length, slotHeap_length]
  simp only [probeTerm, osz, ACC, REJ]
  rw [show compile (sudokuExpr clues) = compile (all (cells.map cellOne ++
    (groups.flatMap fun g => nine.map (groupHas g)) ++ clues.map fun cl => bit (cl.1, cl.2.1) (cl.2.2 - 1))) from rfl, he]
  simp only [List.length_singleton, show ¬ (731 < 729 + 2) by decide, show ¬ (732 < 729 + 2) by decide, if_false]
  omega

/-- The indices a filter over `zipIdx` keeps. -/
theorem zipIdx_filter_length {α : Type} (p : Nat → Bool) : ∀ (l : List α) (n : Nat),
    ((l.zipIdx n).filter fun x => p x.2).length = ((List.range' n l.length).filter p).length
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.length_cons, List.range'_succ, List.filter_cons, List.filter_cons]
    have ih := zipIdx_filter_length p l (n + 1)
    cases p n <;> simp [ih]

set_option maxRecDepth 100000 in
/-- The public cells of a heap of `732 + m` cells: `3 + m`. -/
theorem pubCells_length (heap : List Cell) (m : Nat) (hl : heap.length = 732 + m) :
    (heap.zipIdx.filter fun x => !(3 ≤ x.2 && x.2 < 3 + 729)).length = 3 + m := by
  have e := zipIdx_filter_length (fun i => !(3 ≤ i && i < 3 + 729)) heap 0
  rw [e, hl, ← List.range'_append, List.filter_append, List.length_append]
  have h1 : ((List.range' 0 732).filter fun i => !(3 ≤ i && i < 3 + 729)).length = 3 := by decide
  have h2 : ((List.range' (0 + 732) m).filter fun i => !(3 ≤ i && i < 3 + 729)) = List.range' (0 + 732) m := by
    rw [List.filter_eq_self]
    intro i hi
    rw [List.mem_range'_1] at hi
    have : ¬ (i < 3 + 729) := by omega
    simp [this]
  rw [h1, h2, List.length_range']

theorem filter_length_mono {α : Type} (p q : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
    (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
    have ih := filter_length_mono p q l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [List.filter_cons, List.filter_cons]
    cases hp : p a <;> cases hq : q a
    · exact ih
    · simp only [if_false, if_true, Bool.false_eq_true, List.length_cons]; omega
    · exact absurd (h a List.mem_cons_self hp) (by rw [hq]; decide)
    · simp only [if_true, List.length_cons]; omega

theorem range'_filter_lt (m : Nat) : ∀ n, ((List.range' 0 n).filter fun i => decide (i < m)).length = min n m
  | 0 => by simp
  | n + 1 => by
    rw [List.range'_concat, List.filter_append, List.length_append, range'_filter_lt m n]
    simp only [List.filter_cons, List.filter_nil, Nat.zero_add, Nat.one_mul]
    by_cases h : n < m
    · rw [if_pos (decide_eq_true h), List.length_singleton]; omega
    · rw [if_neg (by simp [h]), List.length_nil]; omega

/-- **At most `81` clues**: `CluesOK` puts every clue's cell below `81`. -/
theorem cluesOf_length_le {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) : (cluesOf puzzle).length ≤ 81 := by
  unfold cluesOf at hc ⊢
  rw [List.length_map]
  have hlt : ∀ p ∈ puzzle.zipIdx, (p.1 != 0) = true → decide (p.2 < 81) = true := fun p hp hnz => by
    have := (hc _ (List.mem_map_of_mem (List.mem_filter.2 ⟨hp, hnz⟩))).1
    exact decide_eq_true (by omega)
  refine Nat.le_trans (filter_length_mono _ _ _ hlt) ?_
  have e := zipIdx_filter_length (fun i => decide (i < 81)) puzzle 0
  rw [e, range'_filter_lt]
  exact Nat.min_le_right _ _

/-- **Every Sudoku puzzle's program table has height `2^15`** (`tP = 14`):
    its `23334 + 2c` public rows, `c ≤ 81` (`cluesOf_length_le`), lie between `2^14` and `2^15`. -/
theorem sud_progTp {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle)) :
    progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap = 14 := by
  have hcl := cluesOf_length_le hc
  generalize hH : (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap = heap
  have hl := sudHeap_length hc (fun _ => false)
  rw [hH] at hl
  have hn := pubCells_length heap (23331 + 2 * (cluesOf puzzle).length) (by rw [hl]; omega)
  generalize hc' : (cluesOf puzzle).length = c at hn hcl
  obtain ⟨_, hh⟩ := progS_height (heap := heap) (by rw [hn]; omega) (by rw [hn]; omega)
  have hge := pow2From_ge_n 64 1 (3 + (23331 + 2 * c)) (by
    calc 3 + (23331 + 2 * c) ≤ 2 ^ 24 := by omega
      _ ≤ 1 * 2 ^ 64 := by rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) (by decide))
  have hle := pow2From_leK (n := 3 + (23331 + 2 * c)) (K := 15) (by omega) 64 0 (by decide)
  rw [Nat.pow_zero] at hle
  have hrows : (progTableS heap).h = pow2From 64 1 (3 + (23331 + 2 * c)) := by
    show (progRowsS heap).length = _
    unfold progRowsS
    simp only [List.length_append, List.length_map, List.length_replicate]
    rw [hn]
    omega
  rw [hrows] at hh
  rw [hh] at hge hle
  generalize progTp heap = t at hge hle ⊢
  rcases Nat.lt_or_ge (t + 1) 15 with h | h
  · have : 2 ^ (t + 1) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by decide) (by omega)
    have : (2 : Nat) ^ 14 = 16384 := rfl
    omega
  · rcases Nat.lt_or_ge (t + 1) 16 with h' | h'
    · omega
    · have : 2 ^ 16 ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by decide) h'
      have : (2 : Nat) ^ 16 = 65536 := rfl
      have : (2 : Nat) ^ 15 = 32768 := rfl
      omega

theorem sudKs_eq (hd0 stk0 ctr0 : Nat) (heap : List Cell) (hd1 stk1 ctr1 : Nat) (heap1 : List Cell) :
    sudKs hd0 stk0 ctr0 heap = sudKs hd1 stk1 ctr1 heap1 := by
  simp only [sudKs, cpuAirS, progAirS, corpusLs]

theorem sudNR_eq (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table)
    (hd1 stk1 ctr1 : Nat) (heap1 : List Cell) (C1 Mm1 Wt1 : Table) (tp : Nat)
    (S16 S10 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) :
    sudNR off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw =
      sudNR off hd1 stk1 ctr1 heap1 C1 Mm1 Wt1 tp S16 S10 SP ζ qv wm wc ww wp ncw := by
  have hcr : tabsCr ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst) =
      tabsCr ((sudTs off hd1 stk1 ctr1 heap1 C1 Mm1 Wt1 tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst) := by
    simp only [sudTs, List.map, tabsCr, QTab.crs, QTab.n, bbTab, airQTabG, List.length_map]
  have hcw : tabsCw ncw ((sudTs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst) =
      tabsCw ncw ((sudTs off hd1 stk1 ctr1 heap1 C1 Mm1 Wt1 tp S16 S10 SP ζ qv wm wc ww wp).map Prod.fst) := by
    simp only [sudTs, List.map, tabsCw, QTab.cws, QTab.n, bbTab, airQTabG]
  unfold sudNR friN1 friN2
  rw [sudKs_eq hd0 stk0 ctr0 heap hd1 stk1 ctr1 heap1, hcr, hcw]
set_option maxRecDepth 100000 in
/-- **Sudoku statements share their draws**: two Sudoku proofs, whatever
    their puzzles, witnesses and runs, count the same draws when their
    program tables share the height `tP` and the parameters the count reads
    agree (`sudNR_eq`). -/
theorem sudFS4T_sm {V Wv P1 P2 P3 P1' P2' P3' : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) (puzzle' : List Nat) (A' : List Cell) (k' : Nat) (row' : Nat → Air.Row) (tP' : Nat) (S16' : Nat → List F) (S10' : Nat → List F) (SP' : Nat → List F) (qv' : EF → EF → List EF → F → List F → List F → List EF) (wm' : Nat → List (EF → EF → List F)) (wc' : Nat → List (EF → EF → List F)) (ww' : Nat → List (EF → EF → List F)) (wp' : Nat → List (EF → EF → List F)) (K2' : Nat) (K4' : Nat) (φ' : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4' : Nat) (ncw' : Nat) (αd' : Nat → EF) (B4' : Nat) (fri' : Nat → EF → EF → List (EF → EF) → V) (NR2' : Nat) (Rb' : Nat → EF → EF → Nat → List (EF → EF)) (Ro' : Nat → EF → EF → Nat → Wv) (NS1' : Nat) (NS2' : Nat) (NS3' : Nat) (n1' : Nat) (n2' : Nat) (n3' : Nat) (Com1' : List (List (List F)) → Nat → Nat) (Pf1' : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1') (Com2' : List (List (List F)) → Nat → Nat) (Pf2' : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2') (Com3' : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3' : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3') (hqr' : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    (htP : tP' = tP) (hS16 : S16' 0 = S16 0) (hS10 : S10' 0 = S10 0) (hSP : SP' 0 = SP 0) (hqv : qv' = qv) (hwm : wm' 0 = wm 0) (hwc : wc' 0 = wc 0) (hww : ww' 0 = ww 0) (hwp : wp' 0 = wp 0) (hncw : ncw' = ncw) (hNR2 : NR2' = NR2) (hNS1 : NS1' = NS1) (hNS2 : NS2' = NS2) (hNS3 : NS3' = NS3) (m : Nat) :
    (sudFS4T (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm m =
      (sudFS4T (V := V) (Wv := Wv) (P1 := P1') (P2 := P2') (P3 := P3') off puzzle' A' k' row' tP' S16' S10' SP' qv' wm' wc' ww' wp' K2' K4' φ' N4' ncw' αd' B4' fri' NR2' Rb' Ro' NS1' NS2' NS3' n1' n2' n3' Com1' Pf1' Com2' Pf2' Com3' Pf3' hqr').sm m := by
  unfold FS4DT.sm
  simp only [sudFS4T]
  rw [htP, hS16, hS10, hSP, hqv, hwm, hwc, hww, hwp, hncw, hNR2, hNS1, hNS2, hNS3,
    sudNR_eq off _ _ _ _ _ _ _ _ _ _ _ _ _ _ tP]

set_option maxRecDepth 100000 in
/-- **Any two Sudoku puzzles' proofs share their draws**, the program
    tables' height following from the puzzles (`sud_progTp`). -/
theorem sud_sm_eq {V Wv P1 P2 P3 P1' P2' P3' : Type} (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (K2 : Nat) (K4 : Nat) (φ : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4 : Nat) (ncw : Nat) (αd : Nat → EF) (B4 : Nat) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) (NS1 : Nat) (NS2 : Nat) (NS3 : Nat) (n1 : Nat) (n2 : Nat) (n3 : Nat) (Com1 : List (List (List F)) → Nat → Nat) (Pf1 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1) (Com2 : List (List (List F)) → Nat → Nat) (Pf2 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2) (Com3 : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hqr : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool) (puzzle' : List Nat) (A' : List Cell) (k' : Nat) (row' : Nat → Air.Row) (tP' : Nat) (S16' : Nat → List F) (S10' : Nat → List F) (SP' : Nat → List F) (qv' : EF → EF → List EF → F → List F → List F → List EF) (wm' : Nat → List (EF → EF → List F)) (wc' : Nat → List (EF → EF → List F)) (ww' : Nat → List (EF → EF → List F)) (wp' : Nat → List (EF → EF → List F)) (K2' : Nat) (K4' : Nat) (φ' : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (N4' : Nat) (ncw' : Nat) (αd' : Nat → EF) (B4' : Nat) (fri' : Nat → EF → EF → List (EF → EF) → V) (NR2' : Nat) (Rb' : Nat → EF → EF → Nat → List (EF → EF)) (Ro' : Nat → EF → EF → Nat → Wv) (NS1' : Nat) (NS2' : Nat) (NS3' : Nat) (n1' : Nat) (n2' : Nat) (n3' : Nat) (Com1' : List (List (List F)) → Nat → Nat) (Pf1' : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P1') (Com2' : List (List (List F)) → Nat → Nat) (Pf2' : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List F)) → Nat → P2') (Com3' : List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3' : Nat → Nat → Nat → Nat → Nat → Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3') (hqr' : Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Nat → Tup) → Bool)
    (hc : CluesOK (cluesOf puzzle))
    (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    (hc' : CluesOK (cluesOf puzzle'))
    (htp' : tP' = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle')) ACC REJ).heap)
    (hS16 : S16' 0 = S16 0) (hS10 : S10' 0 = S10 0) (hSP : SP' 0 = SP 0) (hqv : qv' = qv) (hwm : wm' 0 = wm 0) (hwc : wc' 0 = wc 0) (hww : ww' 0 = ww 0) (hwp : wp' 0 = wp 0) (hncw : ncw' = ncw) (hNR2 : NR2' = NR2) (hNS1 : NS1' = NS1) (hNS2 : NS2' = NS2) (hNS3 : NS3' = NS3) (m : Nat) :
    (sudFS4T (V := V) (Wv := Wv) (P1 := P1) (P2 := P2) (P3 := P3) off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr).sm m =
      (sudFS4T (V := V) (Wv := Wv) (P1 := P1') (P2 := P2') (P3 := P3') off puzzle' A' k' row' tP' S16' S10' SP' qv' wm' wc' ww' wp' K2' K4' φ' N4' ncw' αd' B4' fri' NR2' Rb' Ro' NS1' NS2' NS3' n1' n2' n3' Com1' Pf1' Com2' Pf2' Com3' Pf3' hqr').sm m :=
  sudFS4T_sm off puzzle A k row tP S16 S10 SP qv wm wc ww wp K2 K4 φ N4 ncw αd B4 fri NR2 Rb Ro NS1 NS2 NS3 n1 n2 n3 Com1 Pf1 Com2 Pf2 Com3 Pf3 hqr puzzle' A' k' row' tP' S16' S10' SP' qv' wm' wc' ww' wp' K2' K4' φ' N4' ncw' αd' B4' fri' NR2' Rb' Ro' NS1' NS2' NS3' n1' n2' n3' Com1' Pf1' Com2' Pf2' Com3' Pf3' hqr' (by rw [htp, htp', sud_progTp hc, sud_progTp hc']) hS16 hS10 hSP hqv hwm hwc hww hwp hncw hNR2 hNS1 hNS2 hNS3 m

end Circuit
