import Ski.ZK.SudInst
import Ski.ZK.WitRun

/-!
# The hidden-term proof's composed hiding PCS

The hidden-term circuit commits four tables.  The memory, CPU and witness
tables are private, blinded by the edge tuples (`wMemT`, `wCpuT`,
`wWitT`); the program table is public.  Each is committed as two trace
groups, its main and permutation columns: eight groups, heights `2^10`,
`2^10`, `2^9` and the program's `2^(tp+1)` (`wGroups`, `wCols`), each
table with a quotient table of Plonky3's four chunks (`wTs`), as for the
Sudoku proof (`Ski/ZK/SudInst.lean`).

The program table's height is a power of two set by the statement:
`progW_height` and `wit_prog_height` give `2^(progTpW + 1)` rows, at
least the `2^9` floor, for every run over `2^10` cells.

`wit_pcs`: that PCS meets `PCSCloseN` with `ε = 0` over the hidden-term
transcript's values.  `wit_hiding`: for an accepting run of the
hidden-term statement, `wit_transcriptG` over that PCS, its PCS term zero.

Left out of the view and assumed: as for the Sudoku proof.
-/

namespace Circuit

open ZKF B Air Wit Mach

-- ---------------------------------------------------------------------------
-- A padded table's height
-- ---------------------------------------------------------------------------

/-- **Padding to `pow2From` gives a power of two**: rows padded from the
    floor `2^e`, `e ≤ 24`, number `2^d` with `e ≤ d ≤ 24`, when there
    are at most `2^24` of them. -/
theorem padPow {α : Type} (rows : List α) (z : α) {e : Nat} (he24 : e ≤ 24) (hn : rows.length ≤ 2 ^ 24) :
    ∃ d, e ≤ d ∧ d ≤ 24 ∧
      (rows ++ List.replicate (pow2From 64 (2 ^ e) rows.length - rows.length) z).length = 2 ^ d := by
  have hge := pow2From_ge_n 64 (2 ^ e) rows.length (by
    calc rows.length ≤ 2 ^ 24 := hn
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
      _ ≤ 2 ^ e * 2 ^ 64 := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos e))
  have hle := pow2From_le hn 64 e he24
  obtain ⟨d, hd⟩ := pow2From_pow 64 e rows.length
  rw [hd] at hge hle
  refine ⟨e + d, Nat.le_add_right _ _, ?_, ?_⟩
  · rcases Nat.lt_or_ge (e + d) 25 with h | h
    · omega
    · have : 2 ^ 25 ≤ 2 ^ (e + d) := Nat.pow_le_pow_right (by decide) h
      have : (2 : Nat) ^ 25 = 2 * 2 ^ 24 := rfl
      omega
  · rw [List.length_append, List.length_replicate, hd]; omega

/-- The hidden-term program table's height is `2^(progTpW + 1)`. -/
def progTpW (heap : List Cell) (W : Nat) : Nat := lgF 64 (progTableW heap W).h - 1

/-- **The hidden-term program table's height**: `2^(progTpW + 1)` rows,
    `8 ≤ progTpW ≤ 23`, for a heap of at most `2^24` cells. -/
theorem progW_height {heap : List Cell} {W : Nat} (hh : heap.length ≤ 2 ^ 24) :
    8 ≤ progTpW heap W ∧ progTpW heap W ≤ 23 ∧ (progTableW heap W).h = 2 ^ (progTpW heap W + 1) := by
  obtain ⟨d, h9, h24, hd⟩ := padPow ((heap.zipIdx.filter fun (_, i) => !(i < W)).map
    fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1])
    [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] (e := 9) (by decide)
    (by rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_zipIdx]; exact hh))
  have hh' : (progTableW heap W).h = 2 ^ d := hd
  have ht : progTpW heap W = d - 1 := by unfold progTpW; rw [hh', lgF_pow 64 d (by omega)]
  refine ⟨by omega, by omega, ?_⟩
  rw [ht, hh', Nat.sub_add_cancel (by omega)]

/-- **The hidden-term program table's height**, for a run from the
    witness machine over `2^10` cells. -/
theorem wit_prog_height {V x : Term} {W : Nat} {ws : List Cell} (hwl : ws.length = W) {A : List Cell} {k : Nat}
    {row : Nat → Air.Row} (hA : AcceptsFrom A (wMachine ws (V ⬝ x)) k row) (hlen : A.length = 2 ^ 10) :
    let heap := (wMachine (List.replicate W .S) (V ⬝ x)).heap
    8 ≤ progTpW heap W ∧ progTpW heap W ≤ 23 ∧ (progTableW heap W).h = 2 ^ (progTpW heap W + 1) := by
  intro heap
  have hl : ws.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hwl]
  obtain ⟨_, _, hlenm, _, _⟩ := wMachine_public ws (List.replicate W .S) (V ⬝ x) hl
  have h0 : A.take (wMachine ws (V ⬝ x)).heap.length = (wMachine ws (V ⬝ x)).heap := by
    rw [← hA.ctr0]; exact hA.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (wMachine ws (V ⬝ x)).heap.length = heap.length := hlenm
  have hle : heap.length ≤ 2 ^ 10 := by rw [← e1, ← hlen]; omega
  have h24 : 2 ^ 10 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by decide)
  exact progW_height (by omega)

-- ---------------------------------------------------------------------------
-- The groups, the columns and the quotient tables
-- ---------------------------------------------------------------------------

/-- The blinded private tables. -/
def wMemT (Mm : Table) (t : Nat → Tup) : Table := Mm.setBlind 5 (t 0)
def wCpuT (C : Table) (t : Nat → Tup) : Table := (C.setBlind BLA (t 1)).setBlind BLB (t 0)
def wWitT (Wt : Table) (t : Nat → Tup) : Table := Wt.setBlind WT_BLIND (t 1)

/-- The eight trace groups: memory, CPU (`2^10` rows), witness (`2^9`)
    and program (`2^(tp+1)`), main and permutation each. -/
def wGroups (tp : Nat) (S10 S9 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF) :
    List QGroup :=
  [bbGroup 9 S10 ζ qv, bbGroup 9 S10 ζ qv, bbGroup 9 S10 ζ qv, bbGroup 9 S10 ζ qv, bbGroup 8 S9 ζ qv,
   bbGroup 8 S9 ζ qv, bbGroup tp SP ζ qv, bbGroup tp SP ζ qv]

/-- The committed columns: each blinded table's main and permutation
    columns, and the program table's. -/
def wCols (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table)
    (t : Nat → Tup) (α β : EF) : List (List (List F)) :=
  [mainCols (wMemT Mm t) memAirC.width,
   permCols (wMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC),
   mainCols (wCpuT C t) (cpuAirW hd0 stk0 ctr0).width,
   permCols (wCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirW hd0 stk0 ctr0)) β (corpusLs (cpuAirW hd0 stk0 ctr0)),
   mainCols (wWitT Wt t) (witAirW W).width,
   permCols (wWitT Wt t) (busAlphas (prefixOf α (off β)) (witAirW W)) β (corpusLs (witAirW W)),
   mainCols (progTableW heap W) (progAirW heap W).width,
   permCols (progTableW heap W) (busAlphas (prefixOf α (off β)) (progAirW heap W)) β (corpusLs (progAirW heap W))]

/-- The column counts. -/
def wKs (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) : List Nat :=
  [memAirC.width, 4 * ((corpusLs memAirC).length + 1), (cpuAirW hd0 stk0 ctr0).width,
   4 * ((corpusLs (cpuAirW hd0 stk0 ctr0)).length + 1), (witAirW W).width, 4 * ((corpusLs (witAirW W)).length + 1),
   (progAirW heap W).width, 4 * ((corpusLs (progAirW heap W)).length + 1)]

/-- **The committed columns fit the groups**, when the tables have the
    groups' heights. -/
theorem wCols_shaped (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) {heap : List Cell} {W : Nat} {C Mm Wt : Table}
    {tp : Nat} (hC : C.h = 2 ^ 10) (hM : Mm.h = 2 ^ 10) (hW : Wt.h = 2 ^ 9)
    (hPg : (progTableW heap W).h = 2 ^ (tp + 1)) (S10 S9 SP : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (t : Nat → Tup) (α β : EF) :
    Shaped ((wGroups tp S10 S9 SP ζ qv).map QGroup.ext) (wCols off hd0 stk0 ctr0 heap W C Mm Wt t α β) ∧
      (wCols off hd0 stk0 ctr0 heap W C Mm Wt t α β).map List.length = wKs hd0 stk0 ctr0 heap W := by
  have m1 := mainCols_shape (wMemT Mm t) memAirC.width
  have p1 := permCols_shape (wMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC)
  have m2 := mainCols_shape (wCpuT C t) (cpuAirW hd0 stk0 ctr0).width
  have p2 := permCols_shape (wCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirW hd0 stk0 ctr0)) β
    (corpusLs (cpuAirW hd0 stk0 ctr0))
  have m3 := mainCols_shape (wWitT Wt t) (witAirW W).width
  have p3 := permCols_shape (wWitT Wt t) (busAlphas (prefixOf α (off β)) (witAirW W)) β (corpusLs (witAirW W))
  have m4 := mainCols_shape (progTableW heap W) (progAirW heap W).width
  have p4 := permCols_shape (progTableW heap W) (busAlphas (prefixOf α (off β)) (progAirW heap W)) β
    (corpusLs (progAirW heap W))
  have hMh : (wMemT Mm t).h = 2 ^ (9 + 1) := hM
  have hCh : (wCpuT C t).h = 2 ^ (9 + 1) := hC
  have hWh : (wWitT Wt t).h = 2 ^ (8 + 1) := hW
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, fun c hc => ?_, trivial⟩, ?_⟩
  · rw [m1.2 c hc, hMh]; rfl
  · rw [p1.2 c hc, hMh]; rfl
  · rw [m2.2 c hc, hCh]; rfl
  · rw [p2.2 c hc, hCh]; rfl
  · rw [m3.2 c hc, hWh]; rfl
  · rw [p3.2 c hc, hWh]; rfl
  · rw [m4.2 c hc, hPg]; rfl
  · rw [p4.2 c hc, hPg]; rfl
  · show [_, _, _, _, _, _, _, _] = _
    rw [m1.1, p1.1, m2.1, p2.1, m3.1, p3.1, m4.1, p4.1]; rfl

/-- The hidden-term program table's terminal: public, from the challenges. -/
def progTmW (off : EF → String → EF) (heap : List Cell) (W : Nat) : EF → EF → List EF → EF :=
  fun α β _ => terminal (prefixOf α (off β)) β (progAirW heap W) (progTableW heap W)

/-- The transcript's tables: the blinded private tables and the program. -/
def wTabs (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table) (t : Nat → Tup) :
    List (AirD × Table) :=
  witTables hd0 stk0 ctr0 heap W (wCpuT C t) (wMemT Mm t) (progTableW heap W) (wWitT Wt t)

/-- **The hidden-term proof's four quotient tables**, memory, CPU, witness
    and program, with their data. -/
def wTs (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table) (tp : Nat)
    (S10 S9 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) :
    List (QTab × ((Nat → Tup) → EF → EF → List F → List (List (List F) × List F))) :=
  let tv := fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t
  let qs := wGroups tp S10 S9 SP ζ qv
  let cols := wCols off hd0 stk0 ctr0 heap W C Mm Wt
  let tabs := wTabs hd0 stk0 ctr0 heap W C Mm Wt
  [(bbTab off memAirC (tvAt 0) 9 (2 ^ 10 - 1) Mm 0 1 S10 ζ wm,
     bbData off tv memAirC (tvAt 0) 9 (2 ^ 10 - 1) Mm 0 1 S10 ζ wm qs cols tabs),
   (bbTab off (cpuAirW hd0 stk0 ctr0) (tvAt 1) 9 (2 ^ 10 - 1) C 2 3 S10 ζ wc,
     bbData off tv (cpuAirW hd0 stk0 ctr0) (tvAt 1) 9 (2 ^ 10 - 1) C 2 3 S10 ζ wc qs cols tabs),
   (bbTab off (witAirW W) (tvAt 2) 8 (2 ^ 9 - 1) Wt 4 5 S9 ζ ww,
     bbData off tv (witAirW W) (tvAt 2) 8 (2 ^ 9 - 1) Wt 4 5 S9 ζ ww qs cols tabs),
   (bbTab off (progAirW heap W) (progTmW off heap W) tp (2 ^ (tp + 1) - 1) (progTableW heap W) 6 7 SP ζ wp,
     bbData off tv (progAirW heap W) (progTmW off heap W) tp (2 ^ (tp + 1) - 1) (progTableW heap W) 6 7 SP ζ wp
       qs cols tabs)]

-- ---------------------------------------------------------------------------
-- The hidden-term proof's PCS hides
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
theorem wit_airs_P3 (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) :
    AirP3 memAirC = true ∧ AirP3 (cpuAirW hd0 stk0 ctr0) = true ∧ AirP3 (witAirW W) = true ∧
      AirP3 (progAirW heap W) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- **The hidden-term proof's composed hiding PCS hides exactly**: with the
    run's tables meeting `Sat` at the heights `2^10`, `2^10`, `2^9`, the
    program table at `2^(tp+1)` with `tp ≤ 24`, the query points off each
    trace domain, `ζ` generating the extension and the FRI challenge `αb`
    generic, the PCS whose view is every group's openings, every quotient
    table's chunks, every codeword and FRI meets `PCSCloseN` with
    `ε = 0`, over the hidden-term transcript's values. -/
theorem wit_pcs {V : Type} (off : EF → String → EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat}
    {C Mm Wt : Table}
    (hsC : Sat (cpuAirW hd0 stk0 ctr0) C) (hsM : Sat memAirC Mm) (hsW : Sat (witAirW W) Wt)
    (hC : C.h = 2 ^ 10) (hM : Mm.h = 2 ^ 10) (hW : Wt.h = 2 ^ 9)
    {tp : Nat} (htp : tp ≤ 24) (hPg : (progTableW heap W).h = 2 ^ (tp + 1))
    {S10 S9 SP : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tp + 1)) (2 ^ (tp + 1)))
    (hsz10 : 2 * S10.length + 8 ≤ 2 ^ 10) (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tp + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    let tv := fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t
    let Ts := wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp
    let qs := wGroups tp S10 S9 SP ζ qv
    PCSCloseN off (P ^ (friN1 qs (wKs hd0 stk0 ctr0 heap W) (Ts.map Prod.fst) + friN2 qs (Ts.map Prod.fst) ncw)) tv
      (pcsFri off tv qs (wKs hd0 stk0 ctr0 heap W) (wCols off hd0 stk0 ctr0 heap W C Mm Wt) (Ts.map Prod.fst)
        (fun t α β ms => Ts.map fun p => p.2 t α β ms) ncw αb fri)
      (psimFri qs (wKs hd0 stk0 ctr0 heap W) (Ts.map Prod.fst) ncw αb fri) 0 := by
  intro tv Ts qs
  obtain ⟨_, _, b3, b4, _, _, b7, _, b9, _⟩ := blind_ok hd0 stk0 ctr0 0 0 0 W
  obtain ⟨pM, pC, pW, pP⟩ := wit_airs_P3 hd0 stk0 ctr0 heap W
  have hS4 : S9.length + 4 ≤ 2 ^ 9 - 1 + 1 := by omega
  have hS4' : S10.length + 4 ≤ 2 ^ 10 - 1 + 1 := by omega
  have hpos : 1 ≤ 2 ^ (tp + 1) := Nat.one_le_two_pow
  have hmP : 2 ^ (tp + 1) - 1 + 1 = 2 ^ (tp + 1) := Nat.sub_add_cancel hpos
  have hS4P : SP.length + 4 ≤ 2 ^ (tp + 1) - 1 + 1 := by rw [hmP]; omega
  have hm10 : 2 ^ 10 - 1 + 1 = 2 ^ (9 + 1) := by decide
  have hm9 : 2 ^ 9 - 1 + 1 = 2 ^ (8 + 1) := by decide
  have hsz10' : 2 * S10.length + 8 ≤ 2 ^ (9 + 1) := hsz10
  have hsz9' : 2 * S9.length + 8 ≤ 2 ^ (8 + 1) := hsz9
  have hS10' : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen (9 + 1)) (2 ^ 10 - 1 + 1) := by rw [hm10]; exact hS10
  have hS9' : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ 9 - 1 + 1) := by rw [hm9]; exact hS9
  have hSP' : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tp + 1)) (2 ^ (tp + 1) - 1 + 1) := by rw [hmP]; exact hSP
  have hcl : ∀ (a b : Nat), a < 8 → b < 8 → ∀ t α β, ∀ j ∈ [a, b],
      j < (wCols off hd0 stk0 ctr0 heap W C Mm Wt t α β).length :=
    fun a b ha hb _ _ _ j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      show j < 8
      rcases hj with rfl | rfl
      · exact ha
      · exact hb
  refine pcsCloseN_fri_tabs (fun q hq => ?_) (by rfl)
    (fun t α β => wCols_shaped off hd0 stk0 ctr0 hC hM hW hPg S10 S9 SP ζ qv t α β)
    hdb haw hncw off tv Ts (fun p hp => ?_)
  · simp only [qs, wGroups, List.mem_cons, List.not_mem_nil, or_false] at hq
    have g10 := bbGroup_OK (tb := 9) (qv := qv) (by decide) hS10 hζ hsz10'
    have g9 := bbGroup_OK (tb := 8) (qv := qv) (by decide) hS9 hζ hsz9'
    have gP := bbGroup_OK (tb := tp) (qv := qv) (by omega) hSP hζ hszP
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact g10
    · exact g10
    · exact g10
    · exact g10
    · exact g9
    · exact g9
    · exact gP
    · exact gP
  · simp only [Ts, wTs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact tabsHonest_bb off tv pM (tb := 9) (lq := 1) (m := 2 ^ 10 - 1) (gm := 0) (gp := 1) (tm := tvAt 0)
        (by decide) (by decide) (by decide) hm10 ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (wMemT Mm) Mm (fun _ => rfl)
        (wTabs hd0 stk0 ctr0 heap W C Mm Wt) (fun t => List.mem_cons_of_mem _ List.mem_cons_self)
        (hcl 0 1 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind hsM b7 _, by show Mm.h = _; rw [hM], rfl, rfl, rfl⟩)
        hζ hdet hS10' hS4'
    · exact tabsHonest_bb off tv pC (tb := 9) (lq := 1) (m := 2 ^ 10 - 1) (gm := 2) (gp := 3) (tm := tvAt 1)
        (by decide) (by decide) (by decide) hm10 ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (wCpuT C) C (fun _ => rfl)
        (wTabs hd0 stk0 ctr0 heap W C Mm Wt) (fun t => List.mem_cons_self) (hcl 2 3 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsC b3 _) b4 _, by show C.h = _; rw [hC], rfl, rfl, rfl⟩)
        hζ hdet hS10' hS4'
    · exact tabsHonest_bb off tv pW (tb := 8) (lq := 1) (m := 2 ^ 9 - 1) (gm := 4) (gp := 5) (tm := tvAt 2)
        (by decide) (by decide) (by decide) hm9 ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (wWitT Wt) Wt (fun _ => rfl)
        (wTabs hd0 stk0 ctr0 heap W C Mm Wt)
        (fun t => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
        (hcl 4 5 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind hsW b9 _, by show Wt.h = _; rw [hW], rfl, rfl, rfl⟩)
        hζ hdet hS9' hS4
    · exact tabsHonest_bb off tv pP (tb := tp) (lq := 1) (m := 2 ^ (tp + 1) - 1) (gm := 6) (gp := 7)
        (tm := progTmW off heap W)
        (by omega) (by decide) (by omega) hmP ⟨by show _ < 8; decide, rfl⟩ ⟨by show _ < 8; decide, rfl⟩
        (fun _ => progTableW heap W) (progTableW heap W) (fun _ => rfl)
        (wTabs hd0 stk0 ctr0 heap W C Mm Wt)
        (fun t => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (hcl 6 7 (by decide) (by decide))
        (fun t α β => ⟨(progW_sat heap W).1, by rw [hPg, hmP], rfl, rfl, rfl⟩)
        hζ hdet hSP' hS4P

-- ---------------------------------------------------------------------------
-- The hidden-term proof's transcript, end to end
-- ---------------------------------------------------------------------------

section
variable {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table)
  (tp : Nat) (S10 S9 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
  (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V)

/-- **The hidden-term proof's composed PCS**, its simulator and its
    randomness. -/
def wPcs := pcsFri off (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t) (wGroups tp S10 S9 SP ζ qv)
  (wKs hd0 stk0 ctr0 heap W) (wCols off hd0 stk0 ctr0 heap W C Mm Wt)
  ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst)
  (fun t α β ms => (wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map fun p => p.2 t α β ms)
  ncw αb fri

def wPsim := psimFri (wGroups tp S10 S9 SP ζ qv) (wKs hd0 stk0 ctr0 heap W)
  ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst) ncw αb fri

def wNR : Nat := P ^ (friN1 (wGroups tp S10 S9 SP ζ qv) (wKs hd0 stk0 ctr0 heap W)
  ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst) +
  friN2 (wGroups tp S10 S9 SP ζ qv) ((wTs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp).map Prod.fst)
    ncw)
end

/-- **The simulator reads the tables' preprocessed columns only**: two
    sets of tables with the same preprocessed columns give the same
    simulator.  The hidden-term tables' preprocessed columns are public
    rows (`witRowsG` for the witness, zero for the CPU and memory). -/
theorem wPsim_pre {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat)
    {C Mm Wt C' Mm' Wt' : Table} (hC : C.pre = C'.pre) (hM : Mm.pre = Mm'.pre) (hW : Wt.pre = Wt'.pre) (tp : Nat)
    (S10 S9 SP : List F) (ζ : EF) (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F)) (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V) :
    wPsim off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw αb fri =
      wPsim off hd0 stk0 ctr0 heap W C' Mm' Wt' tp S10 S9 SP ζ qv wm wc ww wp ncw αb fri := by
  simp only [wPsim, wTs, List.map_cons, List.map_nil, bbTab, preInterp_pre hC, preInterp_pre hM,
    preInterp_pre hW]

/-- The composed PCS's view, for any circuit built as `SudInst` builds. -/
abbrev PcsPV (V : Type) : Type := SudPV V

/-- **The hidden-term proof is zero knowledge over its composed hiding
    PCS**, the program table included: for an accepting run of the
    hidden-term statement `V ⬝ x` with its witness `ws`, query points off
    each trace domain, `ζ` generating the extension and the FRI challenge
    generic, the real transcript over that PCS and the simulated one,
    summed over `α, β, r` and the tuples with `β` generic, differ by at
    most the aborting draws: `wit_transcriptG` with its PCS term zero.
    `tP` is the program table's `progTpW`; the simulator reads the tables'
    preprocessed columns only (`wPsim_pre`).  It asks neither `0 < W` nor
    `Fits A`, which `wit_complete` asks for its decoding. -/
theorem wit_hiding {V : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
    (hwl : ws.length = W) (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (wMachine ws (Vt ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10)
    {tP : Nat} (htp : tP = progTpW (wMachine (List.replicate W .S) (Vt ⬝ x)).heap W)
    {S10 S9 SP : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz10 : 2 * S10.length + 8 ≤ 2 ^ 10) (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (E : TViewN (PcsPV V) EF → Bool) :
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let pcs := wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw αb fri
    let psim := wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw αb
      fri
    let NR := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv ptm pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv ptm pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) := by
  intro blank C Pg Wt Mm pcs psim NR tabs tv ptm M
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sm, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := wit_pcs (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
    wm wc ww wp hS10 hS9 hSP hsz10 hsz9 hszP hζ hdet (fri := fri) hdb haw hncw
  exact wit_transcriptG off NR 0 pcs psim hbal hun hpcs E

end Circuit
