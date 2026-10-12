import Ski.ZK.WitInst
import Ski.ZK.CompRunSat

/-!
# The composed proof's composed hiding PCS

The composed circuit commits five tables.  The memory, CPU and witness
tables are private, blinded by the edge tuples (`cMemT`, `cCpuT`,
`cWitT`); the program and segments tables are public.  Each is committed
as two trace groups, its main and permutation columns: ten groups,
heights `2^(tbM+1)` (memory), `2^(tbC+1)` (CPU), `2^9` (witness) and
the program's and segments' `2^(tpP+1)`, `2^(tpS+1)` (`cGroups`,
`cCols`), each table with a quotient table of Plonky3's four chunks
(`cTs`), as for the Sudoku proof (`Ski/ZK/SudInst.lean`).  The two
public tables' LogUp terminals are computed from the challenges
(`progTmC`, `segsTm`).

The public tables' heights are powers of two set by the statement
(`progC_height`, `segsC_height`).

`comp_pcs`: that PCS meets `PCSCloseN` with `ε = 0` over the composed
transcript's values.  `comp_hiding`: for an accepting composed run, with
the CPU table `2^R ≥ 2` rows high, `comp_transcriptG` over that PCS, its
PCS term zero; the simulator reads the tables' preprocessed columns only
(`cPsim_pre`).

Left out of the view and assumed: as for the Sudoku proof.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

-- ---------------------------------------------------------------------------
-- The public tables' heights
-- ---------------------------------------------------------------------------

def progTpC (heap : List Cell) (N W : Nat) : Nat := lgF 64 (progTableC heap N W).h - 1
def segTp (roots : List Nat) : Nat := lgF 64 (segsPub roots).h - 1

theorem progC_height {heap : List Cell} {N W : Nat} (hh : heap.length ≤ 2 ^ 24) :
    progTpC heap N W ≤ 23 ∧ (progTableC heap N W).h = 2 ^ (progTpC heap N W + 1) := by
  obtain ⟨d, h9, h24, hd⟩ := padPow ((heap.zipIdx.filter fun (_, i) => !(3 ≤ i && i < 3 + N + W)).map
    fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1])
    [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0] (e := 9) (by decide)
    (by rw [List.length_map]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [List.length_zipIdx]; exact hh))
  have hh' : (progTableC heap N W).h = 2 ^ d := hd
  have ht : progTpC heap N W = d - 1 := by unfold progTpC; rw [hh', lgF_pow 64 d (by omega)]
  refine ⟨by omega, ?_⟩
  rw [ht, hh', Nat.sub_add_cancel (by omega)]

theorem segsC_height {roots : List Nat} (hr : roots.length ≤ 2 ^ 24) :
    segTp roots ≤ 23 ∧ (segsPub roots).h = 2 ^ (segTp roots + 1) := by
  obtain ⟨d, h9, h24, hd⟩ := padPow (roots.zipIdx.map fun (r, j) => [ofN j, ofN r])
    ((roots.zipIdx.map fun (r, j) => [ofN j, ofN r]).headD []) (e := 9) (by decide)
    (by rw [List.length_map, List.length_zipIdx]; exact hr)
  have hh' : (segsPub roots).h = 2 ^ d := hd
  have ht : segTp roots = d - 1 := by unfold segTp; rw [hh', lgF_pow 64 d (by omega)]
  refine ⟨by omega, ?_⟩
  rw [ht, hh', Nat.sub_add_cancel (by omega)]

-- ---------------------------------------------------------------------------
-- The groups, the columns and the quotient tables
-- ---------------------------------------------------------------------------

def cMemT (Mm : Table) (t : Nat → Tup) : Table := Mm.setBlind 5 (t 0)
def cCpuT (C : Table) (t : Nat → Tup) : Table := (C.setBlind BLA (t 1)).setBlind BLB (t 0)
def cWitT (Wt : Table) (t : Nat → Tup) : Table := Wt.setBlind WT_BLIND (t 1)

/-- The ten trace groups: memory, CPU, witness, program and segments, main
    and permutation each. -/
def cGroups (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) : List QGroup :=
  [bbGroup tbM SM ζ qv, bbGroup tbM SM ζ qv, bbGroup tbC SC ζ qv, bbGroup tbC SC ζ qv, bbGroup 8 S9 ζ qv,
   bbGroup 8 S9 ζ qv, bbGroup tpP SP ζ qv, bbGroup tpP SP ζ qv, bbGroup tpS SS ζ qv, bbGroup tpS SS ζ qv]

/-- The committed columns. -/
def cCols (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Wt : Table) (t : Nat → Tup) (α β : EF) : List (List (List F)) :=
  [mainCols (cMemT Mm t) memAirC.width,
   permCols (cMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC),
   mainCols (cCpuT C t) (cpuAirC hd0 stk0 ctr0 n nilA).width,
   permCols (cCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirC hd0 stk0 ctr0 n nilA)) β
     (corpusLs (cpuAirC hd0 stk0 ctr0 n nilA)),
   mainCols (cWitT Wt t) (witAir N W).width,
   permCols (cWitT Wt t) (busAlphas (prefixOf α (off β)) (witAir N W)) β (corpusLs (witAir N W)),
   mainCols (progTableC heap N W) (progAirC heap N W).width,
   permCols (progTableC heap N W) (busAlphas (prefixOf α (off β)) (progAirC heap N W)) β
     (corpusLs (progAirC heap N W)),
   mainCols (segsPub roots) (segsAir roots).width,
   permCols (segsPub roots) (busAlphas (prefixOf α (off β)) (segsAir roots)) β (corpusLs (segsAir roots))]

/-- The column counts. -/
def cKs (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat) : List Nat :=
  [memAirC.width, 4 * ((corpusLs memAirC).length + 1), (cpuAirC hd0 stk0 ctr0 n nilA).width,
   4 * ((corpusLs (cpuAirC hd0 stk0 ctr0 n nilA)).length + 1), (witAir N W).width,
   4 * ((corpusLs (witAir N W)).length + 1), (progAirC heap N W).width,
   4 * ((corpusLs (progAirC heap N W)).length + 1), (segsAir roots).width,
   4 * ((corpusLs (segsAir roots)).length + 1)]

theorem cCols_shaped (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) {heap : List Cell} {N W : Nat}
    {roots : List Nat} {C Mm Wt : Table} {tbM tbC tpP tpS : Nat}
    (hM : Mm.h = 2 ^ (tbM + 1)) (hC : C.h = 2 ^ (tbC + 1)) (hW : Wt.h = 2 ^ 9)
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub roots).h = 2 ^ (tpS + 1))
    (SM SC S9 SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (t : Nat → Tup) (α β : EF) :
    Shaped ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv).map QGroup.ext)
        (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t α β) ∧
      (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t α β).map List.length =
        cKs hd0 stk0 ctr0 n nilA heap N W roots := by
  have m1 := mainCols_shape (cMemT Mm t) memAirC.width
  have p1 := permCols_shape (cMemT Mm t) (busAlphas (prefixOf α (off β)) memAirC) β (corpusLs memAirC)
  have m2 := mainCols_shape (cCpuT C t) (cpuAirC hd0 stk0 ctr0 n nilA).width
  have p2 := permCols_shape (cCpuT C t) (busAlphas (prefixOf α (off β)) (cpuAirC hd0 stk0 ctr0 n nilA)) β
    (corpusLs (cpuAirC hd0 stk0 ctr0 n nilA))
  have m3 := mainCols_shape (cWitT Wt t) (witAir N W).width
  have p3 := permCols_shape (cWitT Wt t) (busAlphas (prefixOf α (off β)) (witAir N W)) β (corpusLs (witAir N W))
  have m4 := mainCols_shape (progTableC heap N W) (progAirC heap N W).width
  have p4 := permCols_shape (progTableC heap N W) (busAlphas (prefixOf α (off β)) (progAirC heap N W)) β
    (corpusLs (progAirC heap N W))
  have m5 := mainCols_shape (segsPub roots) (segsAir roots).width
  have p5 := permCols_shape (segsPub roots) (busAlphas (prefixOf α (off β)) (segsAir roots)) β
    (corpusLs (segsAir roots))
  have hMh : (cMemT Mm t).h = 2 ^ (tbM + 1) := hM
  have hCh : (cCpuT C t).h = 2 ^ (tbC + 1) := hC
  have hWh : (cWitT Wt t).h = 2 ^ (8 + 1) := hW
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, trivial⟩, ?_⟩
  · rw [m1.2 c hc, hMh]; rfl
  · rw [p1.2 c hc, hMh]; rfl
  · rw [m2.2 c hc, hCh]; rfl
  · rw [p2.2 c hc, hCh]; rfl
  · rw [m3.2 c hc, hWh]; rfl
  · rw [p3.2 c hc, hWh]; rfl
  · rw [m4.2 c hc, hPg]; rfl
  · rw [p4.2 c hc, hPg]; rfl
  · rw [m5.2 c hc, hSg]; rfl
  · rw [p5.2 c hc, hSg]; rfl
  · show [_, _, _, _, _, _, _, _, _, _] = _
    rw [m1.1, p1.1, m2.1, p2.1, m3.1, p3.1, m4.1, p4.1, m5.1, p5.1]; rfl

/-- The public tables' terminals, from the challenges. -/
def progTmC (off : EF → String → EF) (heap : List Cell) (N W : Nat) : EF → EF → List EF → EF :=
  fun α β _ => terminal (prefixOf α (off β)) β (progAirC heap N W) (progTableC heap N W)
def segsTm (off : EF → String → EF) (roots : List Nat) : EF → EF → List EF → EF :=
  fun α β _ => terminal (prefixOf α (off β)) β (segsAir roots) (segsPub roots)

/-- The transcript's tables. -/
def cTabs (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat) (C Mm Wt : Table)
    (t : Nat → Tup) : List (AirD × Table) :=
  compTables hd0 stk0 ctr0 n nilA heap N W roots (cCpuT C t) (cMemT Mm t) (progTableC heap N W) (cWitT Wt t)
    (segsPub roots)

/-- **The composed proof's five quotient tables**, with their data. -/
def cTs (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Wt : Table) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : List (EF → EF → List F)) :
    List (QTab × ((Nat → Tup) → EF → EF → List F → List (List (List F) × List F))) :=
  let tv := fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t
  let qs := cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv
  let cols := cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt
  let tabs := cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt
  [(bbTab off memAirC (tvAt 0) tbM (2 ^ (tbM + 1) - 1) Mm 0 1 SM ζ wm,
     bbData off tv memAirC (tvAt 0) tbM (2 ^ (tbM + 1) - 1) Mm 0 1 SM ζ wm qs cols tabs),
   (bbTab off (cpuAirC hd0 stk0 ctr0 n nilA) (tvAt 1) tbC (2 ^ (tbC + 1) - 1) C 2 3 SC ζ wc,
     bbData off tv (cpuAirC hd0 stk0 ctr0 n nilA) (tvAt 1) tbC (2 ^ (tbC + 1) - 1) C 2 3 SC ζ wc qs cols tabs),
   (bbTab off (witAir N W) (tvAt 2) 8 (2 ^ 9 - 1) Wt 4 5 S9 ζ ww,
     bbData off tv (witAir N W) (tvAt 2) 8 (2 ^ 9 - 1) Wt 4 5 S9 ζ ww qs cols tabs),
   (bbTab off (progAirC heap N W) (progTmC off heap N W) tpP (2 ^ (tpP + 1) - 1) (progTableC heap N W) 6 7 SP ζ wp,
     bbData off tv (progAirC heap N W) (progTmC off heap N W) tpP (2 ^ (tpP + 1) - 1) (progTableC heap N W) 6 7 SP ζ
       wp qs cols tabs),
   (bbTab off (segsAir roots) (segsTm off roots) tpS (2 ^ (tpS + 1) - 1) (segsPub roots) 8 9 SS ζ wsg,
     bbData off tv (segsAir roots) (segsTm off roots) tpS (2 ^ (tpS + 1) - 1) (segsPub roots) 8 9 SS ζ wsg qs cols
       tabs)]

-- ---------------------------------------------------------------------------
-- The composed proof's PCS hides
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
theorem comp_airs_P3 (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat) :
    AirP3 memAirC = true ∧ AirP3 (cpuAirC hd0 stk0 ctr0 n nilA) = true ∧ AirP3 (witAir N W) = true ∧
      AirP3 (progAirC heap N W) = true ∧ AirP3 (segsAir roots) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- **The composed proof's hiding PCS hides exactly**: with the run's
    private tables meeting `Sat` at the heights `2^(tbM+1)`, `2^(tbC+1)`,
    `2^9`, the public tables at `2^(tpP+1)`, `2^(tpS+1)`, every `tb ≤ 24`,
    the query points off each trace domain, `ζ` generating the extension
    and the FRI challenge `αb` generic, the PCS whose view is every
    group's openings, every quotient table's chunks, every codeword and
    FRI meets `PCSCloseN` with `ε = 0`, over the composed transcript's
    values. -/
theorem comp_pcs {V : Type} (off : EF → String → EF) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat}
    {roots : List Nat} {C Mm Wt : Table}
    (hsC : Sat (cpuAirC hd0 stk0 ctr0 n nilA) C) (hsM : Sat memAirC Mm) (hsW : Sat (witAir N W) Wt)
    {tbM tbC tpP tpS : Nat} (hbM : tbM ≤ 24) (hbC : tbC ≤ 24) (hbP : tpP ≤ 24) (hbS : tpS ≤ 24)
    (hM : Mm.h = 2 ^ (tbM + 1)) (hC : C.h = 2 ^ (tbC + 1)) (hW : Wt.h = 2 ^ 9)
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub roots).h = 2 ^ (tpS + 1))
    {SM SC S9 SP SS : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1)) (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9) (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    let tv := fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t
    let Ts := cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg
    let qs := cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv
    let ks := cKs hd0 stk0 ctr0 n nilA heap N W roots
    PCSCloseN off (P ^ (friN1 qs ks (Ts.map Prod.fst) + friN2 qs (Ts.map Prod.fst) ncw)) tv
      (pcsFri off tv qs ks (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt) (Ts.map Prod.fst)
        (fun t α β ms => Ts.map fun p => p.2 t α β ms) ncw αb fri)
      (psimFri qs ks (Ts.map Prod.fst) ncw αb fri) 0 := by
  intro tv Ts qs ks
  obtain ⟨_, _, _, _, b5, b6, b7, _, _, b10⟩ := blind_ok hd0 stk0 ctr0 n nilA N W
  obtain ⟨pM, pC, pW, pP, pS⟩ := comp_airs_P3 hd0 stk0 ctr0 n nilA heap N W roots
  have hm : ∀ b, 2 ^ (b + 1) - 1 + 1 = 2 ^ (b + 1) := fun b => Nat.sub_add_cancel Nat.one_le_two_pow
  have hm9 : 2 ^ 9 - 1 + 1 = 2 ^ (8 + 1) := by decide
  have h4 : ∀ (S : List F) b, 2 * S.length + 8 ≤ 2 ^ (b + 1) → S.length + 4 ≤ 2 ^ (b + 1) - 1 + 1 :=
    fun S b h => by rw [hm b]; omega
  have hoff : ∀ (S : List F) b, (∀ x ∈ S, x ∉ cosetL 1 (bbGen (b + 1)) (2 ^ (b + 1))) →
      ∀ x ∈ S, x ∉ cosetL 1 (bbGen (b + 1)) (2 ^ (b + 1) - 1 + 1) := fun S b h => by rw [hm b]; exact h
  have hsz9' : 2 * S9.length + 8 ≤ 2 ^ (8 + 1) := hsz9
  have hS9' : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)) := hS9
  have hcl : ∀ (a b : Nat), a < 10 → b < 10 → ∀ t α β, ∀ j ∈ [a, b],
      j < (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t α β).length :=
    fun a b ha hb _ _ _ j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      show j < 10
      rcases hj with rfl | rfl
      · exact ha
      · exact hb
  have hmem : ∀ i (hi : i < 5) t, (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t)[i]'(by
      show i < 5; exact hi) ∈ cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t :=
    fun i hi t => List.getElem_mem _
  refine pcsCloseN_fri_tabs (fun q hq => ?_) (by rfl)
    (fun t α β => cCols_shaped off hd0 stk0 ctr0 n nilA hM hC hW hPg hSg SM SC S9 SP SS ζ qv t α β)
    hdb haw hncw off tv Ts (fun p hp => ?_)
  · simp only [qs, cGroups, List.mem_cons, List.not_mem_nil, or_false] at hq
    have gM := bbGroup_OK (tb := tbM) (qv := qv) (by omega) hSM hζ hszM
    have gC := bbGroup_OK (tb := tbC) (qv := qv) (by omega) hSC hζ hszC
    have g9 := bbGroup_OK (tb := 8) (qv := qv) (by decide) hS9' hζ hsz9'
    have gP := bbGroup_OK (tb := tpP) (qv := qv) (by omega) hSP hζ hszP
    have gS := bbGroup_OK (tb := tpS) (qv := qv) (by omega) hSS hζ hszS
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gM
    · exact gM
    · exact gC
    · exact gC
    · exact g9
    · exact g9
    · exact gP
    · exact gP
    · exact gS
    · exact gS
  · simp only [Ts, cTs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact tabsHonest_bb off tv pM (tb := tbM) (lq := 1) (m := 2 ^ (tbM + 1) - 1) (gm := 0) (gp := 1) (tm := tvAt 0)
        (by omega) (by decide) (by omega) (hm tbM) ⟨by show _ < 10; decide, rfl⟩ ⟨by show _ < 10; decide, rfl⟩
        (cMemT Mm) Mm (fun _ => rfl)
        (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt) (fun t => hmem 1 (by decide) t)
        (hcl 0 1 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind hsM b7 _, by show Mm.h = _; rw [hM, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SM tbM hSM) (h4 SM tbM hszM)
    · exact tabsHonest_bb off tv pC (tb := tbC) (lq := 1) (m := 2 ^ (tbC + 1) - 1) (gm := 2) (gp := 3) (tm := tvAt 1)
        (by omega) (by decide) (by omega) (hm tbC) ⟨by show _ < 10; decide, rfl⟩ ⟨by show _ < 10; decide, rfl⟩
        (cCpuT C) C (fun _ => rfl)
        (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt) (fun t => hmem 0 (by decide) t)
        (hcl 2 3 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsC b5 _) b6 _, by show C.h = _; rw [hC, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SC tbC hSC) (h4 SC tbC hszC)
    · exact tabsHonest_bb off tv pW (tb := 8) (lq := 1) (m := 2 ^ 9 - 1) (gm := 4) (gp := 5) (tm := tvAt 2)
        (by decide) (by decide) (by decide) hm9 ⟨by show _ < 10; decide, rfl⟩ ⟨by show _ < 10; decide, rfl⟩
        (cWitT Wt) Wt (fun _ => rfl)
        (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt) (fun t => hmem 3 (by decide) t)
        (hcl 4 5 (by decide) (by decide))
        (fun t α β => ⟨sat_setBlind hsW b10 _, by show Wt.h = _; rw [hW], rfl, rfl, rfl⟩)
        hζ hdet (hoff S9 8 hS9') (h4 S9 8 hsz9')
    · exact tabsHonest_bb off tv pP (tb := tpP) (lq := 1) (m := 2 ^ (tpP + 1) - 1) (gm := 6) (gp := 7)
        (tm := progTmC off heap N W)
        (by omega) (by decide) (by omega) (hm tpP) ⟨by show _ < 10; decide, rfl⟩ ⟨by show _ < 10; decide, rfl⟩
        (fun _ => progTableC heap N W) (progTableC heap N W) (fun _ => rfl)
        (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt) (fun t => hmem 2 (by decide) t)
        (hcl 6 7 (by decide) (by decide))
        (fun t α β => ⟨(progC_sat heap N W).1, by rw [hPg, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SP tpP hSP) (h4 SP tpP hszP)
    · exact tabsHonest_bb off tv pS (tb := tpS) (lq := 1) (m := 2 ^ (tpS + 1) - 1) (gm := 8) (gp := 9)
        (tm := segsTm off roots)
        (by omega) (by decide) (by omega) (hm tpS) ⟨by show _ < 10; decide, rfl⟩ ⟨by show _ < 10; decide, rfl⟩
        (fun _ => segsPub roots) (segsPub roots) (fun _ => rfl)
        (cTabs hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt) (fun t => hmem 4 (by decide) t)
        (hcl 8 9 (by decide) (by decide))
        (fun t α β => ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, by rw [hSg, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SS tpS hSS) (h4 SS tpS hszS)

-- ---------------------------------------------------------------------------
-- The composed proof's transcript, end to end
-- ---------------------------------------------------------------------------

/-- **The public tables' heights for a composed run**: the blank heap and
    the roots fit `2^20`, so both public tables have power-of-two heights
    `2^(tp + 1)`, `tp ≤ 23`. -/
theorem comp_pub_heights {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term} {W : Nat}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    progTpC m.heap (BT.nleaves shp) W ≤ 23 ∧
      (progTableC m.heap (BT.nleaves shp) W).h = 2 ^ (progTpC m.heap (BT.nleaves shp) W + 1) ∧
      segTp roots ≤ 23 ∧ (segsPub roots).h = 2 ^ (segTp roots + 1) := by
  intro m roots
  have hRb : 2 ^ R ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
  have hLb : 2 ^ Lm ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots, hlenm, _, _⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  have hn : 0 < Ps.length := hA.npos
  have hnR : roots.length = Ps.length := blankRoots_length _ _ _
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have h0 : A.take (cMachine ρ shp region Ps).heap.length = (cMachine ρ shp region Ps).heap := by
    rw [← hA.ctr0]; exact hA.heap0
  have hml := congrArg List.length h0
  rw [List.length_take] at hml
  have e1 : (cMachine ρ shp region Ps).heap.length = m.heap.length := hlenm
  obtain ⟨p1, p2⟩ := progC_height (heap := m.heap) (N := BT.nleaves shp) (W := W) (by omega)
  obtain ⟨s1, s2⟩ := segsC_height (roots := roots) (by omega)
  exact ⟨p1, p2, s1, s2⟩

section
variable {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat)
  (roots : List Nat) (C Mm Wt : Table) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS : List F) (ζ : EF)
  (qv : EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : List (EF → EF → List F)) (ncw : Nat)
  (αb : EF) (fri : EF → EF → List (EF → EF) → V)

/-- **The composed proof's PCS**, its simulator and its randomness. -/
def cPcs := pcsFri off (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t)
  (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv) (cKs hd0 stk0 ctr0 n nilA heap N W roots)
  (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt)
  ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map
    Prod.fst)
  (fun t α β ms => (cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww
    wp wsg).map fun p => p.2 t α β ms) ncw αb fri

def cPsim := psimFri (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv) (cKs hd0 stk0 ctr0 n nilA heap N W roots)
  ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map
    Prod.fst) ncw αb fri

def cNR : Nat := P ^ (friN1 (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv) (cKs hd0 stk0 ctr0 n nilA heap N W roots)
  ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map
    Prod.fst) +
  friN2 (cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv)
    ((cTs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map
      Prod.fst) ncw)
end

/-- **The simulator reads the tables' preprocessed columns only**: the
    composed tables' preprocessed columns are public rows (`witRowsG` for
    the witness, zero for the CPU and memory). -/
theorem cPsim_pre {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat)
    (roots : List Nat) {C Mm Wt C' Mm' Wt' : Table} (hC : C.pre = C'.pre) (hM : Mm.pre = Mm'.pre)
    (hW : Wt.pre = Wt'.pre) (tbM tbC tpP tpS : Nat) (SM SC S9 SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : List (EF → EF → List F))
    (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V) :
    cPsim off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb fri =
      cPsim off hd0 stk0 ctr0 n nilA heap N W roots C' Mm' Wt' tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw
        αb fri := by
  simp only [cPsim, cTs, List.map_cons, List.map_nil, bbTab, preInterp_pre hC, preInterp_pre hM,
    preInterp_pre hW]

/-- **The composed proof is zero knowledge over its composed hiding PCS**,
    the public program and segments tables included: for an accepting
    composed run on a memory of `2^Lm` cells with a CPU table of `2^R`
    rows (`tbM + 1 = Lm`, `tbC + 1 = R`), query points off each trace
    domain, `ζ` generating the extension and the FRI challenge generic,
    the real transcript over that PCS and the simulated one, summed over
    `α, β, r` and the tuples with `β` generic, differ by at most the
    aborting draws: `comp_transcriptG` with its PCS term zero.  `tpP`,
    `tpS` are the public tables' `progTpC`, `segTp`; the simulator reads
    the tables' preprocessed columns only (`cPsim_pre`). -/
theorem comp_hiding {V : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
    {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8)
    {tbM tbC tpP tpS : Nat} (htM : tbM + 1 = Lm) (htC : tbC + 1 = R)
    (htP : tpP = progTpC (blankM shp W Ps).heap (BT.nleaves shp) W) (htS : tpS = segTp (blankRoots shp W Ps))
    {SM SC S9 SP SS : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp wsg : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1)) (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9) (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (E : TViewN (PcsPV V) (EF × EF) → Bool) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let pcs := cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb fri
    let psim := cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb fri
    let NR := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw
    let tabs := fun t : Nat → Tup => compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableC m.heap N W)
      (Wt.setBlind WT_BLIND (t 1)) (segsPub roots)
    let tv := fun pre β t => compViewN pre β m.hd m.stk m.heap.length roots.length m.stk N W C Mm Wt t
    let pb := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W),
      terminal pre β (segsAir roots) (segsPub roots))
    let ptm := fun pre β => (terminal pre β (progAirC m.heap N W) (progTableC m.heap N W)).add
      (terminal pre β (segsAir roots) (segsPub roots))
    let M := (allEntries (compTables m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm
      (progTableC m.heap N W) Wt (segsPub roots))).length
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) := by
  intro m roots N C Pg Wt Mm pcs psim NR tabs tv pb ptm M
  obtain ⟨hbal, hun⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
  obtain ⟨sc, sm, sw, hWh, _⟩ := comp_run_sats hR hrl hr hA hlen hLm hK hNW
  obtain ⟨p1, p2, s1, s2⟩ := comp_pub_heights hR hrl hA hlen hLm hK
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hlen
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; rfl
  have hpcs := comp_pcs (heap := m.heap) (roots := roots) off sc sm sw (by omega) (by omega) (by omega) (by omega)
    hM hC hWh p2 s2 qv wm wc ww wp wsg hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS hζ hdet (fri := fri) hdb haw hncw
  exact comp_transcriptG off NR 0 pcs psim hbal hun hpcs E

end Circuit
