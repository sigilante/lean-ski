import Ski.ZK.BbGroupD
import Ski.ZK.PreOpen
import Ski.ZK.CompPHonest
import Ski.Circuit.CompPCompleteFinal

/-!
# The proof with the Poseidon2 jet's composed hiding PCS

The circuit with the Poseidon2 jet commits nine tables (`compPTables`).  Six
are private, blinded by the five edge tuples of the tree `WIT —a— CPU —b—
MEM`, `CPU —c— P2IN —d— P2OUT —e— P2` (`pMemT` … `pPpT`, as
`compP_transcriptG_fri` blinds them); the program, segments and level
tables are public.  Each is committed as two trace groups, main and
permutation: eighteen groups (`pGroups`, `pCols`), the private tables in
the order of the view (`compPViewN`), then the public ones, each with a
quotient table (`pTs`).

The P2OUT and Poseidon2 AIRs have constraints of degree 3 (the S-box
`x³`): they meet `AirP3D 3`, not `AirP3`, and Plonky3 commits eight
quotient chunks to each (`lq = 2`, `tabsHonest_bbD`); the other seven meet
`AirP3` and take four (`compP_airs`).  `compP_pcs`: that PCS meets
`PCSCloseN` with `ε = 0` over the transcript's values.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

-- ---------------------------------------------------------------------------
-- The blinded tables, the groups, the columns and the quotient tables
-- ---------------------------------------------------------------------------

def pMemT (Mm : Table) (t : Nat → Tup) : Table := Mm.setBlind 5 (t 0)
def pCpuT (C : Table) (t : Nat → Tup) : Table := ((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)
def pWitT (Wt : Table) (t : Nat → Tup) : Table := Wt.setBlind WT_BLIND (t 1)
def pPiT (Pi : Table) (t : Nat → Tup) : Table := (Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3)
def pPoT (Po : Table) (t : Nat → Tup) : Table := (Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4)
def pPpT (Pp : Table) (t : Nat → Tup) : Table := Pp.setBlind P2Air.p2Air.width (t 4)

/-- The level table's terminal: public, computed from the challenges. -/
def idxTm (off : EF → String → EF) (calls : Nat) : EF → EF → List EF → EF :=
  fun α β _ => terminal (prefixOf α (off β)) β p2idxAir (idxPub calls)

/-- The eighteen trace groups, main and permutation each. -/
def pGroups (tbM tbC tbI tbO tbQ tpP tpS : Nat) (SM SC S9 SI SO SQ SP SS SX : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) : List QGroup :=
  [bbGroup tbM SM ζ qv,
   bbGroup tbM SM ζ qv,
   bbGroup tbC SC ζ qv,
   bbGroup tbC SC ζ qv,
   bbGroup 8 S9 ζ qv,
   bbGroup 8 S9 ζ qv,
   bbGroup tbI SI ζ qv,
   bbGroup tbI SI ζ qv,
   bbGroup tbO SO ζ qv,
   bbGroup tbO SO ζ qv,
   bbGroup tbQ SQ ζ qv,
   bbGroup tbQ SQ ζ qv,
   bbGroup tpP SP ζ qv,
   bbGroup tpP SP ζ qv,
   bbGroup tpS SS ζ qv,
   bbGroup tpS SS ζ qv,
   bbGroup 8 SX ζ qv,
   bbGroup 8 SX ζ qv]

/-- The committed columns. -/
def pCols (off : EF → String → EF) (hd0 stk0 ctr0 n nilA J root N W : Nat) (heap : List Cell) (segRoots : List Nat) (calls : Nat)
    (C Mm Wt Pi Po Pp : Table) (t : Nat → Tup) (α β : EF) : List (List (List F)) :=
  let pre := prefixOf α (off β)
  [mainCols (pMemT Mm t) memAirC.width,
   permCols (pMemT Mm t) (busAlphas pre memAirC) β (corpusLs memAirC),
   mainCols (pCpuT C t) (cpuAirP2 hd0 stk0 ctr0 n nilA J root).width,
   permCols (pCpuT C t) (busAlphas pre (cpuAirP2 hd0 stk0 ctr0 n nilA J root)) β (corpusLs (cpuAirP2 hd0 stk0 ctr0 n nilA J root)),
   mainCols (pWitT Wt t) (witAirP N W).width,
   permCols (pWitT Wt t) (busAlphas pre (witAirP N W)) β (corpusLs (witAirP N W)),
   mainCols (pPiT Pi t) p2inAirB.width,
   permCols (pPiT Pi t) (busAlphas pre p2inAirB) β (corpusLs p2inAirB),
   mainCols (pPoT Po t) p2outAirB.width,
   permCols (pPoT Po t) (busAlphas pre p2outAirB) β (corpusLs p2outAirB),
   mainCols (pPpT Pp t) p2AirB.width,
   permCols (pPpT Pp t) (busAlphas pre p2AirB) β (corpusLs p2AirB),
   mainCols (progTableC heap N W) (progAirC heap N W).width,
   permCols (progTableC heap N W) (busAlphas pre (progAirC heap N W)) β (corpusLs (progAirC heap N W)),
   mainCols (segsPub segRoots) (segsAir segRoots).width,
   permCols (segsPub segRoots) (busAlphas pre (segsAir segRoots)) β (corpusLs (segsAir segRoots)),
   mainCols (idxPub calls) p2idxAir.width,
   permCols (idxPub calls) (busAlphas pre p2idxAir) β (corpusLs p2idxAir)]

/-- The column counts. -/
def pKs (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat) : List Nat :=
  let k := fun A : AirD => [A.width, 4 * ((corpusLs A).length + 1)]
  k memAirC ++ k (cpuAirP2 hd0 stk0 ctr0 n nilA J root) ++ k (witAirP N W) ++ k p2inAirB ++ k p2outAirB ++ k p2AirB ++ k (progAirC heap N W) ++ k (segsAir segRoots) ++ k p2idxAir

theorem pCols_shaped (off : EF → String → EF) (hd0 stk0 ctr0 n nilA J root : Nat) {heap : List Cell} {N W : Nat}
    {segRoots : List Nat} (calls : Nat) {C Mm Wt Pi Po Pp : Table} {tbM tbC tbI tbO tbQ tpP tpS : Nat}
    (hMem : Mm.h = 2 ^ (tbM + 1)) (hCpu : C.h = 2 ^ (tbC + 1)) (hWit : Wt.h = 2 ^ 9) (hPin : Pi.h = 2 ^ (tbI + 1)) (hPout : Po.h = 2 ^ (tbO + 1)) (hP2 : Pp.h = 2 ^ (tbQ + 1))
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub segRoots).h = 2 ^ (tpS + 1))
    (SM SC S9 SI SO SQ SP SS SX : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (t : Nat → Tup) (α β : EF) :
    Shaped ((pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv).map QGroup.ext)
        (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp t α β) ∧
      (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp t α β).map List.length =
        pKs hd0 stk0 ctr0 n nilA J root heap N W segRoots := by
  have shp := fun (T : Table) (A : AirD) => And.intro (mainCols_shape T A.width)
    (permCols_shape T (busAlphas (prefixOf α (off β)) A) β (corpusLs A))
  obtain ⟨m0, p0⟩ := shp (pMemT Mm t) memAirC
  obtain ⟨m1, p1⟩ := shp (pCpuT C t) (cpuAirP2 hd0 stk0 ctr0 n nilA J root)
  obtain ⟨m2, p2⟩ := shp (pWitT Wt t) (witAirP N W)
  obtain ⟨m3, p3⟩ := shp (pPiT Pi t) p2inAirB
  obtain ⟨m4, p4⟩ := shp (pPoT Po t) p2outAirB
  obtain ⟨m5, p5⟩ := shp (pPpT Pp t) p2AirB
  obtain ⟨m6, p6⟩ := shp (progTableC heap N W) (progAirC heap N W)
  obtain ⟨m7, p7⟩ := shp (segsPub segRoots) (segsAir segRoots)
  obtain ⟨m8, p8⟩ := shp (idxPub calls) p2idxAir
  have eMem : (pMemT Mm t).h = 2 ^ (tbM + 1) := hMem
  have eCpu : (pCpuT C t).h = 2 ^ (tbC + 1) := hCpu
  have eWit : (pWitT Wt t).h = 2 ^ (8 + 1) := hWit
  have ePin : (pPiT Pi t).h = 2 ^ (tbI + 1) := hPin
  have ePout : (pPoT Po t).h = 2 ^ (tbO + 1) := hPout
  have eP2 : (pPpT Pp t).h = 2 ^ (tbQ + 1) := hP2
  have eIdx : (idxPub calls).h = 2 ^ (8 + 1) := idxPub_h calls
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, trivial⟩, ?_⟩
  · rw [m0.2 c hc, eMem]; rfl
  · rw [p0.2 c hc, eMem]; rfl
  · rw [m1.2 c hc, eCpu]; rfl
  · rw [p1.2 c hc, eCpu]; rfl
  · rw [m2.2 c hc, eWit]; rfl
  · rw [p2.2 c hc, eWit]; rfl
  · rw [m3.2 c hc, ePin]; rfl
  · rw [p3.2 c hc, ePin]; rfl
  · rw [m4.2 c hc, ePout]; rfl
  · rw [p4.2 c hc, ePout]; rfl
  · rw [m5.2 c hc, eP2]; rfl
  · rw [p5.2 c hc, eP2]; rfl
  · rw [m6.2 c hc, hPg]; rfl
  · rw [p6.2 c hc, hPg]; rfl
  · rw [m7.2 c hc, hSg]; rfl
  · rw [p7.2 c hc, hSg]; rfl
  · rw [m8.2 c hc, eIdx]; rfl
  · rw [p8.2 c hc, eIdx]; rfl
  · show [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] = _
    rw [m0.1, p0.1, m1.1, p1.1, m2.1, p2.1, m3.1, p3.1, m4.1, p4.1, m5.1, p5.1, m6.1, p6.1, m7.1, p7.1, m8.1, p8.1]; rfl

/-- The transcript's tables. -/
def pTabs (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat) (calls : Nat)
    (C Mm Wt Pi Po Pp : Table) (t : Nat → Tup) : List (AirD × Table) :=
  compPTables hd0 stk0 ctr0 n nilA J root heap N W segRoots (pCpuT C t) (pMemT Mm t) (progTableC heap N W)
    (pWitT Wt t) (segsPub segRoots) (pPiT Pi t) (pPoT Po t) (pPpT Pp t) (idxPub calls)

set_option maxRecDepth 100000 in
/-- **The AIRs of the circuit with the Poseidon2 jet**: P2OUT and Poseidon2 at
    degree 3, the rest at degree 2. -/
theorem compP_airs (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat) :
    AirP3 memAirC = true ∧ AirP3 (cpuAirP2 hd0 stk0 ctr0 n nilA J root) = true ∧ AirP3 (witAirP N W) = true ∧ AirP3 p2inAirB = true ∧ AirP3D 3 p2outAirB = true ∧ AirP3D 3 p2AirB = true ∧ AirP3 (progAirC heap N W) = true ∧ AirP3 (segsAir segRoots) = true ∧ AirP3 p2idxAir = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- **Every blinding column of the circuit with the Poseidon2 jet is one
    its AIR's constraints avoid.** -/
theorem compP_blind_ok (hd0 stk0 ctr0 n nilA J root N W : Nat) :
    blindOK memAirC 5 = true ∧
      blindOK (cpuAirP2 hd0 stk0 ctr0 n nilA J root) BLA = true ∧
      blindOK (cpuAirP2 hd0 stk0 ctr0 n nilA J root) BLB = true ∧
      blindOK (cpuAirP2 hd0 stk0 ctr0 n nilA J root) (P2SEL + 1) = true ∧
      blindOK (witAirP N W) WT_BLIND = true ∧
      blindOK p2inAirB p2inAir.width = true ∧
      blindOK p2inAirB (p2inAir.width + 5) = true ∧
      blindOK p2outAirB p2outAir.width = true ∧
      blindOK p2outAirB (p2outAir.width + 5) = true ∧
      blindOK p2AirB P2Air.p2Air.width = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The proof with the Poseidon2 jet's nine quotient tables**, with their
    data: eight chunks for P2OUT and Poseidon2 (`lq = 2`), four for the rest. -/
def pTs (off : EF → String → EF) (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat)
    (segRoots : List Nat) (calls : Nat) (C Mm Wt Pi Po Pp : Table) (tbM tbC tbI tbO tbQ tpP tpS : Nat) (SM SC S9 SI SO SQ SP SS SX : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F)) :
    List (QTab × ((Nat → Tup) → EF → EF → List F → List (List (List F) × List F))) :=
  let tv := fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t
  let qs := pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv
  let cols := pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp
  let tabs := pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp
  let q := fun (A : AirD) (tm : EF → EF → List EF → EF) (tb lq : Nat) (T : Table) (g : Nat) (S : List F)
      (ws : List (EF → EF → List F)) =>
    (bbTabL off A tm tb lq (2 ^ (tb + 1) - 1) T g (g + 1) S ζ ws,
     bbDataL off tv A tm tb lq (2 ^ (tb + 1) - 1) T g (g + 1) S ζ ws qs cols tabs)
  [q memAirC (tvAt 0) tbM 1 Mm 0 SM wm,
   q (cpuAirP2 hd0 stk0 ctr0 n nilA J root) (tvAt 1) tbC 1 C 2 SC wc,
   q (witAirP N W) (tvAt 2) 8 1 Wt 4 S9 ww,
   q p2inAirB (tvAt 3) tbI 1 Pi 6 SI wi,
   q p2outAirB (tvAt 4) tbO 2 Po 8 SO wo,
   q p2AirB (tvAt 5) tbQ 2 Pp 10 SQ wq,
   q (progAirC heap N W) (progTmC off heap N W) tpP 1 (progTableC heap N W) 12 SP wp,
   q (segsAir segRoots) (segsTm off segRoots) tpS 1 (segsPub segRoots) 14 SS wsg,
   q p2idxAir (idxTm off calls) 8 1 (idxPub calls) 16 SX wx]

section
variable {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat)
  (segRoots : List Nat) (calls : Nat) (C Mm Wt Pi Po Pp : Table) (tbM tbC tbI tbO tbQ tpP tpS : Nat) (SM SC S9 SI SO SQ SP SS SX : List F) (ζ : EF)
  (qv : EF → EF → List EF → F → List F → List F → List EF)
  (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F)) (ncw : Nat) (αb : EF) (fri : EF → EF → List (EF → EF) → V)

/-- **The proof with the Poseidon2 jet's PCS**, its simulator and its randomness. -/
def pPcs := pcsFri off (fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t)
  (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv) (pKs hd0 stk0 ctr0 n nilA J root heap N W segRoots)
  (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp)
  ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst) (fun t α β ms => (pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map fun p => p.2 t α β ms) ncw αb fri

def pPsim := psimFri (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv) (pKs hd0 stk0 ctr0 n nilA J root heap N W segRoots)
  ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst) ncw αb fri

def pNR : Nat := P ^ (friN1 (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv) (pKs hd0 stk0 ctr0 n nilA J root heap N W segRoots)
    ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst) + friN2 (pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv) ((pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx).map Prod.fst) ncw)
end

set_option maxRecDepth 100000 in
/-- **The proof with the Poseidon2 jet's hiding PCS hides exactly**:
    `comp_pcs` for the nine tables, P2OUT and Poseidon2 over eight chunks
    at degree 3 (`tabsHonest_bbD`).  With the private tables meeting `Sat`
    at heights `2^(tb+1)` (the witness's `2^9`), the public ones at
    `2^(tp+1)` (the level table's `2^9`), every `tb, tp ≤ 23`, the query
    points off each trace domain and few enough, `ζ` generating the
    extension and the FRI challenge `αb` generic, the PCS whose view is
    every group's openings, every quotient table's chunks, every codeword
    and FRI meets `PCSCloseN` with `ε = 0`. -/
theorem compP_pcs {V : Type} (off : EF → String → EF) {hd0 stk0 ctr0 n nilA J root : Nat} {heap : List Cell}
    {N W : Nat} {segRoots : List Nat} {calls : Nat} {C Mm Wt Pi Po Pp : Table}
    (hsM : Sat memAirC Mm)
    (hsC : Sat (cpuAirP2 hd0 stk0 ctr0 n nilA J root) C)
    (hsW : Sat (witAirP N W) Wt)
    (hsI : Sat p2inAirB Pi)
    (hsO : Sat p2outAirB Po)
    (hsQ : Sat p2AirB Pp)
    {tbM tbC tbI tbO tbQ tpP tpS : Nat} (hbtbM : tbM ≤ 23) (hbtbC : tbC ≤ 23) (hbtbI : tbI ≤ 23) (hbtbO : tbO ≤ 23) (hbtbQ : tbQ ≤ 23) (hbtpP : tpP ≤ 23) (hbtpS : tpS ≤ 23)
    (hMem : Mm.h = 2 ^ (tbM + 1)) (hCpu : C.h = 2 ^ (tbC + 1)) (hWit : Wt.h = 2 ^ 9) (hPin : Pi.h = 2 ^ (tbI + 1)) (hPout : Po.h = 2 ^ (tbO + 1)) (hP2 : Pp.h = 2 ^ (tbQ + 1))
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub segRoots).h = 2 ^ (tpS + 1))
    {SM SC S9 SI SO SQ SP SS SX : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wi wo wq wp wsg wx : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)))
    (hSI : ∀ x ∈ SI, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1)))
    (hSO : ∀ x ∈ SO, x ∉ cosetL 1 (bbGen (tbO + 1)) (2 ^ (tbO + 1)))
    (hSQ : ∀ x ∈ SQ, x ∉ cosetL 1 (bbGen (tbQ + 1)) (2 ^ (tbQ + 1)))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hSX : ∀ x ∈ SX, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1))
    (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ (8 + 1))
    (hszI : 2 * SI.length + 8 ≤ 2 ^ (tbI + 1))
    (hszO : 2 * SO.length + 8 ≤ 2 ^ (tbO + 1))
    (hszQ : 2 * SQ.length + 8 ≤ 2 ^ (tbQ + 1))
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1))
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1))
    (hszX : 2 * SX.length + 8 ≤ 2 ^ (8 + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    let tv := fun pre β t => compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t
    let Ts := pTs off hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv wm wc ww wi wo wq wp wsg wx
    let qs := pGroups tbM tbC tbI tbO tbQ tpP tpS SM SC S9 SI SO SQ SP SS SX ζ qv
    let ks := pKs hd0 stk0 ctr0 n nilA J root heap N W segRoots
    PCSCloseN off (P ^ (friN1 qs ks (Ts.map Prod.fst) + friN2 qs (Ts.map Prod.fst) ncw)) tv
      (pcsFri off tv qs ks (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp)
        (Ts.map Prod.fst) (fun t α β ms => Ts.map fun p => p.2 t α β ms) ncw αb fri)
      (psimFri qs ks (Ts.map Prod.fst) ncw αb fri) 0 := by
  intro tv Ts qs ks
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := compP_blind_ok hd0 stk0 ctr0 n nilA J root N W
  obtain ⟨aMem, aCpu, aWit, aPin, aPout, aP2, aProg, aSegs, aIdx⟩ := compP_airs hd0 stk0 ctr0 n nilA J root heap N W segRoots
  have hm : ∀ b, 2 ^ (b + 1) - 1 + 1 = 2 ^ (b + 1) := fun b => Nat.sub_add_cancel Nat.one_le_two_pow
  have h4 : ∀ (S : List F) b, 2 * S.length + 8 ≤ 2 ^ (b + 1) → S.length + 4 ≤ 2 ^ (b + 1) - 1 + 1 :=
    fun S b h => by rw [hm b]; omega
  have hoff : ∀ (S : List F) b, (∀ x ∈ S, x ∉ cosetL 1 (bbGen (b + 1)) (2 ^ (b + 1))) →
      ∀ x ∈ S, x ∉ cosetL 1 (bbGen (b + 1)) (2 ^ (b + 1) - 1 + 1) := fun S b h => by rw [hm b]; exact h
  have hcl : ∀ (a : Nat), a + 1 < 18 → ∀ t α β, ∀ j ∈ [a, a + 1],
      j < (pCols off hd0 stk0 ctr0 n nilA J root N W heap segRoots calls C Mm Wt Pi Po Pp t α β).length :=
    fun a ha _ _ _ j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      show j < 18
      rcases hj with rfl | rfl <;> omega
  have hmem : ∀ i (hi : i < 9) t, (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp t)[i]'(by
      show i < 9; exact hi) ∈ pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp t :=
    fun i hi t => List.getElem_mem _
  have hW9 : Wt.h = 2 ^ (8 + 1) := hWit
  have hX9 : (idxPub calls).h = 2 ^ (8 + 1) := idxPub_h calls
  refine pcsCloseN_fri_tabs (fun q hq => ?_) (by rfl)
    (fun t α β => pCols_shaped off hd0 stk0 ctr0 n nilA J root calls hMem hCpu hWit hPin hPout hP2 hPg hSg
      SM SC S9 SI SO SQ SP SS SX ζ qv t α β)
    hdb haw hncw off tv Ts (fun p hp => ?_)
  · simp only [pGroups, List.mem_cons, List.not_mem_nil, or_false] at hq
    have gMem := bbGroup_OK (tb := tbM) (qv := qv) (by omega) hSM hζ hszM
    have gCpu := bbGroup_OK (tb := tbC) (qv := qv) (by omega) hSC hζ hszC
    have gWit := bbGroup_OK (tb := 8) (qv := qv) (by decide) hS9 hζ hsz9
    have gPin := bbGroup_OK (tb := tbI) (qv := qv) (by omega) hSI hζ hszI
    have gPout := bbGroup_OK (tb := tbO) (qv := qv) (by omega) hSO hζ hszO
    have gP2 := bbGroup_OK (tb := tbQ) (qv := qv) (by omega) hSQ hζ hszQ
    have gProg := bbGroup_OK (tb := tpP) (qv := qv) (by omega) hSP hζ hszP
    have gSegs := bbGroup_OK (tb := tpS) (qv := qv) (by omega) hSS hζ hszS
    have gIdx := bbGroup_OK (tb := 8) (qv := qv) (by decide) hSX hζ hszX
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gMem
    · exact gMem
    · exact gCpu
    · exact gCpu
    · exact gWit
    · exact gWit
    · exact gPin
    · exact gPin
    · exact gPout
    · exact gPout
    · exact gP2
    · exact gP2
    · exact gProg
    · exact gProg
    · exact gSegs
    · exact gSegs
    · exact gIdx
    · exact gIdx
  · simp only [Ts, pTs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tabsHonest_bb off tv aMem (tb := tbM) (lq := 1) (m := 2 ^ (tbM + 1) - 1) (gm := 0) (gp := 1)
        (tm := tvAt 0) (by omega) (by decide) (by omega) (hm tbM) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (pMemT Mm) Mm (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 1 (by decide) t)
        (hcl 0 (by decide))
        (fun t α β => ⟨sat_setBlind hsM b0 _, by show Mm.h = _; rw [hMem, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SM tbM hSM) (h4 SM tbM hszM)
    · exact tabsHonest_bb off tv aCpu (tb := tbC) (lq := 1) (m := 2 ^ (tbC + 1) - 1) (gm := 2) (gp := 3)
        (tm := tvAt 1) (by omega) (by decide) (by omega) (hm tbC) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (pCpuT C) C (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 0 (by decide) t)
        (hcl 2 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind (sat_setBlind hsC b1 _) b2 _) b3 _, by show C.h = _; rw [hCpu, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SC tbC hSC) (h4 SC tbC hszC)
    · exact tabsHonest_bb off tv aWit (tb := 8) (lq := 1) (m := 2 ^ (8 + 1) - 1) (gm := 4) (gp := 5)
        (tm := tvAt 2) (by decide) (by decide) (by decide) (hm 8) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (pWitT Wt) Wt (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 3 (by decide) t)
        (hcl 4 (by decide))
        (fun t α β => ⟨sat_setBlind hsW b4 _, by show Wt.h = _; rw [hW9, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff S9 8 hS9) (h4 S9 8 hsz9)
    · exact tabsHonest_bb off tv aPin (tb := tbI) (lq := 1) (m := 2 ^ (tbI + 1) - 1) (gm := 6) (gp := 7)
        (tm := tvAt 3) (by omega) (by decide) (by omega) (hm tbI) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (pPiT Pi) Pi (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 5 (by decide) t)
        (hcl 6 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsI b5 _) b6 _, by show Pi.h = _; rw [hPin, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SI tbI hSI) (h4 SI tbI hszI)
    · exact tabsHonest_bbD off tv aPout (by decide) (tb := tbO) (lq := 2) (m := 2 ^ (tbO + 1) - 1) (gm := 8) (gp := 9)
        (tm := tvAt 4) (by omega) (by decide) (by omega) (by decide) (hm tbO) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (pPoT Po) Po (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 6 (by decide) t)
        (hcl 8 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsO b7 _) b8 _, by show Po.h = _; rw [hPout, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SO tbO hSO) (h4 SO tbO hszO)
    · exact tabsHonest_bbD off tv aP2 (by decide) (tb := tbQ) (lq := 2) (m := 2 ^ (tbQ + 1) - 1) (gm := 10) (gp := 11)
        (tm := tvAt 5) (by omega) (by decide) (by omega) (by decide) (hm tbQ) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (pPpT Pp) Pp (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 7 (by decide) t)
        (hcl 10 (by decide))
        (fun t α β => ⟨sat_setBlind hsQ b9 _, by show Pp.h = _; rw [hP2, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SQ tbQ hSQ) (h4 SQ tbQ hszQ)
    · exact tabsHonest_bb off tv aProg (tb := tpP) (lq := 1) (m := 2 ^ (tpP + 1) - 1) (gm := 12) (gp := 13)
        (tm := progTmC off heap N W) (by omega) (by decide) (by omega) (hm tpP) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (fun _ => progTableC heap N W) (progTableC heap N W) (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 2 (by decide) t)
        (hcl 12 (by decide))
        (fun t α β => ⟨(progC_sat heap N W).1, by rw [hPg, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SP tpP hSP) (h4 SP tpP hszP)
    · exact tabsHonest_bb off tv aSegs (tb := tpS) (lq := 1) (m := 2 ^ (tpS + 1) - 1) (gm := 14) (gp := 15)
        (tm := segsTm off segRoots) (by omega) (by decide) (by omega) (hm tpS) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (fun _ => segsPub segRoots) (segsPub segRoots) (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 4 (by decide) t)
        (hcl 14 (by decide))
        (fun t α β => ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, by rw [hSg, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SS tpS hSS) (h4 SS tpS hszS)
    · exact tabsHonest_bb off tv aIdx (tb := 8) (lq := 1) (m := 2 ^ (8 + 1) - 1) (gm := 16) (gp := 17)
        (tm := idxTm off calls) (by decide) (by decide) (by decide) (hm 8) ⟨by show _ < 18; decide, rfl⟩
        ⟨by show _ < 18; decide, rfl⟩ (fun _ => idxPub calls) (idxPub calls) (fun _ => rfl)
        (pTabs hd0 stk0 ctr0 n nilA J root heap N W segRoots calls C Mm Wt Pi Po Pp) (fun t => hmem 8 (by decide) t)
        (hcl 16 (by decide))
        (fun t α β => ⟨idx_sat calls, by rw [hX9, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SX 8 hSX) (h4 SX 8 hszX)

end Circuit
