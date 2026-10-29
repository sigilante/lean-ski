import Ski.ZK.PreOpen
import Ski.ZK.CompJ

/-!
# The composed proof with jets' composed hiding PCS

The circuit with jets commits ten tables (`compJTables`).  Eight are
private, blinded by the seven edge tuples of the tree `WIT —a— CPU —b— MEM`,
`CPU —c— POP —d— INSTW —e— TMPL —f— HDR —g— ROOTS` (`jMemT` … `jRtT`, as
`compJ_transcriptG_fri` blinds them); the program and segments tables are
public.  Each table is committed as two trace groups, its main and
permutation columns: twenty groups (`jGroups`, `jCols`), the private
tables in the order of the view (`compJViewN`: memory, CPU, witness, POP,
INSTW, TMPL, HDR, ROOTS), then the program and segments tables, each with
a quotient table of Plonky3's four chunks (`jTs`), as for the composed
proof (`Ski/ZK/CompInst.lean`).

Every AIR of the circuit meets `AirP3` (`compJ_airs_P3`), and every
blinding column is one its constraints avoid (`compJ_blind_ok`), so the
composed proof's construction applies table by table: `compJ_pcs`, that
PCS meets `PCSCloseN` with `ε = 0` over the transcript's values with jets.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit

-- ---------------------------------------------------------------------------
-- The blinded tables, the groups, the columns and the quotient tables
-- ---------------------------------------------------------------------------

def jMemT (Mm : Table) (t : Nat → Tup) : Table := Mm.setBlind 5 (t 0)
def jCpuT (C : Table) (t : Nat → Tup) : Table := ((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)
def jWitT (Wt : Table) (t : Nat → Tup) : Table := Wt.setBlind WT_BLIND (t 1)
def jPoT (Po : Table) (t : Nat → Tup) : Table := (Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3)
def jIwT (Iw : Table) (t : Nat → Tup) : Table :=
  (Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4)
def jTmT (Tm : Table) (t : Nat → Tup) : Table := (Tm.setBlind 1 (t 4)).setBlind 6 (t 5)
def jHdT (Hd : Table) (t : Nat → Tup) : Table := (Hd.setBlind 1 (t 5)).setBlind 6 (t 6)
def jRtT (Rt : Table) (t : Nat → Tup) : Table := Rt.setBlind 1 (t 6)

/-- The twenty trace groups: memory, CPU, witness, POP, INSTW, TMPL, HDR,
    ROOTS, program and segments, main and permutation each. -/
def jGroups (tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat) (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) : List QGroup :=
  [bbGroup tbM SM ζ qv, bbGroup tbM SM ζ qv, bbGroup tbC SC ζ qv, bbGroup tbC SC ζ qv, bbGroup 8 S9 ζ qv,
   bbGroup 8 S9 ζ qv, bbGroup tbPo SPo ζ qv, bbGroup tbPo SPo ζ qv, bbGroup tbI SI ζ qv, bbGroup tbI SI ζ qv,
   bbGroup tpT ST ζ qv, bbGroup tpT ST ζ qv, bbGroup tpH SH ζ qv, bbGroup tpH SH ζ qv, bbGroup tpR SR ζ qv,
   bbGroup tpR SR ζ qv, bbGroup tpP SP ζ qv, bbGroup tpP SP ζ qv, bbGroup tpS SS ζ qv, bbGroup tpS SS ζ qv]

/-- The committed columns. -/
def jCols (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table) (t : Nat → Tup) (α β : EF) :
    List (List (List F)) :=
  let pre := prefixOf α (off β)
  [mainCols (jMemT Mm t) memAirC.width,
   permCols (jMemT Mm t) (busAlphas pre memAirC) β (corpusLs memAirC),
   mainCols (jCpuT C t) (cpuAirCJ hd0 stk0 ctr0 n nilA).width,
   permCols (jCpuT C t) (busAlphas pre (cpuAirCJ hd0 stk0 ctr0 n nilA)) β (corpusLs (cpuAirCJ hd0 stk0 ctr0 n nilA)),
   mainCols (jWitT Wt t) (witAir N W).width,
   permCols (jWitT Wt t) (busAlphas pre (witAir N W)) β (corpusLs (witAir N W)),
   mainCols (jPoT Po t) popAirCJ.width,
   permCols (jPoT Po t) (busAlphas pre popAirCJ) β (corpusLs popAirCJ),
   mainCols (jIwT Iw t) instwAirCJ.width,
   permCols (jIwT Iw t) (busAlphas pre instwAirCJ) β (corpusLs instwAirCJ),
   mainCols (jTmT Tm t) (tmplAirCJ jets).width,
   permCols (jTmT Tm t) (busAlphas pre (tmplAirCJ jets)) β (corpusLs (tmplAirCJ jets)),
   mainCols (jHdT Hd t) (hdrAirCJ jets).width,
   permCols (jHdT Hd t) (busAlphas pre (hdrAirCJ jets)) β (corpusLs (hdrAirCJ jets)),
   mainCols (jRtT Rt t) (rootsAirCJ roots).width,
   permCols (jRtT Rt t) (busAlphas pre (rootsAirCJ roots)) β (corpusLs (rootsAirCJ roots)),
   mainCols (progTableC heap N W) (progAirC heap N W).width,
   permCols (progTableC heap N W) (busAlphas pre (progAirC heap N W)) β (corpusLs (progAirC heap N W)),
   mainCols (segsPub segRoots) (segsAir segRoots).width,
   permCols (segsPub segRoots) (busAlphas pre (segsAir segRoots)) β (corpusLs (segsAir segRoots))]

/-- The column counts. -/
def jKs (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) : List Nat :=
  let k := fun A : AirD => [A.width, 4 * ((corpusLs A).length + 1)]
  k memAirC ++ k (cpuAirCJ hd0 stk0 ctr0 n nilA) ++ k (witAir N W) ++ k popAirCJ ++ k instwAirCJ ++
    k (tmplAirCJ jets) ++ k (hdrAirCJ jets) ++ k (rootsAirCJ roots) ++ k (progAirC heap N W) ++ k (segsAir segRoots)

theorem jCols_shaped (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) {heap : List Cell} {N W : Nat}
    {segRoots : List Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat}
    (hM : Mm.h = 2 ^ (tbM + 1)) (hC : C.h = 2 ^ (tbC + 1)) (hW : Wt.h = 2 ^ 9)
    (hPo : Po.h = 2 ^ (tbPo + 1)) (hI : Iw.h = 2 ^ (tbI + 1)) (hT : Tm.h = 2 ^ (tpT + 1))
    (hH : Hd.h = 2 ^ (tpH + 1)) (hR : Rt.h = 2 ^ (tpR + 1))
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub segRoots).h = 2 ^ (tpS + 1))
    (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF) (t : Nat → Tup) (α β : EF) :
    Shaped ((jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv).map QGroup.ext)
        (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t α β) ∧
      (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t α β).map List.length =
        jKs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets := by
  have shp := fun (T : Table) (A : AirD) => And.intro (mainCols_shape T A.width)
    (permCols_shape T (busAlphas (prefixOf α (off β)) A) β (corpusLs A))
  obtain ⟨m1, p1⟩ := shp (jMemT Mm t) memAirC
  obtain ⟨m2, p2⟩ := shp (jCpuT C t) (cpuAirCJ hd0 stk0 ctr0 n nilA)
  obtain ⟨m3, p3⟩ := shp (jWitT Wt t) (witAir N W)
  obtain ⟨m4, p4⟩ := shp (jPoT Po t) popAirCJ
  obtain ⟨m5, p5⟩ := shp (jIwT Iw t) instwAirCJ
  obtain ⟨m6, p6⟩ := shp (jTmT Tm t) (tmplAirCJ jets)
  obtain ⟨m7, p7⟩ := shp (jHdT Hd t) (hdrAirCJ jets)
  obtain ⟨m8, p8⟩ := shp (jRtT Rt t) (rootsAirCJ roots)
  obtain ⟨m9, p9⟩ := shp (progTableC heap N W) (progAirC heap N W)
  obtain ⟨m10, p10⟩ := shp (segsPub segRoots) (segsAir segRoots)
  have hMh : (jMemT Mm t).h = 2 ^ (tbM + 1) := hM
  have hCh : (jCpuT C t).h = 2 ^ (tbC + 1) := hC
  have hWh : (jWitT Wt t).h = 2 ^ (8 + 1) := hW
  have hPoh : (jPoT Po t).h = 2 ^ (tbPo + 1) := hPo
  have hIh : (jIwT Iw t).h = 2 ^ (tbI + 1) := hI
  have hTh : (jTmT Tm t).h = 2 ^ (tpT + 1) := hT
  have hHh : (jHdT Hd t).h = 2 ^ (tpH + 1) := hH
  have hRh : (jRtT Rt t).h = 2 ^ (tpR + 1) := hR
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_, fun c hc => ?_, trivial⟩, ?_⟩
  · rw [m1.2 c hc, hMh]; rfl
  · rw [p1.2 c hc, hMh]; rfl
  · rw [m2.2 c hc, hCh]; rfl
  · rw [p2.2 c hc, hCh]; rfl
  · rw [m3.2 c hc, hWh]; rfl
  · rw [p3.2 c hc, hWh]; rfl
  · rw [m4.2 c hc, hPoh]; rfl
  · rw [p4.2 c hc, hPoh]; rfl
  · rw [m5.2 c hc, hIh]; rfl
  · rw [p5.2 c hc, hIh]; rfl
  · rw [m6.2 c hc, hTh]; rfl
  · rw [p6.2 c hc, hTh]; rfl
  · rw [m7.2 c hc, hHh]; rfl
  · rw [p7.2 c hc, hHh]; rfl
  · rw [m8.2 c hc, hRh]; rfl
  · rw [p8.2 c hc, hRh]; rfl
  · rw [m9.2 c hc, hPg]; rfl
  · rw [p9.2 c hc, hPg]; rfl
  · rw [m10.2 c hc, hSg]; rfl
  · rw [p10.2 c hc, hSg]; rfl
  · show [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] = _
    rw [m1.1, p1.1, m2.1, p2.1, m3.1, p3.1, m4.1, p4.1, m5.1, p5.1, m6.1, p6.1, m7.1, p7.1, m8.1, p8.1,
      m9.1, p9.1, m10.1, p10.1]; rfl

/-- The transcript's tables. -/
def jTabs (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table) (t : Nat → Tup) :
    List (AirD × Table) :=
  compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets (jCpuT C t) (jMemT Mm t) (progTableC heap N W)
    (jWitT Wt t) (segsPub segRoots) (jRtT Rt t) (jHdT Hd t) (jTmT Tm t) (jPoT Po t) (jIwT Iw t)

-- ---------------------------------------------------------------------------
-- The AIRs and their blinding columns
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
/-- **Every AIR of the circuit with jets meets `AirP3`.** -/
theorem compJ_airs_P3 (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) :
    AirP3 memAirC = true ∧ AirP3 (cpuAirCJ hd0 stk0 ctr0 n nilA) = true ∧ AirP3 (witAir N W) = true ∧
      AirP3 popAirCJ = true ∧ AirP3 instwAirCJ = true ∧ AirP3 (tmplAirCJ jets) = true ∧
      AirP3 (hdrAirCJ jets) = true ∧ AirP3 (rootsAirCJ roots) = true ∧ AirP3 (progAirC heap N W) = true ∧
      AirP3 (segsAir segRoots) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- **Every blinding column of the circuit with jets is one its AIR's
    constraints avoid** (or flag as boolean). -/
theorem compJ_blind_ok (hd0 stk0 ctr0 n nilA : Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) (N W : Nat) :
    blindOK memAirC 5 = true ∧ blindOK (cpuAirCJ hd0 stk0 ctr0 n nilA) BLAJ = true ∧
      blindOK (cpuAirCJ hd0 stk0 ctr0 n nilA) BLBJ = true ∧ blindOK (cpuAirCJ hd0 stk0 ctr0 n nilA) BLCJ = true ∧
      blindOK (witAir N W) WT_BLIND = true ∧ blindOK popAirCJ popAir.width = true ∧
      blindOK popAirCJ (popAir.width + 5) = true ∧ blindOK instwAirCJ instwAir.width = true ∧
      blindOK instwAirCJ (instwAir.width + 5) = true ∧ blindOK (tmplAirCJ jets) 1 = true ∧
      blindOK (tmplAirCJ jets) 6 = true ∧ blindOK (hdrAirCJ jets) 1 = true ∧ blindOK (hdrAirCJ jets) 6 = true ∧
      blindOK (rootsAirCJ roots) 1 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- The quotient tables and the PCS
-- ---------------------------------------------------------------------------

/-- **The proof with jets' ten quotient tables**, with their data: the
    private tables' terminals from the view (`tvAt`, in `compJViewN`'s
    order), the public tables' from the challenges. -/
def jTs (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table)
    (tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat) (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ : EF)
    (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F)) :
    List (QTab × ((Nat → Tup) → EF → EF → List F → List (List (List F) × List F))) :=
  let tv := fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t
  let qs := jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv
  let cols := jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw
  let tabs := jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw
  let q := fun (A : AirD) (tm : EF → EF → List EF → EF) (tb : Nat) (T : Table) (g : Nat) (S : List F)
      (ws : List (EF → EF → List F)) =>
    (bbTab off A tm tb (2 ^ (tb + 1) - 1) T g (g + 1) S ζ ws,
     bbData off tv A tm tb (2 ^ (tb + 1) - 1) T g (g + 1) S ζ ws qs cols tabs)
  [q memAirC (tvAt 0) tbM Mm 0 SM wm,
   q (cpuAirCJ hd0 stk0 ctr0 n nilA) (tvAt 1) tbC C 2 SC wc,
   q (witAir N W) (tvAt 2) 8 Wt 4 S9 ww,
   q popAirCJ (tvAt 3) tbPo Po 6 SPo wpo,
   q instwAirCJ (tvAt 4) tbI Iw 8 SI wi,
   q (tmplAirCJ jets) (tvAt 5) tpT Tm 10 ST wt,
   q (hdrAirCJ jets) (tvAt 6) tpH Hd 12 SH wh,
   q (rootsAirCJ roots) (tvAt 7) tpR Rt 14 SR wr,
   q (progAirC heap N W) (progTmC off heap N W) tpP (progTableC heap N W) 16 SP wp,
   q (segsAir segRoots) (segsTm off segRoots) tpS (segsPub segRoots) 18 SS wsg]

section
variable {V : Type} (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat)
  (segRoots : List Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table)
  (tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat) (SM SC S9 SPo SI ST SH SR SP SS : List F) (ζ : EF)
  (qv : EF → EF → List EF → F → List F → List F → List EF)
  (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F)) (ncw : Nat) (αb : EF)
  (fri : EF → EF → List (EF → EF) → V)

/-- **The proof with jets' PCS**, its simulator and its randomness. -/
def jPcs := pcsFri off (fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t)
  (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv)
  (jKs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets)
  (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw)
  ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
    tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst)
  (fun t α β ms => (jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo
    tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map
      fun p => p.2 t α β ms) ncw αb fri

def jPsim := psimFri (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv)
  (jKs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets)
  ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH tpR
    tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst) ncw αb fri

def jNR : Nat :=
  P ^ (friN1 (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv)
      (jKs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets)
      ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH
        tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst) +
    friN2 (jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv)
      ((jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT tpH
        tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg).map Prod.fst) ncw)
end

set_option maxRecDepth 100000 in
/-- **The proof with jets' hiding PCS hides exactly**: `comp_pcs` for the
    ten tables.  With the private tables meeting `Sat` at heights
    `2^(tb+1)` (the witness's `2^9`), the public ones at `2^(tp+1)`, every
    `tb, tp ≤ 24`, the query points off each trace domain and few enough,
    `ζ` generating the extension and the FRI challenge `αb` generic, the
    PCS whose view is every group's openings, every quotient table's
    chunks, every codeword and FRI meets `PCSCloseN` with `ε = 0`, over
    the transcript's values with jets. -/
theorem compJ_pcs {V : Type} (off : EF → String → EF) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat}
    {segRoots : List Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Wt Rt Hd Tm Po Iw : Table}
    (hsC : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) C) (hsM : Sat memAirC Mm) (hsW : Sat (witAir N W) Wt)
    (hsPo : Sat popAirCJ Po) (hsI : Sat instwAirCJ Iw) (hsT : Sat (tmplAirCJ jets) Tm)
    (hsH : Sat (hdrAirCJ jets) Hd) (hsR : Sat (rootsAirCJ roots) Rt)
    {tbM tbC tbPo tbI tpT tpH tpR tpP tpS : Nat} (hbM : tbM ≤ 24) (hbC : tbC ≤ 24) (hbPo : tbPo ≤ 24)
    (hbI : tbI ≤ 24) (hbT : tpT ≤ 24) (hbH : tpH ≤ 24) (hbR : tpR ≤ 24) (hbP : tpP ≤ 24) (hbS : tpS ≤ 24)
    (hM : Mm.h = 2 ^ (tbM + 1)) (hC : C.h = 2 ^ (tbC + 1)) (hW : Wt.h = 2 ^ 9)
    (hPo : Po.h = 2 ^ (tbPo + 1)) (hI : Iw.h = 2 ^ (tbI + 1)) (hT : Tm.h = 2 ^ (tpT + 1))
    (hH : Hd.h = 2 ^ (tpH + 1)) (hR : Rt.h = 2 ^ (tpR + 1))
    (hPg : (progTableC heap N W).h = 2 ^ (tpP + 1)) (hSg : (segsPub segRoots).h = 2 ^ (tpS + 1))
    {SM SC S9 SPo SI ST SH SR SP SS : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wpo wi wt wh wr wp wsg : List (EF → EF → List F))
    (hSM : ∀ x ∈ SM, x ∉ cosetL 1 (bbGen (tbM + 1)) (2 ^ (tbM + 1)))
    (hSC : ∀ x ∈ SC, x ∉ cosetL 1 (bbGen (tbC + 1)) (2 ^ (tbC + 1)))
    (hS9 : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPo : ∀ x ∈ SPo, x ∉ cosetL 1 (bbGen (tbPo + 1)) (2 ^ (tbPo + 1)))
    (hSI : ∀ x ∈ SI, x ∉ cosetL 1 (bbGen (tbI + 1)) (2 ^ (tbI + 1)))
    (hST : ∀ x ∈ ST, x ∉ cosetL 1 (bbGen (tpT + 1)) (2 ^ (tpT + 1)))
    (hSH : ∀ x ∈ SH, x ∉ cosetL 1 (bbGen (tpH + 1)) (2 ^ (tpH + 1)))
    (hSR : ∀ x ∈ SR, x ∉ cosetL 1 (bbGen (tpR + 1)) (2 ^ (tpR + 1)))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tpP + 1)) (2 ^ (tpP + 1)))
    (hSS : ∀ x ∈ SS, x ∉ cosetL 1 (bbGen (tpS + 1)) (2 ^ (tpS + 1)))
    (hszM : 2 * SM.length + 8 ≤ 2 ^ (tbM + 1)) (hszC : 2 * SC.length + 8 ≤ 2 ^ (tbC + 1))
    (hsz9 : 2 * S9.length + 8 ≤ 2 ^ 9) (hszPo : 2 * SPo.length + 8 ≤ 2 ^ (tbPo + 1))
    (hszI : 2 * SI.length + 8 ≤ 2 ^ (tbI + 1)) (hszT : 2 * ST.length + 8 ≤ 2 ^ (tpT + 1))
    (hszH : 2 * SH.length + 8 ≤ 2 ^ (tpH + 1)) (hszR : 2 * SR.length + 8 ≤ 2 ^ (tpR + 1))
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tpP + 1)) (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1))
    (hζ : ∀ x : F, EF.ofF x ≠ ζ) (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} {fri : EF → EF → List (EF → EF) → V}
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw) :
    let tv := fun pre β t => compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t
    let Ts := jTs off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw tbM tbC tbPo tbI tpT
      tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv wm wc ww wpo wi wt wh wr wp wsg
    let qs := jGroups tbM tbC tbPo tbI tpT tpH tpR tpP tpS SM SC S9 SPo SI ST SH SR SP SS ζ qv
    let ks := jKs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets
    PCSCloseN off (P ^ (friN1 qs ks (Ts.map Prod.fst) + friN2 qs (Ts.map Prod.fst) ncw)) tv
      (pcsFri off tv qs ks (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw)
        (Ts.map Prod.fst) (fun t α β ms => Ts.map fun p => p.2 t α β ms) ncw αb fri)
      (psimFri qs ks (Ts.map Prod.fst) ncw αb fri) 0 := by
  intro tv Ts qs ks
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ :=
    compJ_blind_ok hd0 stk0 ctr0 n nilA roots jets N W
  obtain ⟨pM, pC, pW, pPo, pI, pT, pH, pR, pP, pS⟩ := compJ_airs_P3 hd0 stk0 ctr0 n nilA heap N W segRoots roots jets
  have hm : ∀ b, 2 ^ (b + 1) - 1 + 1 = 2 ^ (b + 1) := fun b => Nat.sub_add_cancel Nat.one_le_two_pow
  have h4 : ∀ (S : List F) b, 2 * S.length + 8 ≤ 2 ^ (b + 1) → S.length + 4 ≤ 2 ^ (b + 1) - 1 + 1 :=
    fun S b h => by rw [hm b]; omega
  have hoff : ∀ (S : List F) b, (∀ x ∈ S, x ∉ cosetL 1 (bbGen (b + 1)) (2 ^ (b + 1))) →
      ∀ x ∈ S, x ∉ cosetL 1 (bbGen (b + 1)) (2 ^ (b + 1) - 1 + 1) := fun S b h => by rw [hm b]; exact h
  have hsz9' : 2 * S9.length + 8 ≤ 2 ^ (8 + 1) := hsz9
  have hS9' : ∀ x ∈ S9, x ∉ cosetL 1 (bbGen (8 + 1)) (2 ^ (8 + 1)) := hS9
  have hW' : Wt.h = 2 ^ (8 + 1) := hW
  have hcl : ∀ (a : Nat), a + 1 < 20 → ∀ t α β, ∀ j ∈ [a, a + 1],
      j < (jCols off hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t α β).length :=
    fun a ha _ _ _ j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      show j < 20
      rcases hj with rfl | rfl <;> omega
  have hmem : ∀ i (hi : i < 10) t, (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t)[i]'(by
      show i < 10; exact hi) ∈ jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw t :=
    fun i hi t => List.getElem_mem _
  have hq : ∀ g (hg : g + 1 < 20), ∃ h : g < qs.length, qs[g]'h = qs[g]'(by show g < 20; omega) :=
    fun g hg => ⟨by show g < 20; omega, rfl⟩
  refine pcsCloseN_fri_tabs (fun q hq => ?_) (by rfl)
    (fun t α β => jCols_shaped off hd0 stk0 ctr0 n nilA hM hC hW hPo hI hT hH hR hPg hSg SM SC S9 SPo SI ST SH SR SP
      SS ζ qv t α β)
    hdb haw hncw off tv Ts (fun p hp => ?_)
  · simp only [jGroups, List.mem_cons, List.not_mem_nil, or_false] at hq
    have gM := bbGroup_OK (tb := tbM) (qv := qv) (by omega) hSM hζ hszM
    have gC := bbGroup_OK (tb := tbC) (qv := qv) (by omega) hSC hζ hszC
    have g9 := bbGroup_OK (tb := 8) (qv := qv) (by decide) hS9' hζ hsz9'
    have gPo := bbGroup_OK (tb := tbPo) (qv := qv) (by omega) hSPo hζ hszPo
    have gI := bbGroup_OK (tb := tbI) (qv := qv) (by omega) hSI hζ hszI
    have gT := bbGroup_OK (tb := tpT) (qv := qv) (by omega) hST hζ hszT
    have gH := bbGroup_OK (tb := tpH) (qv := qv) (by omega) hSH hζ hszH
    have gR := bbGroup_OK (tb := tpR) (qv := qv) (by omega) hSR hζ hszR
    have gP := bbGroup_OK (tb := tpP) (qv := qv) (by omega) hSP hζ hszP
    have gS := bbGroup_OK (tb := tpS) (qv := qv) (by omega) hSS hζ hszS
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact gM
    · exact gM
    · exact gC
    · exact gC
    · exact g9
    · exact g9
    · exact gPo
    · exact gPo
    · exact gI
    · exact gI
    · exact gT
    · exact gT
    · exact gH
    · exact gH
    · exact gR
    · exact gR
    · exact gP
    · exact gP
    · exact gS
    · exact gS
  · simp only [Ts, jTs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tabsHonest_bb off tv pM (tb := tbM) (lq := 1) (m := 2 ^ (tbM + 1) - 1) (gm := 0) (gp := 1)
        (tm := tvAt 0) (by omega) (by decide) (by omega) (hm tbM) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jMemT Mm) Mm (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 1 (by decide) t)
        (hcl 0 (by decide))
        (fun t α β => ⟨sat_setBlind hsM b0 _, by show Mm.h = _; rw [hM, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SM tbM hSM) (h4 SM tbM hszM)
    · exact tabsHonest_bb off tv pC (tb := tbC) (lq := 1) (m := 2 ^ (tbC + 1) - 1) (gm := 2) (gp := 3)
        (tm := tvAt 1) (by omega) (by decide) (by omega) (hm tbC) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jCpuT C) C (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 0 (by decide) t)
        (hcl 2 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind (sat_setBlind hsC b1 _) b2 _) b3 _, by show C.h = _; rw [hC, hm],
          rfl, rfl, rfl⟩)
        hζ hdet (hoff SC tbC hSC) (h4 SC tbC hszC)
    · exact tabsHonest_bb off tv pW (tb := 8) (lq := 1) (m := 2 ^ (8 + 1) - 1) (gm := 4) (gp := 5)
        (tm := tvAt 2) (by decide) (by decide) (by decide) (hm 8) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jWitT Wt) Wt (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 3 (by decide) t)
        (hcl 4 (by decide))
        (fun t α β => ⟨sat_setBlind hsW b4 _, by show Wt.h = _; rw [hW', hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff S9 8 hS9') (h4 S9 8 hsz9')
    · exact tabsHonest_bb off tv pPo (tb := tbPo) (lq := 1) (m := 2 ^ (tbPo + 1) - 1) (gm := 6) (gp := 7)
        (tm := tvAt 3) (by omega) (by decide) (by omega) (hm tbPo) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jPoT Po) Po (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 8 (by decide) t)
        (hcl 6 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsPo b5 _) b6 _, by show Po.h = _; rw [hPo, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SPo tbPo hSPo) (h4 SPo tbPo hszPo)
    · exact tabsHonest_bb off tv pI (tb := tbI) (lq := 1) (m := 2 ^ (tbI + 1) - 1) (gm := 8) (gp := 9)
        (tm := tvAt 4) (by omega) (by decide) (by omega) (hm tbI) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jIwT Iw) Iw (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 9 (by decide) t)
        (hcl 8 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsI b7 _) b8 _, by show Iw.h = _; rw [hI, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SI tbI hSI) (h4 SI tbI hszI)
    · exact tabsHonest_bb off tv pT (tb := tpT) (lq := 1) (m := 2 ^ (tpT + 1) - 1) (gm := 10) (gp := 11)
        (tm := tvAt 5) (by omega) (by decide) (by omega) (hm tpT) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jTmT Tm) Tm (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 7 (by decide) t)
        (hcl 10 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsT b9 _) b10 _, by show Tm.h = _; rw [hT, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff ST tpT hST) (h4 ST tpT hszT)
    · exact tabsHonest_bb off tv pH (tb := tpH) (lq := 1) (m := 2 ^ (tpH + 1) - 1) (gm := 12) (gp := 13)
        (tm := tvAt 6) (by omega) (by decide) (by omega) (hm tpH) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jHdT Hd) Hd (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 6 (by decide) t)
        (hcl 12 (by decide))
        (fun t α β => ⟨sat_setBlind (sat_setBlind hsH b11 _) b12 _, by show Hd.h = _; rw [hH, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SH tpH hSH) (h4 SH tpH hszH)
    · exact tabsHonest_bb off tv pR (tb := tpR) (lq := 1) (m := 2 ^ (tpR + 1) - 1) (gm := 14) (gp := 15)
        (tm := tvAt 7) (by omega) (by decide) (by omega) (hm tpR) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (jRtT Rt) Rt (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 5 (by decide) t)
        (hcl 14 (by decide))
        (fun t α β => ⟨sat_setBlind hsR b13 _, by show Rt.h = _; rw [hR, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SR tpR hSR) (h4 SR tpR hszR)
    · exact tabsHonest_bb off tv pP (tb := tpP) (lq := 1) (m := 2 ^ (tpP + 1) - 1) (gm := 16) (gp := 17)
        (tm := progTmC off heap N W) (by omega) (by decide) (by omega) (hm tpP) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (fun _ => progTableC heap N W) (progTableC heap N W) (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 2 (by decide) t)
        (hcl 16 (by decide))
        (fun t α β => ⟨(progC_sat heap N W).1, by rw [hPg, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SP tpP hSP) (h4 SP tpP hszP)
    · exact tabsHonest_bb off tv pS (tb := tpS) (lq := 1) (m := 2 ^ (tpS + 1) - 1) (gm := 18) (gp := 19)
        (tm := segsTm off segRoots) (by omega) (by decide) (by omega) (hm tpS) ⟨by show _ < 20; decide, rfl⟩
        ⟨by show _ < 20; decide, rfl⟩ (fun _ => segsPub segRoots) (segsPub segRoots) (fun _ => rfl)
        (jTabs hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Wt Rt Hd Tm Po Iw) (fun t => hmem 4 (by decide) t)
        (hcl 18 (by decide))
        (fun t α β => ⟨⟨segRows_pos _, fun c hc => nomatch hc⟩, by rw [hSg, hm], rfl, rfl, rfl⟩)
        hζ hdet (hoff SS tpS hSS) (h4 SS tpS hszS)

end Circuit
