import Ski.ZK.FSOpenFri

/-!
# Each circuit under Fiat–Shamir, the commitment opened

`fs_open` applied to each circuit (`sud_fs_open`, `wit_fs_open`,
`comp_fs_open`): the hashed commitment
is of the main groups' matrices, their masked polynomials and random
codewords (`mainF2`), the view opens them at the query points
(`pcsFri_ov2`), and the simulator commits interpolants through its own
openings (`sdF`, `psimFri_ov2`).  Unlike
`Ski/ZK/FSInst.lean` the commitment is opened: the view's opened values
are the committed data's, and the opening proof is in the output.

What the opening reveals (`op`): each main group's matrix at the query
points, its masked columns' and its random codewords' values, as a
Plonky3 Merkle opening reveals the queried rows of a matrix that carries
both (`hiding_pcs.rs`).  The main columns' values at the next rows `g·S`
enter the view only through the quotient values, and the values at `ζ`
are evaluations, not leaves.  The model's view does show the codewords
at `g·S` (each group's codeword matrix opens at its extended points,
`traceInfo`); `op` leaves those out, so `ComPfHides` is assumed for an
opening of the rows at `S` alone, as Plonky3's query phase opens them,
and the codewords' values at `g·S` count as evaluations the view shows,
a difference from Plonky3, which shows none.  The query points may repeat
(`finterp_eval_cons`).

Scope.  One proof per oracle; one round (the LogUp challenges, at
generic `β`; `ζ`, the FRI challenge and the query points stay fixed
parameters, drawn per height independently where Plonky3 derives them
from one index); the oracle ideal and `Com` a primitive apart from it;
hiding perfect, alone and given the openings.  Only the main commitment
is in the output; the later commitments are absent.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit Sudoku SudokuText

theorem sudCols_main (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Wt : Table)
    (t : Nat → Tup) (α β α' β' : EF) :
    ∀ k ∈ [0, 2, 4, 6], (sudCols off hd0 stk0 ctr0 heap C Mm Wt t α β).getD k [] = (sudCols off hd0 stk0 ctr0 heap C Mm Wt t α' β').getD k [] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp only [sudCols, List.getD_cons_zero, List.getD_cons_succ]

set_option maxRecDepth 100000 in
/-- **The Sudoku proof under Fiat–Shamir, its commitment opened**, in the
    programmable random-oracle model: the LogUp challenges are the
    oracle's answer at the commitment of the main groups' masked
    polynomials, the proof opens that commitment (`Pf`) beside the
    view, and the simulator commits and opens polynomials through the
    values its own view shows (`fs_open`).  Assumed: the commitment hides
    given its openings (`ComPfHides`) and alone (`ComHides`); the other challenges stay generic and fixed. -/
theorem sud_fs_open {V Wv Pp : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
    {ρ : Nat → Bool} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hA : AcceptsFrom A (stmtMachine ρ 729 (sudokuExpr (cluesOf puzzle)) ACC REJ) k row)
    (hacc : rd A (row (k - 1)).ctr (row (k - 1)).hd = some (.atom ACC))
    (hlen : A.length = 2 ^ 16) (hk : k ≤ 2 ^ 16)
    {tP : Nat} (htp : tP = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ).heap)
    {S16 S10 SP : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tP + 1)) (2 ^ (tP + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgζ : Generic ζ) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS n : Nat} (Com : List (List (List F)) → Nat → Nat) (Pf : List (List (List F)) → Nat → Pp)
    (hcom : ComHides NS Com) (hpf : ComPfHides NS Com Pf (opF ((sudGroups tP S16 S10 SP ζ qv).map (·.base.S)) [0, 2, 4, 6]))
    (hrange : ∀ d σ, Com d σ < n) (d0 : List (List (List F)))
    (E : Nat → Nat → Option Pp × TViewN (SudPV (V × Wv)) EF → Bool) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp ncw
    let pcs := fun t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psim := fun α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let qsG := sudGroups tP S16 S10 SP ζ qv
    let Ss := qsG.map (·.base.S)
    let mk := [0, 2, 4, 6]
    let tq := (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP S16 S10 SP ζ qv wm wc ww wp).map Prod.fst
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let main := fun (t : Nat → Tup) (r : Nat) => mainF2 qsG ks cols tq ncw mk t (r % NR0)
    let sop := fun (r : Nat) (_ : Nat → Tup) => opF Ss mk (mainZ2 qsG ks tq ncw mk (r % NR0))
    let ov : TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss mk pv)
      | none => none
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (realVN off tabs tv tp pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          realVN off tabs tv tp pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) ≤
      sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sdF Ss mk (sop r t)) σ) H c) (Com (sdF Ss mk (sop r t)) σ)
        (some (Pf (sdF Ss mk (sop r t)) σ), simVN off tp chainBus (fun _ => false) chainPar 3 tp psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sdF Ss mk (sop r t)) σ) H c) (Com (sdF Ss mk (sop r t)) σ)
        (some (Pf (sdF Ss mk (sop r t)) σ), simVN off tp chainBus (fun _ => false) chainPar 3 tp psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
      (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (realVN off tabs tv tp pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          realVN off tabs tv tp pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) := by
  intro blank C Pg Wt Mm NR0 pcs psim NR tabs tv tp M qsG Ss mk tq ks cols main sop ov
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sm, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := sud_pcsX (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv
    wm wc ww wp hS16 hS10 hSP hsz16 hsz hszP (generic_ofF_ne hgζ) (mz_generic hgζ) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
  have h1 := fun E => (sud_transcriptG off NR 0 pcs psim hbal hun hpcs E).1
  have h2 := fun E => (sud_transcriptG off NR 0 pcs psim hbal hun hpcs E).2
  have hmk : ∀ k ∈ mk, k < qsG.length ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, sudCols_main off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt t α β EF.zero EF.zero k hk⟩⟩
  have hlen : ∀ t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length := fun t α β => by
    rw [(sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg S16 S10 SP ζ qv t α β).2, (sudCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) hPg S16 S10 SP ζ qv t EF.zero EF.zero).2]
  have hrvo : ∀ α β r t, realVN off tabs tv tp pcs α β r t = none ∨ ov (realVN off tabs tv tp pcs α β r t) = some (opF Ss mk (main t r)) := by
    intro α β r t
    unfold realVN
    split
    · exact .inl rfl
    · exact .inr (congrArg some (pcsFri_ov2 off _ qsG ks cols tq _ ncw αb _ mk hmk hlen rfl t α β (r % NR0)))
  have hsvo : ∀ α β r t, ov (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t) = some (sop r t) := fun α β r t =>
    congrArg some (psimFri_ov2 qsG ks tq ncw αb _ mk (fun k hk => (hmk k hk).1) rfl α β _ (r % NR0))
  have hsd : ∀ t r, opF Ss mk (sdF Ss mk (opF Ss mk (main t r))) = opF Ss mk (main t r) := fun t r =>
    opF_sdF Ss mk _
  exact fs_open Com Pf (opF Ss mk) (sdF Ss mk) d0 hcom hpf hrange ov rfl main hsd sop h1 h2
    (fun α β r t => realVN_cases _ _ _ _ _ α β r t) (fun α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) hrvo hsvo E

theorem witCols_main (off : EF → String → EF) (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Wt : Table)
    (t : Nat → Tup) (α β α' β' : EF) :
    ∀ k ∈ [0, 2, 4, 6], (wCols off hd0 stk0 ctr0 heap W C Mm Wt t α β).getD k [] = (wCols off hd0 stk0 ctr0 heap W C Mm Wt t α' β').getD k [] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp only [wCols, List.getD_cons_zero, List.getD_cons_succ]

set_option maxRecDepth 100000 in
/-- **The hidden-term proof under Fiat–Shamir, its commitment opened**, in the
    programmable random-oracle model: the LogUp challenges are the
    oracle's answer at the commitment of the main groups' masked
    polynomials, the proof opens that commitment (`Pf`) beside the
    view, and the simulator commits and opens polynomials through the
    values its own view shows (`fs_open`).  Assumed: the commitment hides
    given its openings (`ComPfHides`) and alone (`ComHides`); the other challenges stay generic and fixed. -/
theorem wit_fs_open {V Wv Pp : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
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
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgζ : Generic ζ) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS n : Nat} (Com : List (List (List F)) → Nat → Nat) (Pf : List (List (List F)) → Nat → Pp)
    (hcom : ComHides NS Com) (hpf : ComPfHides NS Com Pf (opF ((wGroups tP S10 S9 SP ζ qv).map (·.base.S)) [0, 2, 4, 6]))
    (hrange : ∀ d σ, Com d σ < n) (d0 : List (List (List F)))
    (E : Nat → Nat → Option Pp × TViewN (PcsPV (V × Wv)) EF → Bool) :
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw
    let pcs := fun t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psim := fun α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let qsG := wGroups tP S10 S9 SP ζ qv
    let Ss := qsG.map (·.base.S)
    let mk := [0, 2, 4, 6]
    let tq := (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP S10 S9 SP ζ qv wm wc ww wp).map Prod.fst
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let main := fun (t : Nat → Tup) (r : Nat) => mainF2 qsG ks cols tq ncw mk t (r % NR0)
    let sop := fun (r : Nat) (_ : Nat → Tup) => opF Ss mk (mainZ2 qsG ks tq ncw mk (r % NR0))
    let ov : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss mk pv)
      | none => none
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (realVN off tabs tv ptm pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          realVN off tabs tv ptm pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) ≤
      sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sdF Ss mk (sop r t)) σ) H c) (Com (sdF Ss mk (sop r t)) σ)
        (some (Pf (sdF Ss mk (sop r t)) σ), simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sdF Ss mk (sop r t)) σ) H c) (Com (sdF Ss mk (sop r t)) σ)
        (some (Pf (sdF Ss mk (sop r t)) σ), simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
      (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (realVN off tabs tv ptm pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          realVN off tabs tv ptm pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) := by
  intro blank C Pg Wt Mm NR0 pcs psim NR tabs tv ptm M qsG Ss mk tq ks cols main sop ov
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sm, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := wit_pcsX (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
    wm wc ww wp hS10 hS9 hSP hsz10 hsz9 hszP (generic_ofF_ne hgζ) (mz_generic hgζ) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
  have h1 := fun E => (wit_transcriptG off NR 0 pcs psim hbal hun hpcs E).1
  have h2 := fun E => (wit_transcriptG off NR 0 pcs psim hbal hun hpcs E).2
  have hmk : ∀ k ∈ mk, k < qsG.length ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 8 := by rcases hk' with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, witCols_main off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt t α β EF.zero EF.zero k hk⟩⟩
  have hlen : ∀ t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length := fun t α β => by
    rw [(wCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 10) hlen hWh hPg S10 S9 SP ζ qv t α β).2, (wCols_shaped off blank.hd blank.stk blank.heap.length (rfl : C.h = 2 ^ 10) hlen hWh hPg S10 S9 SP ζ qv t EF.zero EF.zero).2]
  have hrvo : ∀ α β r t, realVN off tabs tv ptm pcs α β r t = none ∨ ov (realVN off tabs tv ptm pcs α β r t) = some (opF Ss mk (main t r)) := by
    intro α β r t
    unfold realVN
    split
    · exact .inl rfl
    · exact .inr (congrArg some (pcsFri_ov2 off _ qsG ks cols tq _ ncw αb _ mk hmk hlen rfl t α β (r % NR0)))
  have hsvo : ∀ α β r t, ov (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim α β r t) = some (sop r t) := fun α β r t =>
    congrArg some (psimFri_ov2 qsG ks tq ncw αb _ mk (fun k hk => (hmk k hk).1) rfl α β _ (r % NR0))
  have hsd : ∀ t r, opF Ss mk (sdF Ss mk (opF Ss mk (main t r))) = opF Ss mk (main t r) := fun t r =>
    opF_sdF Ss mk _
  exact fs_open Com Pf (opF Ss mk) (sdF Ss mk) d0 hcom hpf hrange ov rfl main hsd sop h1 h2
    (fun α β r t => realVN_cases _ _ _ _ _ α β r t) (fun α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) hrvo hsvo E

theorem compCols_main (off : EF → String → EF) (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat) (C Mm Wt : Table)
    (t : Nat → Tup) (α β α' β' : EF) :
    ∀ k ∈ [0, 2, 4, 6, 8], (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t α β).getD k [] = (cCols off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt t α' β').getD k [] := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> simp only [cCols, List.getD_cons_zero, List.getD_cons_succ]

set_option maxRecDepth 100000 in
/-- **The composed proof under Fiat–Shamir, its commitment opened**, in the
    programmable random-oracle model: the LogUp challenges are the
    oracle's answer at the commitment of the main groups' masked
    polynomials, the proof opens that commitment (`Pf`) beside the
    view, and the simulator commits and opens polynomials through the
    values its own view shows (`fs_open`).  Assumed: the commitment hides
    given its openings (`ComPfHides`) and alone (`ComHides`); the other challenges stay generic and fixed. -/
theorem comp_fs_open {V Wv Pp : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    (hszS : 2 * SS.length + 8 ≤ 2 ^ (tpS + 1)) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V) (hncw : 4 ≤ ncw) (hgζ : Generic ζ) (hgα : Generic αb)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    {NS n : Nat} (Com : List (List (List F)) → Nat → Nat) (Pf : List (List (List F)) → Nat → Pp)
    (hcom : ComHides NS Com) (hpf : ComPfHides NS Com Pf (opF ((cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hrange : ∀ d σ, Com d σ < n) (d0 : List (List (List F)))
    (E : Nat → Nat → Option Pp × TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw
    let pcs := fun t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
      (friX fri Rb Ro (r / NR0)) t α β (r % NR0)
    let psim := fun α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS
      SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
      (friX fri Rb Ro (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
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
    let qsG := cGroups tbM tbC tpP tpS SM SC S9 SP SS ζ qv
    let Ss := qsG.map (·.base.S)
    let mk := [0, 2, 4, 6, 8]
    let tq := (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg).map Prod.fst
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let main := fun (t : Nat → Tup) (r : Nat) => mainF2 qsG ks cols tq ncw mk t (r % NR0)
    let sop := fun (r : Nat) (_ : Nat → Tup) => opF Ss mk (mainZ2 qsG ks tq ncw mk (r % NR0))
    let ov : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun v => match v with
      | some (pv, _) => some (ovF2 Ss mk pv)
      | none => none
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (realVN off tabs tv pb pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          realVN off tabs tv pb pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) ≤
      sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sdF Ss mk (sop r t)) σ) H c) (Com (sdF Ss mk (sop r t)) σ)
        (some (Pf (sdF Ss mk (sop r t)) σ), simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com (sdF Ss mk (sop r t)) σ) H c) (Com (sdF Ss mk (sop r t)) σ)
        (some (Pf (sdF Ss mk (sop r t)) σ), simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
      (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        ((ov (realVN off tabs tv pb pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)).map (fun _ => Pf (main t r) σ),
          realVN off tabs tv pb pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) := by
  intro m roots N C Pg Wt Mm NR0 pcs psim NR tabs tv pb ptm M qsG Ss mk tq ks cols main sop ov
  obtain ⟨hbal, hun⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
  obtain ⟨sc, sm, sw, hWh, _⟩ := comp_run_sats hR hrl hr hA hlen hLm hK hNW
  obtain ⟨p1, p2, s1, s2⟩ := comp_pub_heights hR hrl hA hlen hLm hK
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hlen
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; rfl
  have hpcs := comp_pcsX (heap := m.heap) (roots := roots) off sc sm sw (by omega) (by omega) (by omega) (by omega)
    hM hC hWh p2 s2 qv wm wc ww wp wsg hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS (generic_ofF_ne hgζ) (mz_generic hgζ) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
  have h1 := fun E => (comp_transcriptG off NR 0 pcs psim hbal hun hpcs E).1
  have h2 := fun E => (comp_transcriptG off NR 0 pcs psim hbal hun hpcs E).2
  have hmk : ∀ k ∈ mk, k < qsG.length ∧ ∀ t α β, k < (cols t α β).length ∧
      (cols t α β).getD k [] = (cols t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk' := hk
    simp only [mk, List.mem_cons, List.not_mem_nil, or_false] at hk'
    have hkn : k < 10 := by rcases hk' with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hkn, fun t α β => ⟨hkn, compCols_main off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt t α β EF.zero EF.zero k hk⟩⟩
  have hlen : ∀ t α β, (cols t α β).map List.length = (cols t EF.zero EF.zero).map List.length := fun t α β => by
    rw [(cCols_shaped off m.hd m.stk m.heap.length roots.length m.stk hM hC hWh p2 s2 SM SC S9 SP SS ζ qv t α β).2, (cCols_shaped off m.hd m.stk m.heap.length roots.length m.stk hM hC hWh p2 s2 SM SC S9 SP SS ζ qv t EF.zero EF.zero).2]
  have hrvo : ∀ α β r t, realVN off tabs tv pb pcs α β r t = none ∨ ov (realVN off tabs tv pb pcs α β r t) = some (opF Ss mk (main t r)) := by
    intro α β r t
    unfold realVN
    split
    · exact .inl rfl
    · exact .inr (congrArg some (pcsFri_ov2 off _ qsG ks cols tq _ ncw αb _ mk hmk hlen rfl t α β (r % NR0)))
  have hsvo : ∀ α β r t, ov (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim α β r t) = some (sop r t) := fun α β r t =>
    congrArg some (psimFri_ov2 qsG ks tq ncw αb _ mk (fun k hk => (hmk k hk).1) rfl α β _ (r % NR0))
  have hsd : ∀ t r, opF Ss mk (sdF Ss mk (opF Ss mk (main t r))) = opF Ss mk (main t r) := fun t r =>
    opF_sdF Ss mk _
  exact fs_open Com Pf (opF Ss mk) (sdF Ss mk) d0 hcom hpf hrange ov rfl main hsd sop h1 h2
    (fun α β r t => realVN_cases _ _ _ _ _ α β r t) (fun α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) hrvo hsvo E

end Circuit
