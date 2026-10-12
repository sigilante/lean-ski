import Ski.ZK.CompInst

/-!
# The witness-free matrices: preprocessed columns and randomization

Plonky3 commits matrices beside the trace and quotient groups that hold
no witness: each table's preprocessed columns (public rows, committed at
setup, with or without hiding randomness) and each table's randomization
polynomial (random columns alone).  Each is opened at the query points
and `ζ` and batched into FRI with the rest.  Here they enter as any
batched polynomials `Rb α β δ` joining FRI's input and any openings
`Ro α β δ` joining the view, drawn from their own randomness `δ < NR2`
and the challenges, never from the witness (`friX`).

For each circuit the PCS with them still hides exactly
(`sud_pcsX`, `wit_pcsX`, `comp_pcsX`, by `PCSCloseN.family`), and the
transcript theorems hold over it with no PCS term (`sud_hidingX`,
`wit_hidingX`, `comp_hidingX`).  This closes the earlier argument that
the preprocessed columns fold into FRI's view.  Setup randomness is
drawn once per verifying key, a fixed public draw: `NR2 = 1`, with `Rb`
and `Ro` closing over it; `NR2 > 1` models fresh randomness per proof.
Assumed: that FRI's view is a function of every matrix's batched
polynomial, as before; Plonky3's recombination of the per-matrix batches
(its `αb`-offset sums by height included) is a fixed function of
`Bs ++ Rb`, which `fri` absorbs.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit Sudoku SudokuText

/-- FRI with the witness-free matrices: their batched polynomials join its
    input and their openings join the view. -/
def friX {V Wv : Type} (fri : EF → EF → List (EF → EF) → V) (Rb : EF → EF → Nat → List (EF → EF))
    (Ro : EF → EF → Nat → Wv) (δ : Nat) : EF → EF → List (EF → EF) → V × Wv :=
  fun a b Bs => (fri a b (Bs ++ Rb a b δ), Ro a b δ)

set_option maxRecDepth 100000 in
/-- **The Sudoku proof's PCS with the witness-free matrices hides
    exactly.** -/
theorem sud_pcsX {V Wv : Type} (off : EF → String → EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Wt : Table}
    (hsC : Sat (cpuAirS hd0 stk0 ctr0 ACC) C) (hsM : Sat memAirC Mm) (hsW : Sat witAirS Wt)
    (hC : C.h = 2 ^ 16) (hM : Mm.h = 2 ^ 16) (hW : Wt.h = 2 ^ 10)
    {tp : Nat} (htp : tp ≤ 24) (hPg : (progTableS heap).h = 2 ^ (tp + 1))
    {S16 S10 SP : List F} {ζ : EF} (qv : EF → EF → List EF → F → List F → List F → List EF)
    (wm wc ww wp : List (EF → EF → List F))
    (hS16 : ∀ x ∈ S16, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ x ∈ S10, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSP : ∀ x ∈ SP, x ∉ cosetL 1 (bbGen (tp + 1)) (2 ^ (tp + 1)))
    (hsz16 : 2 * S16.length + 8 ≤ 2 ^ 16) (hsz : 2 * S10.length + 8 ≤ 2 ^ 10)
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tp + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv) :
    let NR := sudNR off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw
    PCSCloseN off (NR * NR2) (fun pre β t => sudViewN pre β hd0 stk0 ctr0 C Mm Wt t)
      (fun t α β r => sudPcs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw αb
        (friX fri Rb Ro (r / NR)) t α β (r % NR))
      (fun α β v r => sudPsim off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw αb
        (friX fri Rb Ro (r / NR)) α β v (r % NR)) 0 :=
  PCSCloseN.family (pcs := fun δ => sudPcs off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw αb
      (friX fri Rb Ro δ))
    (psim := fun δ => sudPsim off hd0 stk0 ctr0 heap C Mm Wt tp S16 S10 SP ζ qv wm wc ww wp ncw αb (friX fri Rb Ro δ))
    (fun δ => by apply sud_pcs (fri := friX fri Rb Ro δ) <;> assumption)

set_option maxRecDepth 100000 in
/-- **The hidden-term proof's PCS with the witness-free matrices hides
    exactly.** -/
theorem wit_pcsX {V Wv : Type} (off : EF → String → EF) {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat}
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
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv) :
    let NR := wNR off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw
    PCSCloseN off (NR * NR2) (fun pre β t => witViewN pre β hd0 stk0 ctr0 W C Mm Wt t)
      (fun t α β r => wPcs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw αb
        (friX fri Rb Ro (r / NR)) t α β (r % NR))
      (fun α β v r => wPsim off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw αb
        (friX fri Rb Ro (r / NR)) α β v (r % NR)) 0 :=
  PCSCloseN.family (pcs := fun δ => wPcs off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw αb
    (friX fri Rb Ro δ))
    (psim := fun δ => wPsim off hd0 stk0 ctr0 heap W C Mm Wt tp S10 S9 SP ζ qv wm wc ww wp ncw αb (friX fri Rb Ro δ))
    (fun δ => by apply wit_pcs (fri := friX fri Rb Ro δ) <;> assumption)

set_option maxRecDepth 100000 in
/-- **The composed proof's PCS with the witness-free matrices hides
    exactly.** -/
theorem comp_pcsX {V Wv : Type} (off : EF → String → EF) {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat}
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
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv) :
    let NR := cNR off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw
    PCSCloseN off (NR * NR2) (fun pre β t => compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t)
      (fun t α β r => cPcs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
        (friX fri Rb Ro (r / NR)) t α β (r % NR))
      (fun α β v r => cPsim off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
        (friX fri Rb Ro (r / NR)) α β v (r % NR)) 0 :=
  PCSCloseN.family (pcs := fun δ => cPcs off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
    (friX fri Rb Ro δ))
    (psim := fun δ => cPsim off hd0 stk0 ctr0 n nilA heap N W roots C Mm Wt tbM tbC tpP tpS SM SC S9 SP SS ζ qv wm wc ww wp wsg ncw αb
      (friX fri Rb Ro δ))
    (fun δ => by apply comp_pcs (fri := friX fri Rb Ro δ) <;> assumption)

/-- **The Sudoku proof is zero knowledge with the witness-free matrices**:
    `sud_hiding` over the PCS that adds them, its PCS term zero. -/
theorem sud_hidingX {V Wv : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
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
    (hszP : 2 * SP.length + 8 ≤ 2 ^ (tP + 1)) (hζ : ∀ x : F, EF.ofF x ≠ ζ)
    (hdet : (mz ζ).det ≠ 0) {ncw : Nat} {αb : EF} (fri : EF → EF → List (EF → EF) → V)
    (hdb : (mz αb).det ≠ 0) (haw : ∀ w, apow αb w ≠ EF.zero) (hncw : 4 ≤ ncw)
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    (E : TViewN (SudPV (V × Wv)) EF → Bool) :
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
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv tp pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) := by
  intro blank C Pg Wt Mm NR0 pcs psim NR tabs tv tp M
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sm, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := sud_pcsX (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv
    wm wc ww wp hS16 hS10 hSP hsz16 hsz hszP hζ hdet fri hdb haw hncw NR2 Rb Ro
  exact sud_transcriptG off NR 0 pcs psim hbal hun hpcs E

/-- **The hidden-term proof is zero knowledge with the witness-free matrices**:
    `wit_hiding` over the PCS that adds them, its PCS term zero. -/
theorem wit_hidingX {V Wv : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
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
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    (E : TViewN (PcsPV (V × Wv)) EF → Bool) :
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
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv ptm pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv ptm pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) := by
  intro blank C Pg Wt Mm NR0 pcs psim NR tabs tv ptm M
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sm, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := wit_pcsX (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
    wm wc ww wp hS10 hS9 hSP hsz10 hsz9 hszP hζ hdet fri hdb haw hncw NR2 Rb Ro
  exact wit_transcriptG off NR 0 pcs psim hbal hun hpcs E

/-- **The composed proof is zero knowledge with the witness-free matrices**:
    `comp_hiding` over the PCS that adds them, its PCS term zero. -/
theorem comp_hidingX {V Wv : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    (NR2 : Nat) (Rb : EF → EF → Nat → List (EF → EF)) (Ro : EF → EF → Nat → Wv)
    (E : TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
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
    tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) ∧
    tsumN NR 2 (fun α β r t => indB (genB β && E (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim α β r t))) ≤
      tsumN NR 2 (fun α β r t => indB (genB β && E (realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)) := by
  intro m roots N C Pg Wt Mm NR0 pcs psim NR tabs tv pb ptm M
  obtain ⟨hbal, hun⟩ := comp_honest_zk hR hrl hr hA hlen hLm hK hNW
  obtain ⟨sc, sm, sw, hWh, _⟩ := comp_run_sats hR hrl hr hA hlen hLm hK hNW
  obtain ⟨p1, p2, s1, s2⟩ := comp_pub_heights hR hrl hA hlen hLm hK
  rw [← htP] at p1 p2
  rw [← htS] at s1 s2
  have hM : Mm.h = 2 ^ (tbM + 1) := by rw [htM]; exact hlen
  have hC : C.h = 2 ^ (tbC + 1) := by rw [htC]; rfl
  have hpcs := comp_pcsX (heap := m.heap) (roots := roots) off sc sm sw (by omega) (by omega) (by omega) (by omega)
    hM hC hWh p2 s2 qv wm wc ww wp wsg hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS hζ hdet fri hdb haw hncw NR2 Rb Ro
  exact comp_transcriptG off NR 0 pcs psim hbal hun hpcs E

end Circuit
