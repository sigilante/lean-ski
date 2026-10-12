import Ski.ZK.FSZK

/-!
# Each circuit under Fiat–Shamir

`fs_transcript` applied to each circuit's transcript theorem with the
witness-free matrices and generic challenges (`*_hidingXG`): the LogUp
challenges `(α, β)` drawn by hashing the commitment of the prover's first
message, in the programmable random-oracle model (`sud_fs`, `wit_fs`,
`comp_fs`).  The commitment is any hiding commitment (`ComHides`) of any
data the prover computes from the witness, the blinding tuples and the
PCS randomness.  Each bound is `fs_transcript`'s with the circuit's
error, the aborting draws, times the salts.

Scope.  One Fiat–Shamir round, the LogUp challenges'.  The later
challenges, `ζ`, the FRI challenge and the query points, stay fixed
(generic) parameters; drawing them by the oracle too is the multi-round
step.  `ComHides` is perfect hiding, the Merkle salts' idealization.
-/

namespace Circuit

open ZKF B Air Compose CompM Stmt Mach Wit Sudoku SudokuText

/-- `fs_transcript` both ways, the transcript bounds first. -/
theorem fs_pair {PV PB D : Type} {NR m e1 e2 NS n : Nat} {rv sv : EF → EF → Nat → (Nat → Tup) → TViewN PV PB}
    (h1 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) + e1 + e2)
    (h2 : ∀ E : TViewN PV PB → Bool, tsumN NR m (fun α β r t => indB (genB β && E (sv α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (rv α β r t))) + e1 + e2)
    (hrv : ∀ α β r t, rv α β r t = none ∨ ∃ p x y, rv α β r t = some (p, α, β, x, y))
    (hsv : ∀ α β r t, ∃ p x y, sv α β r t = some (p, α, β, x, y))
    (Com : D → Nat → Nat) (hcom : ComHides NS Com) (hrange : ∀ d σ, Com d σ < n)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (E : Nat → Nat → TViewN PV PB → Bool) :
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
          r t)))))) ≤
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2)) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (sv (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (rv (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4))
          r t)))))) +
    (Q4 * Q4) ^ n * (NS * (e1 + e2)) :=
  have h1' := fun E => Nat.le_trans (h1 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  have h2' := fun E => Nat.le_trans (h2 E) (Nat.le_of_eq (Nat.add_assoc _ e1 e2))
  ⟨fs_transcript rv sv hrv hsv h1' h2' Com hcom hrange main d0 E,
    fs_transcript' rv sv hrv hsv h1' h2' Com hcom hrange main d0 E⟩

theorem realVN_cases {PV PB : Type} (off : EF → String → EF) (tabs : (Nat → Tup) → List (AirD × Table))
    (tv : (String → EF) → EF → (Nat → Tup) → List EF) (pb : (String → EF) → EF → PB)
    (pcs : (Nat → Tup) → EF → EF → Nat → PV) (α β : EF) (r : Nat) (t : Nat → Tup) :
    realVN off tabs tv pb pcs α β r t = none ∨ ∃ p x y, realVN off tabs tv pb pcs α β r t = some (p, α, β, x, y) := by
  unfold realVN
  split
  · exact .inl rfl
  · exact .inr ⟨_, _, _, rfl⟩

theorem simVN_some {PV PB : Type} (off : EF → String → EF) (pb : (String → EF) → EF → PB) (bus : Nat → String)
    (sg : Nat → Bool) (par : Nat → Nat) (n : Nat) (tp : (String → EF) → EF → EF)
    (psim : EF → EF → List EF → Nat → PV) (α β : EF) (r : Nat) (t : Nat → Tup) :
    ∃ p x y, simVN off pb bus sg par n tp psim α β r t = some (p, α, β, x, y) := ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
/-- **The Sudoku proof is zero knowledge under Fiat–Shamir**, in the
    programmable random-oracle model: the LogUp challenges are the
    oracle's answer at the commitment of the prover's first message
    (`main`, under a hiding commitment), the distinguisher sees the
    oracle's whole table, and the simulator commits to a fixed datum,
    draws the challenges and programs the oracle (`fs_transcript`).  The
    other challenges stay generic and fixed, as in `sud_hidingXG`. -/
theorem sud_fs {V Wv D : Type} (off : EF → String → EF) {puzzle : List Nat} (hc : CluesOK (cluesOf puzzle))
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
    {NS n : Nat} (Com : D → Nat → Nat) (hcom : ComHides NS Com) (hrange : ∀ d σ, Com d σ < n)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (E : Nat → Nat → TViewN (SudPV (V × Wv)) EF → Bool) :
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
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (realVN off tabs tv tp pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) ≤
      sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (simVN off tp chainBus (fun _ => false) chainPar 3 tp psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
      (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (realVN off tabs tv tp pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) := by
  intro blank C Pg Wt Mm NR0 pcs psim NR tabs tv tp M
  obtain ⟨hbal, hun⟩ := sud_honest_zk hc hA hlen hk
  obtain ⟨sc, sm, sw⟩ := sud_run_sats hc hA hacc hlen hk
  obtain ⟨hP23, hPg⟩ := sud_prog_height hc hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := sud_pcsX (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 16) hlen (rfl : Wt.h = 2 ^ 10) (by omega) hPg qv
    wm wc ww wp hS16 hS10 hSP hsz16 hsz hszP (generic_ofF_ne hgζ) (mz_generic hgζ) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
  have h1 := fun E => (sud_transcriptG off NR 0 pcs psim hbal hun hpcs E).1
  have h2 := fun E => (sud_transcriptG off NR 0 pcs psim hbal hun hpcs E).2
  exact fs_pair h1 h2 (fun α β r t => realVN_cases _ _ _ _ _ α β r t)
    (fun α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) Com hcom hrange main d0 E

set_option maxRecDepth 100000 in
/-- **The hidden-term proof is zero knowledge under Fiat–Shamir**, in the
    programmable random-oracle model: the LogUp challenges are the
    oracle's answer at the commitment of the prover's first message
    (`main`, under a hiding commitment), the distinguisher sees the
    oracle's whole table, and the simulator commits to a fixed datum,
    draws the challenges and programs the oracle (`fs_transcript`).  The
    other challenges stay generic and fixed, as in `wit_hidingXG`. -/
theorem wit_fs {V Wv D : Type} (off : EF → String → EF) {Vt x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws)
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
    {NS n : Nat} (Com : D → Nat → Nat) (hcom : ComHides NS Com) (hrange : ∀ d σ, Com d σ < n)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (E : Nat → Nat → TViewN (PcsPV (V × Wv)) EF → Bool) :
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
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (realVN off tabs tv ptm pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) ≤
      sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (simVN off ptm chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
      (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (realVN off tabs tv ptm pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) := by
  intro blank C Pg Wt Mm NR0 pcs psim NR tabs tv ptm M
  obtain ⟨hbal, hun⟩ := wit_honest_zk hwf hwl hW8 hA hlen hk
  obtain ⟨sc, sm, sw, hWh⟩ := wit_run_sats hwf hwl hW8 hA hK hlen hk
  obtain ⟨_, hP23, hPg⟩ := wit_prog_height hwl hA hlen
  rw [← htp] at hP23 hPg
  have hpcs := wit_pcsX (heap := blank.heap) off sc sm sw (rfl : C.h = 2 ^ 10) hlen hWh (by omega) hPg qv
    wm wc ww wp hS10 hS9 hSP hsz10 hsz9 hszP (generic_ofF_ne hgζ) (mz_generic hgζ) fri (mz_generic hgα) (generic_apow_ne hgα) hncw NR2 Rb Ro
  have h1 := fun E => (wit_transcriptG off NR 0 pcs psim hbal hun hpcs E).1
  have h2 := fun E => (wit_transcriptG off NR 0 pcs psim hbal hun hpcs E).2
  exact fs_pair h1 h2 (fun α β r t => realVN_cases _ _ _ _ _ α β r t)
    (fun α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) Com hcom hrange main d0 E

set_option maxRecDepth 100000 in
/-- **The composed proof is zero knowledge under Fiat–Shamir**, in the
    programmable random-oracle model: the LogUp challenges are the
    oracle's answer at the commitment of the prover's first message
    (`main`, under a hiding commitment), the distinguisher sees the
    oracle's whole table, and the simulator commits to a fixed datum,
    draws the challenges and programs the oracle (`fs_transcript`).  The
    other challenges stay generic and fixed, as in `comp_hidingXG`. -/
theorem comp_fs {V Wv D : Type} (off : EF → String → EF) {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term}
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
    {NS n : Nat} (Com : D → Nat → Nat) (hcom : ComHides NS Com) (hrange : ∀ d σ, Com d σ < n)
    (main : (Nat → Tup) → Nat → D) (d0 : D) (E : Nat → Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Bool) :
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
    (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (realVN off tabs tv pb pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) ≤
      sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) ∧
    sumTo ((Q4 * Q4) ^ n) (fun H => sumTo (Q4 * Q4) (fun c => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (c % Q4)) && E (rset (Q4 * Q4) (Com d0 σ) H c) (Com d0 σ)
        (simVN off pb chainBus (fun _ => false) chainPar 3 ptm psim (efOf (c / Q4)) (efOf (c % Q4)) r t))))))) ≤
      (Q4 * Q4) * sumTo ((Q4 * Q4) ^ n) (fun H => sumTo NS (fun σ => sumTo NR (fun r => sumN 2 (fun t =>
      indB (genB (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) && E H (Com (main t r) σ)
        (realVN off tabs tv pb pcs (efOf (rget (Q4 * Q4) (Com (main t r) σ) H / Q4)) (efOf (rget (Q4 * Q4) (Com (main t r) σ) H % Q4)) r t)))))) +
        (Q4 * Q4) ^ n * (NS * (Q4 * (NR * (Q4 ^ 2 * M)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))) := by
  intro m roots N C Pg Wt Mm NR0 pcs psim NR tabs tv pb ptm M
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
  exact fs_pair h1 h2 (fun α β r t => realVN_cases _ _ _ _ _ α β r t)
    (fun α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t) Com hcom hrange main d0 E

end Circuit
