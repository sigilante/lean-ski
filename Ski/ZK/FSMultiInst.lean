import Ski.ZK.FSMulti

/-!
# Two Sudoku proofs under one oracle

`fs_open4_two` for two Sudoku proofs (`sud_fs_open4_two`), the collisions
bounded by the commitment's salt spread (`spread_sum`).
-/

namespace Circuit

open ZKF

/-- **A commitment's salt spread over a proof's draws**: if at most `δs` of
    the salts commit any data to any one value, the first commitment of a
    proof's data hits a value for at most `δs` of its first salts at every
    other draw. -/
theorem spread_sum {D : Type} {NS1 NS2 NR m δs : Nat} (Com : D → Nat → Nat) (main : (Nat → Tup) → Nat → D)
    (h : ∀ d v, sumTo NS1 (fun σ => indB (decide (Com d σ = v))) ≤ δs) (v : Nat) :
    sumTo NS1 (fun σ1 => sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (decide (Com (main t r) σ1 = v)))))) ≤ NS2 * (NR * (Q4 ^ m * δs)) := by
  have e : sumTo NS1 (fun σ1 => sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t =>
      indB (decide (Com (main t r) σ1 = v)))))) =
      sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t => sumTo NS1 (fun σ1 =>
        indB (decide (Com (main t r) σ1 = v)))))) := by
    rw [sumTo_exch _ NS2 NS1]
    refine sumTo_congr _ (fun σ _ => ?_)
    rw [sumTo_exch _ NR NS1]
    refine sumTo_congr _ (fun r _ => ?_)
    exact sumTo_sumN m NS1 _
  rw [e]
  calc sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t => sumTo NS1 (fun σ1 =>
        indB (decide (Com (main t r) σ1 = v))))))
      ≤ sumTo NS2 (fun σ => sumTo NR (fun r => sumN m (fun t => δs))) :=
        sumTo_mono _ (fun σ _ => sumTo_mono _ (fun r _ => sumN_mono m (fun t => h _ _)))
    _ = _ := by rw [sumTo_congr _ (fun σ _ => sumTo_congr _ (fun r _ => sumN_const m δs)), sumTo_congr _
        (fun σ _ => sumTo_const _ NR), sumTo_const]
section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Two Sudoku proofs under one oracle**, each over four Fiat–Shamir
    rounds with every commitment opened and the query points hashed
    (`sud_fs_open4` twice, `fs_open4_two`): the two proofs, of any two
    puzzles, read the same four tables; the simulator programs the second's
    answers and then the first's.  The error is each proof's own over the
    other's draws, and the collisions, bounded by the second proof's first
    commitment's salt spread (`hspB`, at most `δs` of the salts commit any
    data to any one value) through `spread_sum`.  The query hash maps keep
    the transcript's residue mod `n1` (`hφAB`).  Statements fixed in
    advance; two proofs. -/
theorem sud_fs_open4_two {VA WvA P1A P2A P3A : Type} (offA : EF → String → EF) {puzzleA : List Nat} (hcA : CluesOK (cluesOf puzzleA))
    {ρA : Nat → Bool} {AA : List Cell} {kA : Nat} {rowA : Nat → Air.Row}
    (hAA : AcceptsFrom AA (stmtMachine ρA 729 (sudokuExpr (cluesOf puzzleA)) ACC REJ) kA rowA)
    (haccA : rd AA (rowA (kA - 1)).ctr (rowA (kA - 1)).hd = some (.atom ACC))
    (hlenA : AA.length = 2 ^ 16) (hkA : kA ≤ 2 ^ 16)
    {tPA : Nat} (htpA : tPA = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzleA)) ACC REJ).heap)
    (S16A S10A SPA : Nat → List F) (qvA : EF → EF → List EF → F → List F → List F → List EF)
    (wmA wcA wwA wpA : Nat → List (EF → EF → List F)) {LwmA LwcA LwwA LwpA : Nat} (hlwmA : ∀ c, (wmA c).length = LwmA)
    (hlwcA : ∀ c, (wcA c).length = LwcA) (hlwwA : ∀ c, (wwA c).length = LwwA) (hlwpA : ∀ c, (wpA c).length = LwpA)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φA : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφA : ∀ m w, φA m w < N4)
    (hS16A : ∀ c4, ∀ x ∈ S16A c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10A : ∀ c4, ∀ x ∈ S10A c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSPA : ∀ c4, ∀ x ∈ SPA c4, x ∉ cosetL 1 (bbGen (tPA + 1)) (2 ^ (tPA + 1)))
    (hsz16A : ∀ c4, 2 * (S16A c4).length + 8 ≤ 2 ^ 16) (hszA : ∀ c4, 2 * (S10A c4).length + 8 ≤ 2 ^ 10)
    (hszPA : ∀ c4, 2 * (SPA c4).length + 8 ≤ 2 ^ (tPA + 1)) {ncwA : Nat} (αdA : Nat → EF) {B4A : Nat}
    (hB4A : sumTo K4 (fun c4 => indB (!genB (αdA c4))) ≤ B4A) (friA : Nat → EF → EF → List (EF → EF) → VA)
    (hncwA : 4 ≤ ncwA)
    (NR2A : Nat) (RbA : Nat → EF → EF → Nat → List (EF → EF)) (RoA : Nat → EF → EF → Nat → WvA)
    {NS1A NS2A NS3A n1 n2 n3 : Nat}
    (Com1A : List (List (List F)) → Nat → Nat) (Pf1A : Nat → List (List (List F)) → Nat → P1A) (hc1A : ComHides NS1A Com1A)
    (hp1A : ∀ c4, ComPfHides NS1A Com1A (Pf1A c4) (opF ((sudGroups tPA (S16A c4) (S10A c4) (SPA c4) EF.zero qvA).map (·.base.S)) [0, 2, 4, 6]))
    (hr1A : ∀ d σ, Com1A d σ < n1) (d1A : List (List (List F)))
    (Com2A : List (List (List F)) → Nat → Nat) (Pf2A : Nat → List (List (List F)) → Nat → P2A) (hc2A : ComHides NS2A Com2A)
    (hp2A : ∀ c4, ComPfHides NS2A Com2A (Pf2A c4) (opF ((sudGroups tPA (S16A c4) (S10A c4) (SPA c4) EF.zero qvA).map (·.base.S)) [1, 3, 5, 7]))
    (hr2A : ∀ d σ, Com2A d σ < n2) (d2A : List (List (List F)))
    (Com3A : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3A : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3A) (hc3A : ComHides NS3A Com3A)
    (hp3A : ∀ c4, ComPfHides NS3A Com3A (Pf3A c4) (fun d => (opQ (sudSsT (S16A c4) (S10A c4) (SPA c4)) d.1, opCw (sudSsC tPA (S16A c4) (S10A c4) (SPA c4)) d.2)))
    (hr3A : ∀ d σ, Com3A d σ < n3) (d3A : List (List (List (List F))) × List (List (List F)))
    {VB WvB P1B P2B P3B : Type} (offB : EF → String → EF) {puzzleB : List Nat} (hcB : CluesOK (cluesOf puzzleB))
    {ρB : Nat → Bool} {AB : List Cell} {kB : Nat} {rowB : Nat → Air.Row}
    (hAB : AcceptsFrom AB (stmtMachine ρB 729 (sudokuExpr (cluesOf puzzleB)) ACC REJ) kB rowB)
    (haccB : rd AB (rowB (kB - 1)).ctr (rowB (kB - 1)).hd = some (.atom ACC))
    (hlenB : AB.length = 2 ^ 16) (hkB : kB ≤ 2 ^ 16)
    {tPB : Nat} (htpB : tPB = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzleB)) ACC REJ).heap)
    (S16B S10B SPB : Nat → List F) (qvB : EF → EF → List EF → F → List F → List F → List EF)
    (wmB wcB wwB wpB : Nat → List (EF → EF → List F)) {LwmB LwcB LwwB LwpB : Nat} (hlwmB : ∀ c, (wmB c).length = LwmB)
    (hlwcB : ∀ c, (wcB c).length = LwcB) (hlwwB : ∀ c, (wwB c).length = LwwB) (hlwpB : ∀ c, (wpB c).length = LwpB)
    (φB : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (hφB : ∀ m w, φB m w < N4)
    (hS16B : ∀ c4, ∀ x ∈ S16B c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10B : ∀ c4, ∀ x ∈ S10B c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10))
    (hSPB : ∀ c4, ∀ x ∈ SPB c4, x ∉ cosetL 1 (bbGen (tPB + 1)) (2 ^ (tPB + 1)))
    (hsz16B : ∀ c4, 2 * (S16B c4).length + 8 ≤ 2 ^ 16) (hszB : ∀ c4, 2 * (S10B c4).length + 8 ≤ 2 ^ 10)
    (hszPB : ∀ c4, 2 * (SPB c4).length + 8 ≤ 2 ^ (tPB + 1)) {ncwB : Nat} (αdB : Nat → EF) {B4B : Nat}
    (hB4B : sumTo K4 (fun c4 => indB (!genB (αdB c4))) ≤ B4B) (friB : Nat → EF → EF → List (EF → EF) → VB)
    (hncwB : 4 ≤ ncwB)
    (NR2B : Nat) (RbB : Nat → EF → EF → Nat → List (EF → EF)) (RoB : Nat → EF → EF → Nat → WvB)
    {NS1B NS2B NS3B : Nat}
    (Com1B : List (List (List F)) → Nat → Nat) (Pf1B : Nat → List (List (List F)) → Nat → P1B) (hc1B : ComHides NS1B Com1B)
    (hp1B : ∀ c4, ComPfHides NS1B Com1B (Pf1B c4) (opF ((sudGroups tPB (S16B c4) (S10B c4) (SPB c4) EF.zero qvB).map (·.base.S)) [0, 2, 4, 6]))
    (hr1B : ∀ d σ, Com1B d σ < n1) (d1B : List (List (List F)))
    (Com2B : List (List (List F)) → Nat → Nat) (Pf2B : Nat → List (List (List F)) → Nat → P2B) (hc2B : ComHides NS2B Com2B)
    (hp2B : ∀ c4, ComPfHides NS2B Com2B (Pf2B c4) (opF ((sudGroups tPB (S16B c4) (S10B c4) (SPB c4) EF.zero qvB).map (·.base.S)) [1, 3, 5, 7]))
    (hr2B : ∀ d σ, Com2B d σ < n2) (d2B : List (List (List F)))
    (Com3B : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3B : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3B) (hc3B : ComHides NS3B Com3B)
    (hp3B : ∀ c4, ComPfHides NS3B Com3B (Pf3B c4) (fun d => (opQ (sudSsT (S16B c4) (S10B c4) (SPB c4)) d.1, opCw (sudSsC tPB (S16B c4) (S10B c4) (SPB c4)) d.2)))
    (hr3B : ∀ d σ, Com3B d σ < n3) (d3B : List (List (List (List F))) × List (List (List F)))
    (hφAB : ∀ m w m' w', φB m w = φA m' w' → m % n1 = m' % n1) {δs : Nat}
    (hspB : ∀ d v, sumTo NS1B (fun σ => indB (decide (Com1B d σ = v))) ≤ δs) :
    let blankA := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzleA)) ACC REJ
    let CA := cpuTableW AA rowA kA (2 ^ 16)
    let PgA := progTableS blankA.heap
    let WtA := witTableS AA
    let MmA := memTableC AA (cpuAirS blankA.hd blankA.stk blankA.heap.length ACC) (progAirS blankA.heap) witAirS CA PgA WtA
    let NR0A := sudNR offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A 0) (S10A 0) (SPA 0) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA
    let pcsZA := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA (αdA c4)
      (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) t α β (r % NR0A)
    let psimZA := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA (αdA c4)
      (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) α β v (r % NR0A)
    let NRA := NR0A * NR2A
    let tabsA := fun t : Nat → Tup => sudTables blankA.hd blankA.stk blankA.heap.length blankA.heap
      ((CA.setBlind BLA (t 1)).setBlind BLB (t 0)) (MmA.setBlind 5 (t 0)) (progTableS blankA.heap) (WtA.setBlind 1 (t 1))
    let tvA := fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t
    let tpA := fun pre β => terminal pre β (progAirS blankA.heap) (progTableS blankA.heap)
    let MA := (allEntries (sudTables blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA (progTableS blankA.heap) WtA)).length
    let q0A := sudGroups tPA (S16A 0) (S10A 0) (SPA 0) EF.zero qvA
    let qZA := fun (c4 : Nat) (ζ : EF) => sudGroups tPA (S16A c4) (S10A c4) (SPA c4) ζ qvA
    let SsA := fun c4 => (qZA c4 EF.zero).map (·.base.S)
    let ksA := sudKs blankA.hd blankA.stk blankA.heap.length blankA.heap
    let colsA := sudCols offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA
    let tqZA := fun (c4 c2 : Nat) (ζ : EF) => (sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst
    let qdZA := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map (fun p => p.2 t α β ms)
    let SsTA := fun c4 => (tqZA c4 0 EF.zero).map (·.S)
    let SsCA := fun c4 => (tabsInfo ncwA (tqZA c4 0 EF.zero)).map (·.S)
    let mk1A := [0, 2, 4, 6]
    let mk2A := [1, 3, 5, 7]
    let main1A := fun (t : Nat → Tup) (r : Nat) => mainF2 q0A ksA colsA (tqZA 0 0 EF.zero) ncwA mk1A t (r % NR0A)
    let main2A := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0A ksA colsA (tqZA 0 0 EF.zero) ncwA mk2A t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0A)
    let main3A := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZA 0 c2 EF.zero) (qdZA 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0A ksA (tqZA 0 c2 EF.zero) ncwA (r % NR0A))) (crF q0A ksA (tqZA 0 c2 EF.zero) ncwA (r % NR0A)),
       tabsCws ncwA (tqZA 0 c2 EF.zero) (ccF q0A ksA (tqZA 0 c2 EF.zero) ncwA (r % NR0A)))
    let vSA := fun (α β : EF) (t : Nat → Tup) => viewT β (fun kA => prefixOf α (offA β) (chainBus kA)) (fun _ => false)
      chainPar 3 (xrefN (tpA (prefixOf α (offA β)) β)) t
    let sop1A := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (SsA c4) mk1A (mainZ2 (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA mk1A (r % NR0A))
    let sop2A := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (SsA c4) mk2A (mainZ2 (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA mk2A (r % NR0A))
    let sop3A := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsTA c4) (tabsPolys (tqZA c4 c2 (efOf c3)) (canonT (tqZA c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vSA (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZA c4 (efOf c3)).map QGroup.ext) ((((qZA c4 (efOf c3)).map QGroup.ext).zip ksA).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (r % NR0A))))
         (crF (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (r % NR0A))),
       opCw (SsCA c4) (tabsCws ncwA (tqZA c4 c2 (efOf c3)) (ccF (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (r % NR0A))))
    let ov1A : Nat → TViewN (SudPV (VA × WvA)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsA c4) mk1A pv)
      | none => none
    let ov2A : Nat → TViewN (SudPV (VA × WvA)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsA c4) mk2A pv)
      | none => none
    let ov3A : Nat → TViewN (SudPV (VA × WvA)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvFA := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) α β r t
    let svFA := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN offA tpA chainBus (fun _ => false) chainPar 3 tpA (psimZA c4 c2 (efOf c3)) α β r t
    let ozFA : TViewN (SudPV (VA × WvA)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3A := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsTA c4) d.1, opCw (SsCA c4) d.2)
    let sd3A := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsTA c4) o.1, sdCw (SsCA c4) o.2)
    let blankB := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzleB)) ACC REJ
    let CB := cpuTableW AB rowB kB (2 ^ 16)
    let PgB := progTableS blankB.heap
    let WtB := witTableS AB
    let MmB := memTableC AB (cpuAirS blankB.hd blankB.stk blankB.heap.length ACC) (progAirS blankB.heap) witAirS CB PgB WtB
    let NR0B := sudNR offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B 0) (S10B 0) (SPB 0) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB
    let pcsZB := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB (αdB c4)
      (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) t α β (r % NR0B)
    let psimZB := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB (αdB c4)
      (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) α β v (r % NR0B)
    let NRB := NR0B * NR2B
    let tabsB := fun t : Nat → Tup => sudTables blankB.hd blankB.stk blankB.heap.length blankB.heap
      ((CB.setBlind BLA (t 1)).setBlind BLB (t 0)) (MmB.setBlind 5 (t 0)) (progTableS blankB.heap) (WtB.setBlind 1 (t 1))
    let tvB := fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t
    let tpB := fun pre β => terminal pre β (progAirS blankB.heap) (progTableS blankB.heap)
    let MB := (allEntries (sudTables blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB (progTableS blankB.heap) WtB)).length
    let q0B := sudGroups tPB (S16B 0) (S10B 0) (SPB 0) EF.zero qvB
    let qZB := fun (c4 : Nat) (ζ : EF) => sudGroups tPB (S16B c4) (S10B c4) (SPB c4) ζ qvB
    let SsB := fun c4 => (qZB c4 EF.zero).map (·.base.S)
    let ksB := sudKs blankB.hd blankB.stk blankB.heap.length blankB.heap
    let colsB := sudCols offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB
    let tqZB := fun (c4 c2 : Nat) (ζ : EF) => (sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst
    let qdZB := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map (fun p => p.2 t α β ms)
    let SsTB := fun c4 => (tqZB c4 0 EF.zero).map (·.S)
    let SsCB := fun c4 => (tabsInfo ncwB (tqZB c4 0 EF.zero)).map (·.S)
    let mk1B := [0, 2, 4, 6]
    let mk2B := [1, 3, 5, 7]
    let main1B := fun (t : Nat → Tup) (r : Nat) => mainF2 q0B ksB colsB (tqZB 0 0 EF.zero) ncwB mk1B t (r % NR0B)
    let main2B := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0B ksB colsB (tqZB 0 0 EF.zero) ncwB mk2B t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0B)
    let main3B := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZB 0 c2 EF.zero) (qdZB 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0B ksB (tqZB 0 c2 EF.zero) ncwB (r % NR0B))) (crF q0B ksB (tqZB 0 c2 EF.zero) ncwB (r % NR0B)),
       tabsCws ncwB (tqZB 0 c2 EF.zero) (ccF q0B ksB (tqZB 0 c2 EF.zero) ncwB (r % NR0B)))
    let vSB := fun (α β : EF) (t : Nat → Tup) => viewT β (fun kB => prefixOf α (offB β) (chainBus kB)) (fun _ => false)
      chainPar 3 (xrefN (tpB (prefixOf α (offB β)) β)) t
    let sop1B := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (SsB c4) mk1B (mainZ2 (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB mk1B (r % NR0B))
    let sop2B := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (SsB c4) mk2B (mainZ2 (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB mk2B (r % NR0B))
    let sop3B := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsTB c4) (tabsPolys (tqZB c4 c2 (efOf c3)) (canonT (tqZB c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vSB (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZB c4 (efOf c3)).map QGroup.ext) ((((qZB c4 (efOf c3)).map QGroup.ext).zip ksB).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (r % NR0B))))
         (crF (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (r % NR0B))),
       opCw (SsCB c4) (tabsCws ncwB (tqZB c4 c2 (efOf c3)) (ccF (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (r % NR0B))))
    let ov1B : Nat → TViewN (SudPV (VB × WvB)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsB c4) mk1B pv)
      | none => none
    let ov2B : Nat → TViewN (SudPV (VB × WvB)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsB c4) mk2B pv)
      | none => none
    let ov3B : Nat → TViewN (SudPV (VB × WvB)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvFB := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) α β r t
    let svFB := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN offB tpB chainBus (fun _ => false) chainPar 3 tpB (psimZB c4 c2 (efOf c3)) α β r t
    let ozFB : TViewN (SudPV (VB × WvB)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3B := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsTB c4) d.1, opCw (SsCB c4) d.2)
    let sd3B := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsTB c4) o.1, sdCw (SsCB c4) o.2)
    let smA := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1A (fun σ1 => sumTo (NS2A * NS3A) (fun σ => sumTo NRA (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1A := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1A (main1A x.2.2.2 x.2.2.1) x.1
    let m2A := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1A x + n1 * Com2A (main2A c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2A)
    let m3A := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1A x + n1 * comPair NS2A n2 Com2A Com3A (main2A c1 x.2.2.2 x.2.2.1, main3A c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvoA := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1A c4 (rvFA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1A c4 (main1A x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2A c4) (ov3A c4) (rvFA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2A (Pf2A c4) (Pf3A c4) (main2A c1 x.2.2.2 x.2.2.1, main3A c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvFA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1A (sdF (SsA c4) mk1A (sop1A c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1A c4 c1 c2 c3 x + n1 * Com2A (sdF (SsA c4) mk2A (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2A)
    let s3A := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1A c4 c1 c2 c3 x + n1 * comPair NS2A n2 Com2A Com3A
        (sdF (SsA c4) mk2A (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3A c4 (sop3A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svoA := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1A c4 (sdF (SsA c4) mk1A (sop1A c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2A (Pf2A c4) (Pf3A c4) (sdF (SsA c4) mk2A (sop2A c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3A c4 (sop3A c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svFA c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4A := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => smA (fun x => g (H1, H2, H3, x)))))
    let r1A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1A y.2.2.2) y.1
    let r2A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2A (r1A y) y.2.2.2) y.2.1
    let r3A := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3A (r1A y) (r2A y) y.2.2.2) y.2.2.1
    let MqA := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φA (m3A (r1A y) (r2A y) y.2.2.2)
      (ozFA (rvFA 0 (r2A y) (r3A y) (efOf (r1A y / Q4)) (efOf (r1A y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let smB := fun (g : Nat × Nat × Nat × (Nat → Tup) → Nat) =>
      sumTo NS1B (fun σ1 => sumTo (NS2B * NS3B) (fun σ => sumTo NRB (fun r => sumN 2 (fun t => g (σ1, σ, r, t)))))
    let m1B := fun (x : Nat × Nat × Nat × (Nat → Tup)) => Com1B (main1B x.2.2.2 x.2.2.1) x.1
    let m2B := fun (c1 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1B x + n1 * Com2B (main2B c1 x.2.2.2 x.2.2.1) (x.2.1 % NS2B)
    let m3B := fun (c1 c2 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      m1B x + n1 * comPair NS2B n2 Com2B Com3B (main2B c1 x.2.2.2 x.2.2.1, main3B c1 c2 x.2.2.2 x.2.2.1) x.2.1
    let rvoB := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      ((ov1B c4 (rvFB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map (fun _ => Pf1B c4 (main1B x.2.2.2 x.2.2.1) x.1),
       (ovPair (ov2B c4) (ov3B c4) (rvFB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)).map
         (fun _ => pfPair NS2B (Pf2B c4) (Pf3B c4) (main2B c1 x.2.2.2 x.2.2.1, main3B c1 c2 x.2.2.2 x.2.2.1) x.2.1),
       rvFB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let s1B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) => Com1B (sdF (SsB c4) mk1B (sop1B c4 c2 c3 x.2.2.1 x.2.2.2)) x.1
    let s2B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1B c4 c1 c2 c3 x + n1 * Com2B (sdF (SsB c4) mk2B (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) (x.2.1 % NS2B)
    let s3B := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      s1B c4 c1 c2 c3 x + n1 * comPair NS2B n2 Com2B Com3B
        (sdF (SsB c4) mk2B (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3B c4 (sop3B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1
    let svoB := fun (c4 c1 c2 c3 : Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (some (Pf1B c4 (sdF (SsB c4) mk1B (sop1B c4 c2 c3 x.2.2.1 x.2.2.2)) x.1),
       some (pfPair NS2B (Pf2B c4) (Pf3B c4) (sdF (SsB c4) mk2B (sop2B c4 c2 c3 c1 x.2.2.1 x.2.2.2), sd3B c4 (sop3B c4 c2 c3 c1 x.2.2.1 x.2.2.2)) x.2.1),
       svFB c4 c2 c3 (efOf (c1 / Q4)) (efOf (c1 % Q4)) x.2.2.1 x.2.2.2)
    let sm4B := fun (g : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup)) → Nat) =>
      sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 =>
        sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => smB (fun x => g (H1, H2, H3, x)))))
    let r1B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget (Q4 * Q4) (m1B y.2.2.2) y.1
    let r2B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget K2 (m2B (r1B y) y.2.2.2) y.2.1
    let r3B := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => rget Q4 (m3B (r1B y) (r2B y) y.2.2.2) y.2.2.1
    let MqB := fun (y : Nat × Nat × Nat × (Nat × Nat × Nat × (Nat → Tup))) => φB (m3B (r1B y) (r2B y) y.2.2.2)
      (ozFB (rvFB 0 (r2B y) (r3B y) (efOf (r1B y / Q4)) (efOf (r1B y % Q4)) y.2.2.2.2.2.1 y.2.2.2.2.2.2))
    let ST := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 =>
      sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))
    let SC := fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 =>
      sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))
    let rvTA := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1A x, m2A (r1A (H.1, H.2.1, H.2.2.1, x)) x, m3A (r1A (H.1, H.2.1, H.2.2.1, x)) (r2A (H.1, H.2.1, H.2.2.1, x)) x,
       rvoA (rget K4 (MqA (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1A (H.1, H.2.1, H.2.2.1, x)) (r2A (H.1, H.2.1, H.2.2.1, x))
         (r3A (H.1, H.2.1, H.2.2.1, x)) x)
    let pgTA := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset Q4 (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φA (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozFA (svFA c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svTA := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1A c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2A c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3A c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svoA c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let rvTB := fun (H : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (m1B x, m2B (r1B (H.1, H.2.1, H.2.2.1, x)) x, m3B (r1B (H.1, H.2.1, H.2.2.1, x)) (r2B (H.1, H.2.1, H.2.2.1, x)) x,
       rvoB (rget K4 (MqB (H.1, H.2.1, H.2.2.1, x)) H.2.2.2) (r1B (H.1, H.2.1, H.2.2.1, x)) (r2B (H.1, H.2.1, H.2.2.1, x))
         (r3B (H.1, H.2.1, H.2.2.1, x)) x)
    let pgTB := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (rset (Q4 * Q4) (s1B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.1 c.1, rset K2 (s2B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.1 c.2.1,
       rset Q4 (s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x) H.2.2.1 c.2.2.1,
       rset K4 (φB (s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x) (ozFB (svFB c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4))
         x.2.2.1 x.2.2.2))) H.2.2.2 c.2.2.2)
    let svTB := fun (c : Nat × Nat × Nat × Nat) (x : Nat × Nat × Nat × (Nat → Tup)) =>
      (s1B c.2.2.2 c.1 c.2.1 c.2.2.1 x, s2B c.2.2.2 c.1 c.2.1 c.2.2.1 x, s3B c.2.2.2 c.1 c.2.1 c.2.2.1 x,
       svoB c.2.2.2 c.1 c.2.1 c.2.2.1 x)
    let colT := fun (H : Nat × Nat × Nat × Nat) (c : Nat × Nat × Nat × Nat) (xa xb : Nat × Nat × Nat × (Nat → Tup)) =>
      decide (m1B xb = s1A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (m2B (r1B (H.1, H.2.1, H.2.2.1, xb)) xb = s2A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (m3B (r1B (H.1, H.2.1, H.2.2.1, xb)) (r2B (H.1, H.2.1, H.2.2.1, xb)) xb = s3A c.2.2.2 c.1 c.2.1 c.2.2.1 xa) ||
      decide (MqB (H.1, H.2.1, H.2.2.1, xb) = φA (s3A c.2.2.2 c.1 c.2.1 c.2.2.1 xa)
        (ozFA (svFA c.2.2.2 c.2.1 c.2.2.1 (efOf (c.1 / Q4)) (efOf (c.1 % Q4)) xa.2.2.1 xa.2.2.2)))
    let okT := fun (c : Nat × Nat × Nat × Nat) =>
      decide (c.1 < Q4 * Q4) && decide (c.2.1 < K2) && decide (c.2.2.1 < Q4) && decide (c.2.2.2 < K4)
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1A × Option (P2A × P3A) × TViewN (SudPV (VA × WvA)) EF) → Nat × Nat × Nat × (Option P1B × Option (P2B × P3B) × TViewN (SudPV (VB × WvB)) EF) → Bool,
    (K4 * (Q4 * Q4 * (K2 * Q4))) * ((K4 * (Q4 * Q4 * (K2 * Q4))) * ST (fun H => smB (fun xb => smA (fun xa => indB (E H (rvTA H xa) (rvTB H xb)))))) ≤
      SC (fun ca => smA (fun xa => ST (fun H => SC (fun cb => smB (fun xb =>
        indB (E (pgTA (pgTB H cb xb) ca xa) (svTA ca xa) (svTB cb xb))))))) +
      (K4 * (Q4 * Q4 * (K2 * Q4))) * ((K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
        (K2 * (Q4 * (NS1A * (NS2A * NS3A * (Q4 * (NRA * (Q4 ^ 2 * MA)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
          (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1A * (NS2A * NS3A * (NRA * (Q4 ^ 2 * 1)))))))) +
          B4A * (Q4 * Q4 * (K2 * Q4) * sm4A (fun _ => 1)))) * smB (fun _ => 1)) + (K4 ^ N4 * (K4 * ((Q4 * Q4) ^ n1 * (K2 ^ (n1 * n2) * (Q4 ^ (n1 * (n2 * n3)) *
        (K2 * (Q4 * (NS1B * (NS2B * NS3B * (Q4 * (NRB * (Q4 ^ 2 * MB)) + Q4 * (Q4 * (Q4 ^ 2 * 0)))))) +
          (Q4 * (P * P) * (K2 * Q4) + Q4 * Q4 * (K2 * (P * P))) * (NS1B * (NS2B * NS3B * (NRB * (Q4 ^ 2 * 1)))))))) +
          B4B * (Q4 * Q4 * (K2 * Q4) * sm4B (fun _ => 1)))) * SC (fun _ => smA (fun _ => 1)) +
      (K4 * (Q4 * Q4 * (K2 * Q4))) * SC (fun _ => smA (fun _ => ST (fun _ => (NS2B * NS3B * (NRB * (Q4 ^ 2 * δs)))))) := by
  intro blankA CA PgA WtA MmA NR0A pcsZA psimZA NRA tabsA tvA tpA MA q0A qZA SsA ksA colsA tqZA qdZA SsTA SsCA mk1A mk2A main1A main2A main3A vSA sop1A sop2A sop3A ov1A ov2A ov3A rvFA svFA ozFA op3A sd3A blankB CB PgB WtB MmB NR0B pcsZB psimZB NRB tabsB tvB tpB MB q0B qZB SsB ksB colsB tqZB qdZB SsTB SsCB mk1B mk2B main1B main2B main3B vSB sop1B sop2B sop3B ov1B ov2B ov3B rvFB svFB ozFB op3B sd3B smA m1A m2A m3A rvoA s1A s2A s3A svoA sm4A r1A r2A r3A MqA smB m1B m2B m3B rvoB s1B s2B s3B svoB sm4B r1B r2B r3B MqB ST SC rvTA pgTA svTA rvTB pgTB svTB colT okT E
  obtain ⟨hbalA, hunA⟩ := sud_honest_zk hcA hAA hlenA hkA
  obtain ⟨scA, smsA, swA⟩ := sud_run_sats hcA hAA haccA hlenA hkA
  obtain ⟨hP23A, hPgA⟩ := sud_prog_height hcA hAA hlenA
  rw [← htpA] at hP23A hPgA
  have hSwA := fun (c4 c2 c3 : Nat) => sud_same_w offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA])
  have hSzA := fun (c4 c2 c3 : Nat) => sud_same_w offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA rfl rfl rfl rfl
  have hS0A := fun (c4 c2 : Nat) => sud_same_w offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) EF.zero EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA])
  have hSdA := fun (c4 c2 c3 : Nat) => sud_same_d offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (S16A 0) (S10A 0) (SPA 0) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA])
  have hSdzA := fun (c4 c2 c3 : Nat) => sud_same_d offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (S16A 0) (S10A 0) (SPA 0) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) rfl rfl rfl rfl
  have hbA : ∀ c4 c2 c3, genB (αdA c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (SudPV (VA × WvA)) EF → Bool,
        tsumN NRA 2 (fun α β r t => indB (genB β && E' (rvFA c4 c2 c3 α β r t))) ≤
          tsumN NRA 2 (fun α β r t => indB (genB β && E' (svFA c4 c2 c3 α β r t))) + Q4 * (NRA * (Q4 ^ 2 * MA)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (VA × WvA)) EF → Bool,
        tsumN NRA 2 (fun α β r t => indB (genB β && E' (svFA c4 c2 c3 α β r t))) ≤
          tsumN NRA 2 (fun α β r t => indB (genB β && E' (rvFA c4 c2 c3 α β r t))) + Q4 * (NRA * (Q4 ^ 2 * MA)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgzA := (genB_iff _).1 hg
    have hgαA := (genB_iff _).1 hg4
    have hpcsA := sud_pcsX (heap := blankA.heap) (ζ := efOf c3) offA scA smsA swA (rfl : CA.h = 2 ^ 16) hlenA
      (rfl : WtA.h = 2 ^ 10) (by omega) hPgA qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (hS16A c4) (hS10A c4) (hSPA c4) (hsz16A c4) (hszA c4) (hszPA c4)
      (generic_ofF_ne hgzA) (mz_generic hgzA) (friA c4) (mz_generic hgαA) (generic_apow_ne hgαA) hncwA NR2A (RbA c4) (RoA c4)
    have hNRA : sudNR offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA = sudNR offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A 0) (S10A 0) (SPA 0) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA := by
      unfold sudNR; rw [(hSdA c4 c2 c3).n1, (hSdA c4 c2 c3).n2]
    rw [hNRA] at hpcsA
    exact ⟨fun E' => (sud_transcriptG offA NRA 0 (pcsZA c4 c2 (efOf c3)) (psimZA c4 c2 (efOf c3)) hbalA hunA hpcsA E').1,
      fun E' => (sud_transcriptG offA NRA 0 (pcsZA c4 c2 (efOf c3)) (psimZA c4 c2 (efOf c3)) hbalA hunA hpcsA E').2⟩
  have hlen8A : ∀ (c4 : Nat) (ζ : EF) t α β, (colsA t α β).map List.length = (colsA t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(sudCols_shaped offA blankA.hd blankA.stk blankA.heap.length (rfl : CA.h = 2 ^ 16) hlenA (rfl : WtA.h = 2 ^ 10) hPgA
          (S16A c4) (S10A c4) (SPA c4) ζ qvA t α β).2,
        (sudCols_shaped offA blankA.hd blankA.stk blankA.heap.length (rfl : CA.h = 2 ^ 16) hlenA (rfl : WtA.h = 2 ^ 10) hPgA
          (S16A c4) (S10A c4) (SPA c4) ζ qvA t EF.zero EF.zero).2]
  have hmk1A : ∀ kA ∈ mk1A, kA < 8 ∧ ∀ t α β, kA < (colsA t α β).length ∧
      (colsA t α β).getD kA [] = (colsA t EF.zero EF.zero).getD kA [] := by
    intro kA hkA
    have hk'A := hkA
    simp only [mk1A, List.mem_cons, List.not_mem_nil, or_false] at hk'A
    have hknA : kA < 8 := by rcases hk'A with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknA, fun t α β => ⟨hknA, sudCols_main offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA t α β
      EF.zero EF.zero kA hkA⟩⟩
  have hmk2A : ∀ kA ∈ mk2A, kA < 8 ∧ ∀ t α β, kA < (colsA t α β).length := by
    intro kA hkA
    simp only [mk2A, List.mem_cons, List.not_mem_nil, or_false] at hkA
    have hknA : kA < 8 := by rcases hkA with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknA, fun _ _ _ => hknA⟩
  have hvo1A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsA c4) mk1A (main1A t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1A c4 (realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eA := pcsFri_ov2 offA (fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t) (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) ksA colsA ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) (fun t α β ms => (sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk1A hmk1A (hlen8A c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      rw [(hSdA c4 c2 c3).dataF2 colsA mk1A t (r % NR0A), (hSwA c4 c2 c3).S] at eA
      exact .inr (congrArg some eA)
  have hvo2A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsA c4) mk2A (main2A c t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2A c4 (realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eA := pcsFri_ovP offA (fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t) (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) ksA colsA ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) (fun t α β ms => (sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A hmk2A rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      rw [(hSdA c4 c2 c3).dataP2 colsA mk2A t _ _ (r % NR0A), (hSwA c4 c2 c3).S] at eA
      exact .inr (congrArg some eA)
  have hvo3A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3A c4 (main3A c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3A c4 (realVN offA tabsA tvA tpA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab'A : Aborts (prefixOf (efOf (c / Q4)) (offA (efOf (c % Q4)))) (efOf (c % Q4)) (tabsA t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (offA (efOf (c % Q4)))) (efOf (c % Q4)) (tabsA t)
        · rfl
        · exact absurd h hab
      have e0A := pcsFri_ovR2 offA (fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t) (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) ksA colsA ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) (fun t α β ms => (sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A hmk2A rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      have eA := congrArg Prod.snd e0A
      rw [(hSzA c4 c2 c3).tS, (hSzA c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdzA c4 c2 c3).shape,
        tabsCws_congr ncwA _ _ _ (hSdzA c4 c2 c3).shape, (hSdzA c4 c2 c3).cr (r % NR0A), (hSdzA c4 c2 c3).cc (r % NR0A),
        (hSdzA c4 c2 c3).ms (r % NR0A), (hS0A c4 c2).tS, (hS0A c4 c2).iS,
        sud_data_q offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (S16A 0) (S10A 0) (SPA 0) (efOf c3) EF.zero
          qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) t _ _ _ hab'A] at eA
      exact .inr (congrArg some eA)
  have hsvo1A : ∀ c4 c2 c3 c r t, ov1A c4 (svFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1A c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (αdA c4) _ mk1A
      (fun kA hkA => (hmk1A kA hkA).1) rfl _ _ _ (r % NR0A))
  have hsvo2A : ∀ c4 c2 c3 c r t, ov2A c4 (svFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2A c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (αdA c4) _ mk2A
      (fun kA hkA => (hmk2A kA hkA).1) rfl _ _ _ (r % NR0A))
  have hsvo3A : ∀ c4 c2 c3 c r t, ov3A c4 (svFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3A c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0A := psimFri_ovR2 (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) ksA ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ncwA (αdA c4) (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A
      (fun kA hkA => (hmk2A kA hkA).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vSA (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0A)
    have eA := congrArg Prod.snd e0A
    rw [(hSwA c4 c2 c3).tS, (hSwA c4 c2 c3).iS] at eA
    exact congrArg some eA
  have hsd1A : ∀ c4 t r, opF (SsA c4) mk1A (sdF (SsA c4) mk1A (opF (SsA c4) mk1A (main1A t r))) = opF (SsA c4) mk1A (main1A t r) :=
    fun c4 t r => opF_sdF _ _ _
  have hsd2A : ∀ c4 c t r, opF (SsA c4) mk2A (sdF (SsA c4) mk2A (opF (SsA c4) mk2A (main2A c t r))) =
      opF (SsA c4) mk2A (main2A c t r) :=
    fun c4 c t r => opF_sdF _ _ _
  have hsd3A : ∀ c4 c c' t r, op3A c4 (sd3A c4 (op3A c4 (main3A c c' t r))) = op3A c4 (main3A c c' t r) := fun c4 c c' t r =>
    congrArg Prod.snd (op2_sd2 (SsA c4) [] (SsTA c4) (SsCA c4) (fun _ => []) (main3A c c' t r).1 (main3A c c' t r).2)
  have hp3'A : ∀ c4, ComPfHides NS3A Com3A (Pf3A c4) (op3A c4) := by
    intro c4
    have e1A : SsTA c4 = sudSsT (S16A c4) (S10A c4) (SPA c4) := sud_SsT offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0)
    have e2A : SsCA c4 = sudSsC tPA (S16A c4) (S10A c4) (SPA c4) := sud_SsC offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA
    show ComPfHides NS3A Com3A (Pf3A c4) (fun d => (opQ (SsTA c4) d.1, opCw (SsCA c4) d.2))
    rw [e1A, e2A]; exact hp3A c4
  have hozA : ∀ c4 c2 c3 α β r t, ozFA (rvFA c4 c2 c3 α β r t) = ozFA (rvFA 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvFA]
    unfold realVN
    cases hAA : Aborts (prefixOf α (offA β)) β (tabsA t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozFA, Option.some.injEq, Prod.mk.injEq]
      have hdA := sud_same_d offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (S16A 0) (S10A 0) (SPA 0) (efOf c3) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) rfl rfl rfl rfl
      refine ⟨pcsFri_ood offA (fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t) (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) (sudGroups tPA (S16A 0) (S10A 0) (SPA 0) (efOf c3) qvA) ksA colsA
        ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A 0) (S10A 0) (SPA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA rfl rfl t α β (r % NR0A), pcsFri_oodT offA (fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t) (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) (sudGroups tPA (S16A 0) (S10A 0) (SPA 0) (efOf c3) qvA) ksA colsA
        ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A 0) (S10A 0) (SPA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA (by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0A)
        (sud_data_q offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (S16A 0) (S10A 0) (SPA 0) (efOf c3) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) t _ _ _ hAA),
        pcsFri_oodC offA (fun pre β t => sudViewN pre β blankA.hd blankA.stk blankA.heap.length CA MmA WtA t) (sudGroups tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA) (sudGroups tPA (S16A 0) (S10A 0) (SPA 0) (efOf c3) qvA) ksA colsA
        ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A c4) (S10A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ((sudTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap CA MmA WtA tPA (S16A 0) (S10A 0) (SPA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA rfl (by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0A)⟩
    · rfl
  have hgzA : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  obtain ⟨hbalB, hunB⟩ := sud_honest_zk hcB hAB hlenB hkB
  obtain ⟨scB, smsB, swB⟩ := sud_run_sats hcB hAB haccB hlenB hkB
  obtain ⟨hP23B, hPgB⟩ := sud_prog_height hcB hAB hlenB
  rw [← htpB] at hP23B hPgB
  have hSwB := fun (c4 c2 c3 : Nat) => sud_same_w offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB])
  have hSzB := fun (c4 c2 c3 : Nat) => sud_same_w offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB rfl rfl rfl rfl
  have hS0B := fun (c4 c2 : Nat) => sud_same_w offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) EF.zero EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB])
  have hSdB := fun (c4 c2 c3 : Nat) => sud_same_d offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (S16B 0) (S10B 0) (SPB 0) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB])
  have hSdzB := fun (c4 c2 c3 : Nat) => sud_same_d offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (S16B 0) (S10B 0) (SPB 0) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) rfl rfl rfl rfl
  have hbB : ∀ c4 c2 c3, genB (αdB c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (SudPV (VB × WvB)) EF → Bool,
        tsumN NRB 2 (fun α β r t => indB (genB β && E' (rvFB c4 c2 c3 α β r t))) ≤
          tsumN NRB 2 (fun α β r t => indB (genB β && E' (svFB c4 c2 c3 α β r t))) + Q4 * (NRB * (Q4 ^ 2 * MB)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (SudPV (VB × WvB)) EF → Bool,
        tsumN NRB 2 (fun α β r t => indB (genB β && E' (svFB c4 c2 c3 α β r t))) ≤
          tsumN NRB 2 (fun α β r t => indB (genB β && E' (rvFB c4 c2 c3 α β r t))) + Q4 * (NRB * (Q4 ^ 2 * MB)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgzB := (genB_iff _).1 hg
    have hgαB := (genB_iff _).1 hg4
    have hpcsB := sud_pcsX (heap := blankB.heap) (ζ := efOf c3) offB scB smsB swB (rfl : CB.h = 2 ^ 16) hlenB
      (rfl : WtB.h = 2 ^ 10) (by omega) hPgB qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (hS16B c4) (hS10B c4) (hSPB c4) (hsz16B c4) (hszB c4) (hszPB c4)
      (generic_ofF_ne hgzB) (mz_generic hgzB) (friB c4) (mz_generic hgαB) (generic_apow_ne hgαB) hncwB NR2B (RbB c4) (RoB c4)
    have hNRB : sudNR offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB = sudNR offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B 0) (S10B 0) (SPB 0) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB := by
      unfold sudNR; rw [(hSdB c4 c2 c3).n1, (hSdB c4 c2 c3).n2]
    rw [hNRB] at hpcsB
    exact ⟨fun E' => (sud_transcriptG offB NRB 0 (pcsZB c4 c2 (efOf c3)) (psimZB c4 c2 (efOf c3)) hbalB hunB hpcsB E').1,
      fun E' => (sud_transcriptG offB NRB 0 (pcsZB c4 c2 (efOf c3)) (psimZB c4 c2 (efOf c3)) hbalB hunB hpcsB E').2⟩
  have hlen8B : ∀ (c4 : Nat) (ζ : EF) t α β, (colsB t α β).map List.length = (colsB t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(sudCols_shaped offB blankB.hd blankB.stk blankB.heap.length (rfl : CB.h = 2 ^ 16) hlenB (rfl : WtB.h = 2 ^ 10) hPgB
          (S16B c4) (S10B c4) (SPB c4) ζ qvB t α β).2,
        (sudCols_shaped offB blankB.hd blankB.stk blankB.heap.length (rfl : CB.h = 2 ^ 16) hlenB (rfl : WtB.h = 2 ^ 10) hPgB
          (S16B c4) (S10B c4) (SPB c4) ζ qvB t EF.zero EF.zero).2]
  have hmk1B : ∀ kB ∈ mk1B, kB < 8 ∧ ∀ t α β, kB < (colsB t α β).length ∧
      (colsB t α β).getD kB [] = (colsB t EF.zero EF.zero).getD kB [] := by
    intro kB hkB
    have hk'B := hkB
    simp only [mk1B, List.mem_cons, List.not_mem_nil, or_false] at hk'B
    have hknB : kB < 8 := by rcases hk'B with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknB, fun t α β => ⟨hknB, sudCols_main offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB t α β
      EF.zero EF.zero kB hkB⟩⟩
  have hmk2B : ∀ kB ∈ mk2B, kB < 8 ∧ ∀ t α β, kB < (colsB t α β).length := by
    intro kB hkB
    simp only [mk2B, List.mem_cons, List.not_mem_nil, or_false] at hkB
    have hknB : kB < 8 := by rcases hkB with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknB, fun _ _ _ => hknB⟩
  have hvo1B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsB c4) mk1B (main1B t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1B c4 (realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eB := pcsFri_ov2 offB (fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t) (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) ksB colsB ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) (fun t α β ms => (sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk1B hmk1B (hlen8B c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      rw [(hSdB c4 c2 c3).dataF2 colsB mk1B t (r % NR0B), (hSwB c4 c2 c3).S] at eB
      exact .inr (congrArg some eB)
  have hvo2B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsB c4) mk2B (main2B c t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2B c4 (realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eB := pcsFri_ovP offB (fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t) (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) ksB colsB ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) (fun t α β ms => (sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B hmk2B rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      rw [(hSdB c4 c2 c3).dataP2 colsB mk2B t _ _ (r % NR0B), (hSwB c4 c2 c3).S] at eB
      exact .inr (congrArg some eB)
  have hvo3B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3B c4 (main3B c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3B c4 (realVN offB tabsB tvB tpB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab'B : Aborts (prefixOf (efOf (c / Q4)) (offB (efOf (c % Q4)))) (efOf (c % Q4)) (tabsB t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (offB (efOf (c % Q4)))) (efOf (c % Q4)) (tabsB t)
        · rfl
        · exact absurd h hab
      have e0B := pcsFri_ovR2 offB (fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t) (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) ksB colsB ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) (fun t α β ms => (sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B hmk2B rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      have eB := congrArg Prod.snd e0B
      rw [(hSzB c4 c2 c3).tS, (hSzB c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdzB c4 c2 c3).shape,
        tabsCws_congr ncwB _ _ _ (hSdzB c4 c2 c3).shape, (hSdzB c4 c2 c3).cr (r % NR0B), (hSdzB c4 c2 c3).cc (r % NR0B),
        (hSdzB c4 c2 c3).ms (r % NR0B), (hS0B c4 c2).tS, (hS0B c4 c2).iS,
        sud_data_q offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (S16B 0) (S10B 0) (SPB 0) (efOf c3) EF.zero
          qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) t _ _ _ hab'B] at eB
      exact .inr (congrArg some eB)
  have hsvo1B : ∀ c4 c2 c3 c r t, ov1B c4 (svFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1B c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (αdB c4) _ mk1B
      (fun kB hkB => (hmk1B kB hkB).1) rfl _ _ _ (r % NR0B))
  have hsvo2B : ∀ c4 c2 c3 c r t, ov2B c4 (svFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2B c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (αdB c4) _ mk2B
      (fun kB hkB => (hmk2B kB hkB).1) rfl _ _ _ (r % NR0B))
  have hsvo3B : ∀ c4 c2 c3 c r t, ov3B c4 (svFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3B c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0B := psimFri_ovR2 (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) ksB ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ncwB (αdB c4) (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B
      (fun kB hkB => (hmk2B kB hkB).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vSB (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0B)
    have eB := congrArg Prod.snd e0B
    rw [(hSwB c4 c2 c3).tS, (hSwB c4 c2 c3).iS] at eB
    exact congrArg some eB
  have hsd1B : ∀ c4 t r, opF (SsB c4) mk1B (sdF (SsB c4) mk1B (opF (SsB c4) mk1B (main1B t r))) = opF (SsB c4) mk1B (main1B t r) :=
    fun c4 t r => opF_sdF _ _ _
  have hsd2B : ∀ c4 c t r, opF (SsB c4) mk2B (sdF (SsB c4) mk2B (opF (SsB c4) mk2B (main2B c t r))) =
      opF (SsB c4) mk2B (main2B c t r) :=
    fun c4 c t r => opF_sdF _ _ _
  have hsd3B : ∀ c4 c c' t r, op3B c4 (sd3B c4 (op3B c4 (main3B c c' t r))) = op3B c4 (main3B c c' t r) := fun c4 c c' t r =>
    congrArg Prod.snd (op2_sd2 (SsB c4) [] (SsTB c4) (SsCB c4) (fun _ => []) (main3B c c' t r).1 (main3B c c' t r).2)
  have hp3'B : ∀ c4, ComPfHides NS3B Com3B (Pf3B c4) (op3B c4) := by
    intro c4
    have e1B : SsTB c4 = sudSsT (S16B c4) (S10B c4) (SPB c4) := sud_SsT offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0)
    have e2B : SsCB c4 = sudSsC tPB (S16B c4) (S10B c4) (SPB c4) := sud_SsC offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB
    show ComPfHides NS3B Com3B (Pf3B c4) (fun d => (opQ (SsTB c4) d.1, opCw (SsCB c4) d.2))
    rw [e1B, e2B]; exact hp3B c4
  have hozB : ∀ c4 c2 c3 α β r t, ozFB (rvFB c4 c2 c3 α β r t) = ozFB (rvFB 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvFB]
    unfold realVN
    cases hAB : Aborts (prefixOf α (offB β)) β (tabsB t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozFB, Option.some.injEq, Prod.mk.injEq]
      have hdB := sud_same_d offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (S16B 0) (S10B 0) (SPB 0) (efOf c3) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) rfl rfl rfl rfl
      refine ⟨pcsFri_ood offB (fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t) (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) (sudGroups tPB (S16B 0) (S10B 0) (SPB 0) (efOf c3) qvB) ksB colsB
        ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B 0) (S10B 0) (SPB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB rfl rfl t α β (r % NR0B), pcsFri_oodT offB (fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t) (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) (sudGroups tPB (S16B 0) (S10B 0) (SPB 0) (efOf c3) qvB) ksB colsB
        ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B 0) (S10B 0) (SPB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB (by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0B)
        (sud_data_q offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (S16B 0) (S10B 0) (SPB 0) (efOf c3) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) t _ _ _ hAB),
        pcsFri_oodC offB (fun pre β t => sudViewN pre β blankB.hd blankB.stk blankB.heap.length CB MmB WtB t) (sudGroups tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB) (sudGroups tPB (S16B 0) (S10B 0) (SPB 0) (efOf c3) qvB) ksB colsB
        ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B c4) (S10B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ((sudTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap CB MmB WtB tPB (S16B 0) (S10B 0) (SPB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB rfl (by simp only [sudTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0B)⟩
    · rfl
  have hgzB : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  exact fs_open4_two hK2 Q4_pos hK4 φA hφA rvFA svFA (fun c2 c3 => genB (efOf c3)) hgzA (fun c4 => genB (αdA c4)) hB4A
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozFA hozA (fun c4 c2 c3 hg4 hg => (hbA c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hbA c4 c2 c3 hg4 hg).2)
    Com1A Pf1A (fun c4 => opF (SsA c4) mk1A) (fun c4 => sdF (SsA c4) mk1A) d1A hc1A hp1A hr1A ov1A (fun _ => rfl) main1A hsd1A
    Com2A Pf2A (fun c4 => opF (SsA c4) mk2A) (fun c4 => sdF (SsA c4) mk2A) d2A hc2A hp2A hr2A ov2A (fun _ => rfl) main2A hsd2A
    Com3A Pf3A op3A sd3A d3A hc3A hp3'A hr3A ov3A (fun _ => rfl) main3A hsd3A hvo1A hvo2A hvo3A sop1A sop2A sop3A hsvo1A hsvo2A hsvo3A
    φB hφB rvFB svFB (fun c2 c3 => genB (efOf c3)) hgzB (fun c4 => genB (αdB c4)) hB4B
    (fun c4 c2 c3 α β r t => realVN_cases _ _ _ _ _ α β r t) (fun c4 c2 c3 α β r t => simVN_some _ _ _ _ _ _ _ _ α β r t)
    ozFB hozB (fun c4 c2 c3 hg4 hg => (hbB c4 c2 c3 hg4 hg).1) (fun c4 c2 c3 hg4 hg => (hbB c4 c2 c3 hg4 hg).2)
    Com1B Pf1B (fun c4 => opF (SsB c4) mk1B) (fun c4 => sdF (SsB c4) mk1B) d1B hc1B hp1B hr1B ov1B (fun _ => rfl) main1B hsd1B
    Com2B Pf2B (fun c4 => opF (SsB c4) mk2B) (fun c4 => sdF (SsB c4) mk2B) d2B hc2B hp2B hr2B ov2B (fun _ => rfl) main2B hsd2B
    Com3B Pf3B op3B sd3B d3B hc3B hp3'B hr3B ov3B (fun _ => rfl) main3B hsd3B hvo1B hvo2B hvo3B sop1B sop2B sop3B hsvo1B hsvo2B hsvo3B
    hφAB (fun v => spread_sum Com1B main1B hspB v) E

end

end Circuit
