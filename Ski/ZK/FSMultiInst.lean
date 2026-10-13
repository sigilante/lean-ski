import Ski.ZK.FSMulti
import Ski.ZK.FSQueryInst

/-!
# Two proofs of each circuit under one oracle

`fs_open4_two` for two Sudoku proofs (`sud_fs_open4_two`), two hidden-term
proofs (`wit_fs_open4_two`) and two composed proofs (`comp_fs_open4_two`),
the collisions bounded by the commitment's salt spread (`spread_sum`).
-/

namespace Circuit

open ZKF

section
open B Air Stmt Mach Sudoku SudokuText

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Two Sudoku proofs under one oracle**, each over four Fiat–Shamir
    rounds with every commitment opened and the query points hashed
    (`sud_fs_open4` twice, `fs_open4_two`): the two proofs, of any two
    statements, read the same four tables; the simulator programs the second's
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

section
open B Air Compose CompM Stmt Mach Wit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Two composed proofs under one oracle**, each over four Fiat–Shamir
    rounds with every commitment opened and the query points hashed
    (`comp_fs_open4` twice, `fs_open4_two`): the two proofs, of any two
    statements, read the same four tables; the simulator programs the second's
    answers and then the first's.  The error is each proof's own over the
    other's draws, and the collisions, bounded by the second proof's first
    commitment's salt spread (`hspB`, at most `δs` of the salts commit any
    data to any one value) through `spread_sum`.  The query hash maps keep
    the transcript's residue mod `n1` (`hφAB`).  Statements fixed in
    advance; two proofs. -/
theorem comp_fs_open4_two {VA WvA P1A P2A P3A : Type} (offA : EF → String → EF) {RA LmA : Nat} (hRA : RA ≤ 20) {shpA : BT} {PsA : List Term}
    {WA : Nat} {ρA : Nat → Bool} {regionA : List Cell} (hrlA : regionA.length = WA)
    (hrA : ∀ i c, regionA[i]? = some c → cellOK (BT.nleaves shpA + 3 + i) c = true)
    {AA : List Cell} {eA : Nat → Nat} {rowA : Nat → Air.Row}
    (hAA : AcceptsC AA (cMachine ρA shpA regionA PsA) (cHeap ρA shpA regionA PsA).2
      (cHeap ρA shpA regionA PsA).1.length PsA.length eA rowA)
    (hlenA : AA.length = 2 ^ LmA) (hLmA : LmA ≤ 20) (hKA : eA (PsA.length - 1) < 2 ^ RA)
    (hNWA : BT.nleaves shpA + WA ≤ 2 ^ 8)
    {tbMA tbCA tpPA tpSA : Nat} (htMA : tbMA + 1 = LmA) (htCA : tbCA + 1 = RA)
    (htPA : tpPA = progTpC (blankM shpA WA PsA).heap (BT.nleaves shpA) WA) (htSA : tpSA = segTp (blankRoots shpA WA PsA))
    (SMA SCA S9A SPA SSA : Nat → List F) (qvA : EF → EF → List EF → F → List F → List F → List EF)
    (wmA wcA wwA wpA wsgA : Nat → List (EF → EF → List F)) {LwmA LwcA LwwA LwpA LwsgA : Nat} (hlwmA : ∀ c, (wmA c).length = LwmA)
    (hlwcA : ∀ c, (wcA c).length = LwcA) (hlwwA : ∀ c, (wwA c).length = LwwA) (hlwpA : ∀ c, (wpA c).length = LwpA)
    (hlwsgA : ∀ c, (wsgA c).length = LwsgA)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φA : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφA : ∀ mA w, φA mA w < N4)
    (hSMA : ∀ c4, ∀ x ∈ SMA c4, x ∉ cosetL 1 (bbGen (tbMA + 1)) (2 ^ (tbMA + 1)))
    (hSCA : ∀ c4, ∀ x ∈ SCA c4, x ∉ cosetL 1 (bbGen (tbCA + 1)) (2 ^ (tbCA + 1)))
    (hS9A : ∀ c4, ∀ x ∈ S9A c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPA : ∀ c4, ∀ x ∈ SPA c4, x ∉ cosetL 1 (bbGen (tpPA + 1)) (2 ^ (tpPA + 1)))
    (hSSA : ∀ c4, ∀ x ∈ SSA c4, x ∉ cosetL 1 (bbGen (tpSA + 1)) (2 ^ (tpSA + 1)))
    (hszMA : ∀ c4, 2 * (SMA c4).length + 8 ≤ 2 ^ (tbMA + 1)) (hszCA : ∀ c4, 2 * (SCA c4).length + 8 ≤ 2 ^ (tbCA + 1))
    (hsz9A : ∀ c4, 2 * (S9A c4).length + 8 ≤ 2 ^ 9) (hszPA : ∀ c4, 2 * (SPA c4).length + 8 ≤ 2 ^ (tpPA + 1))
    (hszSA : ∀ c4, 2 * (SSA c4).length + 8 ≤ 2 ^ (tpSA + 1)) {ncwA : Nat} (αdA : Nat → EF) {B4A : Nat}
    (hB4A : sumTo K4 (fun c4 => indB (!genB (αdA c4))) ≤ B4A) (friA : Nat → EF → EF → List (EF → EF) → VA) (hncwA : 4 ≤ ncwA)
    (NR2A : Nat) (RbA : Nat → EF → EF → Nat → List (EF → EF)) (RoA : Nat → EF → EF → Nat → WvA)
    {NS1A NS2A NS3A n1 n2 n3 : Nat}
    (Com1A : List (List (List F)) → Nat → Nat) (Pf1A : Nat → List (List (List F)) → Nat → P1A) (hc1A : ComHides NS1A Com1A)
    (hp1A : ∀ c4, ComPfHides NS1A Com1A (Pf1A c4) (opF ((cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) EF.zero qvA).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1A : ∀ d σ, Com1A d σ < n1) (d1A : List (List (List F)))
    (Com2A : List (List (List F)) → Nat → Nat) (Pf2A : Nat → List (List (List F)) → Nat → P2A) (hc2A : ComHides NS2A Com2A)
    (hp2A : ∀ c4, ComPfHides NS2A Com2A (Pf2A c4) (opF ((cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) EF.zero qvA).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2A : ∀ d σ, Com2A d σ < n2) (d2A : List (List (List F)))
    (Com3A : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3A : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3A) (hc3A : ComHides NS3A Com3A)
    (hp3A : ∀ c4, ComPfHides NS3A Com3A (Pf3A c4) (fun d => (opQ (cSsT (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4)) d.1, opCw (cSsC tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4)) d.2)))
    (hr3A : ∀ d σ, Com3A d σ < n3) (d3A : List (List (List (List F))) × List (List (List F)))
    {VB WvB P1B P2B P3B : Type} (offB : EF → String → EF) {RB LmB : Nat} (hRB : RB ≤ 20) {shpB : BT} {PsB : List Term}
    {WB : Nat} {ρB : Nat → Bool} {regionB : List Cell} (hrlB : regionB.length = WB)
    (hrB : ∀ i c, regionB[i]? = some c → cellOK (BT.nleaves shpB + 3 + i) c = true)
    {AB : List Cell} {eB : Nat → Nat} {rowB : Nat → Air.Row}
    (hAB : AcceptsC AB (cMachine ρB shpB regionB PsB) (cHeap ρB shpB regionB PsB).2
      (cHeap ρB shpB regionB PsB).1.length PsB.length eB rowB)
    (hlenB : AB.length = 2 ^ LmB) (hLmB : LmB ≤ 20) (hKB : eB (PsB.length - 1) < 2 ^ RB)
    (hNWB : BT.nleaves shpB + WB ≤ 2 ^ 8)
    {tbMB tbCB tpPB tpSB : Nat} (htMB : tbMB + 1 = LmB) (htCB : tbCB + 1 = RB)
    (htPB : tpPB = progTpC (blankM shpB WB PsB).heap (BT.nleaves shpB) WB) (htSB : tpSB = segTp (blankRoots shpB WB PsB))
    (SMB SCB S9B SPB SSB : Nat → List F) (qvB : EF → EF → List EF → F → List F → List F → List EF)
    (wmB wcB wwB wpB wsgB : Nat → List (EF → EF → List F)) {LwmB LwcB LwwB LwpB LwsgB : Nat} (hlwmB : ∀ c, (wmB c).length = LwmB)
    (hlwcB : ∀ c, (wcB c).length = LwcB) (hlwwB : ∀ c, (wwB c).length = LwwB) (hlwpB : ∀ c, (wpB c).length = LwpB)
    (hlwsgB : ∀ c, (wsgB c).length = LwsgB)
    (φB : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (hφB : ∀ mB w, φB mB w < N4)
    (hSMB : ∀ c4, ∀ x ∈ SMB c4, x ∉ cosetL 1 (bbGen (tbMB + 1)) (2 ^ (tbMB + 1)))
    (hSCB : ∀ c4, ∀ x ∈ SCB c4, x ∉ cosetL 1 (bbGen (tbCB + 1)) (2 ^ (tbCB + 1)))
    (hS9B : ∀ c4, ∀ x ∈ S9B c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPB : ∀ c4, ∀ x ∈ SPB c4, x ∉ cosetL 1 (bbGen (tpPB + 1)) (2 ^ (tpPB + 1)))
    (hSSB : ∀ c4, ∀ x ∈ SSB c4, x ∉ cosetL 1 (bbGen (tpSB + 1)) (2 ^ (tpSB + 1)))
    (hszMB : ∀ c4, 2 * (SMB c4).length + 8 ≤ 2 ^ (tbMB + 1)) (hszCB : ∀ c4, 2 * (SCB c4).length + 8 ≤ 2 ^ (tbCB + 1))
    (hsz9B : ∀ c4, 2 * (S9B c4).length + 8 ≤ 2 ^ 9) (hszPB : ∀ c4, 2 * (SPB c4).length + 8 ≤ 2 ^ (tpPB + 1))
    (hszSB : ∀ c4, 2 * (SSB c4).length + 8 ≤ 2 ^ (tpSB + 1)) {ncwB : Nat} (αdB : Nat → EF) {B4B : Nat}
    (hB4B : sumTo K4 (fun c4 => indB (!genB (αdB c4))) ≤ B4B) (friB : Nat → EF → EF → List (EF → EF) → VB) (hncwB : 4 ≤ ncwB)
    (NR2B : Nat) (RbB : Nat → EF → EF → Nat → List (EF → EF)) (RoB : Nat → EF → EF → Nat → WvB)
    {NS1B NS2B NS3B : Nat}
    (Com1B : List (List (List F)) → Nat → Nat) (Pf1B : Nat → List (List (List F)) → Nat → P1B) (hc1B : ComHides NS1B Com1B)
    (hp1B : ∀ c4, ComPfHides NS1B Com1B (Pf1B c4) (opF ((cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) EF.zero qvB).map (·.base.S)) [0, 2, 4, 6, 8]))
    (hr1B : ∀ d σ, Com1B d σ < n1) (d1B : List (List (List F)))
    (Com2B : List (List (List F)) → Nat → Nat) (Pf2B : Nat → List (List (List F)) → Nat → P2B) (hc2B : ComHides NS2B Com2B)
    (hp2B : ∀ c4, ComPfHides NS2B Com2B (Pf2B c4) (opF ((cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) EF.zero qvB).map (·.base.S)) [1, 3, 5, 7, 9]))
    (hr2B : ∀ d σ, Com2B d σ < n2) (d2B : List (List (List F)))
    (Com3B : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3B : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3B) (hc3B : ComHides NS3B Com3B)
    (hp3B : ∀ c4, ComPfHides NS3B Com3B (Pf3B c4) (fun d => (opQ (cSsT (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4)) d.1, opCw (cSsC tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4)) d.2)))
    (hr3B : ∀ d σ, Com3B d σ < n3) (d3B : List (List (List (List F))) × List (List (List F)))
    (hφAB : ∀ m w m' w', φB m w = φA m' w' → m % n1 = m' % n1) {δs : Nat}
    (hspB : ∀ d v, sumTo NS1B (fun σ => indB (decide (Com1B d σ = v))) ≤ δs) :
    let mA := blankM shpA WA PsA
    let rootsA := blankRoots shpA WA PsA
    let NA := BT.nleaves shpA
    let CA := cpuTableC AA rowA eA PsA.length rootsA (2 ^ RA)
    let PgA := progTableC mA.heap NA WA
    let WtA := witTable AA NA WA
    let MmA := memTableC AA (cpuAirC mA.hd mA.stk mA.heap.length rootsA.length mA.stk) (progAirC mA.heap NA WA)
      (witAir NA WA) CA PgA WtA
    let NR0A := cNR offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0) ncwA
    let pcsZA := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) ncwA (αdA c4)
      (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) t α β (r % NR0A)
    let psimZA := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) ncwA (αdA c4)
      (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) α β v (r % NR0A)
    let NRA := NR0A * NR2A
    let tabsA := fun t : Nat → Tup => compTables mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA
      ((CA.setBlind BLA (t 1)).setBlind BLB (t 0)) (MmA.setBlind 5 (t 0)) (progTableC mA.heap NA WA)
      (WtA.setBlind WT_BLIND (t 1)) (segsPub rootsA)
    let tvA := fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t
    let pbA := fun pre β => (terminal pre β (progAirC mA.heap NA WA) (progTableC mA.heap NA WA),
      terminal pre β (segsAir rootsA) (segsPub rootsA))
    let ptmA := fun pre β => (terminal pre β (progAirC mA.heap NA WA) (progTableC mA.heap NA WA)).add
      (terminal pre β (segsAir rootsA) (segsPub rootsA))
    let MA := (allEntries (compTables mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA
      (progTableC mA.heap NA WA) WtA (segsPub rootsA))).length
    let q0A := cGroups tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) EF.zero qvA
    let qZA := fun (c4 : Nat) (ζ : EF) => cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA
    let SsA := fun c4 => (qZA c4 EF.zero).map (·.base.S)
    let ksA := cKs mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA
    let colsA := cCols offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA
    let tqZA := fun (c4 c2 : Nat) (ζ : EF) => (cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst
    let qdZA := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map (fun p => p.2 t α β ms)
    let SsTA := fun c4 => (tqZA c4 0 EF.zero).map (·.S)
    let SsCA := fun c4 => (tabsInfo ncwA (tqZA c4 0 EF.zero)).map (·.S)
    let mk1A := [0, 2, 4, 6, 8]
    let mk2A := [1, 3, 5, 7, 9]
    let main1A := fun (t : Nat → Tup) (r : Nat) => mainF2 q0A ksA colsA (tqZA 0 0 EF.zero) ncwA mk1A t (r % NR0A)
    let main2A := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0A ksA colsA (tqZA 0 0 EF.zero) ncwA mk2A t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0A)
    let main3A := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZA 0 c2 EF.zero) (qdZA 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0A ksA (tqZA 0 c2 EF.zero) ncwA (r % NR0A))) (crF q0A ksA (tqZA 0 c2 EF.zero) ncwA (r % NR0A)),
       tabsCws ncwA (tqZA 0 c2 EF.zero) (ccF q0A ksA (tqZA 0 c2 EF.zero) ncwA (r % NR0A)))
    let vSA := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (offA β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptmA (prefixOf α (offA β)) β)) t
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
    let ov1A : Nat → TViewN (PcsPV (VA × WvA)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsA c4) mk1A pv)
      | none => none
    let ov2A : Nat → TViewN (PcsPV (VA × WvA)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsA c4) mk2A pv)
      | none => none
    let ov3A : Nat → TViewN (PcsPV (VA × WvA)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvFA := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) α β r t
    let svFA := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN offA pbA chainBus (fun _ => false) chainPar 3 ptmA (psimZA c4 c2 (efOf c3)) α β r t
    let ozFA : TViewN (PcsPV (VA × WvA)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3A := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsTA c4) d.1, opCw (SsCA c4) d.2)
    let sd3A := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsTA c4) o.1, sdCw (SsCA c4) o.2)
    let mB := blankM shpB WB PsB
    let rootsB := blankRoots shpB WB PsB
    let NB := BT.nleaves shpB
    let CB := cpuTableC AB rowB eB PsB.length rootsB (2 ^ RB)
    let PgB := progTableC mB.heap NB WB
    let WtB := witTable AB NB WB
    let MmB := memTableC AB (cpuAirC mB.hd mB.stk mB.heap.length rootsB.length mB.stk) (progAirC mB.heap NB WB)
      (witAir NB WB) CB PgB WtB
    let NR0B := cNR offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0) ncwB
    let pcsZB := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) ncwB (αdB c4)
      (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) t α β (r % NR0B)
    let psimZB := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) ncwB (αdB c4)
      (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) α β v (r % NR0B)
    let NRB := NR0B * NR2B
    let tabsB := fun t : Nat → Tup => compTables mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB
      ((CB.setBlind BLA (t 1)).setBlind BLB (t 0)) (MmB.setBlind 5 (t 0)) (progTableC mB.heap NB WB)
      (WtB.setBlind WT_BLIND (t 1)) (segsPub rootsB)
    let tvB := fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t
    let pbB := fun pre β => (terminal pre β (progAirC mB.heap NB WB) (progTableC mB.heap NB WB),
      terminal pre β (segsAir rootsB) (segsPub rootsB))
    let ptmB := fun pre β => (terminal pre β (progAirC mB.heap NB WB) (progTableC mB.heap NB WB)).add
      (terminal pre β (segsAir rootsB) (segsPub rootsB))
    let MB := (allEntries (compTables mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB
      (progTableC mB.heap NB WB) WtB (segsPub rootsB))).length
    let q0B := cGroups tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) EF.zero qvB
    let qZB := fun (c4 : Nat) (ζ : EF) => cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB
    let SsB := fun c4 => (qZB c4 EF.zero).map (·.base.S)
    let ksB := cKs mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB
    let colsB := cCols offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB
    let tqZB := fun (c4 c2 : Nat) (ζ : EF) => (cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst
    let qdZB := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map (fun p => p.2 t α β ms)
    let SsTB := fun c4 => (tqZB c4 0 EF.zero).map (·.S)
    let SsCB := fun c4 => (tabsInfo ncwB (tqZB c4 0 EF.zero)).map (·.S)
    let mk1B := [0, 2, 4, 6, 8]
    let mk2B := [1, 3, 5, 7, 9]
    let main1B := fun (t : Nat → Tup) (r : Nat) => mainF2 q0B ksB colsB (tqZB 0 0 EF.zero) ncwB mk1B t (r % NR0B)
    let main2B := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0B ksB colsB (tqZB 0 0 EF.zero) ncwB mk2B t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0B)
    let main3B := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZB 0 c2 EF.zero) (qdZB 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0B ksB (tqZB 0 c2 EF.zero) ncwB (r % NR0B))) (crF q0B ksB (tqZB 0 c2 EF.zero) ncwB (r % NR0B)),
       tabsCws ncwB (tqZB 0 c2 EF.zero) (ccF q0B ksB (tqZB 0 c2 EF.zero) ncwB (r % NR0B)))
    let vSB := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (offB β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptmB (prefixOf α (offB β)) β)) t
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
    let ov1B : Nat → TViewN (PcsPV (VB × WvB)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsB c4) mk1B pv)
      | none => none
    let ov2B : Nat → TViewN (PcsPV (VB × WvB)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsB c4) mk2B pv)
      | none => none
    let ov3B : Nat → TViewN (PcsPV (VB × WvB)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvFB := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) α β r t
    let svFB := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN offB pbB chainBus (fun _ => false) chainPar 3 ptmB (psimZB c4 c2 (efOf c3)) α β r t
    let ozFB : TViewN (PcsPV (VB × WvB)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
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
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1A × Option (P2A × P3A) × TViewN (PcsPV (VA × WvA)) (EF × EF)) → Nat × Nat × Nat × (Option P1B × Option (P2B × P3B) × TViewN (PcsPV (VB × WvB)) (EF × EF)) → Bool,
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
  intro mA rootsA NA CA PgA WtA MmA NR0A pcsZA psimZA NRA tabsA tvA pbA ptmA MA q0A qZA SsA ksA colsA tqZA qdZA SsTA SsCA mk1A mk2A main1A main2A main3A vSA sop1A sop2A sop3A ov1A ov2A ov3A rvFA svFA ozFA op3A sd3A mB rootsB NB CB PgB WtB MmB NR0B pcsZB psimZB NRB tabsB tvB pbB ptmB MB q0B qZB SsB ksB colsB tqZB qdZB SsTB SsCB mk1B mk2B main1B main2B main3B vSB sop1B sop2B sop3B ov1B ov2B ov3B rvFB svFB ozFB op3B sd3B smA m1A m2A m3A rvoA s1A s2A s3A svoA sm4A r1A r2A r3A MqA smB m1B m2B m3B rvoB s1B s2B s3B svoB sm4B r1B r2B r3B MqB ST SC rvTA pgTA svTA rvTB pgTB svTB colT okT E
  obtain ⟨hbalA, hunA⟩ := comp_honest_zk hRA hrlA hrA hAA hlenA hLmA hKA hNWA
  obtain ⟨scA, smsA, swA, hWhA, _⟩ := comp_run_sats hRA hrlA hrA hAA hlenA hLmA hKA hNWA
  obtain ⟨p1A, p2A, s1A, s2A⟩ := comp_pub_heights hRA hrlA hAA hlenA hLmA hKA
  rw [← htPA] at p1A p2A
  rw [← htSA] at s1A s2A
  have hMA : MmA.h = 2 ^ (tbMA + 1) := by rw [htMA]; exact hlenA
  have hCA : CA.h = 2 ^ (tbCA + 1) := by rw [htCA]; rfl
  have hSwA := fun (c4 c2 c3 : Nat) => comp_same_w offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0) ncwA (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA]) (by rw [hlwsgA, hlwsgA])
  have hSzA := fun (c4 c2 c3 : Nat) => comp_same_w offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) ncwA rfl rfl rfl rfl rfl
  have hS0A := fun (c4 c2 : Nat) => comp_same_w offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) EF.zero EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0) ncwA (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA]) (by rw [hlwsgA, hlwsgA])
  have hSdA := fun (c4 c2 c3 : Nat) => comp_same_d offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0) (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA]) (by rw [hlwsgA, hlwsgA])
  have hSdzA := fun (c4 c2 c3 : Nat) => comp_same_d offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) rfl rfl rfl rfl rfl
  have hbA : ∀ c4 c2 c3, genB (αdA c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (VA × WvA)) (EF × EF) → Bool,
        tsumN NRA 2 (fun α β r t => indB (genB β && E' (rvFA c4 c2 c3 α β r t))) ≤
          tsumN NRA 2 (fun α β r t => indB (genB β && E' (svFA c4 c2 c3 α β r t))) + Q4 * (NRA * (Q4 ^ 2 * MA)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (VA × WvA)) (EF × EF) → Bool,
        tsumN NRA 2 (fun α β r t => indB (genB β && E' (svFA c4 c2 c3 α β r t))) ≤
          tsumN NRA 2 (fun α β r t => indB (genB β && E' (rvFA c4 c2 c3 α β r t))) + Q4 * (NRA * (Q4 ^ 2 * MA)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgzA := (genB_iff _).1 hg
    have hgαA := (genB_iff _).1 hg4
    have hpcsA := comp_pcsX (heap := mA.heap) (ζ := efOf c3) (roots := rootsA) offA scA smsA swA (by omega) (by omega) (by omega) (by omega)
      hMA hCA hWhA p2A s2A qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (hSMA c4) (hSCA c4) (hS9A c4) (hSPA c4) (hSSA c4) (hszMA c4) (hszCA c4) (hsz9A c4) (hszPA c4) (hszSA c4) (generic_ofF_ne hgzA) (mz_generic hgzA) (friA c4) (mz_generic hgαA) (generic_apow_ne hgαA) hncwA NR2A (RbA c4) (RoA c4)
    have hNRA : cNR offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) ncwA = cNR offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0) ncwA := by
      unfold cNR; rw [(hSdA c4 c2 c3).n1, (hSdA c4 c2 c3).n2]
    rw [hNRA] at hpcsA
    exact ⟨fun E' => (comp_transcriptG offA NRA 0 (pcsZA c4 c2 (efOf c3)) (psimZA c4 c2 (efOf c3)) hbalA hunA hpcsA E').1,
      fun E' => (comp_transcriptG offA NRA 0 (pcsZA c4 c2 (efOf c3)) (psimZA c4 c2 (efOf c3)) hbalA hunA hpcsA E').2⟩
  have hlen8A : ∀ (c4 : Nat) (ζ : EF) t α β, (colsA t α β).map List.length = (colsA t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(cCols_shaped offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk hMA hCA hWhA p2A s2A
          (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA t α β).2,
        (cCols_shaped offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk hMA hCA hWhA p2A s2A
          (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) ζ qvA t EF.zero EF.zero).2]
  have hmk1A : ∀ k ∈ mk1A, k < 10 ∧ ∀ t α β, k < (colsA t α β).length ∧
      (colsA t α β).getD k [] = (colsA t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk'A := hk
    simp only [mk1A, List.mem_cons, List.not_mem_nil, or_false] at hk'A
    have hknA : k < 10 := by rcases hk'A with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknA, fun t α β => ⟨hknA, compCols_main offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2A : ∀ k ∈ mk2A, k < 10 ∧ ∀ t α β, k < (colsA t α β).length := by
    intro k hk
    simp only [mk2A, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hknA : k < 10 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknA, fun _ _ _ => hknA⟩
  have hvo1A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsA c4) mk1A (main1A t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1A c4 (realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eA := pcsFri_ov2 offA (fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t) (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) ksA colsA ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) (fun t α β ms => (cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk1A hmk1A (hlen8A c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      rw [(hSdA c4 c2 c3).dataF2 colsA mk1A t (r % NR0A), (hSwA c4 c2 c3).S] at eA
      exact .inr (congrArg some eA)
  have hvo2A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsA c4) mk2A (main2A c t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2A c4 (realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eA := pcsFri_ovP offA (fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t) (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) ksA colsA ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) (fun t α β ms => (cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A hmk2A rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      rw [(hSdA c4 c2 c3).dataP2 colsA mk2A t _ _ (r % NR0A), (hSwA c4 c2 c3).S] at eA
      exact .inr (congrArg some eA)
  have hvo3A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3A c4 (main3A c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3A c4 (realVN offA tabsA tvA pbA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab'A : Aborts (prefixOf (efOf (c / Q4)) (offA (efOf (c % Q4)))) (efOf (c % Q4)) (tabsA t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (offA (efOf (c % Q4)))) (efOf (c % Q4)) (tabsA t)
        · rfl
        · exact absurd h hab
      have e0A := pcsFri_ovR2 offA (fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t) (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) ksA colsA ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) (fun t α β ms => (cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A hmk2A rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      have eA := congrArg Prod.snd e0A
      rw [(hSzA c4 c2 c3).tS, (hSzA c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdzA c4 c2 c3).shape,
        tabsCws_congr ncwA _ _ _ (hSdzA c4 c2 c3).shape, (hSdzA c4 c2 c3).cr (r % NR0A), (hSdzA c4 c2 c3).cc (r % NR0A),
        (hSdzA c4 c2 c3).ms (r % NR0A), (hS0A c4 c2).tS, (hS0A c4 c2).iS,
        comp_data_q offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) EF.zero
          qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) t _ _ _ hab'A] at eA
      exact .inr (congrArg some eA)
  have hsvo1A : ∀ c4 c2 c3 c r t, ov1A c4 (svFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1A c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (αdA c4) _ mk1A
      (fun k hk => (hmk1A k hk).1) rfl _ _ _ (r % NR0A))
  have hsvo2A : ∀ c4 c2 c3 c r t, ov2A c4 (svFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2A c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZA c4 (efOf c3)) ksA (tqZA c4 c2 (efOf c3)) ncwA (αdA c4) _ mk2A
      (fun k hk => (hmk2A k hk).1) rfl _ _ _ (r % NR0A))
  have hsvo3A : ∀ c4 c2 c3 c r t, ov3A c4 (svFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3A c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0A := psimFri_ovR2 (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) ksA ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) ncwA (αdA c4) (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A
      (fun k hk => (hmk2A k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vSA (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0A)
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
    have e1A : SsTA c4 = cSsT (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) := comp_SsT offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0)
    have e2A : SsCA c4 = cSsC tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) := comp_SsC offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) (wsgA 0) ncwA
    show ComPfHides NS3A Com3A (Pf3A c4) (fun d => (opQ (SsTA c4) d.1, opCw (SsCA c4) d.2))
    rw [e1A, e2A]; exact hp3A c4
  have hozA : ∀ c4 c2 c3 α β r t, ozFA (rvFA c4 c2 c3 α β r t) = ozFA (rvFA 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvFA]
    unfold realVN
    cases hAA : Aborts (prefixOf α (offA β)) β (tabsA t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozFA, Option.some.injEq, Prod.mk.injEq]
      have hdA := comp_same_d offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) rfl rfl rfl rfl rfl
      refine ⟨pcsFri_ood offA (fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t) (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) (cGroups tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) qvA) ksA colsA
        ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA rfl rfl t α β (r % NR0A), pcsFri_oodT offA (fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t) (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) (cGroups tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) qvA) ksA colsA
        ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA (by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0A)
        (comp_data_q offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2) t _ _ _ hAA),
        pcsFri_oodC offA (fun pre β t => compViewN pre β mA.hd mA.stk mA.heap.length rootsA.length mA.stk NA WA CA MmA WtA t) (cGroups tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA) (cGroups tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) qvA) ksA colsA
        ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA c4) (SCA c4) (S9A c4) (SPA c4) (SSA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) ((cTs offA mA.hd mA.stk mA.heap.length rootsA.length mA.stk mA.heap NA WA rootsA CA MmA WtA tbMA tbCA tpPA tpSA (SMA 0) (SCA 0) (S9A 0) (SPA 0) (SSA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wsgA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA rfl (by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0A)⟩
    · rfl
  have hgzA : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  obtain ⟨hbalB, hunB⟩ := comp_honest_zk hRB hrlB hrB hAB hlenB hLmB hKB hNWB
  obtain ⟨scB, smsB, swB, hWhB, _⟩ := comp_run_sats hRB hrlB hrB hAB hlenB hLmB hKB hNWB
  obtain ⟨p1B, p2B, s1B, s2B⟩ := comp_pub_heights hRB hrlB hAB hlenB hLmB hKB
  rw [← htPB] at p1B p2B
  rw [← htSB] at s1B s2B
  have hMB : MmB.h = 2 ^ (tbMB + 1) := by rw [htMB]; exact hlenB
  have hCB : CB.h = 2 ^ (tbCB + 1) := by rw [htCB]; rfl
  have hSwB := fun (c4 c2 c3 : Nat) => comp_same_w offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0) ncwB (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB]) (by rw [hlwsgB, hlwsgB])
  have hSzB := fun (c4 c2 c3 : Nat) => comp_same_w offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) ncwB rfl rfl rfl rfl rfl
  have hS0B := fun (c4 c2 : Nat) => comp_same_w offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) EF.zero EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0) ncwB (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB]) (by rw [hlwsgB, hlwsgB])
  have hSdB := fun (c4 c2 c3 : Nat) => comp_same_d offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0) (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB]) (by rw [hlwsgB, hlwsgB])
  have hSdzB := fun (c4 c2 c3 : Nat) => comp_same_d offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) rfl rfl rfl rfl rfl
  have hbB : ∀ c4 c2 c3, genB (αdB c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (VB × WvB)) (EF × EF) → Bool,
        tsumN NRB 2 (fun α β r t => indB (genB β && E' (rvFB c4 c2 c3 α β r t))) ≤
          tsumN NRB 2 (fun α β r t => indB (genB β && E' (svFB c4 c2 c3 α β r t))) + Q4 * (NRB * (Q4 ^ 2 * MB)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (VB × WvB)) (EF × EF) → Bool,
        tsumN NRB 2 (fun α β r t => indB (genB β && E' (svFB c4 c2 c3 α β r t))) ≤
          tsumN NRB 2 (fun α β r t => indB (genB β && E' (rvFB c4 c2 c3 α β r t))) + Q4 * (NRB * (Q4 ^ 2 * MB)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgzB := (genB_iff _).1 hg
    have hgαB := (genB_iff _).1 hg4
    have hpcsB := comp_pcsX (heap := mB.heap) (ζ := efOf c3) (roots := rootsB) offB scB smsB swB (by omega) (by omega) (by omega) (by omega)
      hMB hCB hWhB p2B s2B qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (hSMB c4) (hSCB c4) (hS9B c4) (hSPB c4) (hSSB c4) (hszMB c4) (hszCB c4) (hsz9B c4) (hszPB c4) (hszSB c4) (generic_ofF_ne hgzB) (mz_generic hgzB) (friB c4) (mz_generic hgαB) (generic_apow_ne hgαB) hncwB NR2B (RbB c4) (RoB c4)
    have hNRB : cNR offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) ncwB = cNR offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0) ncwB := by
      unfold cNR; rw [(hSdB c4 c2 c3).n1, (hSdB c4 c2 c3).n2]
    rw [hNRB] at hpcsB
    exact ⟨fun E' => (comp_transcriptG offB NRB 0 (pcsZB c4 c2 (efOf c3)) (psimZB c4 c2 (efOf c3)) hbalB hunB hpcsB E').1,
      fun E' => (comp_transcriptG offB NRB 0 (pcsZB c4 c2 (efOf c3)) (psimZB c4 c2 (efOf c3)) hbalB hunB hpcsB E').2⟩
  have hlen8B : ∀ (c4 : Nat) (ζ : EF) t α β, (colsB t α β).map List.length = (colsB t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(cCols_shaped offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk hMB hCB hWhB p2B s2B
          (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB t α β).2,
        (cCols_shaped offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk hMB hCB hWhB p2B s2B
          (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) ζ qvB t EF.zero EF.zero).2]
  have hmk1B : ∀ k ∈ mk1B, k < 10 ∧ ∀ t α β, k < (colsB t α β).length ∧
      (colsB t α β).getD k [] = (colsB t EF.zero EF.zero).getD k [] := by
    intro k hk
    have hk'B := hk
    simp only [mk1B, List.mem_cons, List.not_mem_nil, or_false] at hk'B
    have hknB : k < 10 := by rcases hk'B with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknB, fun t α β => ⟨hknB, compCols_main offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB t α β
      EF.zero EF.zero k hk⟩⟩
  have hmk2B : ∀ k ∈ mk2B, k < 10 ∧ ∀ t α β, k < (colsB t α β).length := by
    intro k hk
    simp only [mk2B, List.mem_cons, List.not_mem_nil, or_false] at hk
    have hknB : k < 10 := by rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknB, fun _ _ _ => hknB⟩
  have hvo1B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsB c4) mk1B (main1B t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1B c4 (realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eB := pcsFri_ov2 offB (fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t) (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) ksB colsB ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) (fun t α β ms => (cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk1B hmk1B (hlen8B c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      rw [(hSdB c4 c2 c3).dataF2 colsB mk1B t (r % NR0B), (hSwB c4 c2 c3).S] at eB
      exact .inr (congrArg some eB)
  have hvo2B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsB c4) mk2B (main2B c t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2B c4 (realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eB := pcsFri_ovP offB (fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t) (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) ksB colsB ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) (fun t α β ms => (cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B hmk2B rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      rw [(hSdB c4 c2 c3).dataP2 colsB mk2B t _ _ (r % NR0B), (hSwB c4 c2 c3).S] at eB
      exact .inr (congrArg some eB)
  have hvo3B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3B c4 (main3B c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3B c4 (realVN offB tabsB tvB pbB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab'B : Aborts (prefixOf (efOf (c / Q4)) (offB (efOf (c % Q4)))) (efOf (c % Q4)) (tabsB t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (offB (efOf (c % Q4)))) (efOf (c % Q4)) (tabsB t)
        · rfl
        · exact absurd h hab
      have e0B := pcsFri_ovR2 offB (fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t) (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) ksB colsB ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) (fun t α β ms => (cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B hmk2B rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      have eB := congrArg Prod.snd e0B
      rw [(hSzB c4 c2 c3).tS, (hSzB c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdzB c4 c2 c3).shape,
        tabsCws_congr ncwB _ _ _ (hSdzB c4 c2 c3).shape, (hSdzB c4 c2 c3).cr (r % NR0B), (hSdzB c4 c2 c3).cc (r % NR0B),
        (hSdzB c4 c2 c3).ms (r % NR0B), (hS0B c4 c2).tS, (hS0B c4 c2).iS,
        comp_data_q offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) EF.zero
          qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) t _ _ _ hab'B] at eB
      exact .inr (congrArg some eB)
  have hsvo1B : ∀ c4 c2 c3 c r t, ov1B c4 (svFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (sop1B c4 c2 c3 r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (αdB c4) _ mk1B
      (fun k hk => (hmk1B k hk).1) rfl _ _ _ (r % NR0B))
  have hsvo2B : ∀ c4 c2 c3 c r t, ov2B c4 (svFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop2B c4 c2 c3 c r t) :=
    fun c4 c2 c3 c r t => congrArg some (psimFri_ov2 (qZB c4 (efOf c3)) ksB (tqZB c4 c2 (efOf c3)) ncwB (αdB c4) _ mk2B
      (fun k hk => (hmk2B k hk).1) rfl _ _ _ (r % NR0B))
  have hsvo3B : ∀ c4 c2 c3 c r t, ov3B c4 (svFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) =
      some (sop3B c4 c2 c3 c r t) := by
    intro c4 c2 c3 c r t
    have e0B := psimFri_ovR2 (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) ksB ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) ncwB (αdB c4) (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B
      (fun k hk => (hmk2B k hk).1) rfl (efOf (c / Q4)) (efOf (c % Q4)) (vSB (efOf (c / Q4)) (efOf (c % Q4)) t) (r % NR0B)
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
    have e1B : SsTB c4 = cSsT (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) := comp_SsT offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0)
    have e2B : SsCB c4 = cSsC tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) := comp_SsC offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) (wsgB 0) ncwB
    show ComPfHides NS3B Com3B (Pf3B c4) (fun d => (opQ (SsTB c4) d.1, opCw (SsCB c4) d.2))
    rw [e1B, e2B]; exact hp3B c4
  have hozB : ∀ c4 c2 c3 α β r t, ozFB (rvFB c4 c2 c3 α β r t) = ozFB (rvFB 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvFB]
    unfold realVN
    cases hAB : Aborts (prefixOf α (offB β)) β (tabsB t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozFB, Option.some.injEq, Prod.mk.injEq]
      have hdB := comp_same_d offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) rfl rfl rfl rfl rfl
      refine ⟨pcsFri_ood offB (fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t) (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) (cGroups tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) qvB) ksB colsB
        ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB rfl rfl t α β (r % NR0B), pcsFri_oodT offB (fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t) (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) (cGroups tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) qvB) ksB colsB
        ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB (by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0B)
        (comp_data_q offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2) t _ _ _ hAB),
        pcsFri_oodC offB (fun pre β t => compViewN pre β mB.hd mB.stk mB.heap.length rootsB.length mB.stk NB WB CB MmB WtB t) (cGroups tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB) (cGroups tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) qvB) ksB colsB
        ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB c4) (SCB c4) (S9B c4) (SPB c4) (SSB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) ((cTs offB mB.hd mB.stk mB.heap.length rootsB.length mB.stk mB.heap NB WB rootsB CB MmB WtB tbMB tbCB tpPB tpSB (SMB 0) (SCB 0) (S9B 0) (SPB 0) (SSB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wsgB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB rfl (by simp only [cTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0B)⟩
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

section
open B Air Compose CompM Stmt Mach Wit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Two hidden-term proofs under one oracle**, each over four Fiat–Shamir
    rounds with every commitment opened and the query points hashed
    (`wit_fs_open4` twice, `fs_open4_two`): the two proofs, of any two
    statements, read the same four tables; the simulator programs the second's
    answers and then the first's.  The error is each proof's own over the
    other's draws, and the collisions, bounded by the second proof's first
    commitment's salt spread (`hspB`, at most `δs` of the salts commit any
    data to any one value) through `spread_sum`.  The query hash maps keep
    the transcript's residue mod `n1` (`hφAB`).  Statements fixed in
    advance; two proofs. -/
theorem wit_fs_open4_two {VA WvA P1A P2A P3A : Type} (offA : EF → String → EF) {VtA xA : Term} {WA : Nat} {wsA : List Cell} (hwfA : WF wsA)
    (hwlA : wsA.length = WA) (hW8A : WA ≤ 2 ^ 8) {AA : List Cell} {kA : Nat} {rowA : Nat → Air.Row}
    (hAA : AcceptsFrom AA (wMachine wsA (VtA ⬝ xA)) kA rowA)
    (hKA : rd AA (rowA (kA - 1)).ctr (rowA (kA - 1)).hd = some .K ∧ rd AA (rowA (kA - 1)).ctr (rowA (kA - 1)).stk = some .nil)
    (hlenA : AA.length = 2 ^ 10) (hkA : kA ≤ 2 ^ 10)
    {tPA : Nat} (htpA : tPA = progTpW (wMachine (List.replicate WA .S) (VtA ⬝ xA)).heap WA)
    (S10A S9A SPA : Nat → List F) (qvA : EF → EF → List EF → F → List F → List F → List EF)
    (wmA wcA wwA wpA : Nat → List (EF → EF → List F)) {LwmA LwcA LwwA LwpA : Nat} (hlwmA : ∀ c, (wmA c).length = LwmA)
    (hlwcA : ∀ c, (wcA c).length = LwcA) (hlwwA : ∀ c, (wwA c).length = LwwA) (hlwpA : ∀ c, (wpA c).length = LwpA)
    {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4)
    (φA : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφA : ∀ m w, φA m w < N4)
    (hS10A : ∀ c4, ∀ xA ∈ S10A c4, xA ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9A : ∀ c4, ∀ xA ∈ S9A c4, xA ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPA : ∀ c4, ∀ xA ∈ SPA c4, xA ∉ cosetL 1 (bbGen (tPA + 1)) (2 ^ (tPA + 1)))
    (hsz10A : ∀ c4, 2 * (S10A c4).length + 8 ≤ 2 ^ 10) (hsz9A : ∀ c4, 2 * (S9A c4).length + 8 ≤ 2 ^ 9)
    (hszPA : ∀ c4, 2 * (SPA c4).length + 8 ≤ 2 ^ (tPA + 1)) {ncwA : Nat} (αdA : Nat → EF) {B4A : Nat}
    (hB4A : sumTo K4 (fun c4 => indB (!genB (αdA c4))) ≤ B4A) (friA : Nat → EF → EF → List (EF → EF) → VA) (hncwA : 4 ≤ ncwA)
    (NR2A : Nat) (RbA : Nat → EF → EF → Nat → List (EF → EF)) (RoA : Nat → EF → EF → Nat → WvA)
    {NS1A NS2A NS3A n1 n2 n3 : Nat}
    (Com1A : List (List (List F)) → Nat → Nat) (Pf1A : Nat → List (List (List F)) → Nat → P1A) (hc1A : ComHides NS1A Com1A)
    (hp1A : ∀ c4, ComPfHides NS1A Com1A (Pf1A c4) (opF ((wGroups tPA (S10A c4) (S9A c4) (SPA c4) EF.zero qvA).map (·.base.S)) [0, 2, 4, 6]))
    (hr1A : ∀ d σ, Com1A d σ < n1) (d1A : List (List (List F)))
    (Com2A : List (List (List F)) → Nat → Nat) (Pf2A : Nat → List (List (List F)) → Nat → P2A) (hc2A : ComHides NS2A Com2A)
    (hp2A : ∀ c4, ComPfHides NS2A Com2A (Pf2A c4) (opF ((wGroups tPA (S10A c4) (S9A c4) (SPA c4) EF.zero qvA).map (·.base.S)) [1, 3, 5, 7]))
    (hr2A : ∀ d σ, Com2A d σ < n2) (d2A : List (List (List F)))
    (Com3A : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3A : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3A) (hc3A : ComHides NS3A Com3A)
    (hp3A : ∀ c4, ComPfHides NS3A Com3A (Pf3A c4) (fun d => (opQ (wSsT (S10A c4) (S9A c4) (SPA c4)) d.1, opCw (wSsC tPA (S10A c4) (S9A c4) (SPA c4)) d.2)))
    (hr3A : ∀ d σ, Com3A d σ < n3) (d3A : List (List (List (List F))) × List (List (List F)))
    {VB WvB P1B P2B P3B : Type} (offB : EF → String → EF) {VtB xB : Term} {WB : Nat} {wsB : List Cell} (hwfB : WF wsB)
    (hwlB : wsB.length = WB) (hW8B : WB ≤ 2 ^ 8) {AB : List Cell} {kB : Nat} {rowB : Nat → Air.Row}
    (hAB : AcceptsFrom AB (wMachine wsB (VtB ⬝ xB)) kB rowB)
    (hKB : rd AB (rowB (kB - 1)).ctr (rowB (kB - 1)).hd = some .K ∧ rd AB (rowB (kB - 1)).ctr (rowB (kB - 1)).stk = some .nil)
    (hlenB : AB.length = 2 ^ 10) (hkB : kB ≤ 2 ^ 10)
    {tPB : Nat} (htpB : tPB = progTpW (wMachine (List.replicate WB .S) (VtB ⬝ xB)).heap WB)
    (S10B S9B SPB : Nat → List F) (qvB : EF → EF → List EF → F → List F → List F → List EF)
    (wmB wcB wwB wpB : Nat → List (EF → EF → List F)) {LwmB LwcB LwwB LwpB : Nat} (hlwmB : ∀ c, (wmB c).length = LwmB)
    (hlwcB : ∀ c, (wcB c).length = LwcB) (hlwwB : ∀ c, (wwB c).length = LwwB) (hlwpB : ∀ c, (wpB c).length = LwpB)
    (φB : Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) (hφB : ∀ m w, φB m w < N4)
    (hS10B : ∀ c4, ∀ xB ∈ S10B c4, xB ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9B : ∀ c4, ∀ xB ∈ S9B c4, xB ∉ cosetL 1 (bbGen 9) (2 ^ 9))
    (hSPB : ∀ c4, ∀ xB ∈ SPB c4, xB ∉ cosetL 1 (bbGen (tPB + 1)) (2 ^ (tPB + 1)))
    (hsz10B : ∀ c4, 2 * (S10B c4).length + 8 ≤ 2 ^ 10) (hsz9B : ∀ c4, 2 * (S9B c4).length + 8 ≤ 2 ^ 9)
    (hszPB : ∀ c4, 2 * (SPB c4).length + 8 ≤ 2 ^ (tPB + 1)) {ncwB : Nat} (αdB : Nat → EF) {B4B : Nat}
    (hB4B : sumTo K4 (fun c4 => indB (!genB (αdB c4))) ≤ B4B) (friB : Nat → EF → EF → List (EF → EF) → VB) (hncwB : 4 ≤ ncwB)
    (NR2B : Nat) (RbB : Nat → EF → EF → Nat → List (EF → EF)) (RoB : Nat → EF → EF → Nat → WvB)
    {NS1B NS2B NS3B : Nat}
    (Com1B : List (List (List F)) → Nat → Nat) (Pf1B : Nat → List (List (List F)) → Nat → P1B) (hc1B : ComHides NS1B Com1B)
    (hp1B : ∀ c4, ComPfHides NS1B Com1B (Pf1B c4) (opF ((wGroups tPB (S10B c4) (S9B c4) (SPB c4) EF.zero qvB).map (·.base.S)) [0, 2, 4, 6]))
    (hr1B : ∀ d σ, Com1B d σ < n1) (d1B : List (List (List F)))
    (Com2B : List (List (List F)) → Nat → Nat) (Pf2B : Nat → List (List (List F)) → Nat → P2B) (hc2B : ComHides NS2B Com2B)
    (hp2B : ∀ c4, ComPfHides NS2B Com2B (Pf2B c4) (opF ((wGroups tPB (S10B c4) (S9B c4) (SPB c4) EF.zero qvB).map (·.base.S)) [1, 3, 5, 7]))
    (hr2B : ∀ d σ, Com2B d σ < n2) (d2B : List (List (List F)))
    (Com3B : List (List (List (List F))) × List (List (List F)) → Nat → Nat)
    (Pf3B : Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3B) (hc3B : ComHides NS3B Com3B)
    (hp3B : ∀ c4, ComPfHides NS3B Com3B (Pf3B c4) (fun d => (opQ (wSsT (S10B c4) (S9B c4) (SPB c4)) d.1, opCw (wSsC tPB (S10B c4) (S9B c4) (SPB c4)) d.2)))
    (hr3B : ∀ d σ, Com3B d σ < n3) (d3B : List (List (List (List F))) × List (List (List F)))
    (hφAB : ∀ m w m' w', φB m w = φA m' w' → m % n1 = m' % n1) {δs : Nat}
    (hspB : ∀ d v, sumTo NS1B (fun σ => indB (decide (Com1B d σ = v))) ≤ δs) :
    let blankA := wMachine (List.replicate WA .S) (VtA ⬝ xA)
    let CA := cpuTableW AA rowA kA (2 ^ 10)
    let PgA := progTableW blankA.heap WA
    let WtA := witTableG 0 AA 0 WA
    let MmA := memTableC AA (cpuAirW blankA.hd blankA.stk blankA.heap.length) (progAirW blankA.heap WA) (witAirW WA) CA PgA WtA
    let NR0A := wNR offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A 0) (S9A 0) (SPA 0) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA
    let pcsZA := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA (αdA c4)
      (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) t α β (r % NR0A)
    let psimZA := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA (αdA c4)
      (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) α β v (r % NR0A)
    let NRA := NR0A * NR2A
    let tabsA := fun t : Nat → Tup => witTables blankA.hd blankA.stk blankA.heap.length blankA.heap WA
      ((CA.setBlind BLA (t 1)).setBlind BLB (t 0)) (MmA.setBlind 5 (t 0)) (progTableW blankA.heap WA)
      (WtA.setBlind WT_BLIND (t 1))
    let tvA := fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t
    let ptmA := fun pre β => terminal pre β (progAirW blankA.heap WA) (progTableW blankA.heap WA)
    let MA := (allEntries (witTables blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA (progTableW blankA.heap WA)
      WtA)).length
    let q0A := wGroups tPA (S10A 0) (S9A 0) (SPA 0) EF.zero qvA
    let qZA := fun (c4 : Nat) (ζ : EF) => wGroups tPA (S10A c4) (S9A c4) (SPA c4) ζ qvA
    let SsA := fun c4 => (qZA c4 EF.zero).map (·.base.S)
    let ksA := wKs blankA.hd blankA.stk blankA.heap.length blankA.heap WA
    let colsA := wCols offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA
    let tqZA := fun (c4 c2 : Nat) (ζ : EF) => (wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst
    let qdZA := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) ζ qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map (fun p => p.2 t α β ms)
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
      chainPar 3 (xrefN (ptmA (prefixOf α (offA β)) β)) t
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
    let ov1A : Nat → TViewN (PcsPV (VA × WvA)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsA c4) mk1A pv)
      | none => none
    let ov2A : Nat → TViewN (PcsPV (VA × WvA)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsA c4) mk2A pv)
      | none => none
    let ov3A : Nat → TViewN (PcsPV (VA × WvA)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvFA := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) α β r t
    let svFA := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN offA ptmA chainBus (fun _ => false) chainPar 3 ptmA (psimZA c4 c2 (efOf c3)) α β r t
    let ozFA : TViewN (PcsPV (VA × WvA)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3A := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsTA c4) d.1, opCw (SsCA c4) d.2)
    let sd3A := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsTA c4) o.1, sdCw (SsCA c4) o.2)
    let blankB := wMachine (List.replicate WB .S) (VtB ⬝ xB)
    let CB := cpuTableW AB rowB kB (2 ^ 10)
    let PgB := progTableW blankB.heap WB
    let WtB := witTableG 0 AB 0 WB
    let MmB := memTableC AB (cpuAirW blankB.hd blankB.stk blankB.heap.length) (progAirW blankB.heap WB) (witAirW WB) CB PgB WtB
    let NR0B := wNR offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B 0) (S9B 0) (SPB 0) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB
    let pcsZB := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB (αdB c4)
      (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) t α β (r % NR0B)
    let psimZB := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB (αdB c4)
      (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) α β v (r % NR0B)
    let NRB := NR0B * NR2B
    let tabsB := fun t : Nat → Tup => witTables blankB.hd blankB.stk blankB.heap.length blankB.heap WB
      ((CB.setBlind BLA (t 1)).setBlind BLB (t 0)) (MmB.setBlind 5 (t 0)) (progTableW blankB.heap WB)
      (WtB.setBlind WT_BLIND (t 1))
    let tvB := fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t
    let ptmB := fun pre β => terminal pre β (progAirW blankB.heap WB) (progTableW blankB.heap WB)
    let MB := (allEntries (witTables blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB (progTableW blankB.heap WB)
      WtB)).length
    let q0B := wGroups tPB (S10B 0) (S9B 0) (SPB 0) EF.zero qvB
    let qZB := fun (c4 : Nat) (ζ : EF) => wGroups tPB (S10B c4) (S9B c4) (SPB c4) ζ qvB
    let SsB := fun c4 => (qZB c4 EF.zero).map (·.base.S)
    let ksB := wKs blankB.hd blankB.stk blankB.heap.length blankB.heap WB
    let colsB := wCols offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB
    let tqZB := fun (c4 c2 : Nat) (ζ : EF) => (wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst
    let qdZB := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) ζ qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map (fun p => p.2 t α β ms)
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
      chainPar 3 (xrefN (ptmB (prefixOf α (offB β)) β)) t
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
    let ov1B : Nat → TViewN (PcsPV (VB × WvB)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsB c4) mk1B pv)
      | none => none
    let ov2B : Nat → TViewN (PcsPV (VB × WvB)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (SsB c4) mk2B pv)
      | none => none
    let ov3B : Nat → TViewN (PcsPV (VB × WvB)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvFB := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) α β r t
    let svFB := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN offB ptmB chainBus (fun _ => false) chainPar 3 ptmB (psimZB c4 c2 (efOf c3)) α β r t
    let ozFB : TViewN (PcsPV (VB × WvB)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
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
    ∀ E : Nat × Nat × Nat × Nat → Nat × Nat × Nat × (Option P1A × Option (P2A × P3A) × TViewN (PcsPV (VA × WvA)) EF) → Nat × Nat × Nat × (Option P1B × Option (P2B × P3B) × TViewN (PcsPV (VB × WvB)) EF) → Bool,
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
  intro blankA CA PgA WtA MmA NR0A pcsZA psimZA NRA tabsA tvA ptmA MA q0A qZA SsA ksA colsA tqZA qdZA SsTA SsCA mk1A mk2A main1A main2A main3A vSA sop1A sop2A sop3A ov1A ov2A ov3A rvFA svFA ozFA op3A sd3A blankB CB PgB WtB MmB NR0B pcsZB psimZB NRB tabsB tvB ptmB MB q0B qZB SsB ksB colsB tqZB qdZB SsTB SsCB mk1B mk2B main1B main2B main3B vSB sop1B sop2B sop3B ov1B ov2B ov3B rvFB svFB ozFB op3B sd3B smA m1A m2A m3A rvoA s1A s2A s3A svoA sm4A r1A r2A r3A MqA smB m1B m2B m3B rvoB s1B s2B s3B svoB sm4B r1B r2B r3B MqB ST SC rvTA pgTA svTA rvTB pgTB svTB colT okT E
  obtain ⟨hbalA, hunA⟩ := wit_honest_zk hwfA hwlA hW8A hAA hlenA hkA
  obtain ⟨scA, smsA, swA, hWhA⟩ := wit_run_sats hwfA hwlA hW8A hAA hKA hlenA hkA
  obtain ⟨_, hP23A, hPgA⟩ := wit_prog_height hwlA hAA hlenA
  rw [← htpA] at hP23A hPgA
  have hSwA := fun (c4 c2 c3 : Nat) => wit_same_w offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA])
  have hSzA := fun (c4 c2 c3 : Nat) => wit_same_w offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA rfl rfl rfl rfl
  have hS0A := fun (c4 c2 : Nat) => wit_same_w offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) EF.zero EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA])
  have hSdA := fun (c4 c2 c3 : Nat) => wit_same_d offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (S10A 0) (S9A 0) (SPA 0) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA 0) (wcA 0) (wwA 0) (wpA 0) (by rw [hlwmA, hlwmA]) (by rw [hlwcA, hlwcA]) (by rw [hlwwA, hlwwA]) (by rw [hlwpA, hlwpA])
  have hSdzA := fun (c4 c2 c3 : Nat) => wit_same_d offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (S10A 0) (S9A 0) (SPA 0) (efOf c3) EF.zero qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) rfl rfl rfl rfl
  have hbA : ∀ c4 c2 c3, genB (αdA c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (VA × WvA)) EF → Bool,
        tsumN NRA 2 (fun α β r t => indB (genB β && E' (rvFA c4 c2 c3 α β r t))) ≤
          tsumN NRA 2 (fun α β r t => indB (genB β && E' (svFA c4 c2 c3 α β r t))) + Q4 * (NRA * (Q4 ^ 2 * MA)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (VA × WvA)) EF → Bool,
        tsumN NRA 2 (fun α β r t => indB (genB β && E' (svFA c4 c2 c3 α β r t))) ≤
          tsumN NRA 2 (fun α β r t => indB (genB β && E' (rvFA c4 c2 c3 α β r t))) + Q4 * (NRA * (Q4 ^ 2 * MA)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgzA := (genB_iff _).1 hg
    have hgαA := (genB_iff _).1 hg4
    have hpcsA := wit_pcsX (heap := blankA.heap) (ζ := efOf c3) offA scA smsA swA (rfl : CA.h = 2 ^ 10) hlenA hWhA (by omega) hPgA qvA
      (wmA c2) (wcA c2) (wwA c2) (wpA c2) (hS10A c4) (hS9A c4) (hSPA c4) (hsz10A c4) (hsz9A c4) (hszPA c4) (generic_ofF_ne hgzA) (mz_generic hgzA) (friA c4) (mz_generic hgαA) (generic_apow_ne hgαA) hncwA NR2A (RbA c4) (RoA c4)
    have hNRA : wNR offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) ncwA = wNR offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A 0) (S9A 0) (SPA 0) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA := by
      unfold wNR; rw [(hSdA c4 c2 c3).n1, (hSdA c4 c2 c3).n2]
    rw [hNRA] at hpcsA
    exact ⟨fun E' => (wit_transcriptG offA NRA 0 (pcsZA c4 c2 (efOf c3)) (psimZA c4 c2 (efOf c3)) hbalA hunA hpcsA E').1,
      fun E' => (wit_transcriptG offA NRA 0 (pcsZA c4 c2 (efOf c3)) (psimZA c4 c2 (efOf c3)) hbalA hunA hpcsA E').2⟩
  have hlen8A : ∀ (c4 : Nat) (ζ : EF) t α β, (colsA t α β).map List.length = (colsA t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(wCols_shaped offA blankA.hd blankA.stk blankA.heap.length (rfl : CA.h = 2 ^ 10) hlenA hWhA hPgA
          (S10A c4) (S9A c4) (SPA c4) ζ qvA t α β).2,
        (wCols_shaped offA blankA.hd blankA.stk blankA.heap.length (rfl : CA.h = 2 ^ 10) hlenA hWhA hPgA
          (S10A c4) (S9A c4) (SPA c4) ζ qvA t EF.zero EF.zero).2]
  have hmk1A : ∀ kA ∈ mk1A, kA < 8 ∧ ∀ t α β, kA < (colsA t α β).length ∧
      (colsA t α β).getD kA [] = (colsA t EF.zero EF.zero).getD kA [] := by
    intro kA hkA
    have hk'A := hkA
    simp only [mk1A, List.mem_cons, List.not_mem_nil, or_false] at hk'A
    have hknA : kA < 8 := by rcases hk'A with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknA, fun t α β => ⟨hknA, witCols_main offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA t α β
      EF.zero EF.zero kA hkA⟩⟩
  have hmk2A : ∀ kA ∈ mk2A, kA < 8 ∧ ∀ t α β, kA < (colsA t α β).length := by
    intro kA hkA
    simp only [mk2A, List.mem_cons, List.not_mem_nil, or_false] at hkA
    have hknA : kA < 8 := by rcases hkA with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknA, fun _ _ _ => hknA⟩
  have hvo1A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsA c4) mk1A (main1A t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1A c4 (realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eA := pcsFri_ov2 offA (fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t) (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) ksA colsA ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) (fun t α β ms => (wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk1A hmk1A (hlen8A c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      rw [(hSdA c4 c2 c3).dataF2 colsA mk1A t (r % NR0A), (hSwA c4 c2 c3).S] at eA
      exact .inr (congrArg some eA)
  have hvo2A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsA c4) mk2A (main2A c t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2A c4 (realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eA := pcsFri_ovP offA (fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t) (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) ksA colsA ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) (fun t α β ms => (wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A hmk2A rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      rw [(hSdA c4 c2 c3).dataP2 colsA mk2A t _ _ (r % NR0A), (hSwA c4 c2 c3).S] at eA
      exact .inr (congrArg some eA)
  have hvo3A : ∀ c4 c2 c3 c r t, rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3A c4 (rvFA c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3A c4 (main3A c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3A c4 (realVN offA tabsA tvA ptmA (pcsZA c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab'A : Aborts (prefixOf (efOf (c / Q4)) (offA (efOf (c % Q4)))) (efOf (c % Q4)) (tabsA t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (offA (efOf (c % Q4)))) (efOf (c % Q4)) (tabsA t)
        · rfl
        · exact absurd h hab
      have e0A := pcsFri_ovR2 offA (fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t) (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) ksA colsA ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) (fun t α β ms => (wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map fun p => p.2 t α β ms) ncwA (αdA c4)
        (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A hmk2A rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0A)
      have eA := congrArg Prod.snd e0A
      rw [(hSzA c4 c2 c3).tS, (hSzA c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdzA c4 c2 c3).shape,
        tabsCws_congr ncwA _ _ _ (hSdzA c4 c2 c3).shape, (hSdzA c4 c2 c3).cr (r % NR0A), (hSdzA c4 c2 c3).cc (r % NR0A),
        (hSdzA c4 c2 c3).ms (r % NR0A), (hS0A c4 c2).tS, (hS0A c4 c2).iS,
        wit_data_q offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (S10A 0) (S9A 0) (SPA 0) (efOf c3) EF.zero
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
    have e0A := psimFri_ovR2 (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) ksA ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ncwA (αdA c4) (friX (friA c4) (RbA c4) (RoA c4) (r / NR0A)) mk2A
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
    have e1A : SsTA c4 = wSsT (S10A c4) (S9A c4) (SPA c4) := wit_SsT offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0)
    have e2A : SsCA c4 = wSsC tPA (S10A c4) (S9A c4) (SPA c4) := wit_SsC offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) EF.zero qvA (wmA 0) (wcA 0) (wwA 0) (wpA 0) ncwA
    show ComPfHides NS3A Com3A (Pf3A c4) (fun d => (opQ (SsTA c4) d.1, opCw (SsCA c4) d.2))
    rw [e1A, e2A]; exact hp3A c4
  have hozA : ∀ c4 c2 c3 α β r t, ozFA (rvFA c4 c2 c3 α β r t) = ozFA (rvFA 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvFA]
    unfold realVN
    cases hAA : Aborts (prefixOf α (offA β)) β (tabsA t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozFA, Option.some.injEq, Prod.mk.injEq]
      have hdA := wit_same_d offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (S10A 0) (S9A 0) (SPA 0) (efOf c3) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) (wmA c2) (wcA c2) (wwA c2) (wpA c2) rfl rfl rfl rfl
      refine ⟨pcsFri_ood offA (fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t) (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) (wGroups tPA (S10A 0) (S9A 0) (SPA 0) (efOf c3) qvA) ksA colsA
        ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A 0) (S9A 0) (SPA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA rfl rfl t α β (r % NR0A), pcsFri_oodT offA (fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t) (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) (wGroups tPA (S10A 0) (S9A 0) (SPA 0) (efOf c3) qvA) ksA colsA
        ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A 0) (S9A 0) (SPA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA (by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0A)
        (wit_data_q offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (S10A 0) (S9A 0) (SPA 0) (efOf c3) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2) t _ _ _ hAA),
        pcsFri_oodC offA (fun pre β t => witViewN pre β blankA.hd blankA.stk blankA.heap.length WA CA MmA WtA t) (wGroups tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA) (wGroups tPA (S10A 0) (S9A 0) (SPA 0) (efOf c3) qvA) ksA colsA
        ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A c4) (S9A c4) (SPA c4) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) ((wTs offA blankA.hd blankA.stk blankA.heap.length blankA.heap WA CA MmA WtA tPA (S10A 0) (S9A 0) (SPA 0) (efOf c3) qvA (wmA c2) (wcA c2) (wwA c2) (wpA c2)).map Prod.fst) _ _ ncwA (αdA c4) (αdA 0) _ _
        hdA rfl (by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0A)⟩
    · rfl
  have hgzA : sumTo K2 (fun _ => sumTo Q4 (fun c3 => indB (!genB (efOf c3)))) ≤ K2 * (P * P) := by
    rw [genB_count, sumTo_const]; exact Nat.le_refl _
  obtain ⟨hbalB, hunB⟩ := wit_honest_zk hwfB hwlB hW8B hAB hlenB hkB
  obtain ⟨scB, smsB, swB, hWhB⟩ := wit_run_sats hwfB hwlB hW8B hAB hKB hlenB hkB
  obtain ⟨_, hP23B, hPgB⟩ := wit_prog_height hwlB hAB hlenB
  rw [← htpB] at hP23B hPgB
  have hSwB := fun (c4 c2 c3 : Nat) => wit_same_w offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB])
  have hSzB := fun (c4 c2 c3 : Nat) => wit_same_w offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB rfl rfl rfl rfl
  have hS0B := fun (c4 c2 : Nat) => wit_same_w offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) EF.zero EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB])
  have hSdB := fun (c4 c2 c3 : Nat) => wit_same_d offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (S10B 0) (S9B 0) (SPB 0) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB 0) (wcB 0) (wwB 0) (wpB 0) (by rw [hlwmB, hlwmB]) (by rw [hlwcB, hlwcB]) (by rw [hlwwB, hlwwB]) (by rw [hlwpB, hlwpB])
  have hSdzB := fun (c4 c2 c3 : Nat) => wit_same_d offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (S10B 0) (S9B 0) (SPB 0) (efOf c3) EF.zero qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) rfl rfl rfl rfl
  have hbB : ∀ c4 c2 c3, genB (αdB c4) = true → genB (efOf c3) = true →
      (∀ E' : TViewN (PcsPV (VB × WvB)) EF → Bool,
        tsumN NRB 2 (fun α β r t => indB (genB β && E' (rvFB c4 c2 c3 α β r t))) ≤
          tsumN NRB 2 (fun α β r t => indB (genB β && E' (svFB c4 c2 c3 α β r t))) + Q4 * (NRB * (Q4 ^ 2 * MB)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) ∧
      (∀ E' : TViewN (PcsPV (VB × WvB)) EF → Bool,
        tsumN NRB 2 (fun α β r t => indB (genB β && E' (svFB c4 c2 c3 α β r t))) ≤
          tsumN NRB 2 (fun α β r t => indB (genB β && E' (rvFB c4 c2 c3 α β r t))) + Q4 * (NRB * (Q4 ^ 2 * MB)) +
            Q4 * (Q4 * (Q4 ^ 2 * 0))) := fun c4 c2 c3 hg4 hg => by
    have hgzB := (genB_iff _).1 hg
    have hgαB := (genB_iff _).1 hg4
    have hpcsB := wit_pcsX (heap := blankB.heap) (ζ := efOf c3) offB scB smsB swB (rfl : CB.h = 2 ^ 10) hlenB hWhB (by omega) hPgB qvB
      (wmB c2) (wcB c2) (wwB c2) (wpB c2) (hS10B c4) (hS9B c4) (hSPB c4) (hsz10B c4) (hsz9B c4) (hszPB c4) (generic_ofF_ne hgzB) (mz_generic hgzB) (friB c4) (mz_generic hgαB) (generic_apow_ne hgαB) hncwB NR2B (RbB c4) (RoB c4)
    have hNRB : wNR offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) ncwB = wNR offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B 0) (S9B 0) (SPB 0) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB := by
      unfold wNR; rw [(hSdB c4 c2 c3).n1, (hSdB c4 c2 c3).n2]
    rw [hNRB] at hpcsB
    exact ⟨fun E' => (wit_transcriptG offB NRB 0 (pcsZB c4 c2 (efOf c3)) (psimZB c4 c2 (efOf c3)) hbalB hunB hpcsB E').1,
      fun E' => (wit_transcriptG offB NRB 0 (pcsZB c4 c2 (efOf c3)) (psimZB c4 c2 (efOf c3)) hbalB hunB hpcsB E').2⟩
  have hlen8B : ∀ (c4 : Nat) (ζ : EF) t α β, (colsB t α β).map List.length = (colsB t EF.zero EF.zero).map List.length :=
    fun c4 ζ t α β => by
      rw [(wCols_shaped offB blankB.hd blankB.stk blankB.heap.length (rfl : CB.h = 2 ^ 10) hlenB hWhB hPgB
          (S10B c4) (S9B c4) (SPB c4) ζ qvB t α β).2,
        (wCols_shaped offB blankB.hd blankB.stk blankB.heap.length (rfl : CB.h = 2 ^ 10) hlenB hWhB hPgB
          (S10B c4) (S9B c4) (SPB c4) ζ qvB t EF.zero EF.zero).2]
  have hmk1B : ∀ kB ∈ mk1B, kB < 8 ∧ ∀ t α β, kB < (colsB t α β).length ∧
      (colsB t α β).getD kB [] = (colsB t EF.zero EF.zero).getD kB [] := by
    intro kB hkB
    have hk'B := hkB
    simp only [mk1B, List.mem_cons, List.not_mem_nil, or_false] at hk'B
    have hknB : kB < 8 := by rcases hk'B with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknB, fun t α β => ⟨hknB, witCols_main offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB t α β
      EF.zero EF.zero kB hkB⟩⟩
  have hmk2B : ∀ kB ∈ mk2B, kB < 8 ∧ ∀ t α β, kB < (colsB t α β).length := by
    intro kB hkB
    simp only [mk2B, List.mem_cons, List.not_mem_nil, or_false] at hkB
    have hknB : kB < 8 := by rcases hkB with rfl | rfl | rfl | rfl <;> decide
    exact ⟨hknB, fun _ _ _ => hknB⟩
  have hvo1B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov1B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsB c4) mk1B (main1B t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov1B c4 (realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eB := pcsFri_ov2 offB (fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t) (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) ksB colsB ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) (fun t α β ms => (wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk1B hmk1B (hlen8B c4 (efOf c3)) rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      rw [(hSdB c4 c2 c3).dataF2 colsB mk1B t (r % NR0B), (hSwB c4 c2 c3).S] at eB
      exact .inr (congrArg some eB)
  have hvo2B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov2B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (opF (SsB c4) mk2B (main2B c t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov2B c4 (realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · have eB := pcsFri_ovP offB (fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t) (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) ksB colsB ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) (fun t α β ms => (wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B hmk2B rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      rw [(hSdB c4 c2 c3).dataP2 colsB mk2B t _ _ (r % NR0B), (hSwB c4 c2 c3).S] at eB
      exact .inr (congrArg some eB)
  have hvo3B : ∀ c4 c2 c3 c r t, rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t = none ∨
      ov3B c4 (rvFB c4 c2 c3 (efOf (c / Q4)) (efOf (c % Q4)) r t) = some (op3B c4 (main3B c c2 t r)) := by
    intro c4 c2 c3 c r t
    show realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) _ _ r t = none ∨
      ov3B c4 (realVN offB tabsB tvB ptmB (pcsZB c4 c2 (efOf c3)) _ _ r t) = _
    unfold realVN
    split
    · exact .inl rfl
    · rename_i hab
      have hab'B : Aborts (prefixOf (efOf (c / Q4)) (offB (efOf (c % Q4)))) (efOf (c % Q4)) (tabsB t) = false := by
        cases h : Aborts (prefixOf (efOf (c / Q4)) (offB (efOf (c % Q4)))) (efOf (c % Q4)) (tabsB t)
        · rfl
        · exact absurd h hab
      have e0B := pcsFri_ovR2 offB (fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t) (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) ksB colsB ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) (fun t α β ms => (wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map fun p => p.2 t α β ms) ncwB (αdB c4)
        (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B hmk2B rfl t (efOf (c / Q4)) (efOf (c % Q4)) (r % NR0B)
      have eB := congrArg Prod.snd e0B
      rw [(hSzB c4 c2 c3).tS, (hSzB c4 c2 c3).iS, tabsPolys_congr _ _ _ _ (hSdzB c4 c2 c3).shape,
        tabsCws_congr ncwB _ _ _ (hSdzB c4 c2 c3).shape, (hSdzB c4 c2 c3).cr (r % NR0B), (hSdzB c4 c2 c3).cc (r % NR0B),
        (hSdzB c4 c2 c3).ms (r % NR0B), (hS0B c4 c2).tS, (hS0B c4 c2).iS,
        wit_data_q offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (S10B 0) (S9B 0) (SPB 0) (efOf c3) EF.zero
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
    have e0B := psimFri_ovR2 (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) ksB ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ncwB (αdB c4) (friX (friB c4) (RbB c4) (RoB c4) (r / NR0B)) mk2B
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
    have e1B : SsTB c4 = wSsT (S10B c4) (S9B c4) (SPB c4) := wit_SsT offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0)
    have e2B : SsCB c4 = wSsC tPB (S10B c4) (S9B c4) (SPB c4) := wit_SsC offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) EF.zero qvB (wmB 0) (wcB 0) (wwB 0) (wpB 0) ncwB
    show ComPfHides NS3B Com3B (Pf3B c4) (fun d => (opQ (SsTB c4) d.1, opCw (SsCB c4) d.2))
    rw [e1B, e2B]; exact hp3B c4
  have hozB : ∀ c4 c2 c3 α β r t, ozFB (rvFB c4 c2 c3 α β r t) = ozFB (rvFB 0 c2 c3 α β r t) := by
    intro c4 c2 c3 α β r t
    simp only [rvFB]
    unfold realVN
    cases hAB : Aborts (prefixOf α (offB β)) β (tabsB t)
    · simp only [Bool.false_eq_true, ↓reduceIte, ozFB, Option.some.injEq, Prod.mk.injEq]
      have hdB := wit_same_d offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (S10B 0) (S9B 0) (SPB 0) (efOf c3) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) (wmB c2) (wcB c2) (wwB c2) (wpB c2) rfl rfl rfl rfl
      refine ⟨pcsFri_ood offB (fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t) (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) (wGroups tPB (S10B 0) (S9B 0) (SPB 0) (efOf c3) qvB) ksB colsB
        ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B 0) (S9B 0) (SPB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB rfl rfl t α β (r % NR0B), pcsFri_oodT offB (fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t) (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) (wGroups tPB (S10B 0) (S9B 0) (SPB 0) (efOf c3) qvB) ksB colsB
        ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B 0) (S9B 0) (SPB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB (by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0B)
        (wit_data_q offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (S10B 0) (S9B 0) (SPB 0) (efOf c3) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2) t _ _ _ hAB),
        pcsFri_oodC offB (fun pre β t => witViewN pre β blankB.hd blankB.stk blankB.heap.length WB CB MmB WtB t) (wGroups tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB) (wGroups tPB (S10B 0) (S9B 0) (SPB 0) (efOf c3) qvB) ksB colsB
        ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B c4) (S9B c4) (SPB c4) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) ((wTs offB blankB.hd blankB.stk blankB.heap.length blankB.heap WB CB MmB WtB tPB (S10B 0) (S9B 0) (SPB 0) (efOf c3) qvB (wmB c2) (wcB c2) (wwB c2) (wpB c2)).map Prod.fst) _ _ ncwB (αdB c4) (αdB 0) _ _
        hdB rfl (by simp only [wTs, bbTab, airQTabG, List.map_cons, List.map_nil]) t α β (r % NR0B)⟩
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
