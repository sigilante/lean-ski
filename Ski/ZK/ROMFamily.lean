import Ski.ZK.ROMMulti
import Ski.ZK.FSQueryAbs

/-!
# `n` statements of each circuit, each first commitment drawn from the oracle

`Ski/ZK/FSQueryAbs.lean` bounds `n` statements of each circuit under one
oracle, each first commitment a primitive that hides.  Here each is the
answer of its own table (`comR`), its opening `pfR` at the drawn query
challenge.  The family bound holds at the ideal openings (`comI_hides`,
`pfI_hides`, `comI_spread`), and `powD_transfer` moves every statement's
real view to its ideal one, newest first, each statement's transfer from
`rom4_step` over the instance's own definitions (`*Rv`, `*Oz`, `*Op1`,
`*Ov1`–`*Ov3`, `*Main2`, `*Main3`); `zkb_rom` composes the two
(`sud_fs_open4_powDROM`, `wit_fs_open4_powDROM`, `comp_fs_open4_powDROM`).
Each statement adds `s k / NSh` a draw over the others; one direction; each
statement's commitment table its own, apart from the Fiat–Shamir tables.
-/

set_option autoImplicit false

namespace Circuit
open ZKF
section
open B Air Stmt Mach Sudoku SudokuText Compose CompM Wit

set_option maxRecDepth 100000 in
def sudOp1 (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  fun (c4 : Nat) => opF (Ss c4) mk1

set_option maxRecDepth 100000 in
def sudRv (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  rvF

set_option maxRecDepth 100000 in
def sudOz (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ozF

set_option maxRecDepth 100000 in
def sudOv1 (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov1

set_option maxRecDepth 100000 in
def sudOv2 (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov2

set_option maxRecDepth 100000 in
def sudOv3 (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov3

set_option maxRecDepth 100000 in
def sudMain2 (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  main2

set_option maxRecDepth 100000 in
def sudMain3 (V : Type) (Wv : Type) (off : EF → String → EF) (puzzle : List Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S16 : Nat → List F) (S10 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    let NR0 := sudNR off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 0) (S10 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => sudPcs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => sudPsim off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => sudTables blank.hd blank.stk blank.heap.length blank.heap
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableS blank.heap) (Wt.setBlind 1 (t 1))
    let tv := fun pre β t => sudViewN pre β blank.hd blank.stk blank.heap.length C Mm Wt t
    let tp := fun pre β => terminal pre β (progAirS blank.heap) (progTableS blank.heap)
    let M := (allEntries (sudTables blank.hd blank.stk blank.heap.length blank.heap C Mm (progTableS blank.heap) Wt)).length
    let q0 := sudGroups tP (S16 0) (S10 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => sudGroups tP (S16 c4) (S10 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := sudKs blank.hd blank.stk blank.heap.length blank.heap
    let cols := sudCols off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (sudTs off blank.hd blank.stk blank.heap.length blank.heap C Mm Wt tP (S16 c4) (S10 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (tp (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (SudPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv tp (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off tp chainBus (fun _ => false) chainPar 3 tp (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (SudPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  main3
set_option maxRecDepth 100000 in
set_option autoImplicit false in
/-- **`n` Sudoku statements, each first commitment drawn from the oracle**
    (`sud_fs_open4_powD` at the ideal openings, `powD_transfer` with
    `rom4_step` for each statement, `zkb_rom`): `n1^n` times the real count
    (with the family bound's factor) is at most that bound plus each
    statement's `s k / NSh` a draw over the others (`errTD`); one direction.
    As there: the query hashes keep the first commitment's digit (`hφs`),
    and `n` statements extend to every index by repeating the last.  `n1`
    is both the commitment's range and its table's answer range, the
    spread discharged as `NSh NSo n1^nQ` (a `1/n1` collision term); each
    statement's commitment table its own. -/
theorem sud_fs_open4_powDROM {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {puzzle : ∀ ix : Nat, List Nat} (hc : ∀ ix : Nat, CluesOK (cluesOf (puzzle ix))) {ρ : ∀ ix : Nat, Nat → Bool} {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (stmtMachine (ρ ix) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ) (k ix) (row ix)) (hacc : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some (.atom ACC)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 16) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 16) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTp (stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf (puzzle ix))) ACC REJ).heap) (S16 S10 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS16 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S16 ix) c4, x ∉ cosetL 1 (bbGen 16) (2 ^ 16)) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz16 : ∀ ix : Nat, ∀ c4, 2 * ((S16 ix) c4).length + 8 ≤ 2 ^ 16) (hsz : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NSh NSo sQ kQ nQ NS2 NS3 : ∀ ix : Nat, Nat} (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4) (opF ((sudGroups (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4) (fun d => (opQ (sudSsT ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.1, opCw (sudSsC (tP ix) ((S16 ix) c4) ((S10 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (hKQ : 0 < n1)
    (pos : ∀ ix : Nat, List (List (List F)) → Nat → Nat → Nat) (hpos : ∀ ix d σo σh, pos ix d σo σh < nQ ix)
    (g : ∀ ix : Nat, List (List (List F)) → Nat → Pq)
    (hs : ∀ ix d σo v, sumTo (NSh ix) (fun σh => indB (decide (pos ix d σo σh = v))) ≤ sQ ix)
    (nxt : ∀ ix : Nat, Pq → Nat → List Nat → Nat) :
    ∀ n (E : Nat × Nat × Nat × Nat → PowD (fun _ => Nat × Nat × Nat × (Option (Pq × List Nat) × Option (P2 × P3) × TViewN (SudPV (V × Wv)) EF)) n → Bool),
    KPowD (fun _ => n1) n * KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n
      (fun xs => indB (E H (rvPowD (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out) n H xs)))) ≤
    (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n (fun c =>
      smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n (fun xq =>
        indB (E (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).pts c xx) c) n H c xq) (svPowD (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sv) n c xq))))) +
    (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).ε)
      (fun j => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle j) (A j) (k j) (row j) (tP j) (S16 j) (S10 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NSh j * (NSo j * n1 ^ nQ j) * n1) (NS2 j) (NS3 j) n1 n2 n3 (comI n1 (NSh j) (NSo j) (pos j)) (fun c4 => pfI n1 (NSh j) (NSo j) (kQ j) (pos j) ((sudOp1 V Wv off (puzzle j) (A j) (k j) (row j) (tP j) (S16 j) (S10 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) (ncw j) (αd j) (fri j) (NR2 j) (Rb j) (Ro j)) c4) (g j) (nxt j)) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j)).sm 2 (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ =>
        hitBD (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * (NSh ix * (NSo ix * n1 ^ nQ ix))))) j)))) n +
     KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n * errTD (fun _ => n1) (fun ix => n1 * (NSo ix * (n1 ^ nQ ix * (sQ ix * kQ ix))) * ((NS2 ix * NS3 ix) * ((@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * 1)))) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n) := by
  intro n E
  exact zkb_rom (sud_fs_open4_powD (NS1 := fun ix => (NSh ix * (NSo ix * n1 ^ nQ ix) * n1)) off hc hA hacc hlen hk htp S16 S10 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS16 hS10 hSP hsz16 hsz hszP αd hB4 fri hncw NR2 Rb Ro (fun ix => comI n1 (NSh ix) (NSo ix) (pos ix)) (fun ix c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (fun ix => comI_hides hKQ (pos ix) (hpos ix)) (fun ix c4 => pfI_hides hKQ (pos ix) (hpos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (fun ix _ _ => Nat.mod_lt _ hKQ) d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3 hφs (fun ix => NSh ix * (NSo ix * n1 ^ nQ ix)) (fun ix d v => comI_spread hKQ (pos ix) (hpos ix) d v) n)
    (powD_transfer (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (lin_sum4 _ _ _ _) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2)
      (fun ix => lin_sm _ _ _ _) (fun ix => lin_sm _ _ _ _) (fun ix => comm_sm (lin_sum4 _ _ _ _) _ _ _ _)
      (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _) (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _)
      (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out)
      (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out)
      (fun ix H G => rom4_step (NR := (@sudFS4 V Wv (Pq × List Nat) P2 P3 off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR) (m := 2) (NSh := NSh ix) (NSo := NSo ix) (s := sQ ix) (k := kQ ix) (n := nQ ix)
        (NS2 := NS2 ix) (NS3 := NS3 ix) (K2 := K2) (K3 := Q4) (K4 := K4) (n2 := n2) hKQ (φ ix) (sudRv V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (sudOz V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (pos ix) (hpos ix) (g ix) (hs ix) (nxt ix)
        (sudOp1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (sudOv1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (sudMain1 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (Com2 ix) (Pf2 ix) (sudOv2 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (sudMain2 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (Com3 ix) (Pf3 ix) (sudOv3 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (sudMain3 V Wv off (puzzle ix) (A ix) (k ix) (row ix) (tP ix) (S16 ix) (S10 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) H G) n) E
set_option maxRecDepth 100000 in
def witOp1 (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  fun (c4 : Nat) => opF (Ss c4) mk1

set_option maxRecDepth 100000 in
def witRv (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  rvF

set_option maxRecDepth 100000 in
def witOz (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ozF

set_option maxRecDepth 100000 in
def witOv1 (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov1

set_option maxRecDepth 100000 in
def witOv2 (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov2

set_option maxRecDepth 100000 in
def witOv3 (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov3

set_option maxRecDepth 100000 in
def witMain2 (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  main2

set_option maxRecDepth 100000 in
def witMain3 (V : Type) (Wv : Type) (off : EF → String → EF) (Vt : Term) (x : Term) (W : Nat) (A : List Cell) (k : Nat) (row : Nat → Air.Row) (tP : Nat) (S10 : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let blank := wMachine (List.replicate W .S) (Vt ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    let NR0 := wNR off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 0) (S9 0) (SP 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => wPcs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => wPsim off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
    let NR := NR0 * NR2
    let tabs := fun t : Nat → Tup => witTables blank.hd blank.stk blank.heap.length blank.heap W
      ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) (progTableW blank.heap W)
      (Wt.setBlind WT_BLIND (t 1))
    let tv := fun pre β t => witViewN pre β blank.hd blank.stk blank.heap.length W C Mm Wt t
    let ptm := fun pre β => terminal pre β (progAirW blank.heap W) (progTableW blank.heap W)
    let M := (allEntries (witTables blank.hd blank.stk blank.heap.length blank.heap W C Mm (progTableW blank.heap W)
      Wt)).length
    let q0 := wGroups tP (S10 0) (S9 0) (SP 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => wGroups tP (S10 c4) (S9 c4) (SP c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := wKs blank.hd blank.stk blank.heap.length blank.heap W
    let cols := wCols off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (wTs off blank.hd blank.stk blank.heap.length blank.heap W C Mm Wt tP (S10 c4) (S9 c4) (SP c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6]
    let mk2 := [1, 3, 5, 7]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) EF → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 8 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv ptm (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off ptm chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) EF → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  main3
set_option maxRecDepth 100000 in
set_option autoImplicit false in
/-- **`n` hidden-term statements, each first commitment drawn from the oracle**
    (`wit_fs_open4_powD` at the ideal openings, `powD_transfer` with
    `rom4_step` for each statement, `zkb_rom`): `n1^n` times the real count
    (with the family bound's factor) is at most that bound plus each
    statement's `s k / NSh` a draw over the others (`errTD`); one direction.
    As there: the query hashes keep the first commitment's digit (`hφs`),
    and `n` statements extend to every index by repeating the last.  `n1`
    is both the commitment's range and its table's answer range, the
    spread discharged as `NSh NSo n1^nQ` (a `1/n1` collision term); each
    statement's commitment table its own. -/
theorem wit_fs_open4_powDROM {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {Vt x : ∀ ix : Nat, Term} {W : ∀ ix : Nat, Nat} {ws : ∀ ix : Nat, List Cell} (hwf : ∀ ix : Nat, WF (ws ix)) (hwl : ∀ ix : Nat, (ws ix).length = (W ix)) (hW8 : ∀ ix : Nat, (W ix) ≤ 2 ^ 8) {A : ∀ ix : Nat, List Cell} {k : ∀ ix : Nat, Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsFrom (A ix) (wMachine (ws ix) ((Vt ix) ⬝ (x ix))) (k ix) (row ix)) (hK : ∀ ix : Nat, rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).hd = some .K ∧ rd (A ix) ((row ix) ((k ix) - 1)).ctr ((row ix) ((k ix) - 1)).stk = some .nil) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ 10) (hk : ∀ ix : Nat, (k ix) ≤ 2 ^ 10) {tP : ∀ ix : Nat, Nat} (htp : ∀ ix : Nat, (tP ix) = progTpW (wMachine (List.replicate (W ix) .S) ((Vt ix) ⬝ (x ix))).heap (W ix)) (S10 S9 SP : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hS10 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S10 ix) c4, x ∉ cosetL 1 (bbGen 10) (2 ^ 10)) (hS9 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S9 ix) c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tP ix) + 1)) (2 ^ ((tP ix) + 1))) (hsz10 : ∀ ix : Nat, ∀ c4, 2 * ((S10 ix) c4).length + 8 ≤ 2 ^ 10) (hsz9 : ∀ ix : Nat, ∀ c4, 2 * ((S9 ix) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tP ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NSh NSo sQ kQ nQ NS2 NS3 : ∀ ix : Nat, Nat} (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4) (opF ((wGroups (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4) (fun d => (opQ (wSsT ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4)) d.1, opCw (wSsC (tP ix) ((S10 ix) c4) ((S9 ix) c4) ((SP ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (hKQ : 0 < n1)
    (pos : ∀ ix : Nat, List (List (List F)) → Nat → Nat → Nat) (hpos : ∀ ix d σo σh, pos ix d σo σh < nQ ix)
    (g : ∀ ix : Nat, List (List (List F)) → Nat → Pq)
    (hs : ∀ ix d σo v, sumTo (NSh ix) (fun σh => indB (decide (pos ix d σo σh = v))) ≤ sQ ix)
    (nxt : ∀ ix : Nat, Pq → Nat → List Nat → Nat) :
    ∀ n (E : Nat × Nat × Nat × Nat → PowD (fun _ => Nat × Nat × Nat × (Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) EF)) n → Bool),
    KPowD (fun _ => n1) n * KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n
      (fun xs => indB (E H (rvPowD (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out) n H xs)))) ≤
    (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n (fun c =>
      smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n (fun xq =>
        indB (E (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).pts c xx) c) n H c xq) (svPowD (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sv) n c xq))))) +
    (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).ε)
      (fun j => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt j) (x j) (W j) (A j) (k j) (row j) (tP j) (S10 j) (S9 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NSh j * (NSo j * n1 ^ nQ j) * n1) (NS2 j) (NS3 j) n1 n2 n3 (comI n1 (NSh j) (NSo j) (pos j)) (fun c4 => pfI n1 (NSh j) (NSo j) (kQ j) (pos j) ((witOp1 V Wv off (Vt j) (x j) (W j) (A j) (k j) (row j) (tP j) (S10 j) (S9 j) (SP j) (qv j) (wm j) (wc j) (ww j) (wp j) (ncw j) (αd j) (fri j) (NR2 j) (Rb j) (Ro j)) c4) (g j) (nxt j)) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j)).sm 2 (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ =>
        hitBD (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * (NSh ix * (NSo ix * n1 ^ nQ ix))))) j)))) n +
     KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n * errTD (fun _ => n1) (fun ix => n1 * (NSo ix * (n1 ^ nQ ix * (sQ ix * kQ ix))) * ((NS2 ix * NS3 ix) * ((@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * 1)))) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n) := by
  intro n E
  exact zkb_rom (wit_fs_open4_powD (NS1 := fun ix => (NSh ix * (NSo ix * n1 ^ nQ ix) * n1)) off hwf hwl hW8 hA hK hlen hk htp S10 S9 SP qv wm wc ww wp hlwm hlwc hlww hlwp hK2 hK4 φ hφ hS10 hS9 hSP hsz10 hsz9 hszP αd hB4 fri hncw NR2 Rb Ro (fun ix => comI n1 (NSh ix) (NSo ix) (pos ix)) (fun ix c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (fun ix => comI_hides hKQ (pos ix) (hpos ix)) (fun ix c4 => pfI_hides hKQ (pos ix) (hpos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (fun ix _ _ => Nat.mod_lt _ hKQ) d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3 hφs (fun ix => NSh ix * (NSo ix * n1 ^ nQ ix)) (fun ix d v => comI_spread hKQ (pos ix) (hpos ix) d v) n)
    (powD_transfer (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (lin_sum4 _ _ _ _) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2)
      (fun ix => lin_sm _ _ _ _) (fun ix => lin_sm _ _ _ _) (fun ix => comm_sm (lin_sum4 _ _ _ _) _ _ _ _)
      (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _) (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _)
      (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out)
      (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out)
      (fun ix H G => rom4_step (NR := (@witFS4 V Wv (Pq × List Nat) P2 P3 off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR) (m := 2) (NSh := NSh ix) (NSo := NSo ix) (s := sQ ix) (k := kQ ix) (n := nQ ix)
        (NS2 := NS2 ix) (NS3 := NS3 ix) (K2 := K2) (K3 := Q4) (K4 := K4) (n2 := n2) hKQ (φ ix) (witRv V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (witOz V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (pos ix) (hpos ix) (g ix) (hs ix) (nxt ix)
        (witOp1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (witOv1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (witMain1 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (Com2 ix) (Pf2 ix) (witOv2 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (witMain2 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (Com3 ix) (Pf3 ix) (witOv3 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (witMain3 V Wv off (Vt ix) (x ix) (W ix) (A ix) (k ix) (row ix) (tP ix) (S10 ix) (S9 ix) (SP ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) H G) n) E
set_option maxRecDepth 100000 in
def compOp1 (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  fun (c4 : Nat) => opF (Ss c4) mk1

set_option maxRecDepth 100000 in
def compRv (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  rvF

set_option maxRecDepth 100000 in
def compOz (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ozF

set_option maxRecDepth 100000 in
def compOv1 (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov1

set_option maxRecDepth 100000 in
def compOv2 (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov2

set_option maxRecDepth 100000 in
def compOv3 (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  ov3

set_option maxRecDepth 100000 in
def compMain2 (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  main2

set_option maxRecDepth 100000 in
def compMain3 (V : Type) (Wv : Type) (off : EF → String → EF) (R : Nat) (shp : BT) (Ps : List Term) (W : Nat) (A : List Cell) (e : Nat → Nat) (row : Nat → Air.Row) (tbM : Nat) (tbC : Nat) (tpP : Nat) (tpS : Nat) (SM : Nat → List F) (SC : Nat → List F) (S9 : Nat → List F) (SP : Nat → List F) (SS : Nat → List F) (qv : EF → EF → List EF → F → List F → List F → List EF) (wm : Nat → List (EF → EF → List F)) (wc : Nat → List (EF → EF → List F)) (ww : Nat → List (EF → EF → List F)) (wp : Nat → List (EF → EF → List F)) (wsg : Nat → List (EF → EF → List F)) (ncw : Nat) (αd : Nat → EF) (fri : Nat → EF → EF → List (EF → EF) → V) (NR2 : Nat) (Rb : Nat → EF → EF → Nat → List (EF → EF)) (Ro : Nat → EF → EF → Nat → Wv) :=
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    let NR0 := cNR off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv (wm 0) (wc 0) (ww 0) (wp 0) (wsg 0) ncw
    let pcsZ := fun (c4 c2 : Nat) (ζ : EF) t α β r => cPcs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) t α β (r % NR0)
    let psimZ := fun (c4 c2 : Nat) (ζ : EF) α β v r => cPsim off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2) ncw (αd c4)
      (friX (fri c4) (Rb c4) (Ro c4) (r / NR0)) α β v (r % NR0)
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
    let q0 := cGroups tbM tbC tpP tpS (SM 0) (SC 0) (S9 0) (SP 0) (SS 0) EF.zero qv
    let qZ := fun (c4 : Nat) (ζ : EF) => cGroups tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv
    let Ss := fun c4 => (qZ c4 EF.zero).map (·.base.S)
    let ks := cKs m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots
    let cols := cCols off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt
    let tqZ := fun (c4 c2 : Nat) (ζ : EF) => (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map Prod.fst
    let qdZ := fun (c4 c2 : Nat) (ζ : EF) (t : Nat → Tup) (α β : EF) (ms : List F) =>
      (cTs off m.hd m.stk m.heap.length roots.length m.stk m.heap N W roots C Mm Wt tbM tbC tpP tpS (SM c4) (SC c4) (S9 c4) (SP c4) (SS c4) ζ qv (wm c2) (wc c2) (ww c2) (wp c2) (wsg c2)).map (fun p => p.2 t α β ms)
    let SsT := fun c4 => (tqZ c4 0 EF.zero).map (·.S)
    let SsC := fun c4 => (tabsInfo ncw (tqZ c4 0 EF.zero)).map (·.S)
    let mk1 := [0, 2, 4, 6, 8]
    let mk2 := [1, 3, 5, 7, 9]
    let main1 := fun (t : Nat → Tup) (r : Nat) => mainF2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk1 t (r % NR0)
    let main2 := fun (c1 : Nat) (t : Nat → Tup) (r : Nat) =>
      mainP2 q0 ks cols (tqZ 0 0 EF.zero) ncw mk2 t (efOf (c1 / Q4)) (efOf (c1 % Q4)) (r % NR0)
    let main3 := fun (c1 c2 : Nat) (t : Nat → Tup) (r : Nat) =>
      (tabsPolys (tqZ 0 c2 EF.zero) (qdZ 0 c2 EF.zero t (efOf (c1 / Q4)) (efOf (c1 % Q4))
          (msF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0))) (crF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)),
       tabsCws ncw (tqZ 0 c2 EF.zero) (ccF q0 ks (tqZ 0 c2 EF.zero) ncw (r % NR0)))
    let vS := fun (α β : EF) (t : Nat → Tup) => viewT β (fun k => prefixOf α (off β) (chainBus k)) (fun _ => false)
      chainPar 3 (xrefN (ptm (prefixOf α (off β)) β)) t
    let sop1 := fun (c4 c2 c3 r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk1 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk1 (r % NR0))
    let sop2 := fun (c4 c2 c3 _ r : Nat) (_ : Nat → Tup) =>
      opF (Ss c4) mk2 (mainZ2 (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw mk2 (r % NR0))
    let sop3 := fun (c4 c2 c3 c1 r : Nat) (t : Nat → Tup) =>
      (opQ (SsT c4) (tabsPolys (tqZ c4 c2 (efOf c3)) (canonT (tqZ c4 c2 (efOf c3)) (efOf (c1 / Q4)) (efOf (c1 % Q4))
         (vS (efOf (c1 / Q4)) (efOf (c1 % Q4)) t)
         (openMulti ((qZ c4 (efOf c3)).map QGroup.ext) ((((qZ c4 (efOf c3)).map QGroup.ext).zip ks).map
           (fun p => List.replicate p.2 (List.replicate p.1.n (0 : F))))
           (msF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
         (crF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))),
       opCw (SsC c4) (tabsCws ncw (tqZ c4 c2 (efOf c3)) (ccF (qZ c4 (efOf c3)) ks (tqZ c4 c2 (efOf c3)) ncw (r % NR0))))
    let ov1 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk1 pv)
      | none => none
    let ov2 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List F))) := fun c4 v => match v with
      | some (pv, _) => some (ovF2 (Ss c4) mk2 pv)
      | none => none
    let ov3 : Nat → TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List (List F))) × List (List (List F))) :=
      fun _ v => match v with
      | some (pv, _) => some (ovQ pv, cwQ 10 pv)
      | none => none
    let rvF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      realVN off tabs tv pb (pcsZ c4 c2 (efOf c3)) α β r t
    let svF := fun (c4 c2 c3 : Nat) (α β : EF) (r : Nat) (t : Nat → Tup) =>
      simVN off pb chainBus (fun _ => false) chainPar 3 ptm (psimZ c4 c2 (efOf c3)) α β r t
    let ozF : TViewN (PcsPV (V × Wv)) (EF × EF) → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) := fun v => match v with
      | some (pv, _) => some (pv.1.1.map (fun g => g.1.map Prod.snd), pv.1.2.map (List.map (List.map Prod.snd)),
        pv.2.1.map (List.map Prod.snd))
      | none => none
    let op3 := fun (c4 : Nat) (d : List (List (List (List F))) × List (List (List F))) =>
      (opQ (SsT c4) d.1, opCw (SsC c4) d.2)
    let sd3 := fun (c4 : Nat) (o : List (List (List (List F))) × List (List (List F))) =>
      (sdQ (SsT c4) o.1, sdCw (SsC c4) o.2)
  main3
set_option maxRecDepth 100000 in
set_option autoImplicit false in
/-- **`n` composed statements, each first commitment drawn from the oracle**
    (`comp_fs_open4_powD` at the ideal openings, `powD_transfer` with
    `rom4_step` for each statement, `zkb_rom`): `n1^n` times the real count
    (with the family bound's factor) is at most that bound plus each
    statement's `s k / NSh` a draw over the others (`errTD`); one direction.
    As there: the query hashes keep the first commitment's digit (`hφs`),
    and `n` statements extend to every index by repeating the last.  `n1`
    is both the commitment's range and its table's answer range, the
    spread discharged as `NSh NSo n1^nQ` (a `1/n1` collision term); each
    statement's commitment table its own. -/
theorem comp_fs_open4_powDROM {V Wv Pq P2 P3 : Type} (off : EF → String → EF) {R Lm : ∀ ix : Nat, Nat} (hR : ∀ ix : Nat, (R ix) ≤ 20) {shp : ∀ ix : Nat, BT} {Ps : ∀ ix : Nat, List Term} {W : ∀ ix : Nat, Nat} {ρ : ∀ ix : Nat, Nat → Bool} {region : ∀ ix : Nat, List Cell} (hrl : ∀ ix : Nat, (region ix).length = (W ix)) (hr : ∀ ix : Nat, ∀ i c, (region ix)[i]? = some c → cellOK (BT.nleaves (shp ix) + 3 + i) c = true) {A : ∀ ix : Nat, List Cell} {e : ∀ ix : Nat, Nat → Nat} {row : ∀ ix : Nat, Nat → Air.Row} (hA : ∀ ix : Nat, AcceptsC (A ix) (cMachine (ρ ix) (shp ix) (region ix) (Ps ix)) (cHeap (ρ ix) (shp ix) (region ix) (Ps ix)).2
      (cHeap (ρ ix) (shp ix) (region ix) (Ps ix)).1.length (Ps ix).length (e ix) (row ix)) (hlen : ∀ ix : Nat, (A ix).length = 2 ^ (Lm ix)) (hLm : ∀ ix : Nat, (Lm ix) ≤ 20) (hK : ∀ ix : Nat, (e ix) ((Ps ix).length - 1) < 2 ^ (R ix)) (hNW : ∀ ix : Nat, BT.nleaves (shp ix) + (W ix) ≤ 2 ^ 8) {tbM tbC tpP tpS : ∀ ix : Nat, Nat} (htM : ∀ ix : Nat, (tbM ix) + 1 = (Lm ix)) (htC : ∀ ix : Nat, (tbC ix) + 1 = (R ix)) (htP : ∀ ix : Nat, (tpP ix) = progTpC (blankM (shp ix) (W ix) (Ps ix)).heap (BT.nleaves (shp ix)) (W ix)) (htS : ∀ ix : Nat, (tpS ix) = segTp (blankRoots (shp ix) (W ix) (Ps ix))) (SM SC S9 SP SS : ∀ ix : Nat, Nat → List F) (qv : ∀ ix : Nat, EF → EF → List EF → F → List F → List F → List EF) (wm wc ww wp wsg : ∀ ix : Nat, Nat → List (EF → EF → List F)) {Lwm Lwc Lww Lwp Lwsg : ∀ ix : Nat, Nat} (hlwm : ∀ ix : Nat, ∀ c, ((wm ix) c).length = (Lwm ix)) (hlwc : ∀ ix : Nat, ∀ c, ((wc ix) c).length = (Lwc ix)) (hlww : ∀ ix : Nat, ∀ c, ((ww ix) c).length = (Lww ix)) (hlwp : ∀ ix : Nat, ∀ c, ((wp ix) c).length = (Lwp ix)) (hlwsg : ∀ ix : Nat, ∀ c, ((wsg ix) c).length = (Lwsg ix)) {K2 K4 : Nat} (hK2 : 0 < K2) (hK4 : 0 < K4) (φ : ∀ ix : Nat, Nat → Option (List (List (List EF)) × List (List (List (List EF))) × List (List (List EF))) → Nat) {N4 : Nat} (hφ : ∀ ix : Nat, ∀ m w, (φ ix) m w < N4) (hSM : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SM ix) c4, x ∉ cosetL 1 (bbGen ((tbM ix) + 1)) (2 ^ ((tbM ix) + 1))) (hSC : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SC ix) c4, x ∉ cosetL 1 (bbGen ((tbC ix) + 1)) (2 ^ ((tbC ix) + 1))) (hS9 : ∀ ix : Nat, ∀ c4, ∀ x ∈ (S9 ix) c4, x ∉ cosetL 1 (bbGen 9) (2 ^ 9)) (hSP : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SP ix) c4, x ∉ cosetL 1 (bbGen ((tpP ix) + 1)) (2 ^ ((tpP ix) + 1))) (hSS : ∀ ix : Nat, ∀ c4, ∀ x ∈ (SS ix) c4, x ∉ cosetL 1 (bbGen ((tpS ix) + 1)) (2 ^ ((tpS ix) + 1))) (hszM : ∀ ix : Nat, ∀ c4, 2 * ((SM ix) c4).length + 8 ≤ 2 ^ ((tbM ix) + 1)) (hszC : ∀ ix : Nat, ∀ c4, 2 * ((SC ix) c4).length + 8 ≤ 2 ^ ((tbC ix) + 1)) (hsz9 : ∀ ix : Nat, ∀ c4, 2 * ((S9 ix) c4).length + 8 ≤ 2 ^ 9) (hszP : ∀ ix : Nat, ∀ c4, 2 * ((SP ix) c4).length + 8 ≤ 2 ^ ((tpP ix) + 1)) (hszS : ∀ ix : Nat, ∀ c4, 2 * ((SS ix) c4).length + 8 ≤ 2 ^ ((tpS ix) + 1)) {ncw : ∀ ix : Nat, Nat} (αd : ∀ ix : Nat, Nat → EF) {B4 : ∀ ix : Nat, Nat} (hB4 : ∀ ix : Nat, sumTo K4 (fun c4 => indB (!genB ((αd ix) c4))) ≤ (B4 ix)) (fri : ∀ ix : Nat, Nat → EF → EF → List (EF → EF) → V) (hncw : ∀ ix : Nat, 4 ≤ (ncw ix)) (NR2 : ∀ ix : Nat, Nat) (Rb : ∀ ix : Nat, Nat → EF → EF → Nat → List (EF → EF)) (Ro : ∀ ix : Nat, Nat → EF → EF → Nat → Wv) {n1 n2 n3 : Nat} {NSh NSo sQ kQ nQ NS2 NS3 : ∀ ix : Nat, Nat} (d1 : ∀ ix : Nat, List (List (List F))) (Com2 : ∀ ix : Nat, List (List (List F)) → Nat → Nat) (Pf2 : ∀ ix : Nat, Nat → List (List (List F)) → Nat → P2) (hc2 : ∀ ix : Nat, ComHides (NS2 ix) (Com2 ix)) (hp2 : ∀ ix : Nat, ∀ c4, ComPfHides (NS2 ix) (Com2 ix) ((Pf2 ix) c4) (opF ((cGroups (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4) EF.zero (qv ix)).map (·.base.S)) [1, 3, 5, 7, 9])) (hr2 : ∀ ix : Nat, ∀ d σ, (Com2 ix) d σ < n2) (d2 : ∀ ix : Nat, List (List (List F))) (Com3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F)) → Nat → Nat) (Pf3 : ∀ ix : Nat, Nat → List (List (List (List F))) × List (List (List F)) → Nat → P3) (hc3 : ∀ ix : Nat, ComHides (NS3 ix) (Com3 ix)) (hp3 : ∀ ix : Nat, ∀ c4, ComPfHides (NS3 ix) (Com3 ix) ((Pf3 ix) c4) (fun d => (opQ (cSsT ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4)) d.1, opCw (cSsC (tbM ix) (tbC ix) (tpP ix) (tpS ix) ((SM ix) c4) ((SC ix) c4) ((S9 ix) c4) ((SP ix) c4) ((SS ix) c4)) d.2))) (hr3 : ∀ ix : Nat, ∀ d σ, (Com3 ix) d σ < n3) (d3 : ∀ ix : Nat, List (List (List (List F))) × List (List (List F))) (hφs : ∀ i j m w m' w', φ i m w = φ j m' w' → m % n1 = m' % n1) (hKQ : 0 < n1)
    (pos : ∀ ix : Nat, List (List (List F)) → Nat → Nat → Nat) (hpos : ∀ ix d σo σh, pos ix d σo σh < nQ ix)
    (g : ∀ ix : Nat, List (List (List F)) → Nat → Pq)
    (hs : ∀ ix d σo v, sumTo (NSh ix) (fun σh => indB (decide (pos ix d σo σh = v))) ≤ sQ ix)
    (nxt : ∀ ix : Nat, Pq → Nat → List Nat → Nat) :
    ∀ n (E : Nat × Nat × Nat × Nat → PowD (fun _ => Nat × Nat × Nat × (Option (Pq × List Nat) × Option (P2 × P3) × TViewN (PcsPV (V × Wv)) (EF × EF))) n → Bool),
    KPowD (fun _ => n1) n * KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n * (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n
      (fun xs => indB (E H (rvPowD (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out) n H xs)))) ≤
    (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun H => scPowD (C := fun _ => Nat × Nat × Nat × Nat) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) n (fun c =>
      smPowD (X := fun _ => Nat × Nat × Nat × (Nat → Tup)) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n (fun xq =>
        indB (E (pgPowD (fun ix H c xx => prog4 (Q4 * Q4) K2 Q4 K4 H ((@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).pts c xx) c) n H c xq) (svPowD (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sv) n c xq))))) +
    (errPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4))))))) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).ε)
      (fun j => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo K4 (fun c4 => sumTo (Q4 * Q4) (fun c1 => sumTo K2 (fun c2 => sumTo Q4 (fun c3 => f (c1, c2, c3, c4)))))) (fun _ => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R j) (shp j) (Ps j) (W j) (A j) (e j) (row j) (tbM j) (tbC j) (tpP j) (tpS j) (SM j) (SC j) (S9 j) (SP j) (SS j) (qv j) (wm j) (wc j) (ww j) (wp j) (wsg j) K2 K4 (φ j) N4 (ncw j) (αd j) (B4 j) (fri j) (NR2 j) (Rb j) (Ro j) (NSh j * (NSo j * n1 ^ nQ j) * n1) (NS2 j) (NS3 j) n1 n2 n3 (comI n1 (NSh j) (NSo j) (pos j)) (fun c4 => pfI n1 (NSh j) (NSo j) (kQ j) (pos j) ((compOp1 V Wv off (R j) (shp j) (Ps j) (W j) (A j) (e j) (row j) (tbM j) (tbC j) (tpP j) (tpS j) (SM j) (SC j) (S9 j) (SP j) (SS j) (qv j) (wm j) (wc j) (ww j) (wp j) (wsg j) (ncw j) (αd j) (fri j) (NR2 j) (Rb j) (Ro j)) c4) (g j) (nxt j)) (Com2 j) (Pf2 j) (Com3 j) (Pf3 j)).sm 2 (fun _ => (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun _ =>
        hitBD (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NS * ((@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * (NSh ix * (NSo ix * n1 ^ nQ ix))))) j)))) n +
     KPowD (fun _ => (K4 * (Q4 * Q4 * (K2 * Q4)))) n * errTD (fun _ => n1) (fun ix => n1 * (NSo ix * (n1 ^ nQ ix * (sQ ix * kQ ix))) * ((NS2 ix * NS3 ix) * ((@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR * (Q4 ^ 2 * 1)))) (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) n) := by
  intro n E
  exact zkb_rom (comp_fs_open4_powD (NS1 := fun ix => (NSh ix * (NSo ix * n1 ^ nQ ix) * n1)) off hR hrl hr hA hlen hLm hK hNW htM htC htP htS SM SC S9 SP SS qv wm wc ww wp wsg hlwm hlwc hlww hlwp hlwsg hK2 hK4 φ hφ hSM hSC hS9 hSP hSS hszM hszC hsz9 hszP hszS αd hB4 fri hncw NR2 Rb Ro (fun ix => comI n1 (NSh ix) (NSo ix) (pos ix)) (fun ix c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (fun ix => comI_hides hKQ (pos ix) (hpos ix)) (fun ix c4 => pfI_hides hKQ (pos ix) (hpos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (fun ix _ _ => Nat.mod_lt _ hKQ) d1 Com2 Pf2 hc2 hp2 hr2 d2 Com3 Pf3 hc3 hp3 hr3 d3 hφs (fun ix => NSh ix * (NSo ix * n1 ^ nQ ix)) (fun ix d v => comI_spread hKQ (pos ix) (hpos ix) d v) n)
    (powD_transfer (fun (f : Nat × Nat × Nat × Nat → Nat) => sumTo (K4 ^ N4) (fun H4 => sumTo ((Q4 * Q4) ^ n1) (fun H1 => sumTo (K2 ^ (n1 * n2)) (fun H2 => sumTo (Q4 ^ (n1 * (n2 * n3))) (fun H3 => f (H1, H2, H3, H4)))))) (lin_sum4 _ _ _ _) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2) (fun ix => (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).sm 2)
      (fun ix => lin_sm _ _ _ _) (fun ix => lin_sm _ _ _ _) (fun ix => comm_sm (lin_sum4 _ _ _ _) _ _ _ _)
      (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _) (fun i j => comm_sm (lin_sm _ _ _ _) _ _ _ _)
      (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out)
      (fun ix => read4 (Q4 * Q4) K2 Q4 K4 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m1 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m2 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).m3 (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).q (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix) * n1) (NS2 ix) (NS3 ix) n1 n2 n3 (comI n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfI n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).out)
      (fun ix H G => rom4_step (NR := (@compFS4 V Wv (Pq × List Nat) P2 P3 off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) K2 K4 (φ ix) N4 (ncw ix) (αd ix) (B4 ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix) (NSh ix * (NSo ix * n1 ^ nQ ix)) (NS2 ix) (NS3 ix) n1 n2 n3 (comR n1 (NSh ix) (NSo ix) (pos ix)) (fun c4 => pfR n1 (NSh ix) (NSo ix) (kQ ix) (pos ix) ((compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) c4) (g ix) (nxt ix)) (Com2 ix) (Pf2 ix) (Com3 ix) (Pf3 ix)).NR) (m := 2) (NSh := NSh ix) (NSo := NSo ix) (s := sQ ix) (k := kQ ix) (n := nQ ix)
        (NS2 := NS2 ix) (NS3 := NS3 ix) (K2 := K2) (K3 := Q4) (K4 := K4) (n2 := n2) hKQ (φ ix) (compRv V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (compOz V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (pos ix) (hpos ix) (g ix) (hs ix) (nxt ix)
        (compOp1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (compOv1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (compMain1 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (Com2 ix) (Pf2 ix) (compOv2 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (compMain2 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (Com3 ix) (Pf3 ix) (compOv3 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) (compMain3 V Wv off (R ix) (shp ix) (Ps ix) (W ix) (A ix) (e ix) (row ix) (tbM ix) (tbC ix) (tpP ix) (tpS ix) (SM ix) (SC ix) (S9 ix) (SP ix) (SS ix) (qv ix) (wm ix) (wc ix) (ww ix) (wp ix) (wsg ix) (ncw ix) (αd ix) (fri ix) (NR2 ix) (Rb ix) (Ro ix)) H G) n) E
end
end Circuit
