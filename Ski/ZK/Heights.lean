import Ski.ZK.Reject
import Ski.ZK.Honest

/-!
# The trace heights in the view

A proof publishes each table's height (Plonky3's `degree_bits`).  The
transcript theorems' view leaves them out; here they go in.  Blinding
writes one row and keeps the height (`setBlind_h`), so the heights of the
prover's tables do not depend on its randomness.  When they are a fixed
list `hs`, the transcript with the heights is simulatable within the same
bound, the simulator emitting `hs` (`transcript_zkGH`).

For the honest prover `hs` is the statement's: each circuit's blinded
tables have the unblinded tables' heights (`comp_heights`, `sud_heights`,
`wit_heights`, `compJ_heights`, `compP_heights`), and the honest tables' heights are the statement's
(`comp_honest_heights`, `sud_honest_heights`, `wit_honest_heights`): the
CPU and memory heights the statement names, the witness table's fixed
height, and the public tables'.  The hiding verifiers refuse any other
heights (`bench/plonky3`, each `verify`'s `degree_bits` check).  The jet
circuits' honest heights are public too (`Ski/ZK/HeightsJ.lean`).
-/

namespace Circuit

open ZKF B Air JetTable Compose CompM Stmt Mach Wit

/-- The heights of a proof's tables, in order. -/
def heightsOf (tabs : List (AirD × Table)) : List Nat := tabs.map (fun p => p.2.h)

theorem setBlind_h (T : Table) (c : Nat) (a : Tup) : (T.setBlind c a).h = T.h := rfl

/-- **The transcript with the heights is simulatable**: as
    `transcript_zkG`, the view extended by the tables' heights, which the
    simulator emits as the fixed `hs`. -/
theorem transcript_zkGH {PV PB : Type} {off : EF → String → EF} {NR M ε m : Nat}
    {bus : Nat → String} {sg : Nat → Bool} {par : Nat → Nat} (hpar : ∀ k, par (k + 1) ≤ k)
    {tabs : (Nat → Tup) → List (AirD × Table)}
    {tv : (String → EF) → EF → (Nat → Tup) → List EF} {tp : (String → EF) → EF → EF}
    {pb : (String → EF) → EF → PB}
    {pcs : (Nat → Tup) → EF → EF → Nat → PV} {psim : EF → EF → List EF → Nat → PV}
    {xu : (String → EF) → EF → Nat → EF}
    (hchain : ∀ pre β t, tv pre β t = viewT β (fun k => pre (bus k)) sg par (m + 1) (xu pre β) t)
    (hsum : ∀ pre β, sumL (xu pre β) (List.range (m + 1)) = EF.zero.sub (tp pre β))
    (hM : ∀ t, (allEntries (tabs t)).length ≤ M)
    (hpcs : PCSCloseN off NR tv pcs psim ε) {hs : List Nat} (hH : ∀ t, heightsOf (tabs t) = hs)
    (E : List Nat × TViewN PV PB → Bool) :
    tsumN NR m (fun α β r t => indB (genB β && E (heightsOf (tabs t), realVN off tabs tv pb pcs α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (hs, simVN off pb bus sg par (m + 1) tp psim α β r t))) +
        Q4 * (NR * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * ε)) ∧
    tsumN NR m (fun α β r t => indB (genB β && E (hs, simVN off pb bus sg par (m + 1) tp psim α β r t))) ≤
      tsumN NR m (fun α β r t => indB (genB β && E (heightsOf (tabs t), realVN off tabs tv pb pcs α β r t))) +
        Q4 * (NR * (Q4 ^ m * M)) + Q4 * (Q4 * (Q4 ^ m * ε)) := by
  simp only [hH]
  exact transcript_zkG hpar hchain hsum hM hpcs (fun v => E (hs, v))

/-- The composed proof's blinded tables have the unblinded tables'
    heights, for every blinding. -/
theorem comp_heights (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg : Table) (t : Nat → Tup) :
    heightsOf (compTables hd0 stk0 ctr0 n nilA heap N W roots ((C.setBlind BLA (t 1)).setBlind BLB (t 0))
      (Mm.setBlind 5 (t 0)) Pg (Wt.setBlind WT_BLIND (t 1)) Sg) = [C.h, Mm.h, Pg.h, Wt.h, Sg.h] := rfl

/-- The Sudoku proof's blinded tables have the unblinded tables' heights. -/
theorem sud_heights (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Pg Wt : Table) (t : Nat → Tup) :
    heightsOf (sudTables hd0 stk0 ctr0 heap ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) Pg
      (Wt.setBlind 1 (t 1))) = [C.h, Mm.h, Pg.h, Wt.h] := rfl

/-- The hidden-term proof's blinded tables have the unblinded tables'
    heights. -/
theorem wit_heights (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Pg Wt : Table) (t : Nat → Tup) :
    heightsOf (witTables hd0 stk0 ctr0 heap W ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) (Mm.setBlind 5 (t 0)) Pg
      (Wt.setBlind WT_BLIND (t 1))) = [C.h, Mm.h, Pg.h, Wt.h] := rfl

/-- The proof with jets: its blinded tables have the unblinded tables'
    heights, for every blinding. -/
theorem compJ_heights (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (segRoots : List Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table) (t : Nat → Tup) :
    heightsOf (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets
      (((C.setBlind BLAJ (t 1)).setBlind BLBJ (t 0)).setBlind BLCJ (t 2)) (Mm.setBlind 5 (t 0))
      Pg (Wt.setBlind WT_BLIND (t 1)) Sg (Rt.setBlind 1 (t 6))
      ((Hd.setBlind 1 (t 5)).setBlind 6 (t 6)) ((Tm.setBlind 1 (t 4)).setBlind 6 (t 5))
      ((Po.setBlind popAir.width (t 2)).setBlind (popAir.width + 5) (t 3))
      ((Iw.setBlind instwAir.width (t 3)).setBlind (instwAir.width + 5) (t 4))) =
    heightsOf (compJTables hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw) := rfl

/-- The proof with the Poseidon2 jet: its blinded tables have the
    unblinded tables' heights, for every blinding. -/
theorem compP_heights (hd0 stk0 ctr0 n nilA J root : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg Pi Po Pp Px : Table) (t : Nat → Tup) :
    heightsOf (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots
      (((C.setBlind BLA (t 1)).setBlind BLB (t 0)).setBlind (P2SEL + 1) (t 2)) (Mm.setBlind 5 (t 0))
      Pg (Wt.setBlind WT_BLIND (t 1)) Sg
      ((Pi.setBlind p2inAir.width (t 2)).setBlind (p2inAir.width + 5) (t 3))
      ((Po.setBlind p2outAir.width (t 3)).setBlind (p2outAir.width + 5) (t 4))
      (Pp.setBlind P2Air.p2Air.width (t 4)) Px) =
    heightsOf (compPTables hd0 stk0 ctr0 n nilA J root heap N W roots C Mm Pg Wt Sg Pi Po Pp Px) := rfl

/-- **The composed proof's honest heights are the statement's**: the
    tables of `comp_honest_zk` have `2^R` CPU rows, `2^Lm` memory cells,
    `2^8` witness rows, and the public program and segment tables'
    heights. -/
theorem comp_honest_heights {R Lm : Nat} {shp : BT} {Ps : List Term} {W : Nat} {A : List Cell}
    {e : Nat → Nat} {row : Nat → Air.Row} (hlen : A.length = 2 ^ Lm) (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    [C.h, Mm.h, Pg.h, Wt.h, (segsPub roots).h] = [2 ^ R, 2 ^ Lm, Pg.h, 2 ^ 8, (segsPub roots).h] := by
  intro m roots N C Pg Wt Mm
  have hW : Wt.h = 2 ^ 8 := witRows_len hNW
  have hM : Mm.h = 2 ^ Lm := hlen
  rw [hW, hM]
  rfl

section
open Sudoku SudokuText

/-- **The Sudoku proof's honest heights are the statement's**: `2^16` CPU
    rows and memory cells, `2^10` witness rows, and the public program
    table's height. -/
theorem sud_honest_heights {puzzle : List Nat} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hlen : A.length = 2 ^ 16) :
    let blank := stmtMachine (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
    let C := cpuTableW A row k (2 ^ 16)
    let Pg := progTableS blank.heap
    let Wt := witTableS A
    let Mm := memTableC A (cpuAirS blank.hd blank.stk blank.heap.length ACC) (progAirS blank.heap) witAirS C Pg Wt
    [C.h, Mm.h, Pg.h, Wt.h] = [2 ^ 16, 2 ^ 16, Pg.h, 2 ^ 10] := by
  intro blank C Pg Wt Mm
  have hM : Mm.h = 2 ^ 16 := hlen
  rw [hM]
  rfl

end

/-- **The hidden-term proof's honest heights are the statement's**:
    `2^10` CPU rows and memory cells, `2^8` witness rows, and the public
    program table's height. -/
theorem wit_honest_heights {V x : Term} {W : Nat} {A : List Cell} {k : Nat} {row : Nat → Air.Row}
    (hW8 : W ≤ 2 ^ 8) (hlen : A.length = 2 ^ 10) :
    let blank := wMachine (List.replicate W .S) (V ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    [C.h, Mm.h, Pg.h, Wt.h] = [2 ^ 10, 2 ^ 10, Pg.h, 2 ^ 8] := by
  intro blank C Pg Wt Mm
  have hW : Wt.h = 2 ^ 8 := witRowsG_len (by omega)
  have hM : Mm.h = 2 ^ 10 := hlen
  rw [hW, hM]
  rfl

end Circuit
