import Ski.ZK.CompP
import Ski.ZK.CompJ

/-!
# The blinding blocks of each zero-knowledge circuit, as data

Each circuit's transcript theorem simulates the terminals of its private
tables blinded by `Table.setBlind c (t k)`: edge `k`'s tuple and the flag 1
in row 0 at column `c`.  Here each circuit's blocks are a list,
`(table, column, edge)` with the tables in the view's order, and a theorem
proves the view is each table blinded by its blocks in that list's order
(`blindBy`):

- the composed circuit, `compViewN` (memory, CPU, witness);
- Sudoku, `sudView`, and the hidden-term circuit, `witView` (witness, CPU,
  memory, as `View3` holds them);
- the composed circuit with jets, `compJViewN` (memory, CPU, witness, POP,
  INSTW, TMPL, HDR, ROOTS);
- the circuit with the Poseidon2 jet, `compPViewN` (memory, CPU, witness,
  P2IN, P2OUT, P2).

So a check that reads a list (`check-*-blind`) reads its theorem's blocks,
not a copy of them.
-/

namespace Circuit

open ZKF

/-- Table `k` blinded by its blocks among `bs`, in order, with edge tuples `t`. -/
def blindBy (bs : List (Nat × Nat × Nat)) (k : Nat) (T : Table) (t : Nat → Tup) : Table :=
  (bs.filter (·.1 == k)).foldl (fun T b => T.setBlind b.2.1 (t b.2.2)) T

-- ---------------------------------------------------------------------------
-- The composed circuit: memory 0, CPU 1, witness 2
-- ---------------------------------------------------------------------------

def compBlocks : List (Nat × Nat × Nat) := [(0, 5, 0), (1, BLA, 1), (1, BLB, 0), (2, WT_BLIND, 1)]

theorem compViewN_blocks (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat) (C Mm Wt : Table)
    (t : Nat → Tup) :
    compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t =
      [terminal pre β memAirC (blindBy compBlocks 0 Mm t),
       terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) (blindBy compBlocks 1 C t),
       terminal pre β (witAir N W) (blindBy compBlocks 2 Wt t)] :=
  rfl

-- ---------------------------------------------------------------------------
-- Sudoku and the hidden-term circuit: memory 0, CPU 1, witness 2; edge 1
-- is the tuple `a`, edge 0 the tuple `b`
-- ---------------------------------------------------------------------------

def sudBlocks : List (Nat × Nat × Nat) := [(0, 5, 0), (1, BLA, 1), (1, BLB, 0), (2, 1, 1)]

theorem sudView_blocks (pre : String → EF) (β : EF) (hd0 stk0 ctr0 : Nat) (C Mm Wt : Table) (t : Nat → Tup) :
    sudView pre β hd0 stk0 ctr0 C Mm Wt (t 1) (t 0) =
      ⟨terminal pre β witAirS (blindBy sudBlocks 2 Wt t),
       terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) (blindBy sudBlocks 1 C t),
       terminal pre β memAirC (blindBy sudBlocks 0 Mm t)⟩ :=
  rfl

def witBlocks : List (Nat × Nat × Nat) := [(0, 5, 0), (1, BLA, 1), (1, BLB, 0), (2, WT_BLIND, 1)]

theorem witView_blocks (pre : String → EF) (β : EF) (hd0 stk0 ctr0 W : Nat) (C Mm Wt : Table) (t : Nat → Tup) :
    witView pre β hd0 stk0 ctr0 W C Mm Wt (t 1) (t 0) =
      ⟨terminal pre β (witAirW W) (blindBy witBlocks 2 Wt t),
       terminal pre β (cpuAirW hd0 stk0 ctr0) (blindBy witBlocks 1 C t),
       terminal pre β memAirC (blindBy witBlocks 0 Mm t)⟩ :=
  rfl

-- ---------------------------------------------------------------------------
-- The composed circuit with jets: memory 0, CPU 1, witness 2, POP 3,
-- INSTW 4, TMPL 5, HDR 6, ROOTS 7
-- ---------------------------------------------------------------------------

def compJBlocks : List (Nat × Nat × Nat) :=
  [(0, 5, 0), (1, BLAJ, 1), (1, BLBJ, 0), (1, BLCJ, 2), (2, WT_BLIND, 1),
   (3, popAir.width, 2), (3, popAir.width + 5, 3), (4, instwAir.width, 3), (4, instwAir.width + 5, 4),
   (5, 1, 4), (5, 6, 5), (6, 1, 5), (6, 6, 6), (7, 1, 6)]

theorem compJViewN_blocks (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA N W : Nat)
    (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Wt Rt Hd Tm Po Iw : Table) (t : Nat → Tup) :
    compJViewN pre β hd0 stk0 ctr0 n nilA N W roots jets C Mm Wt Rt Hd Tm Po Iw t =
      [terminal pre β memAirC (blindBy compJBlocks 0 Mm t),
       terminal pre β (cpuAirCJ hd0 stk0 ctr0 n nilA) (blindBy compJBlocks 1 C t),
       terminal pre β (witAir N W) (blindBy compJBlocks 2 Wt t),
       terminal pre β popAirCJ (blindBy compJBlocks 3 Po t),
       terminal pre β instwAirCJ (blindBy compJBlocks 4 Iw t),
       terminal pre β (tmplAirCJ jets) (blindBy compJBlocks 5 Tm t),
       terminal pre β (hdrAirCJ jets) (blindBy compJBlocks 6 Hd t),
       terminal pre β (rootsAirCJ roots) (blindBy compJBlocks 7 Rt t)] :=
  rfl

-- ---------------------------------------------------------------------------
-- The circuit with the Poseidon2 jet: memory 0, CPU 1, witness 2, P2IN 3,
-- P2OUT 4, P2 5
-- ---------------------------------------------------------------------------

def compPBlocks : List (Nat × Nat × Nat) :=
  [(0, 5, 0), (1, BLA, 1), (1, BLB, 0), (1, P2SEL + 1, 2), (2, WT_BLIND, 1),
   (3, p2inAir.width, 2), (3, p2inAir.width + 5, 3), (4, p2outAir.width, 3), (4, p2outAir.width + 5, 4),
   (5, P2Air.p2Air.width, 4)]

theorem compPViewN_blocks (pre : String → EF) (β : EF) (hd0 stk0 ctr0 n nilA J root N W : Nat)
    (C Mm Wt Pi Po Pp : Table) (t : Nat → Tup) :
    compPViewN pre β hd0 stk0 ctr0 n nilA J root N W C Mm Wt Pi Po Pp t =
      [terminal pre β memAirC (blindBy compPBlocks 0 Mm t),
       terminal pre β (cpuAirP2 hd0 stk0 ctr0 n nilA J root) (blindBy compPBlocks 1 C t),
       terminal pre β (witAirP N W) (blindBy compPBlocks 2 Wt t),
       terminal pre β p2inAirB (blindBy compPBlocks 3 Pi t),
       terminal pre β p2outAirB (blindBy compPBlocks 4 Po t),
       terminal pre β p2AirB (blindBy compPBlocks 5 Pp t)] :=
  rfl

end Circuit
