import Ski.Circuit.WitAir
import Ski.SudokuText

/-!
# The Sudoku circuit, as data

The four AIRs of `bench/plonky3/src/sudoku.rs` for a puzzle, the statement
`lake exe sudoku statement` checks, as its verifier builds them (`airs`):
the corpus CPU with two blinding messages, its last row the atom `ACC` at
the head (`HA`); the memory with a blinding message (`memAirC`); the
program table of the public cells; the witness table of the 729 input
bits, each a cell `K` or `A 0 1`.  `lake exe circuit compare-sudoku` checks
the Rust export against it.
-/

namespace Circuit

open B

/-- **The Sudoku CPU**: the corpus CPU, blinded, ending at the atom `acc`. -/
def cpuConsS (hd0 stk0 ctr0 acc : Nat) : List E :=
  cpuCons hd0 stk0 ctr0 ++ [B.bool (col (BLA + 4)), B.bool (col (BLB + 4)),
    whenLast (eq sHA one), whenLast (eq (fld 0) (c acc))]

def cpuAirS (hd0 stk0 ctr0 acc : Nat) : AirD := ⟨"cpu", CPU_WIDTH + 10, 0, cpuConsS hd0 stk0 ctr0 acc, cpuIntersW, []⟩

/-- The program table of the public cells: every cell outside the inputs
    `[3, 732)`, padded to the next power of two. -/
def progRowsS (heap : List Cell) : List (List F) :=
  let rows := (heap.zipIdx.filter fun (_, i) => !(3 ≤ i && i < 3 + 729)).map
    fun (c, i) => [ofN i, ofN (cellTag c), ofN (cellFields c).1, ofN (cellFields c).2, ofN 1]
  rows ++ List.replicate (pow2From 64 1 rows.length - rows.length) [ofN 0, ofN 0, ofN 0, ofN 0, ofN 0]

def progAirS (heap : List Cell) : AirD :=
  ⟨"prog", 1, 5, [col 0], [⟨"mem", 1, prec 4, [prec 0, prec 1, prec 2, prec 3]⟩], progRowsS heap⟩

/-- **The input table**: a bit per input, its cell `K` (`1`) or `A 0 1` (`0`). -/
def witConsS : List E := [B.bool (col 5), B.bool (col 0)]

def witIntersS : List Inter :=
  [⟨"blind_a", 1, col 5, [col 1, col 2, col 3, col 4]⟩,
   ⟨"mem", 1, prec 1, [prec 0, .sub (c 3) (.mul (col 0) (c 2)), zero, .sub one (col 0)]⟩]

/-- Its rows: the inputs' addresses, active, padded to `2^10`. -/
def witRowsS : List (List F) :=
  (List.range 729).map (fun n => [ofN (3 + n), ofN 1]) ++ List.replicate (2 ^ 10 - 729) [ofN 0, ofN 0]

def witAirS : AirD := ⟨"wit", 6, 2, witConsS, witIntersS, witRowsS⟩

/-- **The Sudoku circuit for a puzzle**: what its verifier builds. -/
def sudAirs (puzzle : List Nat) : List AirD :=
  let m := Stmt.stmtMachineA (fun _ => false) 729 (Sudoku.sudokuExpr (Sudoku.cluesOf puzzle))
    SudokuText.ACC SudokuText.REJ
  [cpuAirS m.hd m.stk m.heap.length SudokuText.ACC, memAirC, progAirS m.heap, witAirS]

end Circuit
