import Ski.SudokuCheck
open Term

/-!
# A Sudoku statement's text

`public.txt` of the Sudoku circuit, as `lake exe sudoku statement` checks it
and the verifier's Lean comparison of its circuit reads it: a puzzle, and
the statement machine with the inputs blank (`publicText`), parsed back
only when it is exactly that text and its clues are well formed
(`statementOfText`).
-/

namespace SudokuText

open Sudoku Stmt Mach

def ACC : Nat := 731
def REJ : Nat := 732

def cellText : Cell → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .nil => "N"
  | .app f x => s!"A {f} {x}"
  | .cons x r => s!"C {x} {r}"
  | .atom n => s!"X {n}"

def parseDigits (s : String) : Option (List Nat) :=
  let cs := s.toList
  if cs.length == 81 && cs.all Char.isDigit then some (cs.map fun ch => ch.toNat - '0'.toNat) else none

/-- **The statement** of a puzzle: `public.txt`.  The heap is the statement
    machine's for all-false inputs with the input cells blank; by
    `Stmt.stmtMachine_public` it states the machine for every input. -/
def publicText (puzzle : List Nat) : String := Id.run do
  let m := stmtMachineA (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  let ctr := m.heap.length
  let digits := String.ofList (puzzle.map fun d => Char.ofNat (d + '0'.toNat))
  let mut s := s!"{digits}\n{ACC} {REJ} {m.hd} {m.stk} {ctr} 3 729\n{ctr}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < 3 + 729 then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- The puzzle a statement file names, if the file is exactly that puzzle's
    statement and its clues are well formed. -/
def statementOfText (text : String) : Option (List Nat) :=
  match (text.splitOn "\n").head? >>= fun l => parseDigits l.trimAscii.toString with
  | some puzzle =>
    if cluesOKB (cluesOf puzzle) && text == publicText puzzle then some puzzle else none
  | none => none

end SudokuText
