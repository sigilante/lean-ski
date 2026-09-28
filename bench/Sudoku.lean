import Ski.SudokuCheck
open Term

/-!
The Sudoku statement for the Plonky3 prover, and the check of its tables.

- `sudoku emit DIR` writes the statement machine of Wikipedia's puzzle
  (`Sudoku.wikiPuzzle`): `DIR/public.txt`, the heap with the input cells
  blank, which the verifier sees; `DIR/witness.txt`, the inputs of
  Wikipedia's solution, which only the prover sees; and
  `DIR/witness_swapped.txt`, the inputs of the solution with two cells
  swapped (`Sudoku.wiki_swapped`), for the tamper test.
- `sudoku statement PUBLIC` checks that a statement file is exactly the
  statement of the puzzle on its first line, with well-formed clues: what
  the Plonky3 verifier must check before it trusts `public.txt`.
- `sudoku check PUBLIC TABLE...` checks tables the prover wrote, with
  `Sudoku.sudokuCheck`, against the puzzle and markers of the statement
  `PUBLIC`.  `ACCEPT` means the table's input cells hold a solution of that
  puzzle (`Sudoku.sudokuCheck_sound`).

The markers are the atoms `ACC = 731` and `REJ = 732`, the first variables
past the 729 input slots and the two constant slots.

**`public.txt`**: the puzzle as 81 digits (`0` blank); `acc rej hd stk ctr`,
the first input address and the number of inputs; then `ctr` cells, one
per line, an input cell as `W`.
**`witness.txt`**: 729 digits `0` or `1`.
**A table**: the puzzle as 81 digits (`0` blank); `acc rej`; the number of
memory cells, then the cells; the number of rows, then `hd stk ctr` per row.
A cell is `S`, `K`, `I`, `N`, `A f x`, `C x r` or `X n` (the atom `n`).
-/

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

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def parseCell (ws : List String) : Option Cell :=
  match ws with
  | ["S"] => some .S
  | ["K"] => some .K
  | ["I"] => some .I
  | ["N"] => some .nil
  | ["A", f, x] => do some (.app (← f.toNat?) (← x.toNat?))
  | ["C", x, r] => do some (.cons (← x.toNat?) (← r.toNat?))
  | ["X", n] => do some (.atom (← n.toNat?))
  | _ => none

def parseRow (ws : List String) : Option Air.Row :=
  match ws with
  | [h, s, c] => do some ⟨← h.toNat?, ← s.toNat?, ← c.toNat?⟩
  | _ => none

def parseDigits (s : String) : Option (List Nat) :=
  let cs := s.toList
  if cs.length == 81 && cs.all Char.isDigit then some (cs.map fun ch => ch.toNat - '0'.toNat) else none

/-- A table: the clues, the markers, the memory and the rows. -/
def parseTable (ls : List String) : Option (List Clue × Nat × Nat × Array Cell × List Air.Row) := do
  match ls with
  | pl :: ml :: nl :: rest =>
    let clues := cluesOf (← parseDigits pl.trimAscii.toString)
    let (acc, rej) ← match words ml with
      | [a, r] => do some (← a.toNat?, ← r.toNat?)
      | _ => none
    let n ← nl.trimAscii.toString.toNat?
    let cells ← (rest.take n).mapM (fun l => parseCell (words l))
    if cells.length != n then none
    match rest.drop n with
    | kl :: rest2 =>
      let k ← kl.trimAscii.toString.toNat?
      let rows ← (rest2.take k).mapM (fun l => parseRow (words l))
      if rows.length != k then none
      if !(rest2.drop k).isEmpty then none
      some (clues, acc, rej, cells.toArray, rows)
    | [] => none
  | _ => none

def bits (ρ : Nat → Bool) : String :=
  String.ofList ((List.range 729).map fun n => if ρ n then '1' else '0')

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

def emit (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  let clues := wikiClues
  let m := stmtMachineA (fun _ => false) 729 (sudokuExpr clues) ACC REJ
  let ctr := m.heap.length
  IO.FS.writeFile s!"{dir}/public.txt" (publicText wikiPuzzle)
  IO.FS.writeFile s!"{dir}/witness.txt" (bits (inputsOf wikiSolution) ++ "\n")
  IO.FS.writeFile s!"{dir}/witness_swapped.txt"
    (bits (inputsOf ([3, 5, 4] ++ wikiSolution.drop 3)) ++ "\n")
  IO.println s!"{wikiClues.length} clues; heap {ctr} cells (hd {m.hd}, stk {m.stk}); formula {sudokuExpr clues |> size} nodes"
  return 0
where
  size : BExpr → Nat
    | .and a b | .or a b => size a + size b + 1
    | .not a => size a + 1
    | _ => 1

/-- The puzzle a statement file names, if the file is exactly that puzzle's
    statement and its clues are well formed. -/
def statementOfText (text : String) : Option (List Nat) :=
  match (text.splitOn "\n").head? >>= fun l => parseDigits l.trimAscii.toString with
  | some puzzle =>
    if cluesOKB (cluesOf puzzle) && text == publicText puzzle then some puzzle else none
  | none => none

def statementOf (path : String) : IO (Option (List Nat)) := do
  return statementOfText (← IO.FS.readFile path)

/-- `-` reads the statement from stdin: the bytes the verifier holds, so no
    file is read between its read and this check. -/
def statement (path : String) : IO UInt32 := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  match statementOfText text with
  | some puzzle =>
    IO.println s!"STATEMENT {path}: the statement machine of {String.ofList (puzzle.map fun d => Char.ofNat (d + '0'.toNat))}, markers {ACC} {REJ}"
    return 0
  | none =>
    IO.println s!"NOT A STATEMENT {path}"
    return 1

def check (pub : String) (paths : List String) : IO UInt32 := do
  let some puzzle ← statementOf pub
    | IO.println s!"NOT A STATEMENT {pub}"; return 1
  let mut bad := 0
  for path in paths do
    let text ← IO.FS.readFile path
    let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    match parseTable ls with
    | none =>
      IO.println s!"MALFORMED {path}"
      bad := bad + 1
    | some (clues, acc, rej, A, rows) =>
      if clues != cluesOf puzzle || acc != ACC || rej != REJ then
        IO.println s!"REJECT {path} (not the statement of {pub})"
        bad := bad + 1
      else if sudokuCheck clues acc rej A rows then
        IO.println s!"ACCEPT {path} ({rows.length} rows, {A.size} cells)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["statement", pub] => statement pub
  | "check" :: pub :: paths => check pub paths
  | _ =>
    IO.eprintln "usage: sudoku emit DIR | sudoku statement PUBLIC | sudoku check PUBLIC TABLE..."
    return 2
