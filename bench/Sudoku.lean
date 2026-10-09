import Ski.SudokuCheck
import Ski.SudokuText
import Ski.Circuit.SudComplete
import Ski.Circuit.TraceCheck
import Ski.Circuit.CpuFast
import Ski.ZK.Blocks
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
open SudokuText

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

/-- `sudoku check-tables PUBLIC DIR`: compare the traces `sudoku.rs`
    proves (`ski-air sudoku-dump PUBLIC BITS DIR`) with Lean's honest
    tables, as `Circuit.sud_complete` builds them from the same run
    (`DIR/run.txt`): the CPU (`cpuTableW`, read through
    `Circuit.cpuColW_arr`), the input table (`witTableS`) and the memory
    (`memTableC`, its multiplicities counted over the dumped tables,
    `Circuit.memTableC_mult`), each on every row.  `OK` when every cell compared
    agrees. -/
def checkTables (pub dir : String) : IO UInt32 := do
  let some puzzle ← statementOf pub | do IO.println "NOT A STATEMENT"; return 1
  let ls := ((← IO.FS.readFile (dir ++ "/run.txt")).splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let some (clues, acc, rej, cells, rows) := parseTable ls | do IO.println "MALFORMED run.txt"; return 1
  if clues != cluesOf puzzle || acc != ACC || rej != REJ then IO.println "run.txt is not a run of the statement"; return 1
  let A := cells.toList
  let blank := stmtMachineA (fun _ => false) 729 (sudokuExpr (cluesOf puzzle)) ACC REJ
  let airs := Circuit.sudAirs puzzle
  let air := fun (i : Nat) => airs.getD i ⟨"", 0, 0, [], [], []⟩
  let cpu ← Circuit.TraceCheck.loadTrace dir "cpu"
  let mem ← Circuit.TraceCheck.loadTrace dir "mem"
  let wit ← Circuit.TraceCheck.loadTrace dir "wit"
  let rowA := rows.toArray
  let rowAt := fun i => rowA.getD i ⟨0, 0, 0⟩
  let Wt := Circuit.witTableS A
  -- The proof's heights (`Circuit.sud_complete`): 2^16 rows and memory, the
  -- input table's 2^10.
  if !(← Circuit.TraceCheck.shapesOK
      [("cpu", cpu.size, 2 ^ 16), ("run", rows.length, cpu.size), ("mem", mem.size, 2 ^ 16),
       ("memory", cells.size, 2 ^ 16), ("wit", wit.size, 2 ^ 10)]
      [("cpu", cpu, air 0), ("mem", mem, air 1), ("wit", wit, air 3)] cells.size) then return 1
  let moving := ((List.range rowA.size).find? (fun r => rowAt r == rowAt (r + 1))).getD rowA.size
  let who := "sudoku.rs"
  -- Every CPU row, its memory read from the array (`Circuit.cpuColW_arr`).
  let b1 ← Circuit.TraceCheck.cmpRows who "cpu" cpu (List.range cpu.size) fun r c =>
    (Circuit.cpuColWG (fun a => cells[a]?) rowAt rowA.size r c).val
  let b2 ← Circuit.TraceCheck.cmpRows who "wit" wit (List.range wit.size) fun r c => (Wt.main r c).val
  let msgs := Circuit.sendsOn (air 0) (Circuit.TraceCheck.asTable (air 0) cpu) "mem" ++
    Circuit.sendsOn (air 2) (Circuit.progTableS blank.heap) "mem" ++
    Circuit.sendsOn (air 3) (Circuit.TraceCheck.asTable (air 3) wit) "mem"
  let mult := Circuit.multArr A msgs
  let b3 ← Circuit.TraceCheck.cmpRows who "mem" (mem.map (·.extract 0 5)) (List.range mem.size)
    (Circuit.TraceCheck.memModel cells mult)
  IO.println s!"cpu: all {cpu.size} rows ({moving} moving); wit {wit.size}, mem {mem.size} rows; cells differing: {b1}, {b2}, {b3}"
  if b1 + b2 + b3 == 0 then
    IO.println "OK: sudoku.rs's traces are Lean's model of the honest tables"; return 0
  else
    IO.println "DIFFER"; return 1

/-- `sudoku check-blind DIR`: the blinded traces `sudoku.rs` commits to are
    its unblinded ones blinded as `Circuit.sudView` blinds them, at
    `Circuit.sudBlocks`. -/
def checkBlind (dir : String) : IO UInt32 :=
  Circuit.TraceCheck.checkBlind "sudoku.rs" "sudView" dir ["mem", "cpu", "wit"] Circuit.sudBlocks 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["statement", pub] => statement pub
  | "check" :: pub :: paths => check pub paths
  | ["check-tables", pub, dir] => checkTables pub dir
  | ["check-blind", dir] => checkBlind dir
  | _ =>
    IO.eprintln "usage: sudoku emit DIR | sudoku statement PUBLIC | sudoku check PUBLIC TABLE... | sudoku check-tables PUBLIC DIR | sudoku check-blind DIR"
    return 2
