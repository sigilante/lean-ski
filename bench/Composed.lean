import Ski.Composed
import Ski.ComposeExamples
open Term

/-!
Composed statements for the Plonky3 prover, and the check of their tables
(`Ski/Composed.lean`).

- `composed emit DIR` writes, for each example formula (`or`, the
  disjunction of the two example atoms, and `and`, their conjunction),
  `DIR/<name>/`: `public.txt`, the composed machine with the bit cells and
  the region blank, which the verifier sees; `witness.txt`, the bits and
  the region, which only the prover sees; and four witnesses for the
  tamper tests: `witness_clear.txt` (every bit clear: the formula is
  false), `witness_wrong.txt` (a set atom's component replaced by one its
  verifier rejects), `witness_nonbool.txt` (a bit cell `I`, no Boolean),
  and `witness_forged.txt` (a region cell pointing forward, never read).
- `composed statement PUBLIC` checks that a statement file is exactly the
  composed machine of the formula it names, for the region size it names:
  what the verifier runs before it trusts `public.txt`.  `-` reads stdin.
- `composed check PUBLIC TABLE...` checks tables the prover wrote with
  `CompM.checkC`, for the statement's formula.  `ACCEPT` means the bits
  the table's memory sets and the witness its region holds are accepted by
  the formula's statement and read back as a realizer of the formula
  (`CompM.checkC_realizes`).

**A formula**, on one line, in prefix form: `A <V> <x>` an atom, `& F G`,
`| F G` (terms in prefix form, `` ` `` for application).
**`public.txt`**: `formula …`, `W <size>`, `bits <n>`, `roots r₀ …`,
`nil <address>`, `hd stk ctr`, then `ctr` cells, one per line, a bit or
region cell as `W`.  The blanks stand for literal Scott Booleans (the bits,
`K` or `K I`) and well-formed cells (the region), which the check and the
circuit enforce; `CompM.cMachine_public` covers every such fill.
**A witness**: `n` lines, `0` or `1`, then `W` cells.
**A table**: the `formula` and `W` lines, then the number of memory cells
and the cells, then `ends k` and `k` row indices, then the number of rows
and `hd stk ctr` per row.
-/

open Mach Compose CompM WitEx ComposeEx

def termText : Term → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .app f a => "`" ++ termText f ++ termText a

def parseTermF : Nat → List Char → Option (Term × List Char)
  | 0, _ => none
  | _ + 1, 'S' :: r => some (.S, r)
  | _ + 1, 'K' :: r => some (.K, r)
  | _ + 1, 'I' :: r => some (.I, r)
  | n + 1, '`' :: r => do
    let (f, r1) ← parseTermF n r
    let (a, r2) ← parseTermF n r1
    some (.app f a, r2)
  | _ + 1, _ => none

def parseTerm (s : String) : Option Term :=
  match parseTermF (s.length + 1) s.toList with
  | some (t, []) => some t
  | _ => none

def formulaText : MF → String
  | .atom V x => s!"A {termText V} {termText x}"
  | .and A B => s!"& {formulaText A} {formulaText B}"
  | .or A B => s!"| {formulaText A} {formulaText B}"

def parseFormulaF : Nat → List String → Option (MF × List String)
  | 0, _ => none
  | _ + 1, "A" :: v :: x :: r => do some (.atom (← parseTerm v) (← parseTerm x), r)
  | n + 1, "&" :: r => do
    let (a, r1) ← parseFormulaF n r
    let (b, r2) ← parseFormulaF n r1
    some (.and a b, r2)
  | n + 1, "|" :: r => do
    let (a, r1) ← parseFormulaF n r
    let (b, r2) ← parseFormulaF n r1
    some (.or a b, r2)
  | _ + 1, _ => none

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def parseFormula (ws : List String) : Option MF :=
  match parseFormulaF (ws.length + 1) ws with
  | some (m, []) => some m
  | _ => none

def cellText : Cell → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .nil => "N"
  | .app f x => s!"A {f} {x}"
  | .cons x r => s!"C {x} {r}"
  | .atom n => s!"X {n}"

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

/-- The region holding `w` at its last cell, after `N` bit cells: filler `S`
    cells, then `w`'s cells, children first, at their absolute addresses. -/
def regionOf' (N W : Nat) (w : Term) : Option (List Cell) :=
  let pre := List.replicate (N + 3) Cell.S
  let n := (build pre w).1.length - (N + 3)
  if n ≤ W then some ((build (pre ++ List.replicate (W - n) .S) w).1.drop (N + 3)) else none

/-- **The statement** of a formula and a region size: `public.txt`.  The
    heap is the composed machine's with the bit cells and the region blank;
    by `CompM.cMachine_public` it states the machine for every witness of
    that size. -/
def publicText (M : MF) (W : Nat) : String := Id.run do
  let shp := clear M
  let N := BT.nleaves shp
  let region := List.replicate W Cell.S
  let m := cMachine (fun _ => false) shp region (stmtOf M)
  let roots := (cHeap (fun _ => false) shp region (stmtOf M)).2
  let mut s := s!"formula {formulaText M}\nW {W}\nbits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

def statementOfText (text : String) : Option (MF × Nat) := do
  let ls := text.splitOn "\n"
  let M ← match words (ls.getD 0 "") with
    | "formula" :: ws => parseFormula ws
    | _ => none
  let W ← match words (ls.getD 1 "") with
    | ["W", n] => n.toNat?
    | _ => none
  if 0 < W && text == publicText M W then some (M, W) else none

def bitList (β : BT) : List Bool :=
  match β with
  | .leaf b => [b]
  | .node l r => bitList l ++ bitList r

def witnessText (bits : List Bool) (region : List Cell) : String :=
  bits.foldl (fun s b => s ++ (if b then "1" else "0") ++ "\n") "" ++
    region.foldl (fun s c => s ++ cellText c ++ "\n") ""

/-- The examples: name, formula, region size, the honest bits and witness,
    and a witness a set atom's verifier rejects. -/
def examples : List (String × MF × Nat × BT × Term × Term) :=
  [("or", negOr, 64, bitsL, witL, pairT I K),
   ("and", .and (.atom negV x0) (.atom satV x0), 64, .node (.leaf true) (.leaf true),
     pairT negW satW, pairT negW (triple T T T))]

def emit (dir : String) : IO UInt32 := do
  for (name, M, W, β, w, bad) in examples do
    let d := s!"{dir}/{name}"
    IO.FS.createDirAll d
    let N := BT.nleaves (clear M)
    let some good := regionOf' N W w | do IO.println s!"{name}: the witness does not fit"; return 1
    let some wrong := regionOf' N W bad | do IO.println s!"{name}: the wrong witness does not fit"; return 1
    let bits := bitList β
    IO.FS.writeFile s!"{d}/public.txt" (publicText M W)
    IO.FS.writeFile s!"{d}/witness.txt" (witnessText bits good)
    IO.FS.writeFile s!"{d}/witness_clear.txt" (witnessText (bits.map fun _ => false) good)
    IO.FS.writeFile s!"{d}/witness_wrong.txt" (witnessText bits wrong)
    IO.FS.writeFile s!"{d}/witness_forged.txt"
      (witnessText bits (good.set 0 (.app (N + 3 + W - 1) (N + 3 + W - 1))))
    -- A bit cell that is no Boolean: the prover writes `I` in the first.
    IO.FS.writeFile s!"{d}/witness_nonbool.txt" ("I\n" ++ witnessText (bits.drop 1) good)
    let m := cMachine (fun n => bits.getD n false) (clear M) good (stmtOf M)
    IO.println s!"{name}: {N} bits, region {W} cells, {(stmtOf M).length} segments; heap {m.heap.length} cells"
  return 0

def statement (path : String) : IO UInt32 := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  match statementOfText text with
  | some (M, W) =>
    IO.println s!"STATEMENT {path}: the formula {formulaText M}, a region of {W} cells"
    return 0
  | none =>
    IO.println s!"NOT A STATEMENT {path}"
    return 1

def parseTable (ls : List String) :
    Option (MF × Nat × Array Cell × Array Nat × Array Air.Row) := do
  match ls with
  | fl :: wl :: nl :: rest =>
    let M ← match words fl with
      | "formula" :: ws => parseFormula ws
      | _ => none
    let W ← match words wl with
      | ["W", n] => n.toNat?
      | _ => none
    let n ← nl.trimAscii.toString.toNat?
    let cells ← (rest.take n).mapM (fun l => parseCell (words l))
    if cells.length != n then none
    match rest.drop n with
    | el :: rest2 =>
      let k ← match words el with
        | ["ends", k] => k.toNat?
        | _ => none
      let ends ← (rest2.take k).mapM (fun l => l.trimAscii.toString.toNat?)
      if ends.length != k then none
      match rest2.drop k with
      | rl :: rest3 =>
        let r ← rl.trimAscii.toString.toNat?
        let rows ← (rest3.take r).mapM (fun l => parseRow (words l))
        if rows.length != r then none
        if !(rest3.drop r).isEmpty then none
        some (M, W, cells.toArray, ends.toArray, rows.toArray)
      | [] => none
    | [] => none
  | _ => none

def formulaEq : MF → MF → Bool
  | .atom V x, .atom V' x' => V == V' && x == x'
  | .and A B, .and A' B' => formulaEq A A' && formulaEq B B'
  | .or A B, .or A' B' => formulaEq A A' && formulaEq B B'
  | _, _ => false

def check (pub : String) (paths : List String) : IO UInt32 := do
  let some (M, W) := statementOfText (← IO.FS.readFile pub)
    | do IO.println s!"NOT A STATEMENT {pub}"; return 1
  let mut bad := 0
  for path in paths do
    let text ← match ← (IO.FS.readFile path).toBaseIO with
      | .ok t => pure t
      | .error _ => pure ""
    let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    match parseTable ls with
    | none =>
      IO.println s!"MALFORMED {path}"
      bad := bad + 1
    | some (M', W', A, ends, R) =>
      if !formulaEq M' M || W' != W then
        IO.println s!"REJECT {path} (not the statement of {pub})"
        bad := bad + 1
      else if checkC (clear M) W (stmtOf M) A ends R then
        IO.println s!"ACCEPT {path}: its bits and witness read back as a realizer of the formula ({R.size} rows, {A.size} cells, {ends.size} segments)"
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
    IO.eprintln "usage: composed emit DIR | composed statement PUBLIC | composed check PUBLIC TABLE..."
    return 2
