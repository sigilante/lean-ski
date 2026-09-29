import Ski.WitnessExamples
open Term

/-!
Statements over a hidden term, for the Plonky3 prover, and the check of
their tables (`Ski/Witness.lean`).

- `witness emit DIR` writes, for each example atom (`neg`, `sat`,
  `Ski/WitnessExamples.lean`), `DIR/<name>/`: `public.txt`, the witness
  machine with the region blank, which the verifier sees; `witness.txt`,
  the region of the honest realizer, which only the prover sees; and
  two regions for the tamper tests: `witness_wrong.txt`, a well-formed
  region holding a term that fails the atom, and `witness_forged.txt`,
  the honest region with its first cell an application pointing forward,
  which the run never reads.
- `witness statement PUBLIC` checks that a statement file is exactly the
  witness machine of the atom it names, for the region size it names:
  what the verifier must check before it trusts `public.txt`.  `-` reads
  stdin.
- `witness check PUBLIC TABLE...` checks tables the prover wrote with
  `Wit.witCheck`, against the statement's atom and region size.  `ACCEPT`
  means the table's region holds a realizer of the atom
  (`Wit.witCheck_realizes`).

**`public.txt`**: `V <term>`, `x <term>` (prefix form, `` ` `` for
application), `W <size>`, then `hd stk ctr`, then `ctr` cells, one per
line, a region cell as `W`.  **A region**: `W` cells, one per line.
**A table**: the `V`, `x` and `W` lines, then the number of memory cells
and the cells, then the number of rows and `hd stk ctr` per row.
-/

open Mach Wit WitEx

def termText : Term → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .app f a => "`" ++ termText f ++ termText a

/-- A term in prefix form, with fuel for the recursion. -/
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

/-- The region holding `w` at its last cell: filler `S` cells, then `w`'s
    cells, children first.  `none` when `w` does not fit in `W` cells. -/
def regionOf (W : Nat) (w : Term) : Option (List Cell) :=
  let n := (build [] w).1.length
  if n ≤ W then some (build (List.replicate (W - n) .S) w).1 else none

/-- **The statement** of an atom and a region size: `public.txt`.  The heap
    is the witness machine's with the region blank; by
    `Wit.wMachine_public` it states the machine for every region of that
    size. -/
def publicText (V x : Term) (W : Nat) : String := Id.run do
  let m := wMachine (List.replicate W .S) (V ⬝ x)
  let mut s := s!"V {termText V}\nx {termText x}\nW {W}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if i < W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- The atom and region size a statement names, if the text is exactly
    their statement. -/
def statementOfText (text : String) : Option (Term × Term × Nat) := do
  let ls := text.splitOn "\n"
  let V ← match words (ls.getD 0 "") with
    | ["V", t] => parseTerm t
    | _ => none
  let x ← match words (ls.getD 1 "") with
    | ["x", t] => parseTerm t
    | _ => none
  let W ← match words (ls.getD 2 "") with
    | ["W", n] => n.toNat?
    | _ => none
  if 0 < W && text == publicText V x W then some (V, x, W) else none

def regionText (ws : List Cell) : String :=
  ws.foldl (fun s c => s ++ cellText c ++ "\n") ""

/-- The examples: name, verifier, input, region size, the honest realizer,
    and a term that fails the atom (`neg_not_I`, `sat_not_TTT`). -/
def examples : List (String × Term × Term × Nat × Term × Term) :=
  [("neg", negV, x0, 32, negW, I), ("sat", satV, x0, 32, satW, triple T T T)]

def emit (dir : String) : IO UInt32 := do
  for (name, V, x, W, w, bad) in examples do
    let d := s!"{dir}/{name}"
    IO.FS.createDirAll d
    let some good := regionOf W w | do IO.println s!"{name}: the witness does not fit"; return 1
    let some wrong := regionOf W bad | do IO.println s!"{name}: the wrong witness does not fit"; return 1
    -- The honest region with its first cell pointing forward: never read.
    let forged := good.set 0 (.app (W - 1) (W - 1))
    IO.FS.writeFile s!"{d}/public.txt" (publicText V x W)
    IO.FS.writeFile s!"{d}/witness.txt" (regionText good)
    IO.FS.writeFile s!"{d}/witness_wrong.txt" (regionText wrong)
    IO.FS.writeFile s!"{d}/witness_forged.txt" (regionText forged)
    let m := wMachine good (V ⬝ x)
    IO.println s!"{name}: region {W} cells (witness {(build [] w).1.length}); heap {m.heap.length} cells"
  return 0

def statement (path : String) : IO UInt32 := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  match statementOfText text with
  | some (V, x, W) =>
    IO.println s!"STATEMENT {path}: a realizer of atom {termText V} {termText x}, in {W} cells"
    return 0
  | none =>
    IO.println s!"NOT A STATEMENT {path}"
    return 1

/-- A table: its statement lines, the memory and the rows. -/
def parseTable (ls : List String) : Option (Term × Term × Nat × Array Cell × List Air.Row) := do
  match ls with
  | vl :: xl :: wl :: nl :: rest =>
    let V ← match words vl with
      | ["V", t] => parseTerm t
      | _ => none
    let x ← match words xl with
      | ["x", t] => parseTerm t
      | _ => none
    let W ← match words wl with
      | ["W", n] => n.toNat?
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
      some (V, x, W, cells.toArray, rows)
    | [] => none
  | _ => none

def check (pub : String) (paths : List String) : IO UInt32 := do
  let some (V, x, W) := statementOfText (← IO.FS.readFile pub)
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
    | some (V', x', W', A, rows) =>
      if V' != V || x' != x || W' != W then
        IO.println s!"REJECT {path} (not the statement of {pub})"
        bad := bad + 1
      else if witCheck (V ⬝ x) W A rows then
        IO.println s!"ACCEPT {path}: its region holds a realizer of atom {termText V} {termText x} ({rows.length} rows, {A.size} cells)"
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
    IO.eprintln "usage: witness emit DIR | witness statement PUBLIC | witness check PUBLIC TABLE..."
    return 2
