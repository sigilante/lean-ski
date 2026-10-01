import Ski.Composed
import Ski.ComposedJ
import Ski.ComposedText
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
  composed machine of the statement it names, a formula or a predicate over
  literal bits (`ComposedText.CStmt`), for the region size and heights it
  names: what the verifier runs before it trusts `public.txt`.  `-` reads
  stdin.
- `composed check PUBLIC TABLE...` checks tables the prover wrote with
  `CompM.checkC`, for the statement.  For a formula, `ACCEPT` means the
  bits the table's memory sets and the witness its region holds are
  accepted by the formula's statement and read back as a realizer of the
  formula (`CompM.checkC_realizes`); for a predicate, that its verifier
  accepts the bits (`Circuit.checkPred_sound`).

**A formula**, on one line, in prefix form: `A <V> <x>` an atom, `& F G`,
`| F G` (terms in prefix form, `` ` `` for application).
**A predicate**: `predicate <V> <x> <n>`, the verifier `V` of `x` over `n`
literal bits (`Ski/Predicate.lean`).
**`public.txt`**: `formula …` or `predicate …`, `W <size>`, optionally
`log R M`, `bits <n>`, `roots r₀ …`,
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

open ComposedText

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
  | some (c, W, lg) =>
    IO.println s!"STATEMENT {path}: {c.header}, a region of {W} cells, heights 2^{lg.1} and 2^{lg.2}"
    return 0
  | none =>
    IO.println s!"NOT A STATEMENT {path}"
    return 1

def parseTable (ls : List String) :
    Option (CStmt × Nat × Array Cell × Array Nat × Array Air.Row) := do
  match ls with
  | fl :: wl :: nl :: rest =>
    let M ← parseHeader (words fl)
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

def stmtEq : CStmt → CStmt → Bool
  | .formula M, .formula M' => formulaEq M M'
  | .pred V x n, .pred V' x' n' => V == V' && x == x' && n == n'
  | _, _ => false

def check (pub : String) (paths : List String) : IO UInt32 := do
  let some (c, W, _) := statementOfText (← IO.FS.readFile pub)
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
      if !stmtEq M' c || W' != W then
        IO.println s!"REJECT {path} (not the statement of {pub})"
        bad := bad + 1
      else if checkC c.shp W c.Ps A ends R then
        match c with
        | .formula _ =>
          IO.println s!"ACCEPT {path}: its bits and witness read back as a realizer of the formula ({R.size} rows, {A.size} cells, {ends.size} segments)"
        | .pred _ _ n =>
          IO.println s!"ACCEPT {path}: the predicate accepts its {n} bits ({R.size} rows, {A.size} cells, {ends.size} segments)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- `composed check-cj SRC PUBLIC TABLE…`: the composed checker with jets
    (`CompM.checkCJ`, sound by `CompM.checkCJ_sound`), with the statement's
    jet table as Lean computes it from the templates of the SKIjack source
    `SRC` (`Air.jetTableC`). -/
def checkCJ (src pub : String) (paths : List String) : IO UInt32 := do
  let some (c, W, _) := statementOfText (← IO.FS.readFile pub)
    | do IO.println s!"NOT A STATEMENT {pub}"; return 1
  let tmpls := JetTable.fileTemplates ((← IO.FS.readFile src).toList.map Char.toNat)
  let (roots, jets) := Air.jetTableC c.shp W c.Ps tmpls
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
      if !stmtEq M' c || W' != W then
        IO.println s!"REJECT {path} (not the statement of {pub})"
        bad := bad + 1
      else if CompM.checkCJ c.shp W c.Ps roots jets A ends R then
        IO.println s!"ACCEPT {path}: every term evaluates to K on its bits and witness, with jets ({R.size} rows, {A.size} cells, {ends.size} segments, {roots.length} roots)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["statement", pub] => statement pub
  | "check" :: pub :: paths => check pub paths
  | "check-cj" :: src :: pub :: paths => checkCJ src pub paths
  | _ =>
    IO.eprintln "usage: composed emit DIR | composed statement PUBLIC | composed check PUBLIC TABLE... | composed check-cj SRC PUBLIC TABLE..."
    return 2
