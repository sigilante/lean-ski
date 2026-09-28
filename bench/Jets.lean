import Ski.JetTable
open Term

/-!
The jet tables of the corpus, for the Plonky3 prover, and the check of its
jetted tables.

- `jets emit DIR` writes, for each corpus row, `DIR/<row>.jets`: the
  licensed roots and the jets of its loaded term (`JetTable.jetTable`),
  which the prover's preprocessed ROOTS, HEADER and TEMPLATE tables hold.
- `jets statement CORPUS DIR` checks, for each term the Plonky3 verifier
  will prove (the lines of `CORPUS`), that `DIR/<name>.jets` is exactly
  that term's jet file and that its roots are licensed (`Air.rootsOKB`):
  what the verifier runs before it builds its preprocessed tables.
- `jets check TABLE...` checks jetted tables the prover wrote, in the
  format of `Ski/AirCheck.lean`: it recomputes the roots and jets from the
  table's term and runs `Air.checkJA`.  `ACCEPT` means the table satisfies
  `Air.AcceptsJ` with licensed roots, so it proves the evaluation it ends
  on, up to weak reduction of the value, with the value's head and arity
  (`Air.checkJA_sound`, `Air.air_sound_jet`).

**`<row>.jets`**: `roots R`, then `R` lines `address jet`; `jets G`, then
per jet a line `k n root` (arity, cells written, root operand) and `n`
lines, one per cell in `ibuild` order: a tag (`0 1 2` for `S K I`), or
`3 a b` for an application, whose operands are `L j` (the cell this
instantiation wrote at offset `j`), `A i` (the `i`-th argument) or `G a`
(the public cell at `a`).
-/

open Mach JetTable Air

partial def parseTerm (s : List Char) : Option (Term × List Char) :=
  match s with
  | 'S' :: r => some (.S, r)
  | 'K' :: r => some (.K, r)
  | 'I' :: r => some (.I, r)
  | '`' :: r =>
    match parseTerm r with
    | some (f, r1) =>
      match parseTerm r1 with
      | some (a, r2) => some (.app f a, r2)
      | none => none
    | none => none
  | _ => none

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def parseCell (ws : List String) : Option Cell :=
  match ws with
  | ["S"] => some .S
  | ["K"] => some .K
  | ["I"] => some .I
  | ["N"] => some .nil
  | ["A", f, x] => do some (.app (← f.toNat?) (← x.toNat?))
  | ["C", x, r] => do some (.cons (← x.toNat?) (← r.toNat?))
  | _ => none

def parseRow (ws : List String) : Option Air.Row :=
  match ws with
  | [h, s, c] => do some ⟨← h.toNat?, ← s.toNat?, ← c.toNat?⟩
  | _ => none

def parseTable (ls : List String) : Option (Term × Array Cell × List Air.Row) := do
  match ls with
  | tl :: nl :: rest =>
    let (t, r) ← parseTerm tl.trimAscii.toString.toList
    if !r.isEmpty then none
    let n ← nl.trimAscii.toString.toNat?
    let cells ← (rest.take n).mapM (fun l => parseCell (words l))
    if cells.length != n then none
    match rest.drop n with
    | kl :: rest2 =>
      let k ← kl.trimAscii.toString.toNat?
      let rows ← (rest2.take k).mapM (fun l => parseRow (words l))
      if rows.length != k then none
      if !(rest2.drop k).isEmpty then none
      some (t, cells.toArray, rows)
    | [] => none
  | _ => none

/-- **The jet file** of a term: what the prover's preprocessed tables hold. -/
def jetFile (t : Term) (tmpls : List (List Nat × OTerm)) : String × Nat × Nat := Id.run do
  let (roots, jets) := jetTable (load t).heap tmpls
  let mut s := s!"roots {roots.length}\n"
  for (a, g) in roots do
    s := s ++ s!"{a} {g}\n"
  s := s ++ s!"jets {jets.length}\n"
  for J in jets do
    s := s ++ jetText J
  return (s, roots.length, jets.length)

def emit (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  let tmpls := allTemplates
  for row in corpus do
    let (s, r, g) := jetFile row.term tmpls
    IO.FS.writeFile s!"{dir}/{row.name}.jets" s
    IO.println s!"{row.name}: {r} roots, {g} jets"
  return 0

/-- **The verifier's check of the jet files**, for the terms it proves.
    Each line of `corpus` (`name steps term`, `bench/Dump.lean`'s format)
    names a term and the file `DIR/<name>.jets` the verifier will build its
    preprocessed tables from; that file must be exactly the jet file of that
    term, and its roots must pass `Air.rootsOKB` over the term's loaded
    heap, which gives `Air.RootsOK` (`Air.rootsOKB_sound`), the hypothesis
    of `Air.air_sound_jet`.  Keyed by the verifier's own terms, not by
    Lean's corpus names: a file for any other name or term is checked the
    same way or refused. -/
def statement (corpusPath dir : String) : IO UInt32 := do
  let tmpls := allTemplates
  let text ← IO.FS.readFile corpusPath
  let mut bad := 0
  let mut n := 0
  for line in (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty) do
    match words line with
    | [name, _, termText] =>
      match parseTerm termText.toList with
      | some (t, []) =>
        n := n + 1
        let path := s!"{dir}/{name}.jets"
        let (expected, roots, jets) := jetTable' t tmpls
        let licensed := rootsOKB (load t).heap roots jets
        match ← (IO.FS.readFile path).toBaseIO with
        | .ok given =>
          if given == expected && licensed then IO.println s!"STATEMENT {path}"
          else
            IO.println s!"NOT THE JET FILE {path}"
            bad := bad + 1
        | .error _ =>
          IO.println s!"MISSING {path}"
          bad := bad + 1
      | _ =>
        IO.println s!"MALFORMED TERM {name}"
        bad := bad + 1
    | _ =>
      IO.println s!"MALFORMED LINE {line}"
      bad := bad + 1
  if n == 0 then
    IO.println "NO TERMS"
    bad := bad + 1
  return (if bad == 0 then 0 else 1)
where
  jetTable' (t : Term) (tmpls : List (List Nat × OTerm)) : String × List (Nat × Nat) × List Jet :=
    let (roots, jets) := jetTable (load t).heap tmpls
    ((jetFile t tmpls).1, roots, jets)

def check (paths : List String) : IO UInt32 := do
  let tmpls := allTemplates
  let mut bad := 0
  for path in paths do
    let text ← IO.FS.readFile path
    let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    match parseTable ls with
    | none =>
      IO.println s!"MALFORMED {path}"
      bad := bad + 1
    | some (t, A, rows) =>
      let m := load t
      let (roots, jets) := jetTable m.heap tmpls
      if checkJA A m roots jets rows then
        IO.println s!"ACCEPT {path} ({rows.length} rows, {A.size} cells, {roots.length} roots)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["statement", corpus, dir] => statement corpus dir
  | "check" :: paths => check paths
  | _ =>
    IO.eprintln "usage: jets emit DIR | jets statement CORPUS DIR | jets check TABLE..."
    return 2
