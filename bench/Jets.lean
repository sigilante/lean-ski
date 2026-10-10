import Ski.JetTable
import Ski.AirProbe
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
- `jets plan OUTCOME` prints the probe plan of an outcome
  (`Air.planOf (Probe.toV o) 0`): what the prover's preprocessed PLAN table
  holds.  An outcome is `err`, or `val` and the stack's numbers, top first,
  in plain decimal.  A number's probe tree is unary, so plans are capped
  at 65,536 segments: a larger outcome gets no plan, not a hung Lean.
- `jets check-probe TABLE OUTCOME` checks a table with probe segments:
  the format above, then `starts N` and `N` lines, the segments' start
  rows and the last row, then `fields n` and `n` lines `a p1 … pa`, each
  segment's fields.  It runs `Air.checkPA` for the outcome's plan.
  `ACCEPT` means the table's term decodes to the outcome
  (`Air.checkPA_decodes`).

**A table certifies its own term**, the one on its first line.  `check`
and `check-probe` name it in `ACCEPT`: the Lean corpus row it equals, or
a term outside the corpus.  A caller who claims something of a given row
binds the table to it: with `--row NAME` first (`jets check --row NAME
TABLE…`, `jets check-probe --row NAME TABLE OUTCOME`), a table whose term
is not that row's is refused before it is checked.

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
  | ["X", n] => do some (.atom (← n.toNat?))
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
  return (tableText roots jets, roots.length, jets.length)

def emit (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  let tmpls := allTemplates
  for row in corpus do
    let (s, r, g) := jetFile row.term tmpls
    IO.FS.writeFile s!"{dir}/{row.name}.jets" s
    IO.println s!"{row.name}: {r} roots, {g} jets"
  return 0

/-- One corpus line (`name steps term`, split on spaces as `words` does)
    and the jet file given for it: `none` when they are the statement (the
    file is exactly the term's jet file, and its roots pass `Air.rootsOKB`
    over the term's loaded heap, which gives `Air.RootsOK` by
    `Air.rootsOKB_sound`, the hypothesis of `Air.air_sound_jet`), and
    otherwise the reason they are not.  A name is an identifier: letters,
    digits, `_`.  The steps field is not checked, and nothing is claimed
    about it. -/
def checkLine (tmpls : List (List Nat × OTerm)) (line : String) (given : Option String) :
    Option String :=
  match words line with
  | [name, _, termText] =>
    if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '_') then
      some s!"MALFORMED NAME {name}"
    else
      match parseTerm termText.toList with
      | some (t, []) =>
        match given with
        | none => some s!"MISSING {name}"
        | some text =>
          let (roots, jets) := jetTable (load t).heap tmpls
          if text == (jetFile t tmpls).1 && rootsOKB (load t).heap roots jets then none
          else some s!"NOT THE JET FILE {name}"
      | _ => some s!"MALFORMED TERM {name}"
  | _ => some s!"MALFORMED LINE {line}"

/-- **The verifier's check of the jet files**, for the terms it proves:
    each line of `corpus` names a term and the file `DIR/<name>.jets`,
    checked by `checkLine`.  Keyed by the verifier's own terms, not by
    Lean's corpus names. -/
def statement (corpusPath dir : String) : IO UInt32 := do
  let tmpls := allTemplates
  let text ← IO.FS.readFile corpusPath
  let mut bad := 0
  let mut n := 0
  for line in (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty) do
    let name := (words line).headD ""
    let given ← if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '_') then pure none
      else do
        match ← (IO.FS.readFile s!"{dir}/{name}.jets").toBaseIO with
        | .ok t => pure (some t)
        | .error _ => pure none
    n := n + 1
    match checkLine tmpls line given with
    | none => IO.println s!"STATEMENT {dir}/{name}.jets"
    | some why =>
      IO.println why
      bad := bad + 1
  if n == 0 then
    IO.println "NO TERMS"
    bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- The same check, on bytes the verifier sends on stdin: one corpus line,
    a newline, then the jet file.  No file is read, so what is checked is
    exactly what the verifier holds. -/
def statementStdin : IO UInt32 := do
  let text ← (← IO.getStdin).readToEnd
  match text.splitOn "\n" with
  | line :: rest =>
    match checkLine allTemplates line (some ("\n".intercalate rest)) with
    | none =>
      IO.println s!"STATEMENT {(words line).headD ""}"
      return 0
    | some why =>
      IO.println why
      return 1
  | [] =>
    IO.println "NO TERMS"
    return 1

/-- How `ACCEPT` names a table's term: the corpus row it equals, or none. -/
def termName (t : Term) : String :=
  match corpus.find? (fun r => decide (r.term = t)) with
  | some r => s!"corpus row {r.name}"
  | none => "a term outside the corpus"

/-- With `--row NAME`, the table's term must be that corpus row's. -/
def rowBinds (row : Option String) (t : Term) : Except String Unit :=
  match row with
  | none => .ok ()
  | some name =>
    match corpus.find? (fun r => r.name == name) with
    | none => .error s!"NO CORPUS ROW {name}"
    | some r => if decide (r.term = t) then .ok () else .error s!"NOT THE TERM OF {name}"

def check (row : Option String) (paths : List String) : IO UInt32 := do
  let tmpls := allTemplates
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
    | some (t, A, rows) =>
      if let .error why := rowBinds row t then
        IO.println s!"{why} {path}"
        bad := bad + 1
        continue
      let m := load t
      let (roots, jets) := jetTable m.heap tmpls
      if checkJA A m roots jets rows then
        IO.println s!"ACCEPT {path}: {termName t} ({rows.length} rows, {A.size} cells, {roots.length} roots)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- `jets check-src [--eta] SRC TABLE…`: `check`, with the jets the
    templates of the SKIjack source `SRC` license (`JetTable.fileTemplates`;
    with `--eta`, of the source compiled with η-lifting, as a SKIlark
    predicate's is), for a term compiled from a source outside the corpus.  `ACCEPT` means what it means
    for `check` (`Air.checkJA_sound`): the roots are licensed by `rootOKB`,
    whichever templates proposed them. -/
def checkSrc (src : String) (paths : List String) (eta : Bool := false) : IO UInt32 := do
  let tmpls := fileTemplates ((← IO.FS.readFile src).toList.map Char.toNat) eta
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
    | some (t, A, rows) =>
      let m := load t
      let (roots, jets) := jetTable m.heap tmpls
      if checkJA A m roots jets rows then
        IO.println s!"ACCEPT {path}: the source's term ({rows.length} rows, {A.size} cells, {roots.length} roots, {jets.length} jets)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)

/-- An outcome from words: `err`, or `val` and the stack's numbers, top
    first, each in plain decimal, so one outcome has one spelling. -/
def parseOutcome : List String → Option Outcome
  | ["err"] => some .err
  | "val" :: ns => do
    let ns ← ns.mapM decimal
    -- A number `n` takes `n + 1` segments (its probe tree is unary), each
    -- item two more: refuse plans past `maxSegs` before building them.
    if ns.foldl (· + ·) 0 + 3 * ns.length + 2 > maxSegs then none
    some (.val (ns.map Item.num))
  | _ => none
where
  /-- The most segments a plan may have; a table has at most `2^21` rows. -/
  maxSegs : Nat := 65536
  /-- A number in plain decimal: digits only, no leading zero. -/
  decimal (w : String) : Option Nat :=
    if !w.isEmpty && w.all Char.isDigit && (w == "0" || w.front != '0') then w.toNat? else none

/-- A plan, as the prover reads it: `plan n`, then per segment
    `base k ctor arity parent field`. -/
def planText (plan : List Seg) : String :=
  plan.foldl (fun s g => s ++ s!"{g.base} {g.k} {g.ctor} {g.arity} {g.parent} {g.field}\n")
    s!"plan {plan.length}\n"

def planOfOutcome (o : Outcome) : Option (List Seg) := (Probe.toV o).map (planOf · 0)

def plan (ws : List String) : IO UInt32 := do
  match parseOutcome ws >>= planOfOutcome with
  | some p =>
    IO.print (planText p)
    return 0
  | none =>
    IO.println s!"NO PLAN FOR {" ".intercalate ws}"
    return 1

/-- The probe part of a table: the start rows, then the fields. -/
def parseProbe (ls : List String) : Option (Array Nat × Array (List Nat)) := do
  match ls with
  | sl :: rest =>
    let n ← match words sl with
      | ["starts", n] => n.toNat?
      | _ => none
    let starts ← (rest.take n).mapM (fun l => l.trimAscii.toString.toNat?)
    if starts.length != n then none
    match rest.drop n with
    | fl :: rest2 =>
      let m ← match words fl with
        | ["fields", m] => m.toNat?
        | _ => none
      let flds ← (rest2.take m).mapM fun l => do
        match (words l).mapM String.toNat? with
        | some (a :: ps) => if ps.length == a then some ps else none
        | _ => none
      if flds.length != m then none
      if !(rest2.drop m).isEmpty then none
      some (starts.toArray, flds.toArray)
    | [] => none
  | [] => none

def checkProbe (row : Option String) (path : String) (ws : List String) : IO UInt32 := do
  let tmpls := allTemplates
  let some o := parseOutcome ws | do IO.println "MALFORMED OUTCOME"; return 1
  let some pl := planOfOutcome o | do IO.println "NO PLAN FOR THE OUTCOME"; return 1
  let text ← match ← (IO.FS.readFile path).toBaseIO with
    | .ok t => pure t
    | .error _ => do IO.println s!"MALFORMED {path}"; return 1
  let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  -- The table proper ends where `starts` begins.
  let i := ls.findIdx (fun l => (words l).headD "" == "starts")
  match parseTable (ls.take i), parseProbe (ls.drop i) with
  | some (t, A, rows), some (starts, flds) =>
    if let .error why := rowBinds row t then
      IO.println s!"{why} {path}"
      return 1
    let m := load t
    let (roots, jets) := jetTable m.heap tmpls
    if checkPA A t roots jets pl starts flds rows.toArray then
      IO.println s!"ACCEPT {path}: {termName t} decodes to {" ".intercalate ws} ({rows.length} rows, {A.size} cells, {pl.length} segments)"
      return 0
    else
      IO.println s!"REJECT {path}"
      return 1
  | _, _ =>
    IO.println s!"MALFORMED {path}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | "check-src" :: "--eta" :: src :: paths => checkSrc src paths true
  | "check-src" :: src :: paths => checkSrc src paths
  | ["statement", corpus, dir] => statement corpus dir
  | ["statement-stdin"] => statementStdin
  | "check" :: "--row" :: name :: paths => check (some name) paths
  | "check" :: paths => check none paths
  | "plan" :: ws => plan ws
  | "check-probe" :: "--row" :: name :: path :: ws => checkProbe (some name) path ws
  | "check-probe" :: path :: ws => checkProbe none path ws
  | _ =>
    IO.eprintln "usage: jets emit DIR | jets statement CORPUS DIR | jets statement-stdin | jets check [--row NAME] TABLE... | jets check-src [--eta] SRC TABLE...\n       jets plan OUTCOME | jets check-probe [--row NAME] TABLE OUTCOME"
    return 2
