import Ski.AirCheckOpen
open Term

/-!
Check tables produced outside Lean against the AIR.  Each argument is a
table file in the format of `Ski/AirCheck.lean`; for each, print `ACCEPT`
or `REJECT` and the file name.  The verdict is `Air.checkA`, which decides
the AIR's constraints (`Air.checkA_iff`): `ACCEPT` means the table
satisfies `Air.Accepts`, so it proves the evaluation it ends on
(`Air.checkB_eval`), and `REJECT` means it does not.

A term may hold atoms, `Xi` in prefix form (`X i` as a memory cell).
Such a table is decided by `Air.checkOA` from the open term's load: an
accepted one ends on an open head reduct of the term, for every value of
its atoms (`Air.checkOA_close`), and prints `ACCEPT … open, N atoms`.

Run with `lake build aircheck && lake exe aircheck TABLE...`.
-/

/-- A term in prefix form, `` ` `` for application and `Xi` for the atom `i`. -/
partial def parseTerm (s : List Char) : Option (OTerm × List Char) :=
  match s with
  | 'S' :: r => some (.S, r)
  | 'K' :: r => some (.K, r)
  | 'I' :: r => some (.I, r)
  | 'X' :: r =>
    let ds := r.takeWhile Char.isDigit
    if ds.isEmpty then none
    else (String.ofList ds).toNat?.map fun n => (.var n, r.drop ds.length)
  | '`' :: r =>
    match parseTerm r with
    | some (f, r1) =>
      match parseTerm r1 with
      | some (a, r2) => some (.app f a, r2)
      | none => none
    | none => none
  | _ => none

/-- The term, when it has no atoms. -/
def closedTerm : OTerm → Option Term
  | .S => some .S
  | .K => some .K
  | .I => some .I
  | .var _ => none
  | .app f a => do some (.app (← closedTerm f) (← closedTerm a))

/-- The atoms of a term, each once. -/
def atomsOf : OTerm → List Nat
  | .var n => [n]
  | .app f a => (atomsOf f ++ atomsOf a).eraseDups
  | _ => []

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

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def parseTable (ls : List String) : Option (OTerm × Array Cell × List Air.Row) := do
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

def main (args : List String) : IO UInt32 := do
  let mut bad := 0
  for path in args do
    let text ← IO.FS.readFile path
    let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
    match parseTable ls with
    | none =>
      IO.println s!"MALFORMED {path}"
      bad := bad + 1
    | some (t, M, rows) =>
      match closedTerm t with
      | some c =>
        if Air.checkA M c rows then
          IO.println s!"ACCEPT {path} ({rows.length} rows, {M.size} cells)"
        else
          IO.println s!"REJECT {path}"
          bad := bad + 1
      | none =>
        if Air.checkOA M t rows then
          IO.println s!"ACCEPT {path} ({rows.length} rows, {M.size} cells; open, {(atomsOf t).length} atoms)"
        else
          IO.println s!"REJECT {path}"
          bad := bad + 1
  return (if bad == 0 then 0 else 1)
