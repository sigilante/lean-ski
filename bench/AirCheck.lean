import Ski.AirCheck
open Term

/-!
Check tables produced outside Lean against the AIR.  Each argument is a
table file in the format of `Ski/AirCheck.lean`; for each, print `ACCEPT`
or `REJECT` and the file name.  The verdict is `Air.checkA`, which decides
the AIR's constraints (`Air.checkA_iff`): `ACCEPT` means the table
satisfies `Air.Accepts`, so it proves the evaluation it ends on
(`Air.checkB_eval`), and `REJECT` means it does not.

Run with `lake build aircheck && lake exe aircheck TABLE...`.
-/

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

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

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
      if Air.checkA M t rows then
        IO.println s!"ACCEPT {path} ({rows.length} rows, {M.size} cells)"
      else
        IO.println s!"REJECT {path}"
        bad := bad + 1
  return (if bad == 0 then 0 else 1)
