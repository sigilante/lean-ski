import Ski.Circuit.Base
open Term

/-!
`lake exe circuit compare FILE`: the Rust circuit against the Lean one
(`-` reads standard input; the verifier pipes its AIRs so).

`FILE` is `ski-air export-base TERM`'s output: the three AIRs the verifier
builds for `TERM`, as Plonky3's symbolic builder records them
(`bench/plonky3/src/export.rs`).  This parses them and checks, AIR by AIR,
that they are `Circuit.baseAirs` for the term: the same names, widths and
preprocessed tables, and constraint for constraint and message for message
the same normal forms (`Circuit.sameAirB`, so the same meaning,
`Circuit.sameAirB_sound`).  `MATCH` means the verifier runs the circuit
the Lean proofs are about: `sameAirsB` holds of the parsed export and
`Circuit.baseAirs`, the hypothesis of `Circuit.export_sound` (accepted
tables decode to a run of `Air.Accepts`) and `Circuit.export_complete`
(every evaluation within the bounds has accepted tables).

Trusted here: this parser, the compiled evaluation of `sameAirsB`, and
Plonky3's symbolic builder recording what its verifier checks.
-/

open Circuit

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

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

/-- A leaf token: `m<o>.<i>`, `p<o>.<i>`, `F`, `L`, `T`, `c<v>`. -/
def parseLeaf (w : String) : Option E :=
  match w.toList with
  | ['F'] => some (.atom .first)
  | ['L'] => some (.atom .last)
  | ['T'] => some (.atom .trans)
  | 'c' :: v => do
    let n ← (String.ofList v).toNat?
    if n < P then some (.const (ofN n)) else none
  | 'm' :: rest => do
    match (String.ofList rest).splitOn "." with
    | [o, i] => some (.atom (.main (← o.toNat?) (← i.toNat?)))
    | _ => none
  | 'p' :: rest => do
    match (String.ofList rest).splitOn "." with
    | [o, i] => some (.atom (.pre (← o.toNat?) (← i.toNat?)))
    | _ => none
  | _ => none

/-- An expression in prefix form. -/
def parseEF : Nat → List String → Option (E × List String)
  | 0, _ => none
  | n + 1, "+" :: r => do
    let (a, r1) ← parseEF n r
    let (b, r2) ← parseEF n r1
    some (.add a b, r2)
  | n + 1, "-" :: r => do
    let (a, r1) ← parseEF n r
    let (b, r2) ← parseEF n r1
    some (.sub a b, r2)
  | n + 1, "*" :: r => do
    let (a, r1) ← parseEF n r
    let (b, r2) ← parseEF n r1
    some (.mul a b, r2)
  | n + 1, "n" :: r => do
    let (a, r1) ← parseEF n r
    some (.neg a, r1)
  | _ + 1, w :: r => do some (← parseLeaf w, r)
  | _ + 1, [] => none

def parseE (s : String) : Option E :=
  let ws := words s
  match parseEF (ws.length + 1) ws with
  | some (e, []) => some e
  | _ => none

def parseInter (l : String) : Option Inter := do
  match l.splitOn " ; " with
  | head :: fields =>
    match words head with
    | bus :: w :: count =>
      some ⟨bus, ← w.toNat?, ← parseE (" ".intercalate count), ← fields.mapM parseE⟩
    | _ => none
  | [] => none

def parseRowF (l : String) : Option (List F) :=
  (words l).mapM fun w => do
    let n ← w.toNat?
    if n < P then some (ofN n) else none

/-- One AIR from the export's lines, and the lines after it. -/
def parseAir (ls : List String) : Option (AirD × List String) := do
  match ls with
  | al :: wl :: cl :: rest =>
    let name ← match words al with
      | ["air", n] => some n
      | _ => none
    let (width, pre) ← match words wl with
      | ["width", w, "pre", p] => do some (← w.toNat?, ← p.toNat?)
      | _ => none
    let nc ← match words cl with
      | ["constraints", n] => n.toNat?
      | _ => none
    let cons ← (rest.take nc).mapM parseE
    if cons.length != nc then none
    match rest.drop nc with
    | il :: rest2 =>
      let ni ← match words il with
        | ["interactions", n] => n.toNat?
        | _ => none
      let inters ← (rest2.take ni).mapM parseInter
      if inters.length != ni then none
      match rest2.drop ni with
      | pl :: rest3 =>
        let np ← match words pl with
          | ["pretrace", n] => n.toNat?
          | _ => none
        let pt ← (rest3.take np).mapM parseRowF
        if pt.length != np then none
        some (⟨name, width, pre, cons, inters, pt⟩, rest3.drop np)
      | [] => none
    | [] => none
  | _ => none

def parseAirs : Nat → List String → Option (List AirD)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, ls => do
    let (a, rest) ← parseAir ls
    let as ← parseAirs n rest
    some (a :: as)

/-- Where two AIRs first differ, if they do. -/
def diffAir (a b : AirD) : Option String :=
  if a.name != b.name then some s!"names {a.name} and {b.name}"
  else if a.width != b.width then some s!"widths {a.width} and {b.width}"
  else if a.pre != b.pre then some s!"preprocessed widths {a.pre} and {b.pre}"
  else if a.cons.length != b.cons.length then some s!"{a.cons.length} and {b.cons.length} constraints"
  else match (List.range a.cons.length).find? (fun i => (a.cons.getD i (.const 0)).norm != (b.cons.getD i (.const 0)).norm) with
    | some i => some s!"constraint {i}"
    | none =>
      if a.inters.length != b.inters.length then some s!"{a.inters.length} and {b.inters.length} interactions"
      else match (List.range a.inters.length).find? (fun i => !interEqB (a.inters.getD i ⟨"", 0, .const 0, []⟩)
          (b.inters.getD i ⟨"", 0, .const 0, []⟩)) with
        | some i => some s!"interaction {i}"
        | none => if a.pretrace != b.pretrace then some "preprocessed tables" else none

def compare (path : String) : IO UInt32 := do
  let text ← if path == "-" then (do let h ← IO.getStdin; h.readToEnd) else IO.FS.readFile path
  let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let some t := (match ls with
      | l :: _ => match words l with
        | ["term", s] => parseTerm s
        | _ => none
      | [] => none) | do IO.println "MALFORMED: no term"; return 1
  let some rust := parseAirs (ls.length + 1) (ls.drop 1) | do IO.println "MALFORMED AIRS"; return 1
  let lean := baseAirs t
  if rust.length != lean.length then
    IO.println s!"DIFFER: {rust.length} AIRs, Lean has {lean.length}"
    return 1
  let mut bad := 0
  for (r, l) in rust.zip lean do
    match diffAir r l with
    | none => IO.println s!"MATCH {r.name}: {r.cons.length} constraints, {r.inters.length} interactions"
    | some d =>
      IO.println s!"DIFFER {r.name}: {d}"
      bad := bad + 1
  if bad == 0 && sameAirsB rust lean then
    IO.println "MATCH: the Rust circuit is the Lean circuit, constraint for constraint"
    return 0
  else
    IO.println "DIFFER"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compare", path] => compare path
  | _ =>
    IO.eprintln "usage: circuit compare FILE|-"
    return 2
