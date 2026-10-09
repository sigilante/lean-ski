import Ski.Circuit.SendsFast

/-!
# Comparing a prover's dumped traces with Lean's tables

The pieces each circuit's comparison uses (`lake exe composed check-*`,
`lake exe sudoku check-*`, `lake exe witness check-*`), for traces a
prover writes as `H W` and then `H` rows of `W` canonical values
(`ski-air *-dump`):

- `parseMatrix`, `loadTrace`, and `asTable`, a dump as a `Table` under an
  AIR's preprocessed columns;
- `cmpRows`, the cells of chosen rows that differ from a model;
- `cmpRowsBy`, the same with a value computed once a row;
- `memModel`, a memory row as the honest memory tables have it, its
  multiplicity from `multArr` (`memTable5_mult`, `memTableC_mult`);
- `checkBlind`, the blinded traces against the unblinded ones blinded at a
  circuit's blocks (`Ski/ZK/Blocks.lean`).
-/

namespace Circuit.TraceCheck

open Circuit

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

/-- A dumped trace: `H W`, then `H` rows of `W` numbers. -/
def parseMatrix (text : String) : Option (Array (Array Nat)) := do
  let ls := (text.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  match ls with
  | hl :: rest =>
    let (h, w) ← match words hl with
      | [a, b] => do some (← a.toNat?, ← b.toNat?)
      | _ => none
    let rows ← rest.mapM (fun l => (words l).mapM String.toNat?)
    if rows.length != h || rows.any (·.length != w) then none
    some (rows.map List.toArray).toArray
  | [] => none

/-- `DIR/NAME.txt`, parsed, or an error naming it. -/
def loadTrace (dir n : String) : IO (Array (Array Nat)) := do
  match parseMatrix (← IO.FS.readFile s!"{dir}/{n}.txt") with
  | some m => pure m
  | none => throw (IO.userError s!"MALFORMED {n}.txt")

/-- **The dumps' shapes**: each height the expected one, nonzero; each
    width its AIR's; and the memory shorter than `P`, as the one-pass
    count's lemmas need (`multArr_get`).  `MALFORMED` and false otherwise. -/
def shapesOK (heights : List (String × Nat × Nat)) (widths : List (String × Array (Array Nat) × AirD))
    (memLen : Nat) : IO Bool := do
  for (n, got, want) in heights do
    if got != want || got == 0 then IO.println s!"MALFORMED: {n} has {got} rows, not {want}"; return false
  for (n, m, A) in widths do
    if (m.getD 0 #[]).size != A.width then
      IO.println s!"MALFORMED: {n} is {(m.getD 0 #[]).size} wide, its AIR {A.width}"; return false
  if memLen ≥ P then IO.println s!"MALFORMED: a memory of {memLen} cells, not below P"; return false
  return true

/-- A dump as a table, its preprocessed columns the AIR's. -/
def asTable (A : AirD) (m : Array (Array Nat)) : Table :=
  ⟨m.size, fun r c => ofN ((m.getD r #[]).getD c 0), fun r i => (A.pretrace.getD r []).getD i 0⟩

/-- The cells of rows `rs` of a dump that differ from `model`, the first
    few printed with the prover's name `who`. -/
def cmpRows (who name : String) (m : Array (Array Nat)) (rs : List Nat) (model : Nat → Nat → Nat) : IO Nat := do
  let mut bad := 0
  for r in rs do
    let row := m.getD r #[]
    for c in [0:row.size] do
      let x := row.getD c 0
      let y := model r c
      if x != y then
        if bad < 5 then IO.println s!"  {name} row {r} column {c}: {who} {x}, Lean {y}"
        bad := bad + 1
  return bad

/-- `cmpRows`, the model given `pre r`, computed once for row `r`: what a
    row's every column asks, such as the jet it instantiates. -/
def cmpRowsBy {α : Type} (who name : String) (m : Array (Array Nat)) (rs : List Nat) (pre : Nat → α)
    (model : α → Nat → Nat → Nat) : IO Nat := do
  let mut bad := 0
  for r in rs do
    let row := m.getD r #[]
    let p := pre r
    for c in [0:row.size] do
      let x := row.getD c 0
      let y := model p r c
      if x != y then
        if bad < 5 then IO.println s!"  {name} row {r} column {c}: {who} {x}, Lean {y}"
        bad := bad + 1
  return bad

/-- A memory row as `memTableC` and `memTable5` have it, for the memory
    `A.toList`: address, tag, fields, and the multiplicity `mult` holds for
    it (`multArr` over the senders' messages).  The cells are read from the
    array, `A.getD r` being `A.toList.getD r` (`getD_toList`), so a row
    costs no walk down the list. -/
def memModel (A : Array Cell) (mult : Array F) (r c : Nat) : Nat :=
  let cl := A.getD r .nil
  if c = 0 then (ofN r).val else if c = 1 then (ofN (cellTag cl)).val
  else if c = 2 then (ofN (cellFields cl).1).val
  else if c = 3 then (ofN (cellFields cl).2).val
  else if c = 4 then ((mult[r]?).getD 0).val else 0

/-- **The blinded traces are the unblinded ones blinded at `blocks`**, the
    blocks `(table, column, edge)` of a circuit's view, the tables named
    `names` in the view's order (`DIR/NAME.txt`, `DIR/NAME.blind.txt`):
    every cell agrees but row 0's block cells; each block holds a tuple, not
    all zero, and the flag 1; the unblinded tables' block columns are zero
    on every row (their flags clear); and each edge's blocks hold one tuple.
    `OK` when all of it holds. -/
def checkBlind (who view dir : String) (names : List String) (blocks : List (Nat × Nat × Nat)) (edges : Nat) :
    IO UInt32 := do
  let mut bad : Nat := 0
  let mut tuples : Array (Option (List Nat)) := Array.replicate edges none
  for (n, k) in names.zipIdx do
    let u ← loadTrace dir n
    let b ← loadTrace dir s!"{n}.blind"
    if u.size != b.size || u.size == 0 || (u.getD 0 #[]).size != (b.getD 0 #[]).size then
      IO.println s!"MALFORMED: {n}.blind.txt is not {n}.txt's shape"; return 1
    let bl := (blocks.filter (·.1 == k)).map (·.2)
    let w := (u.getD 0 #[]).size
    if bl.any (fun (c, e) => c + 5 > w || e ≥ edges) then
      IO.println s!"MALFORMED: {n} is {w} wide, narrower than its blinding blocks"; return 1
    let inBlock := fun (c : Nat) => bl.any fun (c₀, _) => c₀ ≤ c && c < c₀ + 5
    for r in [0:u.size] do
      let ur := u.getD r #[]
      let br := b.getD r #[]
      for (c₀, _) in bl do
        if (List.range 5).any (fun i => ur.getD (c₀ + i) 0 != 0) then
          if bad < 5 then IO.println s!"  {n} row {r}: the unblinded block at {c₀} is not clear"
          bad := bad + 1
      for c in [0:w] do
        if !(r == 0 && inBlock c) && ur.getD c 0 != br.getD c 0 then
          if bad < 5 then IO.println s!"  {n} row {r} column {c}: unblinded {ur.getD c 0}, blinded {br.getD c 0}"
          bad := bad + 1
    for (c₀, e) in bl do
      let b0 := (List.range 5).map fun i => (b.getD 0 #[]).getD (c₀ + i) 0
      if b0.getD 4 0 != 1 then IO.println s!"  {n} block at {c₀}: the flag is not 1"; bad := bad + 1
      let tup := b0.take 4
      if tup.all (· == 0) then IO.println s!"  {n} block at {c₀}: an all-zero tuple"; bad := bad + 1
      match tuples[e]! with
      | none => tuples := tuples.set! e (some tup)
      | some t => if t != tup then IO.println s!"  edge {e}: its blocks hold different tuples"; bad := bad + 1
  if tuples.any (·.isNone) then IO.println "MALFORMED: an edge without its blocks"; return 1
  IO.println s!"blinding: {blocks.length} blocks on {edges} edges over {names.length} tables; cells differing outside them or wrong in them: {bad}"
  if bad == 0 then
    IO.println s!"OK: {who}'s blinded traces are its honest ones blinded as {view} blinds them"; return 0
  else
    IO.println "DIFFER"; return 1

theorem getD_toList (A : Array Cell) (r : Nat) : A.getD r .nil = A.toList.getD r .nil := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

end Circuit.TraceCheck
