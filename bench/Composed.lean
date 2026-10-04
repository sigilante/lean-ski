import Ski.Composed
import Ski.ComposedJ
import Ski.ComposedText
import Ski.ComposeExamples
import Ski.ComposeXExamples
import Ski.ChainExamples
import Ski.ComposedPText
import Ski.P2Commit
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

open Mach Compose CompM WitEx ComposeEx ComposeXEx

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

/-- The examples with `∃` and knowledge implication: name, formula, region
    size, the honest bits and witness, and a witness a set atom's verifier
    rejects. -/
def xexamples : List (String × XS × Nat × BT × Term × Term) :=
  [("exists", exEq, 64, exEqBits, exEqW, pairT K (pairT K K)),
   ("fst", fstAnd, 64, fstAndBits, pairT negW satW, pairT I satW),
   ("inl", inlNeg, 64, .leaf true, negW, I),
   -- a chain of two stages over the public hand-off `F`, each its own proof
   ("chain1", ChainEx.stage₁ ChainEx.o, 64, .leaf true, satW, triple T T T),
   ("chain2", ChainEx.stage₂ ChainEx.o, 64, .leaf true, negW, I)]

def emitX (dir : String) : IO UInt32 := do
  for (name, s, W, β, w, bad) in xexamples do
    let d := s!"{dir}/{name}"
    IO.FS.createDirAll d
    let M := s.toXF
    let N := BT.nleaves (clearX M)
    let some good := regionOf' N W w | do IO.println s!"{name}: the witness does not fit"; return 1
    let some wrong := regionOf' N W bad | do IO.println s!"{name}: the wrong witness does not fit"; return 1
    let bits := bitList β
    IO.FS.writeFile s!"{d}/public.txt" (publicTextC (.xformula s) W)
    IO.FS.writeFile s!"{d}/witness.txt" (witnessText bits good)
    IO.FS.writeFile s!"{d}/witness_wrong.txt" (witnessText bits wrong)
    IO.println s!"{name}: {N} bits, region {W} cells, {(stmtOfX M).length} segments"
  return 0

def emit (dir : String) : IO UInt32 := do
  let r ← emitX dir
  if r != 0 then return r
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

/-- `composed statement-jets PUBLIC`: a statement for the circuit with jets,
    its `log R M Lp Li` line fixing all four free heights. -/
def statementJ (path : String) : IO UInt32 := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  match statementOfTextJ text with
  | some (c, W, lg, bud) =>
    IO.println s!"STATEMENT {path}: {c.header}, a region of {W} cells, heights 2^{lg.1} and 2^{lg.2}, budgets 2^{bud.1} and 2^{bud.2}"
    return 0
  | none =>
    IO.println s!"NOT A STATEMENT WITH JETS {path}"
    return 1

/-- `composed budget PUBLIC LP LI OUT`: the statement with jets of the
    composed statement `PUBLIC`, its POP and INSTW budgets `2^LP` and
    `2^LI`, written to `OUT`. -/
def budget (path lp li out : String) : IO UInt32 := do
  let some (c, W, lg) := statementOfText (← IO.FS.readFile path)
    | do IO.println s!"NOT A STATEMENT {path}"; return 1
  let some bud := (do some (← lp.toNat?, ← li.toNat?) : Option (Nat × Nat))
    | do IO.println "LP and LI are numbers"; return 1
  if !logOK bud then IO.println "LP and LI are in [8, 20]"; return 1
  IO.FS.writeFile out (publicTextC c W lg (some bud))
  IO.println s!"{out}: {c.header}, heights 2^{lg.1} and 2^{lg.2}, budgets 2^{bud.1} and 2^{bud.2}"
  return 0

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

def xsEq : XS → XS → Bool
  | .atom V x, .atom V' x' => V == V' && x == x'
  | .and A B, .and A' B' => xsEq A A' && xsEq B B'
  | .or A B, .or A' B' => xsEq A A' && xsEq B B'
  | .ex B, .ex B' => xsEq B B'
  | .swap A, .swap A' => xsEq A A'
  | .fst A, .fst A' => xsEq A A'
  | .snd A, .snd A' => xsEq A A'
  | .inl A B, .inl A' B' => xsEq A A' && xsEq B B'
  | .inr A B, .inr A' B' => xsEq A A' && xsEq B B'
  | _, _ => false

def stmtEq : CStmt → CStmt → Bool
  | .formula M, .formula M' => formulaEq M M'
  | .xformula s, .xformula s' => xsEq s s'
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
        | .xformula _ =>
          IO.println s!"ACCEPT {path}: its bits and witness read back as a realizer of the formula it concludes ({R.size} rows, {A.size} cells, {ends.size} segments)"
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
  let some (c, W, _) := statementOfTextAny (← IO.FS.readFile pub)
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

/-- `composed emit-p2 DIR`: the Poseidon2 preimage statement for Plonky3's
    test vector 1 (`ComposedPText.publicTextP`), and its witness: the
    inputs' 496 bits, then the region's one cell. -/
def emitP2 (dir : String) : IO UInt32 := do
  let some (inp, outp) := Poseidon2.vectors[1]? | return 1
  let h := outp.headD 0
  let lg : ComposedPText.PLogs := ⟨14, 15, 9, 9, 8⟩
  IO.FS.writeFile s!"{dir}/p2pre.public.txt" (ComposedPText.publicTextP h lg)
  let bits := inp.flatMap (BitArith.bitsOf 31)
  IO.FS.writeFile s!"{dir}/p2pre.witness.txt" (witnessText bits ComposedPText.regionP)
  IO.println s!"wrote {dir}/p2pre.public.txt (h = {h}) and its witness"
  return 0

/-- The hand-off's value: eight elements below `2^30` (a credential: an
    age, a country code, six more fields), and its randomness. -/
def handoffValue : List Nat := [21, 840, 1, 2, 3, 4, 5, 6]
def handoffRand : List Nat :=
  [1384390411, 278963108, 1807244539, 1259281112, 925470542, 1663934283, 1027398213, 1536893713]

/-- A pattern over the 496 bits: bit `j` of element `e` per `fix`, and the
    top bit of each of the value's eight elements clear, so its elements are
    below `2^30`, canonical. -/
def handoffPat (fix : Nat → Nat → Option Bool) : List (Option Bool) :=
  (List.range 496).map fun i =>
    let e := i / 31
    let j := i % 31
    if e < 8 && j == 30 then some false else if e < 8 then fix e j else none

/-- Stage 1 discloses the value's element 1: all its bits. -/
def handoffPat1 : List (Option Bool) :=
  handoffPat fun e j => if e == 1 then some ((BitArith.bitsOf 31 840).getD j false) else none

/-- Stage 2 shows the value's element 0 is odd: its bit 0. -/
def handoffPat2 : List (Option Bool) := handoffPat fun e j => if e == 0 && j == 0 then some true else none

/-- `composed emit-handoff DIR`: the hidden hand-off's two statements, each
    `p2commit c pat` with the commitment `c` of `handoffValue` and
    `handoffRand`, and their witness, the same for both. -/
def emitHandoff (dir : String) : IO UInt32 := do
  let c := (Poseidon2.permute (handoffValue ++ handoffRand)).take 8
  let lg : ComposedPText.PLogs := ⟨14, 16, 9, 9, 8⟩
  IO.FS.writeFile s!"{dir}/handoff1.public.txt" (ComposedPText.publicTextG (.commit c handoffPat1) lg)
  IO.FS.writeFile s!"{dir}/handoff2.public.txt" (ComposedPText.publicTextG (.commit c handoffPat2) lg)
  let bits := (handoffValue ++ handoffRand).flatMap (BitArith.bitsOf 31)
  IO.FS.writeFile s!"{dir}/handoff.witness.txt" (witnessText bits ComposedPText.regionP)
  IO.println s!"wrote the hand-off's two statements (c = {c}) and their witness in {dir}"
  return 0

/-- `composed statement-p2 PUBLIC`: `OK` when the file is exactly a
    statement with the Poseidon2 jet. -/
def statementP2 (path : String) : IO UInt32 := do
  let text ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
  match ComposedPText.statementOfTextG text with
  | some (.pre h, _) => IO.println s!"OK p2pre {h}"; return 0
  | some (.commit c _, _) => IO.println s!"OK p2commit {c}"; return 0
  | none => IO.println "NOT A STATEMENT"; return 1

/-- `composed chain-p2 PUBLIC1 PUBLIC2`: `CHAIN OK` when both files are
    statements with the Poseidon2 jet that `P2Commit.chainB` accepts: two
    valid `p2commit` statements with one commitment, both patterns fixing
    value bits only and keeping the value canonical
    (`Circuit.p2commit_chainB`). -/
def chainTexts (t1 t2 : String) : IO UInt32 := do
  match ComposedPText.statementOfTextG t1, ComposedPText.statementOfTextG t2 with
  | some (st₁, _), some (st₂, _) =>
    if P2Commit.chainB st₁ st₂ then
      match st₁ with
      | .commit c _ => IO.println s!"CHAIN OK p2commit {c}"; return 0
      | _ => IO.println "NOT A CHAIN"; return 1
    else IO.println "NOT A CHAIN"; return 1
  | _, _ => IO.println "NOT A STATEMENT"; return 1

/-- The two files' texts, or with `-` both from stdin, split at a NUL. -/
def chainP2 (p1 p2 : String) : IO UInt32 := do chainTexts (← IO.FS.readFile p1) (← IO.FS.readFile p2)

def chainP2In : IO UInt32 := do
  match ((← (← IO.getStdin).readToEnd).splitOn "\u0000") with
  | [t1, t2] => chainTexts t1 t2
  | _ => IO.println "NOT TWO STATEMENTS"; return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["emit-p2", dir] => emitP2 dir
  | ["emit-handoff", dir] => emitHandoff dir
  | ["statement-p2", pub] => statementP2 pub
  | ["chain-p2", "-"] => chainP2In
  | ["chain-p2", p1, p2] => chainP2 p1 p2
  | ["statement", pub] => statement pub
  | ["statement-jets", pub] => statementJ pub
  | ["budget", pub, lp, li, out] => budget pub lp li out
  | "check" :: pub :: paths => check pub paths
  | "check-cj" :: src :: pub :: paths => checkCJ src pub paths
  | _ =>
    IO.eprintln "usage: composed emit DIR | composed emit-p2 DIR | composed emit-handoff DIR | composed statement-p2 PUBLIC | composed chain-p2 PUBLIC1 PUBLIC2|-\n       composed statement PUBLIC | composed statement-jets PUBLIC\n       composed budget PUBLIC LP LI OUT | composed check PUBLIC TABLE... | composed check-cj SRC PUBLIC TABLE..."
    return 2
