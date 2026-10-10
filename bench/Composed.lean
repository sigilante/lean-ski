import Ski.Composed
import Ski.ComposedJ
import Ski.ComposedText
import Ski.ComposeExamples
import Ski.ComposeXExamples
import Ski.ChainExamples
import Ski.ComposedPText
import Ski.P2Commit
import Ski.Circuit.CompPHonest
import Ski.ZK.Blocks
import Ski.Circuit.SendsFast
import Ski.Circuit.TraceCheck
import Ski.Circuit.JetCntFast
import Ski.Circuit.CpuFast
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

/-- A run table's body, after its header line: the region's size, the
    memory, the segments' ends and the rows. -/
def parseRun (ls : List String) : Option (Nat × Array Cell × Array Nat × Array Air.Row) := do
  match ls with
  | wl :: nl :: rest =>
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
        some (W, cells.toArray, ends.toArray, rows.toArray)
      | [] => none
    | [] => none
  | _ => none

def parseTable (ls : List String) :
    Option (CStmt × Nat × Array Cell × Array Nat × Array Air.Row) := do
  match ls with
  | fl :: rest =>
    let M ← parseHeader (words fl)
    let (W, cells, ends, rows) ← parseRun rest
    some (M, W, cells, ends, rows)
  | [] => none

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
  let tmpls := JetTable.fileTemplatesEta ((← IO.FS.readFile src).toList.map Char.toNat)
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
def emitP2 (dir : String) (k : Nat := 1) : IO UInt32 := do
  let some (inp, outp) := Poseidon2.vectors[k]? | IO.eprintln "no such vector"; return 1
  let h := outp.headD 0
  let lg : ComposedPText.PLogs := ⟨14, 15, 9, 9, 8⟩
  IO.FS.writeFile s!"{dir}/p2pre.public.txt" (ComposedPText.publicTextP h lg)
  let bits := inp.flatMap (BitArith.bitsOf 31)
  IO.FS.writeFile s!"{dir}/p2pre.witness.txt" (witnessText bits ComposedPText.regionP)
  IO.println s!"wrote {dir}/p2pre.public.txt (h = {h}) and its witness"
  return 0

/-- The hand-off's value for tests: eight elements below `2^30` (a
    credential: an age, a country code, six more fields), and its fixed
    randomness.  A commitment to them hides nothing, since both are in this
    source.  The released statements take a fresh value and fresh
    randomness (`emit-handoff DIR --fresh`). -/
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

/-- The hand-off statements' heights. -/
def handoffLogs : ComposedPText.PLogs := ⟨14, 16, 9, 9, 8⟩

/-- A number below `2^k`, `k ≤ 32`, uniform, from the system's entropy
    (Lean's runtime reads `/dev/urandom`). -/
def freshBits (k : Nat) : IO Nat := do
  let b ← IO.getRandomBytes 4
  return ((b[0]!.toNat <<< 24) ||| (b[1]!.toNat <<< 16) ||| (b[2]!.toNat <<< 8) ||| b[3]!.toNat) % 2 ^ k

/-- A fresh value that meets both patterns, its undisclosed elements
    uniform: element 0 odd, element 1 840, the other six below `2^30`. -/
def freshValue : IO (List Nat) := do
  let e0 := 2 * (← freshBits 29) + 1
  let mut rest : Array Nat := #[]
  for _ in [0:6] do rest := rest.push (← freshBits 30)
  return e0 :: 840 :: rest.toList

/-- Eight elements below `p`, uniform, from the system's entropy: 31-bit
    draws, each redrawn while `≥ p`. -/
def freshRand : IO (List Nat) := do
  let mut out : Array Nat := #[]
  for _ in [0:1000] do
    if out.size == 8 then break
    let v ← freshBits 31
    if v < Poseidon2.p then out := out.push v
  if out.size != 8 then throw (IO.userError "too few draws below p")
  return out.toList

/-- Eight elements below `p`, read from a file, separated by white space. -/
def readRand (path : String) : IO (List Nat) := do
  let ws := words ((← IO.FS.readFile path).map fun ch => if ch.isWhitespace then ' ' else ch)
  let some vs := ws.mapM String.toNat? | throw (IO.userError s!"{path}: not numbers")
  if vs.length != 8 || vs.any (· ≥ Poseidon2.p) then
    throw (IO.userError s!"{path}: not eight elements below p")
  return vs

/-- `composed emit-handoff DIR [--fresh | --rand=FILE]`: the hidden
    hand-off's two statements, each `p2commit c pat` with the commitment `c`
    of a value and randomness, and their witness, the same for both.  By
    default the value and randomness are the tests' (`handoffValue`,
    `handoffRand`); `--fresh` draws both from the system's entropy, the
    value's undisclosed parts with it (`freshValue`); `--rand=FILE` reads
    the randomness, with the tests' value.  The witness holds the value and
    the randomness: it is the prover's secret, and neither is printed. -/
def emitHandoff (dir : String) (value : List Nat := handoffValue) (rand : List Nat := handoffRand) :
    IO UInt32 := do
  let c := (Poseidon2.permute (value ++ rand)).take 8
  IO.FS.writeFile s!"{dir}/handoff1.public.txt" (ComposedPText.publicTextG (.commit c handoffPat1) handoffLogs)
  IO.FS.writeFile s!"{dir}/handoff2.public.txt" (ComposedPText.publicTextG (.commit c handoffPat2) handoffLogs)
  let bits := (value ++ rand).flatMap (BitArith.bitsOf 31)
  IO.FS.writeFile s!"{dir}/handoff.witness.txt" (witnessText bits ComposedPText.regionP)
  IO.println s!"wrote the hand-off's two statements (c = {c}) and their witness in {dir}"
  return 0

/-- `composed check-handoff PUBLIC1 PUBLIC2`: `OK HANDOFF c` when the files
    are exactly Lean's two hand-off statements for the commitment `c` they
    name: `p2commit c pat` with the documented patterns (`handoffPat1`,
    `handoffPat2`) and heights.  The release's statements commit with fresh
    randomness, which the check does not know, so it takes `c` from the
    files; everything else it fixes. -/
def checkHandoff (p1 p2 : String) : IO UInt32 := do
  match ComposedPText.statementOfTextG (← IO.FS.readFile p1), ComposedPText.statementOfTextG (← IO.FS.readFile p2) with
  | some (.commit c₁ pat₁, lg₁), some (.commit c₂ pat₂, lg₂) =>
    if c₁ == c₂ && pat₁ == handoffPat1 && pat₂ == handoffPat2 && lg₁ == handoffLogs && lg₂ == handoffLogs then
      IO.println s!"OK HANDOFF {c₁}"; return 0
    else IO.println "NOT THE HAND-OFF"; return 1
  | _, _ => IO.println "NOT THE HAND-OFF"; return 1

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


/-- `composed check-p2-tables PUBLIC DIR`: compare the traces `compp.rs`
    proves (`ski-air compp-dump PUBLIC WITNESS DIR`) with Lean's model of
    the honest tables (`Ski/Circuit/CompPHonest.lean`), built from the
    same run (`DIR/run.txt`).  Each table's height must be the statement's,
    and the run's the CPU's; the Poseidon2 tables must be at least as wide
    as Lean's rows, the columns past them compared with 0.
    Then every row of P2IN, P2OUT, the Poseidon2 table, the witness table
    and the CPU (read through `Circuit.P2Run.cpuColP_arr`); of the memory,
    every row: its address, tag and fields, and its multiplicity,
    `memTable5`'s count of the messages the dumped tables send with its
    tuple (`Circuit.memTable5_mult`).  `OK` when every cell compared
    agrees.
    The traces compared are unblinded (`blind = false`), as Lean's model
    is; `check-p2-blind` compares the blinded traces with these. -/
def checkP2Tables (pub dir : String) : IO UInt32 := do
  let text ← IO.FS.readFile pub
  let some (st, lg) := ComposedPText.statementOfTextG text | do IO.println "NOT A STATEMENT"; return 1
  let runText ← IO.FS.readFile (dir ++ "/run.txt")
  let ls := (runText.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let some (hl, rest) := (match ls with | l :: r => some (l, r) | [] => none) | do IO.println "MALFORMED run.txt"; return 1
  if hl != (text.splitOn "\n").headD "" then
    IO.println "run.txt is not a run of the statement"; return 1
  let some (_, cells, ends, rows) := parseRun rest | do IO.println "MALFORMED run.txt"; return 1
  let roots := (CompM.cHeapO (fun _ => false) ComposedPText.shpP ComposedPText.regionP st.Vs).2
  let R : Circuit.P2Run := ⟨cells.toList, ComposedPText.JP2, ComposedPText.rootP, roots,
    fun j => ends.getD j 0, ends.size, fun i => rows.getD i ⟨0, 0, 0⟩⟩
  let load := fun (n : String) => do
    Circuit.TraceCheck.loadTrace dir n
  let cpu ← load "cpu"
  let pin ← load "p2in"
  let pout ← load "p2out"
  let p2 ← load "p2"
  let wit ← load "wit"
  let mem ← load "mem"
  let K := cpu.size
  let runRows := rows.size
  -- Every CPU row, its memory read from the array, whether it takes the
  -- jet's step found once and its restart count from a prefix sum
  -- (`Circuit.P2Run.cpuColP_arr`).
  let get := fun (a : Nat) => cells[a]?
  let jets := (List.range runRows).filter (R.jetAtG get)
  let moving := ((List.range runRows).find? (fun r => rows.getD r ⟨0, 0, 0⟩ == rows.getD (r + 1) ⟨0, 0, 0⟩)).getD runRows
  let cnts := Circuit.cntArr (Circuit.rsI R.e R.n) K
  let pinL := R.pinRows K
  let poutL := R.poutRows K
  let p2L := R.p2Rows K ++ List.replicate (p2.size - (R.p2Rows K).length) Circuit.p2Pad
  let N := BT.nleaves ComposedPText.shpP
  let W := ComposedPText.regionP.length
  -- Each dump's height is the statement's, and the Poseidon2 tables are at
  -- least as wide as the model's rows (the columns past them compared with
  -- 0): a short, empty or narrow dump agrees with nothing.
  let width := fun (rs : List (List Circuit.F)) (pad : Nat) => if rs.isEmpty then pad else (rs.headD []).length
  let shape := [("cpu", cpu.size, 2 ^ lg.rows), ("p2in", pin.size, 2 ^ lg.pin),
    ("p2out", pout.size, 2 ^ lg.pout), ("p2", p2.size, 2 ^ lg.p2),
    ("wit", wit.size, (Circuit.witRowsP N W).length), ("run", runRows, K),
    ("mem", mem.size, 2 ^ lg.mem), ("memory", cells.size, 2 ^ lg.mem)]
  let widths := [("p2in", pin, width pinL ((pin.getD 0 #[]).size)),
    ("p2out", pout, width poutL ((pout.getD 0 #[]).size)), ("p2", p2, Circuit.p2Pad.length)]
  for (n, got, want) in shape do
    if got != want then IO.println s!"MALFORMED: {n} has {got} rows, the statement {want}"; return 1
  for (n, m, w) in widths do
    if (m.getD 0 #[]).size < w then IO.println s!"MALFORMED: {n} is {(m.getD 0 #[]).size} wide, Lean's {w}"; return 1
  let airsP := Circuit.compPAirsG st.Vs
  let airP := fun (i : Nat) => airsP.getD i ⟨"", 0, 0, [], [], []⟩
  if !(← Circuit.TraceCheck.shapesOK []
      [("cpu", cpu, airP 0), ("mem", mem, airP 1), ("wit", wit, airP 3), ("p2in", pin, airP 5),
       ("p2out", pout, airP 6), ("p2", p2, airP 7)] cells.size) then return 1
  let b1 ← Circuit.TraceCheck.cmpRowsBy "compp.rs" "cpu" cpu (List.range K) (R.jetAtG get) fun jet r c =>
    (R.cpuColPG get jet (cnts.getD r 0) r c).val
  let b2 ← Circuit.TraceCheck.cmpRows "compp.rs" "p2in" pin (List.range pin.size) fun r c => ((pinL.getD r []).getD c 0).val
  let b3 ← Circuit.TraceCheck.cmpRows "compp.rs" "p2out" pout (List.range pout.size) fun r c => ((poutL.getD r []).getD c 0).val
  let b4 ← Circuit.TraceCheck.cmpRows "compp.rs" "p2" p2 (List.range p2.size) fun r c => ((p2L.getD r []).getD c 0).val
  let b5 ← Circuit.TraceCheck.cmpRows "compp.rs" "wit" wit (List.range wit.size) fun r c => (Circuit.witColG 3 R.A N W r c).val
  -- The memory, as `memTable5` has it in `P2Run.honest_zkP`: each row's
  -- address, tag and fields, and its multiplicity, the counts the other
  -- tables send on `mem` with that row's tuple, here those the dumped
  -- tables send under the verifier's AIRs (`compPAirsG`), the program
  -- table public, counted in one pass (`Circuit.memTable5_mult`).  Its
  -- blinding block `check-p2-blind` compares.
  let airs := Circuit.compPAirsG st.Vs
  let air := fun (i : Nat) => airs.getD i ⟨"", 0, 0, [], [], []⟩
  let asTable := fun (A : Circuit.AirD) (m : Array (Array Nat)) => (⟨m.size,
    fun r c => Circuit.ofN ((m.getD r #[]).getD c 0),
    fun r i => (A.pretrace.getD r []).getD i 0⟩ : Circuit.Table)
  let m0 := CompM.cMachineO (fun _ => false) ComposedPText.shpP ComposedPText.regionP st.Vs
  let msgs := Circuit.sendsOn (air 0) (asTable (air 0) cpu) "mem" ++
    Circuit.sendsOn (air 2) (Circuit.progTableC m0.heap N W) "mem" ++
    Circuit.sendsOn (air 5) (asTable (air 5) pin) "mem" ++ Circuit.sendsOn (air 6) (asTable (air 6) pout) "mem" ++
    Circuit.sendsOn (air 3) (asTable (air 3) wit) "mem"
  let mult := Circuit.multArr R.A msgs
  let memCut := mem.map (·.extract 0 5)
  let b6 ← Circuit.TraceCheck.cmpRows "compp.rs" "mem" memCut (List.range mem.size)
    (Circuit.TraceCheck.memModel cells mult)
  IO.println s!"cpu: all {K} rows ({moving} moving, {jets.length} jet calls); p2in {pin.size}, p2out {pout.size}, p2 {p2.size}, wit {wit.size} rows; cells differing: {b1}, {b2}, {b3}, {b4}, {b5}, mem {b6}"
  if b1 + b2 + b3 + b4 + b5 + b6 == 0 then
    IO.println "OK: compp.rs's traces are Lean's model of the honest tables"; return 0
  else
    IO.println "DIFFER"; return 1

/-- `composed check-p2-blind DIR`: the blinded traces `compp.rs` commits to
    (`DIR/NAME.blind.txt`, from `ski-air compp-dump`) are its unblinded
    ones (`DIR/NAME.txt`, which `check-p2-tables` compares with Lean's model
    of the honest tables) blinded as `Circuit.compPViewN` blinds them, at
    its blocks `Circuit.compPBlocks` (`Circuit.TraceCheck.checkBlind`). -/
def checkP2Blind (dir : String) : IO UInt32 :=
  Circuit.TraceCheck.checkBlind "compp.rs" "compPViewN" dir ["mem", "cpu", "wit", "p2in", "p2out", "p2"]
    Circuit.compPBlocks 5

/-- `composed check-c-tables PUBLIC DIR`: compare the traces `composed.rs`
    proves for a composed statement (`ski-air composed-dump PUBLIC WITNESS
    DIR`) with Lean's honest tables, as `Circuit.comp_completeG_log` builds
    them from the same run (`DIR/run.txt`): the CPU (`cpuTableC`, read
    through `Circuit.cpuColC_arr`), the witness table (`witTable`) and the
    memory (`memTableC`, its multiplicities counted over the dumped tables
    by `multArr`, `Circuit.memTableC_mult`), each on every row.  Each table's height
    must be the run's.  `OK` when every cell compared agrees. -/
def checkCTables (pub dir : String) : IO UInt32 := do
  let some (c, W, (lr, lm)) := statementOfText (← IO.FS.readFile pub) | do IO.println "NOT A STATEMENT"; return 1
  let ls := ((← IO.FS.readFile (dir ++ "/run.txt")).splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let some (M', W', cells, ends, rows) := parseTable ls | do IO.println "MALFORMED run.txt"; return 1
  if !stmtEq M' c || W' != W then IO.println "run.txt is not a run of the statement"; return 1
  let shp := c.shp
  let Ps := c.Ps
  let N := BT.nleaves shp
  let A := cells.toList
  let roots := Circuit.blankRoots shp W Ps
  let blank := Circuit.blankM shp W Ps
  let airs := Circuit.compAirsG shp Ps W
  let air := fun (i : Nat) => airs.getD i ⟨"", 0, 0, [], [], []⟩
  let cpu ← Circuit.TraceCheck.loadTrace dir "cpu"
  let mem ← Circuit.TraceCheck.loadTrace dir "mem"
  let wit ← Circuit.TraceCheck.loadTrace dir "wit"
  let K := cpu.size
  let Wt := Circuit.witTable A N W
  if !(← Circuit.TraceCheck.shapesOK
      [("cpu", K, 2 ^ lr), ("run", rows.size, K), ("mem", mem.size, 2 ^ lm), ("memory", cells.size, 2 ^ lm),
       ("wit", wit.size, Wt.h), ("ends", ends.size, Ps.length)]
      [("cpu", cpu, air 0), ("mem", mem, air 1), ("wit", wit, air 3)] cells.size) then return 1
  let rowAt := fun i => rows.getD i ⟨0, 0, 0⟩
  let e := fun j => ends.getD j 0
  let moving := ((List.range rows.size).find? (fun r => rowAt r == rowAt (r + 1))).getD rows.size
  -- Every CPU row, its memory read from the array and its restart count
  -- from a prefix sum (`Circuit.cpuColC_arr`).
  let cnts := Circuit.cntArr (Circuit.rsI e Ps.length) K
  let who := "composed.rs"
  let b1 ← Circuit.TraceCheck.cmpRows who "cpu" cpu (List.range K) fun r col =>
    (Circuit.cpuColCG (fun a => cells[a]?) rowAt e Ps.length roots (cnts.getD r 0) r col).val
  let b2 ← Circuit.TraceCheck.cmpRows who "wit" wit (List.range wit.size) fun r col => (Wt.main r col).val
  let msgs := Circuit.sendsOn (air 0) (Circuit.TraceCheck.asTable (air 0) cpu) "mem" ++
    Circuit.sendsOn (air 2) (Circuit.progTableC blank.heap N W) "mem" ++
    Circuit.sendsOn (air 3) (Circuit.TraceCheck.asTable (air 3) wit) "mem"
  let mult := Circuit.multArr A msgs
  let b3 ← Circuit.TraceCheck.cmpRows who "mem" (mem.map (·.extract 0 5)) (List.range mem.size)
    (Circuit.TraceCheck.memModel cells mult)
  IO.println s!"cpu: all {K} rows ({moving} moving, {ends.size} segments); wit {wit.size}, mem {mem.size} rows; cells differing: {b1}, {b2}, {b3}"
  if b1 + b2 + b3 == 0 then
    IO.println "OK: composed.rs's traces are Lean's model of the honest tables"; return 0
  else
    IO.println "DIFFER"; return 1

/-- `composed check-c-blind DIR`: the blinded traces `composed.rs` commits
    to are its unblinded ones blinded as `Circuit.compViewN` blinds them, at
    `Circuit.compBlocks`. -/
def checkCBlind (dir : String) : IO UInt32 :=
  Circuit.TraceCheck.checkBlind "composed.rs" "compViewN" dir ["mem", "cpu", "wit"] Circuit.compBlocks 2

/-- `composed check-cj-tables SRC PUBLIC DIR`: compare the traces
    `compj.rs` proves for a composed statement with jets (`ski-air compj-dump
    PUBLIC JETS SRC WITNESS DIR`) with Lean's honest tables, as
    `Circuit.compJ_complete_log` builds them from the same run
    (`DIR/run.txt`) and the jet table Lean computes from the source:

    - the CPU (`CRun.cpuColCJ`, read through `CRun.cpuColCJ_arr`) on
      every row;
    - the witness table (`witTable`), POP and INSTW (`JRun.popRows`,
      `instwRows`, read as `ofRows` reads them) on every row;
    - the providers ROOTS, HDR and TMPL (`provTableCJ`: each tuple's count on
      its first row, the counts over the run's instantiations listed once,
      `JRun.cntRoots_eq` and its kin, `firstOcc` from an array,
      `firstOcc_arr`): HDR and TMPL on every row, ROOTS on its first 256,
      every 64th and its last 64;
    - the memory (`memTable5`, its multiplicities counted over the dumped
      tables, `Circuit.memTable5_mult`) on every row.

    Each table's height must be the run's or the statement's.  `OK` when
    every cell compared agrees. -/
def checkCJTables (src pub dir : String) : IO UInt32 := do
  let some (c, W, (lr, lm), some (lp, li)) := statementOfTextAny (← IO.FS.readFile pub)
    | do IO.println "NOT A STATEMENT WITH JETS"; return 1
  let tmpls := JetTable.fileTemplatesEta ((← IO.FS.readFile src).toList.map Char.toNat)
  let (jroots, jets) := Air.jetTableC c.shp W c.Ps tmpls
  let ls := ((← IO.FS.readFile (dir ++ "/run.txt")).splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let some (M', W', cells, ends, rows) := parseTable ls | do IO.println "MALFORMED run.txt"; return 1
  if !stmtEq M' c || W' != W then IO.println "run.txt is not a run of the statement"; return 1
  let shp := c.shp
  let Ps := c.Ps
  let N := BT.nleaves shp
  let A := cells.toList
  let blank := Circuit.blankM shp W Ps
  let rowAt := fun i => rows.getD i ⟨0, 0, 0⟩
  let e := fun j => ends.getD j 0
  let Rn : Circuit.CRun := ⟨A, jroots, jets, Circuit.blankRoots shp W Ps, e, Ps.length, rowAt⟩
  let airs := Circuit.compJAirs shp Ps W jroots jets
  let air := fun (i : Nat) => airs.getD i ⟨"", 0, 0, [], [], []⟩
  let ld := Circuit.TraceCheck.loadTrace dir
  let mem ← ld "mem"
  let cpu ← ld "cpu"
  let wit ← ld "wit"
  let pop ← ld "pop"
  let instw ← ld "instw"
  let tmpl ← ld "tmpl"
  let hdr ← ld "hdr"
  let roots ← ld "roots"
  let K := cpu.size
  let Wt := Circuit.witTable A N W
  let rootsRows := (Circuit.rootsRowsCJ jroots).toArray
  let hdrRows := (Circuit.hdrRowsCJ jets).toArray
  let tmplRows := (Circuit.tmplRowsCJ jets).toArray
  if !(← Circuit.TraceCheck.shapesOK
      [("cpu", K, 2 ^ lr), ("run", rows.size, K), ("mem", mem.size, 2 ^ lm), ("memory", cells.size, 2 ^ lm),
       ("wit", wit.size, Wt.h), ("pop", pop.size, 2 ^ lp), ("instw", instw.size, 2 ^ li),
       ("roots", roots.size, rootsRows.size), ("hdr", hdr.size, hdrRows.size), ("tmpl", tmpl.size, tmplRows.size),
       ("ends", ends.size, Ps.length)]
      [("cpu", cpu, air 0), ("mem", mem, air 1), ("wit", wit, air 3), ("roots", roots, air 5), ("hdr", hdr, air 6),
       ("tmpl", tmpl, air 7), ("pop", pop, air 8), ("instw", instw, air 9)] cells.size) then return 1
  let J := Rn.J
  -- The memory read from the array: the instantiations
  -- (`Circuit.JRun.insts_arr`), and every CPU row, each row's
  -- instantiation found once and its restart count from a prefix sum
  -- (`Circuit.CRun.cpuColCJ_arr`).
  let get := fun (a : Nat) => cells[a]?
  let insts := J.instsG get K
  let moving := ((List.range rows.size).find? (fun r => rowAt r == rowAt (r + 1))).getD rows.size
  let cnts := Circuit.cntArr (Circuit.rsI e Ps.length) K
  let who := "compj.rs"
  let cmp := Circuit.TraceCheck.cmpRows who
  let all := fun (m : Array (Array Nat)) => List.range m.size
  let b1 ← Circuit.TraceCheck.cmpRowsBy who "cpu" cpu (List.range K) (J.instAtG get) fun inst r col =>
    (Rn.cpuColCJG get inst (cnts.getD r 0) r col).val
  let b2 ← cmp "wit" wit (all wit) fun r col => (Wt.main r col).val
  let popA := (J.popRows K).toArray
  let instwA := (J.instwRows K).toArray
  let b3 ← cmp "pop" pop (all pop) fun r col => ((popA.getD r []).getD col 0).val
  let b4 ← cmp "instw" instw (all instw) fun r col => ((instwA.getD r []).getD col 0).val
  -- A provider's model row: its count on a tuple's first row, in column 0.
  let prov := fun (rs : Array (List Circuit.F)) (cnt : List Circuit.F → Nat) (q col : Nat) =>
    if col = 0 && (List.range q).all (fun q' => !(decide (rs.getD q' [] = rs.getD q []))) then
      (Circuit.ofN (cnt (rs.getD q []))).val else 0
  let cntRoots := fun v => insts.foldr (fun p acc =>
    (if [Circuit.ofN (J.row p.1).hd, Circuit.ofN p.2.1] = v then 1 else 0) + acc) 0
  let cntHdr := fun v => insts.foldr (fun p acc => (if Circuit.hdrRow p.2.2 p.2.1 = v then 1 else 0) + acc) 0
  let cntTmpl := fun v => insts.foldr (fun p acc =>
    ((JetTable.symCells p.2.2 p.2.2.body 0).1.zipIdx.map fun x =>
      if Circuit.tmplRow p.2.1 x.2 x.1 = v then 1 else 0).sum + acc) 0
  let rootsSample := (all roots).filter fun q => q < 256 || q % 64 = 0 || q + 64 ≥ roots.size
  let b5 ← cmp "roots" roots rootsSample (prov rootsRows cntRoots)
  let b6 ← cmp "hdr" hdr (all hdr) (prov hdrRows cntHdr)
  let b7 ← cmp "tmpl" tmpl (all tmpl) (prov tmplRows cntTmpl)
  let msgs := Circuit.sendsOn (air 0) (Circuit.TraceCheck.asTable (air 0) cpu) "mem" ++
    Circuit.sendsOn (air 2) (Circuit.progTableC blank.heap N W) "mem" ++
    Circuit.sendsOn (air 8) (Circuit.TraceCheck.asTable (air 8) pop) "mem" ++
    Circuit.sendsOn (air 9) (Circuit.TraceCheck.asTable (air 9) instw) "mem" ++
    Circuit.sendsOn (air 3) (Circuit.TraceCheck.asTable (air 3) wit) "mem"
  let mult := Circuit.multArr A msgs
  let b8 ← cmp "mem" (mem.map (·.extract 0 5)) (all mem) (Circuit.TraceCheck.memModel cells mult)
  IO.println s!"cpu: all {K} rows ({moving} moving, {insts.length} instantiations); roots {rootsSample.length} of {roots.size}; cells differing: cpu {b1}, wit {b2}, pop {b3}, instw {b4}, roots {b5}, hdr {b6}, tmpl {b7}, mem {b8}"
  if b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 == 0 then
    IO.println "OK: compj.rs's traces are Lean's model of the honest tables"; return 0
  else
    IO.println "DIFFER"; return 1

/-- `composed check-cj-blind DIR`: the blinded traces `compj.rs` commits to
    are its unblinded ones blinded as `Circuit.compJViewN` blinds them, at
    `Circuit.compJBlocks`. -/
def checkCJBlind (dir : String) : IO UInt32 :=
  Circuit.TraceCheck.checkBlind "compj.rs" "compJViewN" dir
    ["mem", "cpu", "wit", "pop", "instw", "tmpl", "hdr", "roots"] Circuit.compJBlocks 7

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", dir] => emit dir
  | ["emit-p2", dir] => emitP2 dir
  | ["emit-p2", dir, k] => emitP2 dir k.toNat!
  | ["emit-handoff", dir] => emitHandoff dir
  | ["emit-handoff", dir, "--fresh"] => emitHandoff dir (← freshValue) (← freshRand)
  | ["emit-handoff", dir, r] =>
    if r.startsWith "--rand=" then emitHandoff dir handoffValue (← readRand (r.drop 7).toString)
    else IO.eprintln "usage: composed emit-handoff DIR [--fresh | --rand=FILE]"; return 2
  | ["check-handoff", p1, p2] => checkHandoff p1 p2
  | ["statement-p2", pub] => statementP2 pub
  | ["chain-p2", "-"] => chainP2In
  | ["check-p2-tables", pub, dir] => checkP2Tables pub dir
  | ["check-p2-blind", dir] => checkP2Blind dir
  | ["check-c-tables", pub, dir] => checkCTables pub dir
  | ["check-c-blind", dir] => checkCBlind dir
  | ["check-cj-tables", src, pub, dir] => checkCJTables src pub dir
  | ["check-cj-blind", dir] => checkCJBlind dir
  | ["chain-p2", p1, p2] => chainP2 p1 p2
  | ["statement", pub] => statement pub
  | ["statement-jets", pub] => statementJ pub
  | ["budget", pub, lp, li, out] => budget pub lp li out
  | "check" :: pub :: paths => check pub paths
  | "check-cj" :: src :: pub :: paths => checkCJ src pub paths
  | _ =>
    IO.eprintln "usage: composed emit DIR | composed emit-p2 DIR [K] | composed emit-handoff DIR [--fresh | --rand=FILE] | composed check-handoff PUBLIC1 PUBLIC2 | composed statement-p2 PUBLIC | composed chain-p2 PUBLIC1 PUBLIC2|- | composed check-p2-tables PUBLIC DIR | composed check-p2-blind DIR\n       composed check-c-tables PUBLIC DIR | composed check-c-blind DIR\n       composed check-cj-tables SRC PUBLIC DIR | composed check-cj-blind DIR\n       composed statement PUBLIC | composed statement-jets PUBLIC\n       composed budget PUBLIC LP LI OUT | composed check PUBLIC TABLE... | composed check-cj SRC PUBLIC TABLE..."
    return 2
