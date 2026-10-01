import Ski.Front
import Ski.ComposedText
import Ski.JetPublic
import Ski.JetRun
open Term

/-!
SKIlark predicates in zero knowledge: a SKIlark program as the verifier of
a predicate statement over literal bits (`Ski/Predicate.lean`), proved by
the composed circuit.

The predicate `split`, from `skilark.zk` (the SKIlark repository): its
verifier `vsplitB x r` decodes `r`, `2k` literal bits, into the bits of two
numbers `a` and `b` (interleaved, least significant first), and accepts
when they add up to `x` in `k` bits.  Lean compiles it here from its
SKIjack source (`Front.compileFile`), so a statement is checked against
the source, not the Python that wrote it; that the source is
`skilark.zk`'s `split` for width `k` is the producer's word.  `x` is one
quotation of its bits, least significant outermost.

**What an accepted proof shows** (`Circuit.predExport_sound`): the proof's
memory holds `2k` Booleans `bs` with `vsplitB x (boolsT bs)` evaluating to
`K`.  The bits are the circuit's constrained slot cells, `K` or `K I`, so
the verifier runs on data a prover cannot shape.  That `vsplitB` accepts
exactly the bits of two numbers adding up to `x` is tested, not proved:
exhaustively at `k` = 2 and 3, sampled at `k = 8` (`tests/test_zk.py`).
And the claim is weak: some `a, b < 2^k` add up to every `x < 2^k`
(`a = x`, `b = 0`), so an accepted proof shows only that `x < 2^k`.  A
range proof needs a commitment binding the hidden number to something
public.

- `skilark emit SRC K X A B R M DIR` compiles `SRC` and writes to `DIR`
  the predicate statement `vsplitB x` over `2K` bits at CPU and memory
  heights `2^R` and `2^M` (`public.txt`), the honest witness (the bits of
  `A` and `B`, then a one-cell region: `witness.txt`), and the composed
  circuit's four tamper witnesses: every bit clear (`witness_clear.txt`),
  the bits of `B + 1` for `B` (`witness_wrong.txt`), a bit cell that is no
  Boolean (`witness_nonbool.txt`), and a region cell pointing forward
  (`witness_forged.txt`).
- `skilark statement SRC K X PUBLIC` checks that `PUBLIC` is the predicate
  statement `vsplitB x` over `2K` bits, for `vsplitB` compiled from `SRC`
  and `x` the bits of `X < 2^K`, at any heights `ComposedText` accepts.
-/

open Mach Compose ComposedText CompM

namespace SkilarkZK

def nm (s : String) : List Nat := s.toList.map Char.toNat

/-- The compiled source's terms, by name. -/
structure Src where
  terms : List (List Nat × Term)

def Src.get (s : Src) (n : String) : Option Term := s.terms.lookup (nm n)

def compile (text : String) : Option Src :=
  (Front.compileFile (text.toList.map Char.toNat)).map (⟨·⟩)

def apps (f : Term) : List Term → Term
  | [] => f
  | a :: r => apps (f ⬝ a) r

/-- The bits of `n`, least significant first. -/
def bitsOf (k n : Nat) : List Nat := (List.range k).map fun i => n / 2 ^ i % 2

section
variable (Zero Suc Num Quot QCons QUnit Push Empty : Term)

def numT (n : Nat) : Term := Num ⬝ (Nat.repeat (Suc ⬝ ·) n Zero)

/-- A quotation's body pushing `items` in order (at least one). -/
def quotBody : List Term → Term
  | [] => QUnit
  | [t] => QUnit ⬝ t
  | t :: r => QCons ⬝ t ⬝ quotBody r

def quotT (items : List Term) : Term := Quot ⬝ quotBody QCons QUnit items

def stackT : List Term → Term
  | [] => Empty
  | t :: r => Push ⬝ t ⬝ stackT r

end
/-- The encoders, from the compiled constructors. -/
structure Enc where
  num : Nat → Term
  quot : List Term → Term
  stack : List Term → Term

def Src.enc (s : Src) : Option Enc := do
  let Zero ← s.get "Zero"; let Suc ← s.get "Suc"; let Num ← s.get "Num"
  let Quot ← s.get "Quot"; let QCons ← s.get "QCons"; let QUnit ← s.get "QUnit"
  let Push ← s.get "Push"; let Empty ← s.get "Empty"
  some ⟨numT Zero Suc Num, quotT Quot QCons QUnit, stackT Push Empty⟩

/-- `x`: `X_i = [X_{i+1} x_i]`, `X_{k-1} = [x_{k-1}]`. -/
def xTerm (E : Enc) (ds : List Nat) : Term :=
  let rec go : List Nat → Term
    | [] => E.quot []
    | [d] => E.quot [E.num d]
    | d :: r => E.quot [go r, E.num d]
  E.stack [go ds]

def witnessText (bits : List Bool) (region : List Cell) : String :=
  bits.foldl (fun s b => s ++ (if b then "1" else "0") ++ "\n") "" ++
    region.foldl (fun s c => s ++ cellText c ++ "\n") ""

/-- The region: one cell, since the predicate reads no witness. -/
def W : Nat := 1

def readB (path : String) : IO (Option (Term × Enc)) := do
  let some s := compile (← IO.FS.readFile path) | return none
  let some V := s.get "vsplitB" | return none
  let some E := s.enc | return none
  return some (V, E)

/-- `a`'s and `b`'s bits, interleaved, least significant first. -/
def splitBits (k a b : Nat) : List Bool :=
  ((bitsOf k a).zip (bitsOf k b)).flatMap fun (u, v) => [u == 1, v == 1]

def emit (src : String) (k x a b r m : Nat) (dir : String) : IO UInt32 := do
  if k == 0 || 2 ^ k ≤ x || 2 ^ k ≤ a || 2 ^ k ≤ b then
    IO.println s!"x, a and b must be below 2^{k}"; return 1
  let some (V, E) ← readB src | do IO.println s!"{src}: not a SKIlark predicate source"; return 1
  if !logOK (r, m) then IO.println "heights out of bounds"; return 1
  let c := CStmt.pred V (xTerm E (bitsOf k x)) (2 * k)
  if !privateOK c W then IO.println "too many bits"; return 1
  let N := 2 * k
  let bits := splitBits k a b
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/public.txt" (publicTextC c W (r, m))
  IO.FS.writeFile s!"{dir}/witness.txt" (witnessText bits [.S])
  IO.FS.writeFile s!"{dir}/witness_clear.txt" (witnessText (bits.map fun _ => false) [.S])
  IO.FS.writeFile s!"{dir}/witness_wrong.txt" (witnessText (splitBits k a ((b + 1) % 2 ^ k)) [.S])
  IO.FS.writeFile s!"{dir}/witness_nonbool.txt" ("I\n" ++ witnessText (bits.drop 1) [.S])
  IO.FS.writeFile s!"{dir}/witness_forged.txt" (witnessText bits [.app (N + 3) (N + 3)])
  IO.println s!"split k={k}: x = {x}, a = {a}, b = {b} (a + b = x: {a + b == x}); {N} bits, heights 2^{r} and 2^{m}"
  return 0

def statement (src : String) (k x : Nat) (pub : String) : IO UInt32 := do
  if k == 0 || 2 ^ k ≤ x then IO.println s!"NOT A STATEMENT: x = {x} is not below 2^{k}"; return 1
  let some (V, E) ← readB src | do IO.println s!"{src}: not a SKIlark predicate source"; return 1
  match statementOfText (← IO.FS.readFile pub) with
  | some (.pred V' x' n, W', lg) =>
    if V' == V && x' == xTerm E (bitsOf k x) && n == 2 * k && W' == W then
      IO.println s!"STATEMENT {pub}: some {2 * k} literal bits make vsplitB accept x = {x} in {k} bits (vsplitB compiled from {src}; heights 2^{lg.1} and 2^{lg.2})"
      return 0
    IO.println s!"NOT THIS STATEMENT {pub}"
    return 1
  | _ =>
    IO.println s!"NOT A PREDICATE STATEMENT {pub}"
    return 1

-- ---------------------------------------------------------------------------
-- The committed split
-- ---------------------------------------------------------------------------

/-- The knapsack's public weights, `skilark.zk.weights`: from `seed`, a
    linear congruential sequence, each weight `1 + x mod (bound - 1)`. -/
def weightsOf (n seed bound : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat
    | 0, _ => []
    | n + 1, x =>
      let x' := (x * 1103515245 + 12345) % 2 ^ 31
      (1 + x' % (bound - 1)) :: go n x'
  go n seed

/-- The toy commitment: the weights of `a`'s and `r`'s set bits, summed. -/
def commitOf (k m : Nat) (ws : List Nat) (a r : Nat) : Nat :=
  ((ws.zip (bitsOf k a ++ bitsOf m r)).map fun (w, d) => w * d).sum

/-- `x` for the committed split: `X_i = [X_{i+1} A_i x_i]`, the last
    `[[C W] A x]`, `W_j = [W_{j+1} B_j]` the weights of `r`. -/
def xcTerm (E : Enc) (k _m : Nat) (ws : List Nat) (x c : Nat) : Term :=
  let rs := ws.drop k
  let rec goW : List Nat → Term
    | [] => E.quot []
    | [b] => E.quot [E.num b]
    | b :: r => E.quot [goW r, E.num b]
  let cw := E.quot [E.num c, goW rs]
  let rec goX : List (Nat × Nat) → Term
    | [] => E.quot []
    | [(w, d)] => E.quot [cw, E.num w, E.num d]
    | (w, d) :: r => E.quot [goX r, E.num w, E.num d]
  E.stack [goX ((ws.take k).zip (bitsOf k x))]

/-- The committed split's bits: `a`'s and `b`'s interleaved, then `r`'s. -/
def cbits (k m a b r : Nat) : List Bool := splitBits k a b ++ (bitsOf m r).map (· == 1)

def readC (path : String) : IO (Option (Term × Enc)) := do
  let some s := compile (← IO.FS.readFile path) | return none
  let some V := s.get "vcsplitB" | return none
  let some E := s.enc | return none
  return some (V, E)

/-- The weights' bound, `skilark.zk.weights`'s default. -/
def bound : Nat := 64

def cemit (src : String) (k m seed x a b r rl ml : Nat) (dir : String) : IO UInt32 := do
  if k == 0 || m == 0 || 2 ^ k ≤ x || 2 ^ k ≤ a || 2 ^ k ≤ b || 2 ^ m ≤ r then
    IO.println s!"k and m positive, x, a, b below 2^{k}, r below 2^{m}"; return 1
  let some (V, E) ← readC src | do IO.println s!"{src}: not a committed split's source"; return 1
  if !logOK (rl, ml) then IO.println "heights out of bounds"; return 1
  let ws := weightsOf (k + m) seed bound
  let c := commitOf k m ws a r
  let st := CStmt.pred V (xcTerm E k m ws x c) (2 * k + m)
  if !privateOK st W then IO.println "too many bits"; return 1
  let N := 2 * k + m
  let bits := cbits k m a b r
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/public.txt" (publicTextC st W (rl, ml))
  IO.FS.writeFile s!"{dir}/witness.txt" (witnessText bits [.S])
  IO.FS.writeFile s!"{dir}/witness_clear.txt" (witnessText (bits.map fun _ => false) [.S])
  IO.FS.writeFile s!"{dir}/witness_wrong.txt" (witnessText (cbits k m a b (r ^^^ 1)) [.S])
  IO.FS.writeFile s!"{dir}/witness_nonbool.txt" ("I\n" ++ witnessText (bits.drop 1) [.S])
  IO.FS.writeFile s!"{dir}/witness_forged.txt" (witnessText bits [.app (N + 3) (N + 3)])
  IO.println s!"csplit k={k} m={m} seed={seed}: x = {x}, c = {c}; a = {a}, b = {b}, r = {r} (a + b = x: {a + b == x}); weights {ws}; {N} bits, heights 2^{rl} and 2^{ml}"
  return 0

def cstatement (src : String) (k m seed x c : Nat) (pub : String) : IO UInt32 := do
  if k == 0 || m == 0 || 2 ^ k ≤ x then IO.println s!"NOT A STATEMENT: bad sizes, or x = {x} not below 2^{k}"; return 1
  let some (V, E) ← readC src | do IO.println s!"{src}: not a committed split's source"; return 1
  let ws := weightsOf (k + m) seed bound
  match statementOfText (← IO.FS.readFile pub) with
  | some (.pred V' x' n, W', lg) =>
    if V' == V && x' == xcTerm E k m ws x c && n == 2 * k + m && W' == W then
      IO.println s!"STATEMENT {pub}: some {2 * k + m} literal bits make vcsplitB accept x = {x} and c = {c}, weights {ws} (vcsplitB compiled from {src}; heights 2^{lg.1} and 2^{lg.2})"
      return 0
    IO.println s!"NOT THIS STATEMENT {pub}"
    return 1
  | _ =>
    IO.println s!"NOT A PREDICATE STATEMENT {pub}"
    return 1

-- ---------------------------------------------------------------------------
-- In the clear, with jets
-- ---------------------------------------------------------------------------

/-- `skilark jets SRC K X A B DIR`: the closed term `vsplitB x (boolsT bits)`
    of `split`'s verifier, in the clear, and its jet table from the
    source's own templates (`JetTable.fileTemplates`): `DIR/split.term`,
    `DIR/split.jets`, for `ski-air jets-measure` and `lake exe jets
    check-src`.  Then the closure rule (`Air.publicB`) with the bits'
    cells private: `DIR/split_pub.jets`, and both tables' runs counted
    (`JetRun.runJ`).  A measurement in the clear, over the heap of these
    bits: the verifier's table is `cjets`'s, over the blank composed heap. -/
def jets (src : String) (k x a b : Nat) (dir : String) : IO UInt32 := do
  let text ← IO.FS.readFile src
  let some (V, E) ← readB src | do IO.println s!"{src}: not a SKIlark predicate source"; return 1
  let t := V ⬝ xTerm E (bitsOf k x) ⬝ CompM.boolsT (splitBits k a b)
  let tmpls := JetTable.fileTemplates (text.toList.map Char.toNat)
  let (roots, js) := JetTable.jetTable (Mach.load t).heap tmpls
  let s := JetTable.tableText roots js
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/split.term" (termText t ++ "\n")
  IO.FS.writeFile s!"{dir}/split.jets" s
  -- The bits' cells come last before the two applications: `load` builds
  -- `V`, then `x`, then the bits, children first.
  let bitsStart := (Mach.build (Mach.build [] V).1 (xTerm E (bitsOf k x))).1.length
  IO.println s!"split k={k}, x = {x}, a = {a}, b = {b}: {tmpls.length} templates, {js.length} jets, {roots.length} roots, loaded heap {(Mach.load t).heap.length} cells, the bits' cells from {bitsStart}"
  let bitsEnd := (Mach.build (Mach.build (Mach.build [] V).1 (xTerm E (bitsOf k x))).1
    (CompM.boolsT (splitBits k a b))).1.length
  let priv := fun i => decide (bitsStart ≤ i) && decide (i < bitsEnd)
  let (rootsP, jsP) := JetTable.jetTable (Mach.load t).heap tmpls (priv := priv)
  IO.FS.writeFile s!"{dir}/split_pub.jets" (JetTable.tableText rootsP jsP)
  let pubOK := Air.publicB (Mach.load t).heap priv rootsP jsP && Air.rootsOKB (Mach.load t).heap rootsP jsP
  IO.println s!"  the closure rule, the bits' cells [{bitsStart}, {bitsEnd}) private: {jsP.length} jets, {rootsP.length} roots ({roots.length - rootsP.length} dropped); publicB and rootsOKB: {pubOK}"
  let m := Mach.load t
  let heap := m.heap.toArray
  let fuel := 2 ^ 22
  for (label, rs, jss) in [("jetted     ", roots, js), ("closure rule", rootsP, jsP)] do
    match JetRun.runJ (JetRun.rootMap rs jss) heap m.hd m.stk fuel with
    | some (sf, c, rows) =>
      let acc := Air.checkJA sf.1 m rs jss rows.toList
      IO.println s!"  {label}  rows {c.rows} = {c.cpu} cpu + {c.pop} pop + {c.instw} instw, cells {c.cells}, {c.insts} insts, halts at {repr (JetRun.shape sf)}; checkJA {acc}"
    | none => IO.println s!"  {label}  did not halt"
  return 0

-- ---------------------------------------------------------------------------
-- A composed statement's jets, under the closure rule
-- ---------------------------------------------------------------------------

/-- The composed statement of `PUBLIC`, its bits' shape, region size and
    terms, as the verifier holds it (`statementOfText`), with or without
    jet budgets (`statementOfTextJ`). -/
def readStmt (pub : String) : IO (Option (CStmt × Nat)) := do
  match statementOfTextAny (← IO.FS.readFile pub) with
  | some (c, W', _) => return some (c, W')
  | none => return none

def srcTemplates (src : String) : IO (List (List Nat × OTerm)) := do
  return JetTable.fileTemplates ((← IO.FS.readFile src).toList.map Char.toNat)

/-- `skilark cjets SRC PUBLIC OUT [--no-rule]`: the jet table of the
    composed statement `PUBLIC` over its blank heap, from the templates of
    `SRC`, under the closure rule (`Air.jetTableC`), written to `OUT`; with
    `--no-rule`, the table without it, which the statement check refuses. -/
def cjets (src pub out : String) (noRule : Bool := false) : IO UInt32 := do
  let some (c, W') ← readStmt pub | do IO.println s!"NOT A STATEMENT {pub}"; return 1
  let tmpls ← srcTemplates src
  let blank := (cMachine (fun _ => false) c.shp (List.replicate W' .S) c.Ps).heap
  let (roots, js) := Air.jetTableC c.shp W' c.Ps tmpls
  let (roots0, js0) := JetTable.jetTable blank tmpls
  IO.FS.writeFile out (if noRule then JetTable.tableText roots0 js0 else JetTable.tableText roots js)
  let N := BT.nleaves c.shp
  IO.println s!"{pub}: blank heap {blank.length} cells, private [3, {3 + N + W'}); {tmpls.length} templates"
  let priv := Air.privC N W'
  let privGlobs := js0.foldl (fun n J => n + (J.glob.filter fun (_, a) => !Air.pubAtG (fun i => blank[i]?) priv (blank.length + 1) a).length) 0
  IO.println s!"  without the rule: {js0.length} jets, {roots0.length} roots; rootsOKB {Air.rootsOKB blank roots0 js0}, publicB {Air.publicB blank priv roots0 js0}: {(roots0.filter fun (a, _) => !Air.pubAtG (fun i => blank[i]?) priv (blank.length + 1) a).length} roots and {privGlobs} globals reach a private cell"
  IO.println s!"  the closure rule: {js.length} jets, {roots.length} roots ({roots0.length - roots.length} dropped); {if noRule then "the table without it" else "the table"} written to {out}"
  return 0

/-- `skilark cjets-statement SRC PUBLIC JETS`: the verifier's check of a
    composed statement's jet table (`Air.jetStmtC`): `JETS` is the table
    Lean computes over `PUBLIC`'s blank heap from `SRC`'s templates, its
    roots licensed (`rootsOKB`) and their closures public (`publicB`).
    Accepted, the roots are licensed over every filled heap
    (`Air.jetStmtC_sound`). -/
def cjetsStatement (src pub jf : String) : IO UInt32 := do
  let some (c, W') ← readStmt pub | do IO.println s!"NOT A STATEMENT {pub}"; return 1
  let tmpls ← srcTemplates src
  let text ← IO.FS.readFile jf
  if Air.jetStmtC text c.shp W' c.Ps tmpls then
    IO.println s!"ACCEPT {jf}: the jet table of {pub}, licensed over every filled heap (Air.jetStmtC_sound)"
    return 0
  -- why not: the same checks, on the table as given
  let blank := (cMachine (fun _ => false) c.shp (List.replicate W' .S) c.Ps).heap
  let (roots, js) := Air.jetTableC c.shp W' c.Ps tmpls
  IO.println s!"REFUSE {jf}: {if text == JetTable.tableText roots js then "the table Lean computes, but" else "not the table Lean computes; Lean's own table:"} rootsOKB {Air.rootsOKB blank roots js}, publicB {Air.publicB blank (Air.privC (BT.nleaves c.shp) W') roots js}"
  return 1

/-- Parse a witness file: `N` bits, `0` or `1`, then the region's cells. -/
def readWitness (path : String) (N : Nat) : IO (Option (List Bool × List Cell)) := do
  let ls := ((← IO.FS.readFile path).splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let bits := (ls.take N).map fun l => l.trimAscii.toString == "1"
  let cells := (ls.drop N).filterMap fun l => parseCell (words l.trimAscii.toString)
  if (ls.take N).length != N || cells.length != (ls.drop N).length then return none
  return some (bits, cells)

/-- `skilark cjets-measure SRC PUBLIC WITNESS`: a predicate statement's run
    over its **filled** heap (the witness's bits and region), plain, jetted
    in the clear (the table over the filled heap, no rule), and with the
    statement's table (over the blank heap, the closure rule), counted by
    `JetRun.runJ`; each run's table checked by `Air.checkJA` from the
    filled machine.  A measurement: the witness itself is not checked
    (bit mode, `cellOK`; `lake exe composed check` does that), so a forged
    witness measures too. -/
def cjetsMeasure (src pub wit : String) : IO UInt32 := do
  let some (c, W') ← readStmt pub | do IO.println s!"NOT A STATEMENT {pub}"; return 1
  if c.Ps.length != 1 then IO.println "one term only"; return 1
  let N := BT.nleaves c.shp
  let some (bits, region) ← readWitness wit N | do IO.println s!"MALFORMED {wit}"; return 1
  if region.length != W' then IO.println s!"the region is not {W'} cells"; return 1
  let tmpls ← srcTemplates src
  let m := cMachine (fun n => bits.getD n false) c.shp region c.Ps
  let heap := m.heap.toArray
  let (rootsS, jsS) := Air.jetTableC c.shp W' c.Ps tmpls
  let (rootsF, jsF) := JetTable.jetTable m.heap tmpls
  IO.println s!"{pub} with {wit} (measured, not checked): filled heap {heap.size} cells; the statement's table {jsS.length} jets, {rootsS.length} roots; in the clear {jsF.length} jets, {rootsF.length} roots"
  let blank := (cMachine (fun _ => false) c.shp (List.replicate W' .S) c.Ps).heap
  let (roots0, js0) := JetTable.jetTable blank tmpls
  IO.println s!"  licensed over this filled heap (rootsOKB): the statement's table {Air.rootsOKB m.heap rootsS jsS}; the blank heap's table without the rule {Air.rootsOKB m.heap roots0 js0}"
  let fuel := 2 ^ 22
  let mut bad := 0
  let mut plain := 0
  for (label, rs, jss) in [("plain       ", [], []), ("in the clear", rootsF, jsF), ("the rule    ", rootsS, jsS)] do
    match JetRun.runJ (JetRun.rootMap rs jss) heap m.hd m.stk fuel with
    | some (sf, cst, rows) =>
      let halts := JetRun.shape sf == (some .K, 0)
      let acc := Air.checkJA sf.1 m rs jss rows.toList
      if label == "plain       " then plain := cst.cpu
      if !halts || !acc then bad := bad + 1
      IO.println s!"  {label}  cpu {cst.cpu} ({JetRun.pct cst.cpu plain}), pop {cst.pop}, instw {cst.instw}, cells {cst.cells}, {cst.insts} insts; {if halts then "halts at K over the nil" else "DOES NOT HALT AT K"}; checkJA {acc}"
    | none =>
      bad := bad + 1
      IO.println s!"  {label}  did not halt"
  return (if bad == 0 then 0 else 1)

end SkilarkZK

def main (args : List String) : IO UInt32 := do
  let n (s : String) : Option Nat := s.toNat?
  match args with
  | ["emit", src, k, x, a, b, r, m, dir] =>
    match n k, n x, n a, n b, n r, n m with
    | some k, some x, some a, some b, some r, some m => SkilarkZK.emit src k x a b r m dir
    | _, _, _, _, _, _ => IO.println "bad numbers"; return 2
  | ["statement", src, k, x, pub] =>
    match n k, n x with
    | some k, some x => SkilarkZK.statement src k x pub
    | _, _ => IO.println "bad numbers"; return 2
  | ["cemit", src, k, m, seed, x, a, b, r, rl, ml, dir] =>
    match n k, n m, n seed, n x, n a, n b, n r, n rl, n ml with
    | some k, some m, some seed, some x, some a, some b, some r, some rl, some ml =>
      SkilarkZK.cemit src k m seed x a b r rl ml dir
    | _, _, _, _, _, _, _, _, _ => IO.println "bad numbers"; return 2
  | ["jets", src, k, x, a, b, dir] =>
    match n k, n x, n a, n b with
    | some k, some x, some a, some b => SkilarkZK.jets src k x a b dir
    | _, _, _, _ => IO.println "bad numbers"; return 2
  | ["cjets", src, pub, out] => SkilarkZK.cjets src pub out
  | ["cjets", src, pub, out, "--no-rule"] => SkilarkZK.cjets src pub out true
  | ["cjets-statement", src, pub, jf] => SkilarkZK.cjetsStatement src pub jf
  | ["cjets-measure", src, pub, wit] => SkilarkZK.cjetsMeasure src pub wit
  | ["cstatement", src, k, m, seed, x, c, pub] =>
    match n k, n m, n seed, n x, n c with
    | some k, some m, some seed, some x, some c => SkilarkZK.cstatement src k m seed x c pub
    | _, _, _, _, _ => IO.println "bad numbers"; return 2
  | _ =>
    IO.println "usage: skilark emit SRC K X A B R M DIR | skilark statement SRC K X PUBLIC\n       skilark cemit SRC K M SEED X A B R RLOG MLOG DIR | skilark cstatement SRC K M SEED X C PUBLIC\n       skilark jets SRC K X A B DIR\n       skilark cjets SRC PUBLIC OUT [--no-rule] | skilark cjets-statement SRC PUBLIC JETS | skilark cjets-measure SRC PUBLIC WITNESS"
    return 2
