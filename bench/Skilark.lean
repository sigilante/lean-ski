import Ski.Front
import Ski.ComposedText
import Ski.JetTable
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
    check-src`. -/
def jets (src : String) (k x a b : Nat) (dir : String) : IO UInt32 := do
  let text ← IO.FS.readFile src
  let some (V, E) ← readB src | do IO.println s!"{src}: not a SKIlark predicate source"; return 1
  let t := V ⬝ xTerm E (bitsOf k x) ⬝ CompM.boolsT (splitBits k a b)
  let tmpls := JetTable.fileTemplates (text.toList.map Char.toNat)
  let (roots, js) := JetTable.jetTable (Mach.load t).heap tmpls
  let mut s := s!"roots {roots.length}\n"
  for (addr, g) in roots do
    s := s ++ s!"{addr} {g}\n"
  s := s ++ s!"jets {js.length}\n"
  for J in js do
    s := s ++ JetTable.jetText J
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/split.term" (termText t ++ "\n")
  IO.FS.writeFile s!"{dir}/split.jets" s
  -- The bits' cells come last before the two applications: `load` builds
  -- `V`, then `x`, then the bits, children first.
  let bitsStart := (Mach.build (Mach.build [] V).1 (xTerm E (bitsOf k x))).1.length
  IO.println s!"split k={k}, x = {x}, a = {a}, b = {b}: {tmpls.length} templates, {js.length} jets, {roots.length} roots, loaded heap {(Mach.load t).heap.length} cells, the bits' cells from {bitsStart}"
  return 0

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
  | ["cstatement", src, k, m, seed, x, c, pub] =>
    match n k, n m, n seed, n x, n c with
    | some k, some m, some seed, some x, some c => SkilarkZK.cstatement src k m seed x c pub
    | _, _, _, _, _ => IO.println "bad numbers"; return 2
  | _ =>
    IO.println "usage: skilark emit SRC K X A B R M DIR | skilark statement SRC K X PUBLIC\n       skilark cemit SRC K M SEED X A B R RLOG MLOG DIR | skilark cstatement SRC K M SEED X C PUBLIC"
    return 2
