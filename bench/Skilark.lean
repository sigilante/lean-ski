import Ski.Front
import Ski.ComposedText
open Term

/-!
SKIlark statements for the composed circuit: a SKIlark predicate as the
verifier of one atom, proved in zero knowledge.

The statement `split`, from `skilark.zk` (the SKIlark repository), is
that some hidden term `w` makes `vsplit x w` reduce to `K`.  Its verifier
`vsplit` is SKIjack source; Lean compiles it here (`Front.compileFile`),
so a statement is checked against the source, not against the Python that
wrote it; that the source is `skilark.zk`'s `split` for width `k` is the
producer's word.  On a witness that is a stack of bit numerals, `vsplit`
accepts exactly two numbers below `2^k` adding up to `x`.  What the proof
shows is weaker, in two ways:

- the witness is a term, and a term answers the verifier's case analysis
  however it likes: `K (K (RVal R))`, with `R` a stack of `2k - 1`
  zeros, is no stack at all and passes at `x` = 0 or 1;
- some `a, b < 2^k` add up to every `x < 2^k` (`a = x`, `b = 0`), so even
  a well-formed witness shows only that `x < 2^k`.

It is the path from a SKIlark program to a proof, not a range proof: a
claim about data needs the witness as literal bits the circuit
constrains, and a range proof needs a commitment binding the hidden
number to something public.  `x` is one quotation of `x`'s bits,
least significant outermost; the hidden `w` is the stack of `a`'s and
`b`'s bits, interleaved, least significant first.

- `skilark emit SRC K X A B R M DIR` compiles `SRC`, and writes to `DIR`
  the statement of the atom `vsplit x` at CPU and memory heights `2^R` and
  `2^M` (`public.txt`), the honest witness (`witness.txt`: the atom's bit,
  then the region, `w`'s cells shared), and the composed circuit's four
  tamper witnesses: the bit clear (`witness_clear.txt`), `b + 1` in place
  of `b` (`witness_wrong.txt`), a bit cell that is no Boolean
  (`witness_nonbool.txt`), and a region cell pointing forward
  (`witness_forged.txt`); and `witness_nonbit.txt`, `a`'s first bit `2`.
- `skilark statement SRC K X PUBLIC` checks that `PUBLIC` is the statement
  of `vsplit x`, for `vsplit` compiled from `SRC` and `x` the bits of `X`
  in `K` bits, at any heights `ComposedText` accepts.
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

/-- `w`: `a_0 b_0 a_1 b_1 …`. -/
def wTerm (E : Enc) (da db : List Nat) : Term :=
  E.stack ((da.zip db).flatMap fun (a, b) => [E.num a, E.num b])

/-- Write `t`'s cells after `h`, children first, each distinct cell once. -/
def hcons : List (Cell × Nat) → List Cell → Term → List (Cell × Nat) × List Cell × Nat
  | memo, h, t =>
    let intern (memo : List (Cell × Nat)) (h : List Cell) (c : Cell) :=
      match memo.lookup c with
      | some a => (memo, h, a)
      | none => ((c, h.length) :: memo, h ++ [c], h.length)
    match t with
    | .S => intern memo h .S
    | .K => intern memo h .K
    | .I => intern memo h .I
    | .app f a =>
      let (m1, h1, pf) := hcons memo h f
      let (m2, h2, pa) := hcons m1 h1 a
      intern m2 h2 (.app pf pa)

/-- The region holding `w` at its last cell, after `N` bit cells: filler
    `S` cells, then `w`'s cells shared. -/
def regionShared (N W : Nat) (w : Term) : Option (List Cell) :=
  let pre := List.replicate (N + 3) Cell.S
  let n := (hcons [] pre w).2.1.length - (N + 3)
  if n ≤ W then some ((hcons [] (pre ++ List.replicate (W - n) .S) w).2.1.drop (N + 3)) else none

def witnessText (bits : List Bool) (region : List Cell) : String :=
  bits.foldl (fun s b => s ++ (if b then "1" else "0") ++ "\n") "" ++
    region.foldl (fun s c => s ++ cellText c ++ "\n") ""

def readSrc (path : String) : IO (Option (Src × Term × Enc)) := do
  let some s := compile (← IO.FS.readFile path) | return none
  let some V := s.get "vsplit" | return none
  let some E := s.enc | return none
  return some (s, V, E)

/-- The region size: the private cells the composed circuit allows, less
    the atom's bit. -/
def W : Nat := 2 ^ 8 - 1

def emit (src : String) (k x a b r m : Nat) (dir : String) : IO UInt32 := do
  if k == 0 || 2 ^ k ≤ x || 2 ^ k ≤ a || 2 ^ k ≤ b then
    IO.println s!"x, a and b must be below 2^{k}"; return 1
  let some (_, V, E) ← readSrc src | do IO.println s!"{src}: not a SKIlark statement source"; return 1
  if !logOK (r, m) then IO.println "heights out of bounds"; return 1
  let M := MF.atom V (xTerm E (bitsOf k x))
  let N := BT.nleaves (clear M)
  let w := wTerm E (bitsOf k a) (bitsOf k b)
  let some good := regionShared N W w | do IO.println "the witness does not fit"; return 1
  let some wrong := regionShared N W (wTerm E (bitsOf k a) (bitsOf k (b + 1))) | do
    IO.println "the wrong witness does not fit"; return 1
  let some nonbit := regionShared N W (wTerm E (2 :: (bitsOf k a).drop 1) (bitsOf k b)) | do
    IO.println "the non-bit witness does not fit"; return 1
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/public.txt" (publicText M W (r, m))
  IO.FS.writeFile s!"{dir}/witness.txt" (witnessText [true] good)
  IO.FS.writeFile s!"{dir}/witness_clear.txt" (witnessText [false] good)
  IO.FS.writeFile s!"{dir}/witness_wrong.txt" (witnessText [true] wrong)
  IO.FS.writeFile s!"{dir}/witness_nonbool.txt" ("I\n" ++ witnessText [] good)
  IO.FS.writeFile s!"{dir}/witness_forged.txt"
    (witnessText [true] (good.set 0 (.app (N + 3 + W - 1) (N + 3 + W - 1))))
  IO.FS.writeFile s!"{dir}/witness_nonbit.txt" (witnessText [true] nonbit)
  let used := good.length - (good.takeWhile (· == .S)).length
  IO.println s!"split k={k}: x = {x}, a = {a}, b = {b} (a + b = x: {a + b == x}); region {used} of {W} cells; heights 2^{r} and 2^{m}"
  return 0

def statement (src : String) (k x : Nat) (pub : String) : IO UInt32 := do
  if k == 0 || 2 ^ k ≤ x then IO.println s!"NOT A STATEMENT: x = {x} is not below 2^{k}"; return 1
  let some (_, V, E) ← readSrc src | do IO.println s!"{src}: not a SKIlark statement source"; return 1
  match statementOfText (← IO.FS.readFile pub) with
  | some (.atom V' x', W', lg) =>
    if V' == V && x' == xTerm E (bitsOf k x) && W' == W then
      IO.println s!"STATEMENT {pub}: some hidden term w makes vsplit x w reduce to K, for x = {x} in {k} bits (vsplit compiled from {src}; heights 2^{lg.1} and 2^{lg.2})"
      return 0
    IO.println s!"NOT THIS STATEMENT {pub}"
    return 1
  | _ =>
    IO.println s!"NOT A STATEMENT {pub}"
    return 1

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
  | _ =>
    IO.println "usage: skilark emit SRC K X A B R M DIR | skilark statement SRC K X PUBLIC"
    return 2
