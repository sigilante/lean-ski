import Ski.PsiSkel
import Lean
import Ski.GCertData
open Term

/-!
# Rank certificate for the finite graph fact G: the checker

`notes/S4-bounded-exposure.md`, section R6.  A *root frame* is an hnf-less term `S x y z`; a
*round* leads from one root frame to the next.  Two abstractions of a round on blocks:

* **coarse** (G1): `T(x, y, z) ↦ T(a, z, β y z)` if `x = β 0 a` is a one-item block; otherwise
  `T(x, y, z) ↦ M(h, w, z) ↦ T(p, β y' p, w)` with `h = β x z`, `w = β y z`, `p ∈ Lz z` and
  `β (β 1 y') p = h`;
* **fine** (G2), on nodes `(c, e, y, z)` with `x = β c e`, used on the `fine` triples (the
  nontrivial strongly connected component of G1): the states `(n, P, a, b, eb)` of the frame
  `pre ++ [a, b]` of `x z` (`P` the block of `S pre`, `n = 3` iff `pre` has one item, `eb` the
  block of the argument part of `b` once `b` has changed), with the successors `stepAll`.

The certificate (`Ski/GCertData.lean`) is a rank for each node and an invariant set of states
for each fine start.  This module checks in the kernel that every edge lowers the rank by at
least the weight of its source: `1 + pw (β x z)` if `x` has at least two items, `0` otherwise.
So the weights along any path sum to at most the rank of its start, which is at most 67.

A chain node has weight `0`, so the rank may stay the same along chain edges, as it must at the
chain loop `(0, 27, 36, 36)`.  The certificate therefore bounds the weighted number of other
rounds; it does not show that the graphs are acyclic apart from that loop, nor that the fine
triples are a strongly connected component (they are any set on which the checks pass).
-/

namespace GCert
open HnfS HnfSound PsiSkel

/-! ## Tables

Fast copies of `β`, `pw`, `oneBlocks`, `combBlocks` (proved equal to the originals in
`Ski/GCertSound.lean`) and the certificate lookups. -/

def m228 : Nat := 2 ^ 228 - 1
def m266 : Nat := 2 ^ 266 - 1
def m532 : Nat := 2 ^ 532 - 1
def m10108 : Nat := 2 ^ 10108 - 1
def m20216 : Nat := 2 ^ 20216 - 1

def bf (a b : Nat) : Nat :=
  bif Nat.ble 38 a || Nat.ble 38 b then 36 else (((bN >>> (228 * a)) &&& m228) >>> (6 * b)) &&& 63
def pwf (q : Nat) : Nat := bif Nat.ble 38 q then 0 else (pwN >>> (4 * q)) &&& 15
def isOne (x : Nat) : Bool := !Nat.ble 38 x && Nat.beq ((oneN >>> x) &&& 1) 1
def isComb (x : Nat) : Bool := !Nat.ble 38 x && Nat.beq ((combN >>> x) &&& 1) 1

def rho1 (x y z : Nat) : Nat :=
  (((((rho1N >>> (10108 * x)) &&& m10108) >>> (266 * y)) &&& m266) >>> (7 * z)) &&& 127
def rhoM (h w z : Nat) : Nat :=
  (((((rhoMN >>> (10108 * h)) &&& m10108) >>> (266 * w)) &&& m266) >>> (7 * z)) &&& 127
def zb (z : Nat) : Nat := bif Nat.beq z 36 then 1 else 0
def rho2 (c e y z : Nat) : Nat :=
  (((((rho2N >>> (20216 * c)) &&& m20216) >>> (532 * e)) &&& m532) >>> (7 * (y * 2 + zb z))) &&& 127
/-- The fine triples: the nontrivial strongly connected component of the coarse graph. -/
def fine (x y z : Nat) : Bool :=
  (Nat.beq z 31 || Nat.beq z 36) && Nat.beq ((fineN >>> ((x * 38 + y) * 2 + zb z)) &&& 1) 1
/-- Blocks of a root frame: the head is not a right comb and the frame is hnf-less. -/
def valid (x y z : Nat) : Bool := !isComb x && Nat.beq (bf (bf (bf 0 x) y) z) 36
/-- The rank of the root frame `S (c e) y z`. -/
def phi (c e y z : Nat) : Nat := bif fine (bf c e) y z then rho2 c e y z else rho1 (bf c e) y z

/-! ## Coarse checks -/

/-- Chain rounds outside the fine triples. -/
def a1B (a : Nat) : Bool := r38.all fun y => r38.all fun z =>
  !(valid (bf 0 a) y z && !fine (bf 0 a) y z && valid a z (bf y z)) ||
    Nat.ble (rho1 a z (bf y z)) (rho1 (bf 0 a) y z)
/-- Other rounds outside the fine triples, first half. -/
def a2B (x : Nat) : Bool := r38.all fun y => r38.all fun z =>
  !(valid x y z && !isOne x && !fine x y z) ||
    Nat.ble (1 + pwf (bf x z) + rhoM (bf x z) (bf y z) z) (rho1 x y z)
/-- Other rounds, second half. -/
def a3B (z : Nat) : Bool := (Lz z).all fun p => isComb p || r38.all fun y' =>
  Nat.beq (bf (bf 1 y') p) 36 || r38.all fun w =>
    !Nat.beq (bf (bf (bf 0 p) (bf y' p)) w) 36 ||
      Nat.ble (rho1 p (bf y' p) w) (rhoM (bf (bf 1 y') p) w z)
/-- On a fine triple the coarse rank bounds the fine ranks. -/
def cB (c : Nat) : Bool := r38.all fun e => r38.all fun y => [31, 36].all fun z =>
  !(fine (bf c e) y z) || Nat.ble (rho2 c e y z) (rho1 (bf c e) y z)
def bndB (x : Nat) : Bool := r38.all fun y => r38.all fun z => Nat.ble (rho1 x y z) 67

/-! ## Round states -/

def mk (l P a b k : Nat) : Nat := (((l * 38 + P) * 38 + a) * 38 + b) * 39 + k
def sK (s : Nat) : Nat := s % 39
def sB (s : Nat) : Nat := s / 39 % 38
def sA (s : Nat) : Nat := s / 1482 % 38
def sP (s : Nat) : Nat := s / 56316 % 38
def sL (s : Nat) : Nat := s / 2140008
/-- The block of the term a state describes. -/
def sH (s : Nat) : Nat := bf (bf (sP s) (sA s)) (sB s)

/-- `f` holds of every successor of the state `s`. -/
def stepAll (s : Nat) (f : Nat → Bool) : Bool :=
  bif Nat.beq (sL s) 1 then
    r38.all fun x => !(Nat.beq (bf 0 x) (sP s) && !Nat.beq x 0) ||
      f (mk (bif isOne x then 1 else 0) x (sB s) (bf (sA s) (sB s)) (sB s + 1))
  else
    r38.all fun x => r38.all fun y => !(Nat.beq (bf (bf 0 x) y) (sP s)) ||
      f (mk (bif Nat.beq x 0 then 1 else 0) (bf x (sA s)) (bf y (sA s)) (sB s) (sK s))

def inv (c e z : Nat) : List Nat := invRow ((c * 38 + e) * 2 + zb z)

/-- The invariant set of `(c, e, z)` is closed under the successors that keep the block. -/
def invOK (c e z : Nat) : Bool :=
  (inv c e z).all fun s => stepAll s fun t =>
    !Nat.beq (sH t) (bf (bf c e) z) || (inv c e z).any fun u => Nat.beq u t
def invB (c : Nat) : Bool := r38.all fun e => invOK c e 31 && invOK c e 36

/-! ## Fine checks -/

/-- A fine chain node `(0, e, y, z)`: the next root frame is `S e z (y z)`. -/
def chainOK (e y z : Nat) : Bool :=
  !(valid e z (bf y z)) || r38.all fun c2 => r38.all fun e2 =>
    !(Nat.beq (bf c2 e2) e) || Nat.ble (phi c2 e2 z (bf y z)) (rho2 0 e y z)
/-- A fine node `(c, e, y, z)` with `c ≠ 0`: the ends of the round are the final states
(`n = 3`, `P = 1`) of the invariant set. -/
def otherOK (c e y z : Nat) : Bool :=
  Nat.ble (1 + pwf (bf (bf c e) z)) (rho2 c e y z) && (Nat.beq (bf (bf c e) z) 36 ||
    ((inv c e z).any (fun u => Nat.beq u (mk (bif isOne c then 1 else 0) c e z 0)) &&
     (inv c e z).all fun s =>
       !(Nat.beq (sL s) 1 && Nat.beq (sP s) 1 && valid (sB s) (bf (sA s) (sB s)) (bf y z)) ||
         (bif Nat.beq (sK s) 0 then
            Nat.ble (1 + pwf (bf (bf c e) z) + rho1 (sB s) (bf (sA s) (sB s)) (bf y z)) (rho2 c e y z)
          else r38.all fun c2 => !(Nat.beq (bf c2 (sK s - 1)) (sB s)) ||
            Nat.ble (1 + pwf (bf (bf c e) z) + phi c2 (sK s - 1) (bf (sA s) (sB s)) (bf y z))
              (rho2 c e y z))))
def b0B (e : Nat) : Bool := r38.all fun y => [31, 36].all fun z =>
  !(fine (bf 0 e) y z) || chainOK e y z
def bB (c : Nat) : Bool := r38.all fun e => r38.all fun y => [31, 36].all fun z =>
  !(fine (bf c e) y z) || Nat.beq c 0 || otherOK c e y z

/-! ## The fast copies agree with the originals (finite checks) -/

def bfB : Bool := r38.all fun a => r38.all fun b => Nat.beq (bf a b) (β a b)
def pwfB : Bool := r38.all fun q => Nat.beq (pwf q) (pw q)
def oneFB : Bool := r38.all fun x => isOne x == oneBlocks.contains x
def combFB : Bool := r38.all fun x => isComb x == combBlocks.contains x
def rowLenB : Bool := blockTable.length == 38 && blockTable.all fun r => r.length == 38

/-! ## The kernel checks

One theorem for each value of the first coordinate, checked one after another
(`Elab.async false`): the kernel keeps its caches for the length of one check.  Measured: the
module builds in about 155 s with a peak of 2.4 GB. -/

set_option Elab.async false

theorem bfB_eq : bfB = true := by decide +kernel
theorem pwfB_eq : pwfB = true := by decide +kernel
theorem oneFB_eq : oneFB = true := by decide +kernel
theorem combFB_eq : combFB = true := by decide +kernel
theorem rowLenB_eq : rowLenB = true := by decide +kernel

theorem below_zero (p : Nat → Prop) : ∀ z, z < 0 → p z := fun _ h => absurd h (Nat.not_lt_zero _)
theorem below_succ (p : Nat → Prop) (n : Nat) (h : ∀ z, z < n → p z) (hn : p n) :
    ∀ z, z < n + 1 → p z := fun z hz =>
  (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hz)).elim (h z) (fun e => e ▸ hn)

open Lean Elab Command in
/-- `chunks38 nm f` proves `nm_i : f i = true` for `i < 38` by `decide +kernel`, one theorem
each, and `nm : ∀ z, z < 38 → f z = true`. -/
elab "chunks38 " nm:ident f:ident : command => do
  let mut acc : TSyntax `term ← `(below_zero (fun z => $f z = true))
  for i in [0:38] do
    let id := mkIdent (nm.getId.appendAfter s!"_{i}")
    elabCommand (← `(theorem $id : $f $(quote i) = true := by decide +kernel))
    acc ← `(below_succ (fun z => $f z = true) $(quote i) $acc $id)
  elabCommand (← `(theorem $nm : ∀ z, z < 38 → $f z = true := $acc))

chunks38 a1 a1B
chunks38 a2 a2B
chunks38 a3 a3B
chunks38 cc cB
chunks38 bnd bndB
chunks38 invc invB
chunks38 b0 b0B
chunks38 bb bB

end GCert
