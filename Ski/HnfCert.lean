import Ski.HnfQ5
open Term

/-!
# A checker for hypothesis (A), the minimal pairs of *Dance of the Starlings* Question 5

Computable definitions only (the data is in `Ski/HnfCertData.lean`, the run in `HnfCertRun`).
The checker mirrors `notes/checks/s15/cert/kcheck.py` line by line.  A product state is coded
as `class * 64 + block`; tables are big `Nat` literals read by shifts (GMP in the kernel).
-/

namespace HnfCert

/-- hnf shapes of a state: `S`, `S a`, `S a b`. -/
inductive Shape | s0 | s1 (a : Nat) | s2 (a b : Nat)
  deriving Repr

/-- Claim terms: `S`, a variable of a product state, an application. -/
inductive CT | S | V (s : Nat) | A (l r : CT)
  deriving DecidableEq, Repr

structure Claim where
  term : CT
  stratum : Nat
  rank : Nat
  split : Option Nat
  /-- Choices at hnf descents, depth first: `2 * i` closes argument `i` by a claim, `2 * i + 1`
  descends into it. -/
  hints : List Nat

/-- Claims indexed by a numeric code of their term. -/
inductive CBST
  | leaf
  | node (key : Nat) (items : List Claim) (l r : CBST)

/-- All claims, in order. -/
def CBST.toList : CBST → List Claim
  | .leaf => []
  | .node _ items l r => l.toList ++ items ++ r.toList

end HnfCert
