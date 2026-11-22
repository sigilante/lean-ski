import Ski.D2Slaw
import Ski.D2Sem
open Term

/-!
# The depth-2 prefix of `t^∞` is regular (S4, Prefix Regularity at depth 2)

For every closed S-term `t`, the depth-2 prefix `Pre 2 t` is `out2 (foldD t)`, where `foldD` is
the fold of `t` into the 373-element S-model `D` (`notes/checks/s4/d2_model.json`).  The table
conditions are kernel-checked (`D2K/`, `D2Slaw`); the argument is in `D2Sem`.  Pencil proof and
certificate: `notes/S4-d2-theorem.md`.

Scope.  `Pre` is the prefix convention of `notes/checks/s4/s4lib.py` (the head `S` of a head
normal form is shown even at depth 2); `d2_nf` gives the same for `InfNF.NF`, which cuts the
head too.  Both relations are defined by the rules of S3's Prop. "compute".  That they are the
prefixes of the limit `t^∞` of a strongly convergent reduction is S3's cited, un-mechanized
identification (see `InfNF`); nothing here proves it.  Uniqueness of `Pre d` is proved for
`d ≤ 2` only.
-/

namespace D2
open HnfS InfNF

/-- All table conditions hold (kernel-checked in `D2K/`). -/
theorem checks : Checks :=
  ⟨slawChunk_all, colsRow_all, closedRow_all, homRow_all, out2Row_all⟩

/-- `D` is closed under its product. -/
theorem d2_closed {a b : Nat} (ha : a < 373) (hb : b < 373) : τ a b < 373 := τ_lt checks ha hb

/-- `D` is an S-model: `s·a·b·c = a·c·(b·c)` on all 373³ triples. -/
theorem d2_slaw {a b c : Nat} (ha : a < 373) (hb : b < 373) (hc : c < 373) :
    τ (τ (τ 0 a) b) c = τ (τ a c) (τ b c) := slaw checks ha hb hc

/-- The fold into `D` is invariant under reduction. -/
theorem d2_wsteps {t u : Term} (ht : PureS t) (h : WSteps t u) : foldD u = foldD t :=
  wsteps_foldD checks h ht

/-- S1's 38-block model is a quotient of `D`. -/
theorem d2_block {t : Term} (ht : PureS t) : fold t = φD (foldD t) := fold_eq checks ht

/-- The depth-1 prefix of `t^∞` is `out1 (foldD t)`. -/
theorem d1_prefix {t : Term} {P : PT} (ht : PureS t) (h : Pre 1 t P) : P = out1 (foldD t) :=
  pre1 checks ht h

/-- **Prefix Regularity at depth 2.**  For a closed S-term `t`, `Pre 2 t P` iff
`P = out2 (foldD t)`: the depth-2 prefix (in the sense of `Pre`) exists, is unique, and is read
off the value of `t` in the 373-element S-model. -/
theorem d2_prefix {t : Term} {P : PT} (ht : PureS t) : Pre 2 t P ↔ P = out2 (foldD t) :=
  pre2_iff checks ht

/-- The same for S3's prefix relation `NF`, which also cuts the head at depth 2. -/
theorem d2_nf {t : Term} {P : PT} (ht : PureS t) (h : NF 2 t P) : P = (out2 (foldD t)).trunc 2 :=
  nf2 checks ht h

end D2
