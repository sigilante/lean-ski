import Ski.Unquote

open Term

/-!
# The self-interpreter of the metacircular paper, and its fuel adequacy

The paper *A self-interpreter for SKI* builds one closed term `whnfF` of 618
atoms: a fueled loop that walks the spine of an encoded term to its head
leaf, performs one head contraction as data, rebuilds the spine, and repeats
until the head is unsaturated or the fuel numeral runs out.  This module
defines that term from the artifact's source equations (`tower_harness.py`)
by `absN`, checks that it is the term the paper prints (`whnfF_eq_paper`),
and proves the paper's two numbered results about it.

* Lemma 5.1, step adequacy: `step_whnf`, `step_step`.
* Theorem 5.2, fuel adequacy: `fuel_adequacy_value`, `fuel_adequacy_timeout`;
  both are read off `whnfF_evalF`, which says the term computes
  `Ski/Fuel.lean`'s `evalF` on encodings.

The object strategy is the paper's: normal-order head reduction to weak head
normal form (`Step`, `Whnf`), counted by `Down n M N`, the paper's `M ⇓ₙ N`.
The host relation `↠` is weak reduction, `WSteps`.  Remark, not a theorem
here: head reduction would not do, since `step` answers `just (rb x rest)`
with the rebuild unevaluated under the constructor.  So the theorems give a
weak reduction to `just ⟨N⟩`, and no bound on host contractions; the one host
count stated is `t0`'s, the paper's 340.

`just_nothing_apart` separates the two answers, which the paper leaves
implicit, and gives the abstract's "exactly" (`fuel_exact`).
`UQ` is the paper's 43-atom unquoter (`UQ_eq_paper`), with `UQ ⟨t⟩ ↠ t`
(`UQ_unquote`); `fuel_adequacy_decoded` composes the two.  Encodings of
distinct terms have no common reduct (`quote_inj`), so the returned value is
identified (`fuel_exact_value`) and does not depend on the budget
(`value_independent`).

The encoding is `quoteT` with `Requote.appC`, which are the paper's terms
(`quote_eq_paper`).  The proof of `walk` generalizes Lemma 5.1 over the
walker's accumulator and is by induction on the term; the paper's proof
sketch argues the same decomposition in prose.
-/

namespace SelfInterp

open Requote

-- ---------------------------------------------------------------------------
-- The source, definition for definition as `tower_harness.py` gives it
-- ---------------------------------------------------------------------------

/-- `nil = λ n c. n`. -/
def nilBody : OTerm := .var 0
def nilT : Term := toTerm (absN [0, 1] nilBody)

/-- `cons h t = λ n c. c h t`. -/
def consBody : OTerm := .var 3 ⬝ₒ .var 0 ⬝ₒ .var 1
def consT : Term := toTerm (absN [0, 1, 2, 3] consBody)

/-- `nothing = λ n j. n`. -/
def nothingT : Term := toTerm (absN [0, 1] (.var 0))

/-- `just x = λ n j. j x`. -/
def justBody : OTerm := .var 2 ⬝ₒ .var 0
def justT : Term := toTerm (absN [0, 1, 2] justBody)

/-- `zero = λ z s. z`. -/
def zeroT : Term := toTerm (absN [0, 1] (.var 0))

/-- `suc n = λ z s. s n`. -/
def sucT : Term := toTerm (absN [0, 1, 2] justBody)

/-- `resS acc = λ s k i. s acc`, the spine walker's answer at an `S` head;
    `resK`, `resI` likewise. -/
def resSBody : OTerm := .var 1 ⬝ₒ .var 0
def resKBody : OTerm := .var 2 ⬝ₒ .var 0
def resIBody : OTerm := .var 3 ⬝ₒ .var 0
def resS : Term := toTerm (absN [0, 1, 2, 3] resSBody)
def resK : Term := toTerm (absN [0, 1, 2, 3] resKBody)
def resI : Term := toTerm (absN [0, 1, 2, 3] resIBody)

/-- `spApp f acc t u = f t (cons u acc)`. -/
def spAppBody : OTerm := .var 0 ⬝ₒ .var 2 ⬝ₒ (consT.toO ⬝ₒ .var 3 ⬝ₒ .var 1)
def spApp : Term := toTerm (absN [0, 1, 2, 3] spAppBody)

/-- `spGen f m acc = m (resS acc) (resK acc) (resI acc) (spApp f acc)`. -/
def spGenBody : OTerm :=
  .var 1 ⬝ₒ (resS.toO ⬝ₒ .var 2) ⬝ₒ (resK.toO ⬝ₒ .var 2) ⬝ₒ (resI.toO ⬝ₒ .var 2)
    ⬝ₒ (spApp.toO ⬝ₒ .var 0 ⬝ₒ .var 2)
def spGen : Term := toTerm (absN [0, 1, 2] spGenBody)

/-- The spine walker, `sp = Y spGen`. -/
def sp : Term := fixY ⬝ spGen

/-- `rb1 f h x xs = f (App h x) xs`. -/
def rb1Body : OTerm := .var 0 ⬝ₒ (appC.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ .var 3
def rb1 : Term := toTerm (absN [0, 1, 2, 3] rb1Body)

/-- `rbGen f h args = args h (rb1 f h)`. -/
def rbGenBody : OTerm := .var 2 ⬝ₒ .var 1 ⬝ₒ (rb1.toO ⬝ₒ .var 0 ⬝ₒ .var 1)
def rbGen : Term := toTerm (absN [0, 1, 2] rbGenBody)

/-- The rebuilder, `rb = Y rbGen`. -/
def rb : Term := fixY ⬝ rbGen

/-- `stepI1 x rest = just (rb x rest)`. -/
def stepI1Body : OTerm := justT.toO ⬝ₒ (rb.toO ⬝ₒ .var 0 ⬝ₒ .var 1)
def stepI1 : Term := toTerm (absN [0, 1] stepI1Body)

/-- `stepI args = args nothing stepI1`. -/
def stepIBody : OTerm := .var 0 ⬝ₒ nothingT.toO ⬝ₒ stepI1.toO
def stepI : Term := toTerm (absN [0] stepIBody)

/-- `stepK2 x y rest = just (rb x rest)`. -/
def stepK2Body : OTerm := justT.toO ⬝ₒ (rb.toO ⬝ₒ .var 0 ⬝ₒ .var 2)
def stepK2 : Term := toTerm (absN [0, 1, 2] stepK2Body)

/-- `stepK1 x r = r nothing (stepK2 x)`. -/
def stepK1Body : OTerm := .var 1 ⬝ₒ nothingT.toO ⬝ₒ (stepK2.toO ⬝ₒ .var 0)
def stepK1 : Term := toTerm (absN [0, 1] stepK1Body)

/-- `stepK args = args nothing stepK1`. -/
def stepKBody : OTerm := .var 0 ⬝ₒ nothingT.toO ⬝ₒ stepK1.toO
def stepK : Term := toTerm (absN [0] stepKBody)

/-- `stepS3 x y z rest = just (rb (App (App x z) (App y z)) rest)`. -/
def stepS3Body : OTerm :=
  justT.toO ⬝ₒ (rb.toO
    ⬝ₒ (appC.toO ⬝ₒ (appC.toO ⬝ₒ .var 0 ⬝ₒ .var 2) ⬝ₒ (appC.toO ⬝ₒ .var 1 ⬝ₒ .var 2))
    ⬝ₒ .var 3)
def stepS3 : Term := toTerm (absN [0, 1, 2, 3] stepS3Body)

/-- `stepS2 x y r2 = r2 nothing (stepS3 x y)`. -/
def stepS2Body : OTerm := .var 2 ⬝ₒ nothingT.toO ⬝ₒ (stepS3.toO ⬝ₒ .var 0 ⬝ₒ .var 1)
def stepS2 : Term := toTerm (absN [0, 1, 2] stepS2Body)

/-- `stepS1 x r = r nothing (stepS2 x)`. -/
def stepS1Body : OTerm := .var 1 ⬝ₒ nothingT.toO ⬝ₒ (stepS2.toO ⬝ₒ .var 0)
def stepS1 : Term := toTerm (absN [0, 1] stepS1Body)

/-- `stepS args = args nothing stepS1`. -/
def stepSBody : OTerm := .var 0 ⬝ₒ nothingT.toO ⬝ₒ stepS1.toO
def stepS : Term := toTerm (absN [0] stepSBody)

/-- `step m = sp m nil stepS stepK stepI`. -/
def stepBody : OTerm :=
  sp.toO ⬝ₒ .var 0 ⬝ₒ nilT.toO ⬝ₒ stepS.toO ⬝ₒ stepK.toO ⬝ₒ stepI.toO
def stepT : Term := toTerm (absN [0] stepBody)

/-- `wf1 w m n2 = step m (just m) (w n2)`. -/
def wf1Body : OTerm :=
  stepT.toO ⬝ₒ .var 1 ⬝ₒ (justT.toO ⬝ₒ .var 1) ⬝ₒ (.var 0 ⬝ₒ .var 2)
def wf1 : Term := toTerm (absN [0, 1, 2] wf1Body)

/-- `wfGen w n m = n nothing (wf1 w m)`. -/
def wfGenBody : OTerm := .var 1 ⬝ₒ nothingT.toO ⬝ₒ (wf1.toO ⬝ₒ .var 0 ⬝ₒ .var 2)
def wfGen : Term := toTerm (absN [0, 1, 2] wfGenBody)

/-- **The interpreter**, `whnfF = Y wfGen`. -/
def whnfF : Term := fixY ⬝ wfGen

/-- The interpreter as the paper prints it (Appendix A; the artifact's
    `figures/whnff-618.txt`), transcribed mechanically. -/
def paperWhnfF : Term :=
  (((S ⬝ (K ⬝ ((S ⬝ I) ⬝ I))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ I) ⬝ I)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ I) ⬝ (K ⬝ K))))))) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ ((S ⬝ ((S ⬝ ((S ⬝ ((S ⬝ (((S ⬝ (K ⬝ ((S ⬝ I) ⬝ I))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ I) ⬝ I)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))))) ⬝ (K ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))))) ⬝ (K ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))))))) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ S)))) ⬝ (S ⬝ (K ⬝ K))))))) ⬝ (K ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K)))))) ⬝ K)))))))) ⬝ (K ⬝ K))) ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ K))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ I) ⬝ (K ⬝ K))))) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ ((S ⬝ I) ⬝ (K ⬝ K))))))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K)))))))))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ (((S ⬝ (K ⬝ ((S ⬝ I) ⬝ I))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ I) ⬝ I)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K)))))))))))))))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K))))))))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K)))))))))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K)))))))))))))))))) ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ K))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ I) ⬝ (K ⬝ K))))) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K)))))) ⬝ (((S ⬝ (K ⬝ ((S ⬝ I) ⬝ I))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ I) ⬝ I)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K))))))))))))))))))) ⬝ (K ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ K))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K)))))) ⬝ (((S ⬝ (K ⬝ ((S ⬝ I) ⬝ I))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ I) ⬝ I)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)))) ⬝ (K ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K))))) ⬝ (K ⬝ K)))))))))))))))) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K)))))))) ⬝ K))))

/-- The interpreter is the paper's term, atom for atom. -/
theorem whnfF_eq_paper : whnfF = paperWhnfF := by decide

/-- Atoms (leaves) of a term, the paper's size measure. -/
def atoms : Term → Nat
  | .app f x => atoms f + atoms x
  | _ => 1

/-- 618 atoms. -/
theorem whnfF_atoms : atoms whnfF = 618 := by decide

/-- The leaf encodings are the paper's (§3.1), and `App` has 32 atoms. -/
theorem quote_eq_paper :
    quoteT .S = S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ K) ⬝ K) ∧ quoteT .K = K ⬝ (S ⬝ (K ⬝ K) ⬝ K) ∧
      quoteT .I = K ⬝ (K ⬝ K) ∧ atoms appC = 32 := by decide

-- ---------------------------------------------------------------------------
-- Data: lists of encodings, fuel numerals, outcomes
-- ---------------------------------------------------------------------------

/-- The Scott list of the encodings of `xs`. -/
def qlist : List Term → Term
  | [] => nilT
  | a :: as => consT ⬝ quoteT a ⬝ qlist as

/-- The Scott numeral `⟨k⟩`. -/
def natT : Nat → Term
  | 0 => zeroT
  | k + 1 => sucT ⬝ natT k

/-- The interpreter's answer for a metalevel outcome: `just ⟨N⟩` or `nothing`. -/
def outcome : Option Term → Term
  | some N => justT ⬝ quoteT N
  | none => nothingT

/-- `M ⇓ₙ N`: `M` reaches the weak head normal form `N` in exactly `n`
    normal-order (head) contractions. -/
inductive Down : Nat → Term → Term → Prop
  | whnf {t : Term} (h : Whnf t) : Down 0 t t
  | step {n : Nat} {t t' u : Term} (h : Step t t') (hs : Down n t' u) : Down (n + 1) t u

-- ---------------------------------------------------------------------------
-- β for each definition
-- ---------------------------------------------------------------------------

/-- β for `toTerm (absN xs body)` at the arguments `Ns`. -/
macro "beta_close" xs:term:max b:ident ns:term:max : tactic =>
  `(tactic| (have h := absN_beta_close $xs $b (fun _ => K) $ns rfl
             simp only [$b:ident, OTerm.close, close_toO] at h
             exact h))

theorem nil_elim (n c : Term) : WSteps (nilT ⬝ n ⬝ c) n := by
  beta_close [0, 1] nilBody [n, c]

theorem cons_elim (h t n c : Term) : WSteps (consT ⬝ h ⬝ t ⬝ n ⬝ c) (c ⬝ h ⬝ t) := by
  beta_close [0, 1, 2, 3] consBody [h, t, n, c]

theorem nothing_elim (n j : Term) : WSteps (nothingT ⬝ n ⬝ j) n := nil_elim n j

theorem just_elim (x n j : Term) : WSteps (justT ⬝ x ⬝ n ⬝ j) (j ⬝ x) := by
  beta_close [0, 1, 2] justBody [x, n, j]

theorem zero_elim (z s : Term) : WSteps (zeroT ⬝ z ⬝ s) z := nil_elim z s

theorem suc_elim (n z s : Term) : WSteps (sucT ⬝ n ⬝ z ⬝ s) (s ⬝ n) := just_elim n z s

theorem resS_elim (acc s k i : Term) : WSteps (resS ⬝ acc ⬝ s ⬝ k ⬝ i) (s ⬝ acc) := by
  beta_close [0, 1, 2, 3] resSBody [acc, s, k, i]

theorem resK_elim (acc s k i : Term) : WSteps (resK ⬝ acc ⬝ s ⬝ k ⬝ i) (k ⬝ acc) := by
  beta_close [0, 1, 2, 3] resKBody [acc, s, k, i]

theorem resI_elim (acc s k i : Term) : WSteps (resI ⬝ acc ⬝ s ⬝ k ⬝ i) (i ⬝ acc) := by
  beta_close [0, 1, 2, 3] resIBody [acc, s, k, i]

theorem spApp_beta (f acc t u : Term) :
    WSteps (spApp ⬝ f ⬝ acc ⬝ t ⬝ u) (f ⬝ t ⬝ (consT ⬝ u ⬝ acc)) := by
  beta_close [0, 1, 2, 3] spAppBody [f, acc, t, u]

theorem spGen_beta (f m acc : Term) :
    WSteps (spGen ⬝ f ⬝ m ⬝ acc)
      (m ⬝ (resS ⬝ acc) ⬝ (resK ⬝ acc) ⬝ (resI ⬝ acc) ⬝ (spApp ⬝ f ⬝ acc)) := by
  beta_close [0, 1, 2] spGenBody [f, m, acc]

theorem rb1_beta (f h x xs : Term) :
    WSteps (rb1 ⬝ f ⬝ h ⬝ x ⬝ xs) (f ⬝ (appC ⬝ h ⬝ x) ⬝ xs) := by
  beta_close [0, 1, 2, 3] rb1Body [f, h, x, xs]

theorem rbGen_beta (f h args : Term) :
    WSteps (rbGen ⬝ f ⬝ h ⬝ args) (args ⬝ h ⬝ (rb1 ⬝ f ⬝ h)) := by
  beta_close [0, 1, 2] rbGenBody [f, h, args]

theorem stepI1_beta (x rest : Term) :
    WSteps (stepI1 ⬝ x ⬝ rest) (justT ⬝ (rb ⬝ x ⬝ rest)) := by
  beta_close [0, 1] stepI1Body [x, rest]

theorem stepI_beta (args : Term) : WSteps (stepI ⬝ args) (args ⬝ nothingT ⬝ stepI1) := by
  beta_close [0] stepIBody [args]

theorem stepK2_beta (x y rest : Term) :
    WSteps (stepK2 ⬝ x ⬝ y ⬝ rest) (justT ⬝ (rb ⬝ x ⬝ rest)) := by
  beta_close [0, 1, 2] stepK2Body [x, y, rest]

theorem stepK1_beta (x r : Term) :
    WSteps (stepK1 ⬝ x ⬝ r) (r ⬝ nothingT ⬝ (stepK2 ⬝ x)) := by
  beta_close [0, 1] stepK1Body [x, r]

theorem stepK_beta (args : Term) : WSteps (stepK ⬝ args) (args ⬝ nothingT ⬝ stepK1) := by
  beta_close [0] stepKBody [args]

theorem stepS3_beta (x y z rest : Term) :
    WSteps (stepS3 ⬝ x ⬝ y ⬝ z ⬝ rest)
      (justT ⬝ (rb ⬝ (appC ⬝ (appC ⬝ x ⬝ z) ⬝ (appC ⬝ y ⬝ z)) ⬝ rest)) := by
  beta_close [0, 1, 2, 3] stepS3Body [x, y, z, rest]

theorem stepS2_beta (x y r2 : Term) :
    WSteps (stepS2 ⬝ x ⬝ y ⬝ r2) (r2 ⬝ nothingT ⬝ (stepS3 ⬝ x ⬝ y)) := by
  beta_close [0, 1, 2] stepS2Body [x, y, r2]

theorem stepS1_beta (x r : Term) :
    WSteps (stepS1 ⬝ x ⬝ r) (r ⬝ nothingT ⬝ (stepS2 ⬝ x)) := by
  beta_close [0, 1] stepS1Body [x, r]

theorem stepS_beta (args : Term) : WSteps (stepS ⬝ args) (args ⬝ nothingT ⬝ stepS1) := by
  beta_close [0] stepSBody [args]

theorem stepT_beta (m : Term) :
    WSteps (stepT ⬝ m) (sp ⬝ m ⬝ nilT ⬝ stepS ⬝ stepK ⬝ stepI) := by
  beta_close [0] stepBody [m]

theorem wf1_beta (w m n2 : Term) :
    WSteps (wf1 ⬝ w ⬝ m ⬝ n2) (stepT ⬝ m ⬝ (justT ⬝ m) ⬝ (w ⬝ n2)) := by
  beta_close [0, 1, 2] wf1Body [w, m, n2]

theorem wfGen_beta (w n m : Term) :
    WSteps (wfGen ⬝ w ⬝ n ⬝ m) (n ⬝ nothingT ⬝ (wf1 ⬝ w ⬝ m)) := by
  beta_close [0, 1, 2] wfGenBody [w, n, m]

-- ---------------------------------------------------------------------------
-- Recursion through `Y`
-- ---------------------------------------------------------------------------

/-- The self-reference `Y F` unrolls through. -/
def selfT (F : Term) : Term := fixSelf F (fixB F)

/-- `Y F` reaches its self-reference in one contraction. -/
theorem fixY_self (F : Term) : WSteps (fixY ⬝ F) (selfT F) := .single (.S _ _ _)

/-- The self-reference unrolls: `selfT F ↠ F (selfT F)`. -/
theorem selfT_unroll (F : Term) : WSteps (selfT F) (F ⬝ selfT F) := by
  have h := (fixSelf_unroll (F := F) (Steps.refl (fixB F))).weak
  have hI : WSteps (fixSelf F (I ⬝ fixB F)) (selfT F) := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

/-- `sp`, `rb` and `whnfF` after their first contraction. -/
def spX : Term := selfT spGen
def rbX : Term := selfT rbGen
def wfX : Term := selfT wfGen

theorem spX_case (m acc : Term) :
    WSteps (spX ⬝ m ⬝ acc)
      (m ⬝ (resS ⬝ acc) ⬝ (resK ⬝ acc) ⬝ (resI ⬝ acc) ⬝ (spApp ⬝ spX ⬝ acc)) :=
  (WSteps.left acc (WSteps.left m (selfT_unroll spGen))).trans (spGen_beta spX m acc)

theorem rbX_case (h args : Term) :
    WSteps (rbX ⬝ h ⬝ args) (args ⬝ h ⬝ (rb1 ⬝ rbX ⬝ h)) :=
  (WSteps.left args (WSteps.left h (selfT_unroll rbGen))).trans (rbGen_beta rbX h args)

theorem wfX_case (n m : Term) :
    WSteps (wfX ⬝ n ⬝ m) (n ⬝ nothingT ⬝ (wf1 ⬝ wfX ⬝ m)) :=
  (WSteps.left m (WSteps.left n (selfT_unroll wfGen))).trans (wfGen_beta wfX n m)

-- ---------------------------------------------------------------------------
-- The rebuilder
-- ---------------------------------------------------------------------------

/-- `rb ⟨H⟩ ⟨xs⟩ ↠ ⟨H xs⟩`: the rebuilder re-applies the arguments, as data. -/
theorem rbX_spec : ∀ (xs : List Term) (H : Term),
    WSteps (rbX ⬝ quoteT H ⬝ qlist xs) (quoteT (appT H xs))
  | [], _ => (rbX_case _ _).trans (nil_elim _ _)
  | a :: as, H =>
    ((rbX_case _ _).trans (cons_elim _ _ _ _)).trans
      ((rb1_beta _ _ _ _).trans (rbX_spec as (H ⬝ a)))

theorem rb_spec (xs : List Term) (H : Term) :
    WSteps (rb ⬝ quoteT H ⬝ qlist xs) (quoteT (appT H xs)) :=
  (WSteps.left _ (WSteps.left _ (fixY_self rbGen))).trans (rbX_spec xs H)

/-- A contracted spine, rebuilt under `just`. -/
theorem just_rb (xs : List Term) (H : Term) :
    WSteps (justT ⬝ (rb ⬝ quoteT H ⬝ qlist xs)) (justT ⬝ quoteT (appT H xs)) :=
  WSteps.right _ (rb_spec xs H)

-- ---------------------------------------------------------------------------
-- The three arms, on argument lists
-- ---------------------------------------------------------------------------

theorem stepI_nil : WSteps (stepI ⬝ nilT) nothingT :=
  (stepI_beta _).trans (nil_elim _ _)

theorem stepI_one (x r : Term) :
    WSteps (stepI ⬝ (consT ⬝ x ⬝ r)) (justT ⬝ (rb ⬝ x ⬝ r)) :=
  ((stepI_beta _).trans (cons_elim _ _ _ _)).trans (stepI1_beta _ _)

theorem stepK_nil : WSteps (stepK ⬝ nilT) nothingT :=
  (stepK_beta _).trans (nil_elim _ _)

theorem stepK_cons (x r : Term) :
    WSteps (stepK ⬝ (consT ⬝ x ⬝ r)) (r ⬝ nothingT ⬝ (stepK2 ⬝ x)) :=
  ((stepK_beta _).trans (cons_elim _ _ _ _)).trans (stepK1_beta _ _)

theorem stepK_one (x : Term) : WSteps (stepK ⬝ (consT ⬝ x ⬝ nilT)) nothingT :=
  (stepK_cons _ _).trans (nil_elim _ _)

theorem stepK_two (x y r : Term) :
    WSteps (stepK ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ r))) (justT ⬝ (rb ⬝ x ⬝ r)) :=
  ((stepK_cons _ _).trans (cons_elim _ _ _ _)).trans (stepK2_beta _ _ _)

theorem stepS_nil : WSteps (stepS ⬝ nilT) nothingT :=
  (stepS_beta _).trans (nil_elim _ _)

theorem stepS_cons (x r : Term) :
    WSteps (stepS ⬝ (consT ⬝ x ⬝ r)) (r ⬝ nothingT ⬝ (stepS2 ⬝ x)) :=
  ((stepS_beta _).trans (cons_elim _ _ _ _)).trans (stepS1_beta _ _)

theorem stepS_one (x : Term) : WSteps (stepS ⬝ (consT ⬝ x ⬝ nilT)) nothingT :=
  (stepS_cons _ _).trans (nil_elim _ _)

theorem stepS_cons2 (x y r : Term) :
    WSteps (stepS ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ r))) (r ⬝ nothingT ⬝ (stepS3 ⬝ x ⬝ y)) :=
  ((stepS_cons _ _).trans (cons_elim _ _ _ _)).trans (stepS2_beta _ _ _)

theorem stepS_two (x y : Term) :
    WSteps (stepS ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ nilT))) nothingT :=
  (stepS_cons2 _ _ _).trans (nil_elim _ _)

theorem stepS_three (x y z r : Term) :
    WSteps (stepS ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ (consT ⬝ z ⬝ r))))
      (justT ⬝ (rb ⬝ (appC ⬝ (appC ⬝ x ⬝ z) ⬝ (appC ⬝ y ⬝ z)) ⬝ r)) :=
  ((stepS_cons2 _ _ _).trans (cons_elim _ _ _ _)).trans (stepS3_beta _ _ _ _)

-- ---------------------------------------------------------------------------
-- The spine walker and dispatch
-- ---------------------------------------------------------------------------

/-- A walker's answer handed the three arms. -/
def disp (t : Term) : Term := t ⬝ stepS ⬝ stepK ⬝ stepI

theorem disp_mono {t u : Term} (h : WSteps t u) : WSteps (disp t) (disp u) :=
  WSteps.left _ (WSteps.left _ (WSteps.left _ h))

/-- The walker moves an application's argument onto the accumulator. -/
theorem spX_app (f a acc : Term) :
    WSteps (spX ⬝ quoteT (f ⬝ a) ⬝ acc) (spX ⬝ quoteT f ⬝ (consT ⬝ quoteT a ⬝ acc)) :=
  ((spX_case _ _).trans (quoteApp_elim f a _ _ _ _)).trans (spApp_beta _ _ _ _)

theorem walk_S (acc : Term) : WSteps (disp (spX ⬝ quoteT .S ⬝ acc)) (stepS ⬝ acc) :=
  (disp_mono ((spX_case _ _).trans (quoteS_elim _ _ _ _))).trans (resS_elim _ _ _ _)

theorem walk_K (acc : Term) : WSteps (disp (spX ⬝ quoteT .K ⬝ acc)) (stepK ⬝ acc) :=
  (disp_mono ((spX_case _ _).trans (quoteK_elim _ _ _ _))).trans (resK_elim _ _ _ _)

theorem walk_I (acc : Term) : WSteps (disp (spX ⬝ quoteT .I ⬝ acc)) (stepI ⬝ acc) :=
  (disp_mono ((spX_case _ _).trans (quoteI_elim _ _ _ _))).trans (resI_elim _ _ _ _)

theorem step_appT {t u : Term} (h : Step t u) : ∀ as : List Term, Step (appT t as) (appT u as)
  | [] => h
  | a :: as => step_appT (.left a h) as

/-- **The walk, generalized over the accumulator.**  With the spine of
    `M xs` walked down to `M` and `xs` on the accumulator, the dispatch
    answers `nothing` if `M xs` is a weak head normal form, and otherwise
    `just` of the encoding of its head contraction. -/
theorem walk (M : Term) : ∀ xs : List Term,
    (Whnf (appT M xs) ∧ WSteps (disp (spX ⬝ quoteT M ⬝ qlist xs)) nothingT) ∨
      (∃ N, Step (appT M xs) N ∧
        WSteps (disp (spX ⬝ quoteT M ⬝ qlist xs)) (justT ⬝ quoteT N)) := by
  induction M with
  | S =>
    intro xs
    match xs with
    | [] => exact .inl ⟨.S, (walk_S _).trans stepS_nil⟩
    | [x] => exact .inl ⟨.S1 x, (walk_S _).trans (stepS_one _)⟩
    | [x, y] => exact .inl ⟨.S2 x y, (walk_S _).trans (stepS_two _ _)⟩
    | x :: y :: z :: rest =>
      exact .inr ⟨appT (x ⬝ z ⬝ (y ⬝ z)) rest, step_appT (.S x y z) rest,
        ((walk_S _).trans (stepS_three _ _ _ _)).trans (just_rb rest (x ⬝ z ⬝ (y ⬝ z)))⟩
  | K =>
    intro xs
    match xs with
    | [] => exact .inl ⟨.K, (walk_K _).trans stepK_nil⟩
    | [x] => exact .inl ⟨.K1 x, (walk_K _).trans (stepK_one _)⟩
    | x :: y :: rest =>
      exact .inr ⟨appT x rest, step_appT (.K x y) rest,
        ((walk_K _).trans (stepK_two _ _ _)).trans (just_rb rest x)⟩
  | I =>
    intro xs
    match xs with
    | [] => exact .inl ⟨.I, (walk_I _).trans stepI_nil⟩
    | x :: rest =>
      exact .inr ⟨appT x rest, step_appT (.I x) rest,
        ((walk_I _).trans (stepI_one _ _)).trans (just_rb rest x)⟩
  | app f a ihf _ =>
    intro xs
    have hw := disp_mono (spX_app f a (qlist xs))
    cases ihf (a :: xs) with
    | inl h => exact .inl ⟨h.1, hw.trans h.2⟩
    | inr h =>
      cases h with
      | intro N hN => exact .inr ⟨N, hN.1, hw.trans hN.2⟩

theorem stepT_walk (M : Term) :
    WSteps (stepT ⬝ quoteT M) (disp (spX ⬝ quoteT M ⬝ qlist [])) :=
  (stepT_beta _).trans (disp_mono (WSteps.left _ (WSteps.left _ (fixY_self spGen))))

-- ---------------------------------------------------------------------------
-- Lemma 5.1 (step adequacy)
-- ---------------------------------------------------------------------------

/-- **Step adequacy, first case** (the paper's Lemma 5.1): on a weak head
    normal form, `step ⟨M⟩ ↠ nothing`. -/
theorem step_whnf {M : Term} (hw : Whnf M) : WSteps (stepT ⬝ quoteT M) nothingT := by
  cases walk M [] with
  | inl h => exact (stepT_walk M).trans h.2
  | inr h =>
    cases h with
    | intro N hN => exact (hw.no_step hN.1).elim

/-- **Step adequacy, second case** (the paper's Lemma 5.1): if `M → M'`
    contracts the head redex, `step ⟨M⟩ ↠ just ⟨M'⟩`. -/
theorem step_step {M M' : Term} (hs : Step M M') :
    WSteps (stepT ⬝ quoteT M) (justT ⬝ quoteT M') := by
  cases walk M [] with
  | inl h => exact (h.1.no_step hs).elim
  | inr h =>
    cases h with
    | intro N hN =>
      have e : M' = N := Step.det hs hN.1
      rw [e]
      exact (stepT_walk M).trans hN.2

-- ---------------------------------------------------------------------------
-- Theorem 5.2 (fuel adequacy)
-- ---------------------------------------------------------------------------

/-- One turn of the loop at positive fuel. -/
theorem wfX_suc (n m : Term) :
    WSteps (wfX ⬝ (sucT ⬝ n) ⬝ m) (stepT ⬝ m ⬝ (justT ⬝ m) ⬝ (wfX ⬝ n)) :=
  ((wfX_case _ _).trans (suc_elim _ _ _)).trans (wf1_beta _ _ _)

/-- The loop computes the metalevel fuel interpreter `evalF`, on encodings. -/
theorem wfX_evalF : ∀ (k : Nat) (M : Term),
    WSteps (wfX ⬝ natT k ⬝ quoteT M) (outcome (evalF k M))
  | 0, M => (wfX_case _ _).trans (zero_elim _ _)
  | k + 1, M => by
    have h1 := wfX_suc (natT k) (quoteT M)
    cases hs : step? M with
    | none =>
      have e : evalF (k + 1) M = some M := by simp only [evalF, hs]
      rw [e]
      exact h1.trans ((WSteps.left _ (WSteps.left _ (step_whnf (step?_none hs)))).trans
        (nothing_elim _ _))
    | some M' =>
      have e : evalF (k + 1) M = evalF k M' := by simp only [evalF, hs]
      rw [e]
      exact h1.trans ((WSteps.left _ (WSteps.left _ (step_step (step?_sound hs)))).trans
        ((just_elim _ _ _).trans (wfX_evalF k M')))

/-- **The interpreter computes `evalF`.**  For every fuel `k` and term `M`,
    `whnfF ⟨k⟩ ⟨M⟩` weakly reduces to `just ⟨N⟩` when the fuel interpreter
    returns `N`, and to `nothing` when it times out. -/
theorem whnfF_evalF (k : Nat) (M : Term) :
    WSteps (whnfF ⬝ natT k ⬝ quoteT M) (outcome (evalF k M)) :=
  (WSteps.left _ (WSteps.left _ (fixY_self wfGen))).trans (wfX_evalF k M)

theorem down_evalF : ∀ {n k : Nat} {M N : Term}, Down n M N → n < k → evalF k M = some N
  | _, 0, _, _, _, hk => (Nat.not_lt_zero _ hk).elim
  | _, k + 1, _, _, .whnf hw, _ => by simp only [evalF, whnf_iff_step?_none.mp hw]
  | _, k + 1, _, _, .step h hs, hk => by
    simp only [evalF, step?_complete h]
    exact down_evalF hs (Nat.lt_of_succ_lt_succ hk)

theorem down_timeout : ∀ {n k : Nat} {M N : Term}, Down n M N → k ≤ n → evalF k M = none
  | _, 0, _, _, _, _ => rfl
  | _, k + 1, _, _, .whnf _, hk => (Nat.not_succ_le_zero _ hk).elim
  | _, k + 1, _, _, .step h hs, hk => by
    simp only [evalF, step?_complete h]
    exact down_timeout hs (Nat.le_of_succ_le_succ hk)

theorem evalF_down : ∀ {k : Nat} {M N : Term}, evalF k M = some N → ∃ n, n < k ∧ Down n M N
  | 0, _, _, h => by simp [evalF] at h
  | k + 1, M, N, h => by
    simp only [evalF] at h
    cases hs : step? M with
    | none =>
      rw [hs] at h
      cases h
      exact ⟨0, Nat.succ_pos _, .whnf (step?_none hs)⟩
    | some M' =>
      rw [hs] at h
      cases evalF_down h with
      | intro n hn => exact ⟨n + 1, Nat.succ_lt_succ hn.1, .step (step?_sound hs) hn.2⟩

/-- **Fuel adequacy, part 1** (the paper's Theorem 5.2(1)): if `M ⇓ₙ N` and
    `n < k`, then `whnfF ⟨k⟩ ⟨M⟩ ↠ just ⟨N⟩`. -/
theorem fuel_adequacy_value {M N : Term} {n k : Nat} (h : Down n M N) (hk : n < k) :
    WSteps (whnfF ⬝ natT k ⬝ quoteT M) (justT ⬝ quoteT N) := by
  have h1 := whnfF_evalF k M
  rw [down_evalF h hk] at h1
  exact h1

/-- **Fuel adequacy, part 2** (the paper's Theorem 5.2(2)): if `M` has no
    weak head normal form, or `M ⇓ₙ N` with `n ≥ k`, then
    `whnfF ⟨k⟩ ⟨M⟩ ↠ nothing`. -/
theorem fuel_adequacy_timeout {M : Term} {k : Nat}
    (h : Diverges M ∨ ∃ n N, Down n M N ∧ k ≤ n) :
    WSteps (whnfF ⬝ natT k ⬝ quoteT M) nothingT := by
  have h1 := whnfF_evalF k M
  have e : evalF k M = none := by
    cases h with
    | inl hd => exact (diverges_iff_fuel M).mp hd k
    | inr hn =>
      cases hn with
      | intro n hn =>
        cases hn with
        | intro N hN => exact down_timeout hN.1 hN.2
  rw [e] at h1
  exact h1

-- ---------------------------------------------------------------------------
-- The two outcomes are distinct, so "exactly"
-- ---------------------------------------------------------------------------

theorem S_normal {w : Term} (h : WSteps S w) : w = S := by
  cases h with
  | refl => rfl
  | step h _ => cases h

theorem K_normal {w : Term} (h : WSteps K w) : w = K := by
  cases h with
  | refl => rfl
  | step h _ => cases h

/-- No term weakly reduces both to a `just` and to `nothing`: applied to
    `S` and `K K`, the first gives `K` and the second `S`. -/
theorem just_nothing_apart {t q : Term} (hj : WSteps t (justT ⬝ q))
    (hn : WSteps t nothingT) : False := by
  have a : WSteps (t ⬝ S ⬝ (K ⬝ K)) K :=
    (WSteps.left _ (WSteps.left _ hj)).trans
      ((just_elim q S (K ⬝ K)).trans (.single (.K K q)))
  have b : WSteps (t ⬝ S ⬝ (K ⬝ K)) S :=
    (WSteps.left _ (WSteps.left _ hn)).trans (nothing_elim S (K ⬝ K))
  cases church_rosser a b with
  | intro w hw =>
    have e1 := K_normal hw.1
    have e2 := S_normal hw.2
    rw [e1] at e2
    cases e2

/-- **Fuel adequacy, exactly** (the abstract's form): the interpreter at
    budget `k` returns a `just` of an encoding if and only if `M` reaches a
    weak head normal form in fewer than `k` head contractions. -/
theorem fuel_exact (k : Nat) (M : Term) :
    (∃ N, WSteps (whnfF ⬝ natT k ⬝ quoteT M) (justT ⬝ quoteT N)) ↔
      ∃ n N, n < k ∧ Down n M N := by
  constructor
  · intro h
    cases h with
    | intro N hN =>
      cases e : evalF k M with
      | none =>
        have h1 := whnfF_evalF k M
        rw [e] at h1
        exact (just_nothing_apart hN h1).elim
      | some N' =>
        cases evalF_down e with
        | intro n hn => exact ⟨n, N', hn.1, hn.2⟩
  · intro h
    cases h with
    | intro n h =>
      cases h with
      | intro N hN => exact ⟨N, fuel_adequacy_value hN.2 hN.1⟩

-- ---------------------------------------------------------------------------
-- The paper's unquoter `UQ`
-- ---------------------------------------------------------------------------

/-- `UQA f t u = (f t) (f u)`. -/
def uqaBody : OTerm := (.var 0 ⬝ₒ .var 1) ⬝ₒ (.var 0 ⬝ₒ .var 2)
def UQA : Term := toTerm (absN [0, 1, 2] uqaBody)

/-- `UQGen f m = m S K I (UQA f)`. -/
def uqGenBody : OTerm :=
  .var 1 ⬝ₒ Term.S.toO ⬝ₒ Term.K.toO ⬝ₒ Term.I.toO ⬝ₒ (UQA.toO ⬝ₒ .var 0)
def UQGen : Term := toTerm (absN [0, 1] uqGenBody)

/-- **The paper's unquoter**, `UQ = Y UQGen`. -/
def UQ : Term := fixY ⬝ UQGen

/-- The unquoter as the paper prints it (Appendix A; the artifact's
    `figures/uq-43.txt`), transcribed mechanically. -/
def paperUQ: Term :=
  (((S ⬝ (K ⬝ ((S ⬝ I) ⬝ I))) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ K)) ⬝ (K ⬝ ((S ⬝ I) ⬝ I)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ ((S ⬝ ((S ⬝ ((S ⬝ I) ⬝ (K ⬝ S))) ⬝ (K ⬝ K))) ⬝ (K ⬝ I))))) ⬝ ((S ⬝ (K ⬝ K)) ⬝ ((S ⬝ ((S ⬝ (K ⬝ S)) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ S)))) ⬝ (S ⬝ (K ⬝ K))))) ⬝ K))))

/-- The unquoter is the paper's term, atom for atom. -/
theorem UQ_eq_paper : UQ = paperUQ := by decide

/-- 43 atoms. -/
theorem UQ_atoms : atoms UQ = 43 := by decide

theorem UQA_beta (f t u : Term) : WSteps (UQA ⬝ f ⬝ t ⬝ u) ((f ⬝ t) ⬝ (f ⬝ u)) := by
  beta_close [0, 1, 2] uqaBody [f, t, u]

theorem UQGen_beta (f m : Term) :
    WSteps (UQGen ⬝ f ⬝ m) (m ⬝ S ⬝ K ⬝ I ⬝ (UQA ⬝ f)) := by
  beta_close [0, 1] uqGenBody [f, m]

/-- `UQ` after its first contraction. -/
def uqX : Term := selfT UQGen

theorem uqX_case (m : Term) : WSteps (uqX ⬝ m) (m ⬝ S ⬝ K ⬝ I ⬝ (UQA ⬝ uqX)) :=
  (WSteps.left m (selfT_unroll UQGen)).trans (UQGen_beta uqX m)

theorem uqX_unquote : ∀ t : Term, WSteps (uqX ⬝ quoteT t) t
  | .S => (uqX_case _).trans (quoteS_elim _ _ _ _)
  | .K => (uqX_case _).trans (quoteK_elim _ _ _ _)
  | .I => (uqX_case _).trans (quoteI_elim _ _ _ _)
  | .app f x =>
    (((uqX_case _).trans (quoteApp_elim f x _ _ _ _)).trans (UQA_beta _ _ _)).trans
      (WSteps.app (uqX_unquote f) (uqX_unquote x))

/-- **The unquoter is correct** (§3.1: `UQ` "maps encoded data back to a
    live term"): `UQ ⟨t⟩ ↠ t` for every term `t`, for the paper's 43-atom
    term. -/
theorem UQ_unquote (t : Term) : WSteps (UQ ⬝ quoteT t) t :=
  (WSteps.left _ (fixY_self UQGen)).trans (uqX_unquote t)

-- ---------------------------------------------------------------------------
-- Encodings of distinct terms have no common reduct
-- ---------------------------------------------------------------------------

/-- `t` and `u` have a common weak reduct. -/
def Joinable (t u : Term) : Prop := ∃ v, WSteps t v ∧ WSteps u v

theorem Joinable.app {t u : Term} (h : Joinable t u) (a : Term) : Joinable (t ⬝ a) (u ⬝ a) := by
  cases h with
  | intro v hv => exact ⟨v ⬝ a, WSteps.left a hv.1, WSteps.left a hv.2⟩

/-- Joinability passes to reducts, by confluence. -/
theorem Joinable.red {t u t' u' : Term} (h : Joinable t u) (ht : WSteps t t')
    (hu : WSteps u u') : Joinable t' u' := by
  cases h with
  | intro v hv =>
    cases church_rosser ht hv.1 with
    | intro w hw =>
      cases church_rosser hu (hv.2.trans hw.2) with
      | intro z hz => exact ⟨z, hw.1.trans hz.2, hz.1⟩

theorem Joinable.symm {t u : Term} (h : Joinable t u) : Joinable u t := by
  cases h with
  | intro v hv => exact ⟨v, hv.2, hv.1⟩

/-- An encoding applied to four continuations. -/
theorem Joinable.app4 {t u : Term} (h : Joinable t u) (a b c d : Term) :
    Joinable (t ⬝ a ⬝ b ⬝ c ⬝ d) (u ⬝ a ⬝ b ⬝ c ⬝ d) :=
  (((h.app a).app b).app c).app d

theorem I_normal {w : Term} (h : WSteps I w) : w = I := by
  cases h with
  | refl => rfl
  | step h _ => cases h

theorem S_K_apart (h : Joinable S K) : False := by
  cases h with
  | intro v hv =>
    have e := S_normal hv.1
    rw [K_normal hv.2] at e
    cases e

theorem S_I_apart (h : Joinable S I) : False := by
  cases h with
  | intro v hv =>
    have e := S_normal hv.1
    rw [I_normal hv.2] at e
    cases e

theorem K_I_apart (h : Joinable K I) : False := by
  cases h with
  | intro v hv =>
    have e := K_normal hv.1
    rw [I_normal hv.2] at e
    cases e

/-- The application continuation that answers `K` whatever the children. -/
theorem appK (f x : Term) : WSteps (K ⬝ (K ⬝ K) ⬝ f ⬝ x) K :=
  .step (.left x (.K (K ⬝ K) f)) (.single (.K K x))

/-- A leaf's encoding and an application's are apart. -/
theorem leaf_app_apart {l f x : Term} (hl : WSteps (quoteT l ⬝ S ⬝ S ⬝ S ⬝ (K ⬝ (K ⬝ K))) S)
    (h : Joinable (quoteT l) (quoteT (f ⬝ x))) : False :=
  S_K_apart ((h.app4 S S S (K ⬝ (K ⬝ K))).red hl
    ((quoteApp_elim f x _ _ _ _).trans (appK _ _)))

/-- **Encodings of distinct terms are unjoinable**: if `⟨N⟩` and `⟨N'⟩`
    have a common weak reduct then `N = N'`. -/
theorem quote_inj : ∀ N N' : Term, Joinable (quoteT N) (quoteT N') → N = N'
  | .S, .S, _ => rfl
  | .K, .K, _ => rfl
  | .I, .I, _ => rfl
  | .S, .K, h => (S_K_apart ((h.app4 S K I I).red (quoteS_elim _ _ _ _) (quoteK_elim _ _ _ _))).elim
  | .K, .S, h => (S_K_apart ((h.symm.app4 S K I I).red (quoteS_elim _ _ _ _)
      (quoteK_elim _ _ _ _))).elim
  | .S, .I, h => (S_I_apart ((h.app4 S K I I).red (quoteS_elim _ _ _ _) (quoteI_elim _ _ _ _))).elim
  | .I, .S, h => (S_I_apart ((h.symm.app4 S K I I).red (quoteS_elim _ _ _ _)
      (quoteI_elim _ _ _ _))).elim
  | .K, .I, h => (K_I_apart ((h.app4 S K I I).red (quoteK_elim _ _ _ _) (quoteI_elim _ _ _ _))).elim
  | .I, .K, h => (K_I_apart ((h.symm.app4 S K I I).red (quoteK_elim _ _ _ _)
      (quoteI_elim _ _ _ _))).elim
  | .S, .app _ _, h => (leaf_app_apart (quoteS_elim _ _ _ _) h).elim
  | .K, .app _ _, h => (leaf_app_apart (quoteK_elim _ _ _ _) h).elim
  | .I, .app _ _, h => (leaf_app_apart (quoteI_elim _ _ _ _) h).elim
  | .app _ _, .S, h => (leaf_app_apart (quoteS_elim _ _ _ _) h.symm).elim
  | .app _ _, .K, h => (leaf_app_apart (quoteK_elim _ _ _ _) h.symm).elim
  | .app _ _, .I, h => (leaf_app_apart (quoteI_elim _ _ _ _) h.symm).elim
  | .app f x, .app f' x', h => by
    have hf : Joinable (quoteT f) (quoteT f') :=
      (h.app4 S S S K).red ((quoteApp_elim f x _ _ _ _).trans (.single (.K _ _)))
        ((quoteApp_elim f' x' _ _ _ _).trans (.single (.K _ _)))
    have hx : Joinable (quoteT x) (quoteT x') :=
      (h.app4 S S S (K ⬝ I)).red
        ((quoteApp_elim f x _ _ _ _).trans (.step (.left _ (.K _ _)) (.single (.I _))))
        ((quoteApp_elim f' x' _ _ _ _).trans (.step (.left _ (.K _ _)) (.single (.I _))))
    rw [quote_inj f f' hf, quote_inj x x' hx]

/-- `just` is injective up to joinability. -/
theorem just_joinable {q q' : Term} (h : Joinable (justT ⬝ q) (justT ⬝ q')) : Joinable q q' :=
  ((h.app S).app I).red ((just_elim q S I).trans (.single (.I q)))
    ((just_elim q' S I).trans (.single (.I q')))

/-- **Fuel adequacy, exactly, with the value**: the interpreter at budget
    `k` weakly reduces to `just ⟨N⟩` if and only if `M ⇓ₙ N` for some
    `n < k`.  The right-to-left half is Theorem 5.2(1); the other is its
    converse. -/
theorem fuel_exact_value (k : Nat) (M N : Term) :
    WSteps (whnfF ⬝ natT k ⬝ quoteT M) (justT ⬝ quoteT N) ↔ ∃ n, n < k ∧ Down n M N := by
  constructor
  · intro h
    have h1 := whnfF_evalF k M
    cases e : evalF k M with
    | none =>
      rw [e] at h1
      exact (just_nothing_apart h h1).elim
    | some N' =>
      rw [e] at h1
      have hj : Joinable (justT ⬝ quoteT N) (justT ⬝ quoteT N') := church_rosser h h1
      rw [quote_inj N N' (just_joinable hj)]
      exact evalF_down e
  · intro h
    cases h with
    | intro n hn => exact fuel_adequacy_value hn.2 hn.1

theorem down_det : ∀ {n n' : Nat} {M N N' : Term}, Down n M N → Down n' M N' → N = N'
  | _, _, _, _, _, .whnf _, .whnf _ => rfl
  | _, _, _, _, _, .whnf hw, .step h _ => (hw.no_step h).elim
  | _, _, _, _, _, .step h _, .whnf hw => (hw.no_step h).elim
  | _, _, _, _, _, .step h hs, .step h' hs' => by
    rw [Step.det h h'] at hs
    exact down_det hs hs'

/-- **The value is independent of the budget** (§5.1, third consequence):
    two runs on `⟨M⟩`, at any budgets `k` and `k'`, that both return a `just`
    return the same term. -/
theorem value_independent {M N N' : Term} {k k' : Nat}
    (h : WSteps (whnfF ⬝ natT k ⬝ quoteT M) (justT ⬝ quoteT N))
    (h' : WSteps (whnfF ⬝ natT k' ⬝ quoteT M) (justT ⬝ quoteT N')) : N = N' := by
  cases (fuel_exact_value k M N).mp h with
  | intro n hn =>
    cases (fuel_exact_value k' M N').mp h' with
    | intro n' hn' => exact down_det hn.2 hn'.2

/-- **Decoded** (§3.2, "the decoded result equals the host's own reduction"):
    handed the paper's unquoter `UQ` as its `just` continuation, a run with
    enough fuel reduces to the live weak head normal form itself. -/
theorem fuel_adequacy_decoded {M N : Term} {n k : Nat} (h : Down n M N) (hk : n < k)
    (d : Term) : WSteps (whnfF ⬝ natT k ⬝ quoteT M ⬝ d ⬝ UQ) N :=
  (WSteps.left _ (WSteps.left _ (fuel_adequacy_value h hk))).trans
    ((just_elim _ _ _).trans (UQ_unquote N))

/-- The paper's T0 run (§3.2), `whnfF 3 ⟨I K⟩`: head reduction of the host
    stops at a weak head normal form after exactly 340 contractions, and the
    run weakly reduces to `just ⟨K⟩`.  The term head reduction stops at is
    not itself `just ⟨K⟩`; the two are joined by weak reduction. -/
theorem t0 :
    (runF 341 (whnfF ⬝ natT 3 ⬝ quoteT (I ⬝ K))).map (·.2) = some 340 ∧
      WSteps (whnfF ⬝ natT 3 ⬝ quoteT (I ⬝ K)) (justT ⬝ quoteT K) :=
  ⟨by decide +kernel, fuel_adequacy_value (.step (.I K) (.whnf .K)) (by decide)⟩

-- ---------------------------------------------------------------------------
-- The tower counts, by compiled evaluation only
-- ---------------------------------------------------------------------------

/-- Head contractions of the host to weak head normal form, within `f`
    step-attempts. -/
def hostCount : Nat → Term → Nat → Option Nat
  | 0, _, _ => none
  | f + 1, t, acc =>
    match step? t with
    | none => some acc
    | some t' => hostCount f t' (acc + 1)

-- The paper's T1 and T2 counts (§3.2), on the pinned terms.  These two lines
-- are checked by the compiled evaluator, not by the kernel: they are tests,
-- not theorems, and are not in the axiom gate.  A kernel check of the first
-- (`decide +kernel`) passed 2.8 GB of memory and was stopped.
#guard hostCount 91557 (whnfF ⬝ natT 120 ⬝ quoteT (UQ ⬝ quoteT (I ⬝ K))) 0 == some 91556
#guard hostCount 504931 (whnfF ⬝ natT 500 ⬝ quoteT (whnfF ⬝ natT 3 ⬝ quoteT (I ⬝ K))) 0
  == some 504930

end SelfInterp
