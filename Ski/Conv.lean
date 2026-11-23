import Ski.BExp
import Ski.D2Sem
open Term

/-!
# Conversion invariance of the observable, and uniqueness of prefixes at every depth

Two supporting results of the S6 paper (*Prefix Regularity*), Section 2.

**The observable** (`HasObs`, the paper's Def. 1).  For a valuation `v : Term → M`, the observable
of a closed S-term `t` is `(m, v u₁, …, v uₘ)` if the head run of `t` reaches the head normal form
`S u₁ ⋯ uₘ` (`m ≤ 2`), and `(⊥, v f, v w)` if it reaches a stable frame `f w` (`f` without a head
normal form, i.e. `fold f = 36`: `stable_iff`).  The paper takes the *first* stable frame; `HasObs`
allows any stable stage, as `D2.Pre` does, and `obs_bot_first` shows that the two agree.

**Lemma 3** (`lemma3`, `obs_conv`).  If `t` and `t'` are convertible, they have the same
observable.  It is proved for every valuation that is invariant under weak reduction of closed
S-terms (`Inv`), which covers the fold into any S-model (`SModel.inv`, `lemma3_model`) and the
fold into the 373-element table `D` relative to its kernel checks (`lemma3_D`).  The paper's
further hypothesis, a homomorphism from `M` to the 38 blocks, is not used: frames and stability
are read off the term, not off its value.  `Convertible` is the equivalence closure of `WStep` on
all SKI terms; the lemma needs only its two ends to be closed S-terms.

**Prefixes** (`pre_unique`, `pre_total`).  `D2.Pre d t P` is a total functional relation in `t`
at every depth `d`, for closed S-terms `t`.  Existence is `D2.pre_exists`.

The proofs follow the paper: Church–Rosser and standardization (`Ski/Weak.lean`) for Lemma 3;
determinism of the head run and `InfNF.steps_bot_fun` for uniqueness.  That the head run reaches a
head normal form or a stable frame (`reach_frame`) is `TopTerm.reach_all`.

The relation `HasObs` is this module's own; the full observable of Theorem 6 is defined
elsewhere and is not connected here.
-/

namespace Conv
open HnfS HnfSound InfNF TopTerm D2

/-! ## Convertibility -/

/-- Convertibility: the reflexive, symmetric, transitive closure of weak reduction (a contraction
at any position), as a zigzag of steps. -/
inductive Convertible : Term → Term → Prop
  | refl (t : Term) : Convertible t t
  | fwd {t u v : Term} : WStep t u → Convertible u v → Convertible t v
  | bwd {t u v : Term} : WStep u t → Convertible u v → Convertible t v

theorem Convertible.trans {t u v : Term} (h₁ : Convertible t u) (h₂ : Convertible u v) :
    Convertible t v := by
  sorry

theorem Convertible.symm {t u : Term} (h : Convertible t u) : Convertible u t := by
  sorry

theorem Convertible.of_wsteps {t u : Term} (h : WSteps t u) : Convertible t u := by
  sorry

/-- `Convertible` is the least equivalence relation containing `WStep`. -/
theorem Convertible.least {R : Term → Term → Prop} (hr : ∀ t, R t t)
    (hs : ∀ {t u}, R t u → R u t) (ht : ∀ {t u v}, R t u → R u v → R t v)
    (hw : ∀ {t u}, WStep t u → R t u) {t u : Term} (h : Convertible t u) : R t u := by
  sorry

/-- Church–Rosser: convertible terms have a common reduct, and conversely. -/
theorem conv_iff_join {t t' : Term} :
    Convertible t t' ↔ ∃ w, WSteps t w ∧ WSteps t' w := by
  sorry

/-! ## Frames -/

/-- A closed S-term has no head normal form iff its block is `⊥ = 36` (S1). -/
theorem stable_iff {f : Term} (hf : PureS f) : fold f = 36 ↔ ¬ HasHnf f := by
  sorry

/-- The head run of every closed S-term reaches a head normal form or a stable frame. -/
theorem reach_frame {t : Term} (ht : PureS t) :
    ∃ T, Steps t T ∧ (IsHnf T ∨ ∃ f w, T = f ⬝ w ∧ fold f = 36) := by
  sorry

/-- `f w` is the first stable frame on the head run of `t`: the run reaches it, and every stable
stage of the run is at or after it. -/
def FirstStable (t f w : Term) : Prop :=
  Steps t (f ⬝ w) ∧ fold f = 36 ∧
    ∀ g x, Steps t (g ⬝ x) → fold g = 36 → Steps (f ⬝ w) (g ⬝ x)

/-- A run with a stable stage `f w` has a first stable frame `f₀ w`, and `f₀` head-reduces to
`f`. -/
theorem first_stable {t f w : Term} (ht : PureS t) (h : Steps t (f ⬝ w)) (hb : fold f = 36) :
    ∃ f₀, FirstStable t f₀ w ∧ Steps f₀ f := by
  sorry

/-! ## The observable -/

/-- Values of the observable: the arity of the head normal form with the values of its items, or
`⊥` with the values of the two parts of a stable frame. -/
inductive Obs (M : Type) : Type
  | s0 : Obs M
  | s1 (a : M) : Obs M
  | s2 (a b : M) : Obs M
  | bot (f w : M) : Obs M

/-- A valuation that is invariant under weak reduction of closed S-terms. -/
def Inv {M : Type} (v : Term → M) : Prop := ∀ {t u : Term}, PureS t → WStep t u → v u = v t

/-- `HasObs v t o`: the observable of `t` over the valuation `v` is `o`. -/
inductive HasObs {M : Type} (v : Term → M) : Term → Obs M → Prop
  | s0 {t : Term} : Steps t S → HasObs v t .s0
  | s1 {t a : Term} : Steps t (S ⬝ a) → HasObs v t (.s1 (v a))
  | s2 {t a b : Term} : Steps t (S ⬝ a ⬝ b) → HasObs v t (.s2 (v a) (v b))
  | bot {t f w : Term} : Steps t (f ⬝ w) → fold f = 36 → HasObs v t (.bot (v f) (v w))

/-- Every closed S-term has an observable. -/
theorem obs_exists {M : Type} (v : Term → M) {t : Term} (ht : PureS t) : ∃ o, HasObs v t o := by
  sorry

/-- The observable is unique. -/
theorem obs_unique {M : Type} {v : Term → M} (hv : Inv v) {t : Term} {o o' : Obs M}
    (ht : PureS t) (h : HasObs v t o) (h' : HasObs v t o') : o = o' := by
  sorry

/-- The `⊥` case of `HasObs` is the paper's: the values are those of the first stable frame. -/
theorem obs_bot_first {M : Type} {v : Term → M} (hv : Inv v) {t : Term} {m n : M}
    (ht : PureS t) :
    HasObs v t (.bot m n) ↔ ∃ f w, FirstStable t f w ∧ v f = m ∧ v w = n := by
  sorry

/-! ## Lemma 3 -/

/-- The observable is invariant under weak reduction, in both directions. -/
theorem obs_wsteps {M : Type} {v : Term → M} (hv : Inv v) {t u : Term} {o : Obs M}
    (ht : PureS t) (h : WSteps t u) : HasObs v t o ↔ HasObs v u o := by
  sorry

/-- **Lemma 3**, relational form: convertible closed S-terms have the same observables. -/
theorem obs_conv {M : Type} {v : Term → M} (hv : Inv v) {t t' : Term} {o : Obs M}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') : HasObs v t o ↔ HasObs v t' o := by
  sorry

/-- **Lemma 3.**  If `t` and `t'` are convertible, then `O(t) = O(t')`. -/
theorem lemma3 {M : Type} {v : Term → M} (hv : Inv v) {t t' : Term} {o o' : Obs M}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') (ho : HasObs v t o)
    (ho' : HasObs v t' o') : o = o' := by
  sorry

/-! ## S-models -/

/-- An S-model: a set with a binary operation and an element `s` with `s a b c = a c (b c)`. -/
structure SModel (M : Type) where
  s : M
  ap : M → M → M
  law : ∀ a b c, ap (ap (ap s a) b) c = ap (ap a c) (ap b c)

/-- The fold of a term into an S-model (`K` and `I` are sent to `s`; only closed S-terms
matter). -/
def SModel.val {M : Type} (m : SModel M) : Term → M
  | .S => m.s
  | .app f x => m.ap (m.val f) (m.val x)
  | _ => m.s

theorem SModel.inv {M : Type} (m : SModel M) : Inv m.val := by
  sorry

/-- **Lemma 3** for the fold into an S-model. -/
theorem lemma3_model {M : Type} (m : SModel M) {t t' : Term} {o o' : Obs M}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') (ho : HasObs m.val t o)
    (ho' : HasObs m.val t' o') : o = o' :=
  lemma3 m.inv ht ht' h ho ho'

/-- **Lemma 3** for the fold into the 373-element table `D`, relative to its checks. -/
theorem lemma3_D (C : Checks) {t t' : Term} {o o' : Obs Nat}
    (ht : PureS t) (ht' : PureS t') (h : Convertible t t') (ho : HasObs foldD t o)
    (ho' : HasObs foldD t' o') : o = o' := by
  sorry

/-! ## Prefixes at every depth -/

/-- **Uniqueness of prefixes.**  `Pre d t` has at most one value, at every depth. -/
theorem pre_unique : ∀ (d : Nat) {t : Term} {P P' : PT}, PureS t → Pre d t P → Pre d t P' →
    P = P' := by
  sorry

/-- `π_d` is a total function on closed S-terms. -/
theorem pre_total (d : Nat) {t : Term} (ht : PureS t) :
    ∃ P, Pre d t P ∧ ∀ Q, Pre d t Q → Q = P := by
  sorry

end Conv
