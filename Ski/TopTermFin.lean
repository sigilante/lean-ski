import Ski.TopTerm
open Term

/-!
# Root steps on the head path

`Fin t`: the head path of `t` does not make arbitrarily many root steps (stated negatively,
`¬ ∀ k, ∃ v, HRun k t v`; an explicit bound follows only classically, and is not needed).  Closure rules:

* `fin_of_step`, `fin_of_steps`: `Fin` passes back along head reduction (head steps are
  deterministic);
* `fin_of_hnf`, `fin_of_fold`: a term with a head normal form (`HnfSound.sound_head`);
* `fin_of_bot_fun`: a term `f w` whose function part `f` has no head normal form makes no root
  step at all (its head path is `f`'s, with `w` carried along).

Waldmann's sets P (right combs) and Q (the rest) are sets of blocks: `qB b` iff `b ∉
{0, 1, 2, 4, 8, 17}`.  `qqq`: three Q-terms applied have block ⊥ (Waldmann, thesis, 7.2.1).
-/

namespace TopTerm
open HnfS HnfSound

def Fin (t : Term) : Prop := ¬ ∀ k, ∃ v, HRun k t v

theorem HRun.pred : ∀ {k : Nat} {t v : Term}, HRun (k + 1) t v → HRun k t v := by
  intro k t v h
  generalize hk : k + 1 = m at h
  induction h generalizing k with
  | refl => cases hk
  | head s _ ih => exact .head s (ih hk)
  | @root k' f g x u hs _ =>
    have : k' = k := by injection hk with h; exact h.symm
    subst this
    exact .head (.S f g x) hs

/-- Along the deterministic head path, a run from `t` continues from its successor. -/
theorem HRun.step {t t' : Term} (s : Step t t') :
    ∀ {k : Nat} {v : Term}, HRun (k + 1) t v → ∃ v', HRun k t' v' := by
  intro k v h
  generalize hk : k + 1 = m at h
  induction h generalizing k with
  | refl => cases hk
  | head s' hs _ =>
    subst hk; rw [Step.det s s']; exact ⟨_, hs.pred⟩
  | @root k' f g x u hs _ =>
    have : k' = k := by injection hk with h; exact h.symm
    subst this
    rw [Step.det s (.S f g x)]; exact ⟨u, hs⟩

theorem fin_of_step {t t' : Term} (s : Step t t') (h : Fin t') : Fin t := fun hall =>
  h fun k => by
    obtain ⟨v, hv⟩ := hall (k + 1)
    exact HRun.step s hv

theorem fin_of_steps {t t' : Term} (s : Steps t t') (h : Fin t') : Fin t := by
  induction s with
  | refl => exact h
  | step s _ ih => exact fin_of_step s (ih h)

theorem step_foldl {a b : Term} (h : Step a b) : ∀ (rest : List Term),
    Step (rest.foldl Term.app a) (rest.foldl Term.app b) := by
  intro rest
  induction rest generalizing a b with
  | nil => exact h
  | cons r rest ih => exact ih (.left r h)

theorem headChain_steps {t u : Term} (h : HeadChain t u) : Steps t u := by
  induction h with
  | refl => exact .refl _
  | step _ hS _ ih => rw [hS]; exact .step (step_foldl (.S _ _ _) _) ih

theorem no_step_hnf {u u' : Term} (hu : IsHnf u) (s : Step u u') : False := by
  rcases hu with rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩
  · cases s
  · cases s with | left _ s => cases s
  · cases s with | left _ s => cases s with | left _ s => cases s

theorem fin_of_hnf {u : Term} (hu : IsHnf u) : Fin u := fun hall => by
  obtain ⟨v, hv⟩ := hall 1
  cases hv with
  | head s _ => exact no_step_hnf hu s
  | root _ =>
    rcases hu with h | ⟨x, h⟩ | ⟨x, y, h⟩ <;> cases h

theorem fin_of_fold {t : Term} (ht : PureS t) (hb : fold t ≠ 36) : Fin t := by
  obtain ⟨u, hc, _, hu⟩ := sound_head t ht hb
  exact fin_of_steps (headChain_steps hc) (fin_of_hnf hu)

/-- A term whose function part has no head normal form makes no root step. -/
theorem hrun_bot_fun : ∀ {k : Nat} {t v : Term}, HRun k t v →
    ∀ {f w : Term}, t = f ⬝ w → PureS f → fold f = 36 → k = 0 := by
  intro k t v h
  induction h with
  | refl => intro _ _ _ _ _; rfl
  | head s _ ih =>
    intro f w ht hf hb
    subst ht
    cases s with
    | S a b c =>
      exact absurd hb (fold_hnf hf (.inr (.inr ⟨a, b, rfl⟩)))
    | K => cases hf with | app h _ => cases h
    | I => cases hf
    | left _ s =>
      have hw := (HnfS.wstep_pure s.weak hf)
      exact ih rfl hw.1 (hw.2 ▸ hb)
  | root _ _ =>
    intro f w ht hf hb
    cases ht
    exact absurd hb (fold_hnf hf (.inr (.inr ⟨_, _, rfl⟩)))

theorem fin_of_bot_fun {f w : Term} (hf : PureS f) (hb : fold f = 36) : Fin (f ⬝ w) :=
  fun hall => by
    obtain ⟨v, hv⟩ := hall 1
    exact absurd (hrun_bot_fun hv rfl hf hb) (by decide)

/-! ## Reaching the end of root steps, constructively -/

/-- The head path of `t` reaches a head normal form, or a term whose function part has no head
normal form; either way no root step follows (`fin_of_reach`).  Positive form of `Fin`. -/
inductive Reach : Term → Prop
  | hnf {t : Term} : IsHnf t → Reach t
  | bot {f w : Term} : PureS f → fold f = 36 → Reach (f ⬝ w)
  | step {t t' : Term} : Step t t' → Reach t' → Reach t

theorem reach_of_step {t t' : Term} (s : Step t t') (h : Reach t') : Reach t := .step s h

theorem reach_of_steps {t t' : Term} (s : Steps t t') (h : Reach t') : Reach t := by
  induction s with
  | refl => exact h
  | step s _ ih => exact .step s (ih h)

theorem reach_of_hnf {u : Term} (hu : IsHnf u) : Reach u := .hnf hu

theorem reach_of_bot_fun {f w : Term} (hf : PureS f) (hb : fold f = 36) : Reach (f ⬝ w) := .bot hf hb

theorem reach_of_fold {t : Term} (ht : PureS t) (hb : fold t ≠ 36) : Reach t := by
  obtain ⟨u, hc, _, hu⟩ := sound_head t ht hb
  exact reach_of_steps (headChain_steps hc) (.hnf hu)

theorem fin_of_reach {t : Term} (h : Reach t) : Fin t := by
  induction h with
  | hnf hu => exact fin_of_hnf hu
  | bot hf hb => exact fin_of_bot_fun hf hb
  | step s _ ih => exact fin_of_step s ih

/-! ## Right combs and the rest, as blocks -/

/-- Block of a non-right-comb (Waldmann's `Q`); the right combs `S`, `S S`, `S (S S)`, … have
blocks `0, 1, 2, 4, 8, 17`. -/
def qB (b : Nat) : Bool := !([0, 1, 2, 4, 8, 17].contains b)

def r38 : List Nat := List.range 38

def qAppB : Bool := r38.all fun x => r38.all fun y => qB (β x y) == (x != 0 || qB y)
def qqqB : Bool := r38.all fun a => r38.all fun b => r38.all fun c =>
  !qB a || !qB b || !qB c || β (β a b) c == 36

theorem qAppB_eq : qAppB = true := by decide +kernel
theorem qqqB_eq : qqqB = true := by decide +kernel

theorem q_app {x y : Nat} (hx : x < 38) (hy : y < 38) : qB (β x y) = (x != 0 || qB y) := by
  have h := qAppB_eq
  simp only [qAppB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h x hx y hy

theorem qqq {a b c : Nat} (ha : a < 38) (hb : b < 38) (hc : c < 38)
    (qa : qB a = true) (qb : qB b = true) (qc : qB c = true) : β (β a b) c = 36 := by
  have h := qqqB_eq
  simp only [qqqB, r38, List.all_eq_true, List.mem_range] at h
  have := h a ha b hb c hc
  simp only [qa, qb, qc, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

/-- Waldmann 7.2.1: three non-right-combs applied have no head normal form. -/
theorem qqq_bot {A B C : Term} (hA : PureS A) (hB : PureS B) (hC : PureS C)
    (qa : qB (fold A) = true) (qb : qB (fold B) = true) (qc : qB (fold C) = true) :
    fold (A ⬝ B ⬝ C) = 36 :=
  qqq (fold_lt hA) (fold_lt hB) (fold_lt hC) qa qb qc

end TopTerm
