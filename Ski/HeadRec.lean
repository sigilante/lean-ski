import Ski.HnfS
open Term

/-!
# No head recurrence in pure S: the cases of zero and one emitted argument

A *head recurrence* is a closed S-term `t` with `t →h⁺ t X₁ … X_k` by head reduction (`Step`).
Such a term has no head normal form and emits `X₁ … X_k` forever.  This module proves, for
closed pure-S terms, that there is none with `k = 0` and none with `k = 1`:

* `no_head_cycle`: no `t` with `t →h⁺ t`;
* `no_head_recurrence_one`: no `t`, `X` with `t →h⁺ t X`.

The case `k ≥ 2` is **not** proved here (see `notes/A1-no-head-recurrence.md`).

The tools are three facts about the last arguments of the spine along head reduction:

* `split`: a head reduction from `e l` either never touches `l` (it is a head reduction of `e`),
  or passes through a root redex `S f g l` with `e →h* S f g`;
* `last_wrap`: the last argument only ever gets wrapped, `G ↦ d G` (`Wrap`);
* `last2`: from `v F G` with `|F| < |G|`, either the last two arguments are untouched, or the
  second-to-last has become larger than `F` for good.

From these:

* `no_snd_self`: no `c` with `c →h* S p c`;
* `no_fst_self`: no `x` with `x →h* S x y`.

No use is made of the fold or of top-termination.
-/

namespace HeadRec
open HnfS

/-- Leaf count. -/
def sz : Term → Nat
  | .app f x => sz f + sz x
  | .S => 1
  | .K => 1
  | .I => 1

theorem sz_pos : ∀ t : Term, 0 < sz t
  | .S => Nat.lt_succ_self 0
  | .K => Nat.lt_succ_self 0
  | .I => Nat.lt_succ_self 0
  | .app f _ => Nat.lt_of_lt_of_le (sz_pos f) (Nat.le_add_right _ _)

theorem sz_arg_lt (f x : Term) : sz x < sz (f ⬝ x) := by
  have := sz_pos f
  show sz x < sz f + sz x
  omega

theorem sz_fun_lt (f x : Term) : sz f < sz (f ⬝ x) := by
  have := sz_pos x
  show sz f < sz f + sz x
  omega

theorem ne_app_arg (f x : Term) : x ≠ f ⬝ x := fun h => by
  have h' := sz_arg_lt f x
  rw [← h] at h'
  exact Nat.lt_irrefl _ h'

theorem steps_pure {t u : Term} (ht : PureS t) (h : Steps t u) : PureS u := by
  induction h with
  | refl => exact ht
  | step s _ ih => exact ih (wstep_pure s.weak ht).1

/-- A head step of `u a`, for pure `u`: inside `u`, or the root step of `S f g a`. -/
theorem step_inv {u a w : Term} (hu : PureS u) (s : Step (u ⬝ a) w) :
    (∃ u', Step u u' ∧ w = u' ⬝ a) ∨ (∃ f g, u = S ⬝ f ⬝ g ∧ w = f ⬝ a ⬝ (g ⬝ a)) := by
  cases s with
  | S f g => exact .inr ⟨f, g, rfl, rfl⟩
  | K => cases hu with | app h _ => cases h
  | I => cases hu
  | left _ s' => exact .inl ⟨_, s', rfl⟩

/-- The result of a head step of a pure term has at least two arguments. -/
theorem step_two {t t' : Term} (ht : PureS t) (s : Step t t') : ∃ a b c, t' = a ⬝ b ⬝ c := by
  induction s with
  | S f g x => exact ⟨f, x, g ⬝ x, rfl⟩
  | K => cases ht with | app h _ => cases h with | app h _ => cases h
  | I => cases ht with | app h _ => cases h
  | left x _ ih =>
    obtain ⟨a, b, c, e⟩ := ih ht.app_inv.1
    exact ⟨a ⬝ b, c, x, by rw [e]⟩

theorem steps_S {w : Term} (h : Steps S w) : w = S := by
  cases h with
  | refl => rfl
  | step s _ => cases s

/-- A head reduction is empty or has a last step. -/
theorem steps_last {t w : Term} (h : Steps t w) : t = w ∨ ∃ t', Steps t t' ∧ Step t' w := by
  induction h with
  | refl => exact .inl rfl
  | @step t t₁ w s _ ih =>
    rcases ih with rfl | ⟨t', h1, h2⟩
    · exact .inr ⟨t, .refl _, s⟩
    · exact .inr ⟨t', .step s h1, h2⟩

/-- The only head step into `S p q` is `S S y p → S p (y p)`. -/
theorem step_to_S2 {t p q : Term} (ht : PureS t) (s : Step t (S ⬝ p ⬝ q)) :
    ∃ y, t = S ⬝ S ⬝ y ⬝ p ∧ q = y ⬝ p := by
  obtain ⟨u, a, rfl⟩ : ∃ u a, t = u ⬝ a := by
    cases s with
    | S f g x => exact ⟨_, _, rfl⟩
    | K x y => exact ⟨_, _, rfl⟩
    | I x => exact ⟨_, _, rfl⟩
    | left x _ => exact ⟨_, _, rfl⟩
  rcases step_inv ht.app_inv.1 s with ⟨u', s', e⟩ | ⟨f, g, rfl, e⟩
  · injection e with e1 _
    subst e1
    obtain ⟨_, _, _, e'⟩ := step_two ht.app_inv.1 s'
    injection e' with e'' _
    cases e''
  · injection e with e1 e2
    injection e1 with e3 e4
    subst e3 e4
    exact ⟨g, rfl, e2⟩

/-- `Wrap G H`: `H = dₙ (… (d₁ G))`, the shapes the last argument can take. -/
inductive Wrap (G : Term) : Term → Prop
  | refl : Wrap G G
  | wrap (d : Term) {H : Term} : Wrap G H → Wrap G (d ⬝ H)

theorem Wrap.sz_le {G H : Term} (h : Wrap G H) : sz G ≤ sz H := by
  induction h with
  | refl => exact Nat.le_refl _
  | wrap d _ ih => exact Nat.le_trans ih (Nat.le_of_lt (sz_arg_lt d _))

theorem Wrap.trans {G H M : Term} (h1 : Wrap G H) (h2 : Wrap H M) : Wrap G M := by
  induction h2 with
  | refl => exact h1
  | wrap d _ ih => exact .wrap d ih

/-- A wrapping of `g a` that equals `c a` is trivial. -/
theorem Wrap.app_eq {g c a : Term} (h : Wrap (g ⬝ a) (c ⬝ a)) : g = c := by
  generalize hH : c ⬝ a = H at h
  cases h with
  | refl => injection hH with e _; exact e.symm
  | wrap d h' =>
    injection hH with _ e
    subst e
    exact absurd h'.sz_le (Nat.not_le_of_lt (sz_arg_lt g a))

/-- Along head reduction the last argument only gets wrapped. -/
theorem last_wrap {t w : Term} (h : Steps t w) : ∀ {u G : Term}, t = u ⬝ G → PureS t →
    ∃ u' G', w = u' ⬝ G' ∧ Wrap G G' := by
  induction h with
  | refl => intro u G e _; exact ⟨u, G, e, .refl⟩
  | step s _ ih =>
    intro u G e hp
    subst e
    have hp' := (wstep_pure s.weak hp).1
    rcases step_inv hp.app_inv.1 s with ⟨u', _, rfl⟩ | ⟨f, g, rfl, rfl⟩
    · exact ih rfl hp'
    · obtain ⟨u', G', e, hw⟩ := ih rfl hp'
      exact ⟨u', G', e, Wrap.trans (.wrap g .refl) hw⟩

/-- A head reduction from `e l` never touches `l`, or passes through a root redex `S f g l`. -/
theorem split {t w : Term} (h : Steps t w) : ∀ {e l : Term}, t = e ⬝ l → PureS t →
    (∃ e', w = e' ⬝ l ∧ Steps e e') ∨
    (∃ f g, Steps e (S ⬝ f ⬝ g) ∧ Steps (f ⬝ l ⬝ (g ⬝ l)) w) := by
  induction h with
  | refl => intro e l h _; exact .inl ⟨e, h, .refl _⟩
  | step s rest ih =>
    intro e l h hp
    subst h
    have hp' := (wstep_pure s.weak hp).1
    rcases step_inv hp.app_inv.1 s with ⟨u', s', rfl⟩ | ⟨f, g, rfl, rfl⟩
    · rcases ih rfl hp' with ⟨e', h1, h2⟩ | ⟨f, g, h1, h2⟩
      · exact .inl ⟨e', h1, .step s' h2⟩
      · exact .inr ⟨f, g, .step s' h1, h2⟩
    · exact .inr ⟨f, g, .refl _, rest⟩

/-- Once the last two arguments are both larger than `n`, they stay so. -/
theorem last2_grown {n : Nat} {t w : Term} (h : Steps t w) : ∀ {v F G : Term},
    t = v ⬝ F ⬝ G → PureS t → n < sz F → n < sz G →
    ∃ v' F' G', w = v' ⬝ F' ⬝ G' ∧ n < sz F' ∧ n < sz G' := by
  induction h with
  | refl => intro v F G e _ h1 h2; exact ⟨v, F, G, e, h1, h2⟩
  | step s _ ih =>
    intro v F G e hp h1 h2
    subst e
    have hp' := (wstep_pure s.weak hp).1
    rcases step_inv hp.app_inv.1 s with ⟨u', s', rfl⟩ | ⟨f, g, e, rfl⟩
    · rcases step_inv hp.app_inv.1.app_inv.1 s' with ⟨v', _, rfl⟩ | ⟨f, g, rfl, rfl⟩
      · exact ih rfl hp' h1 h2
      · exact ih rfl hp' (Nat.lt_trans h1 (sz_arg_lt g F)) h2
    · injection e with _ e2
      subst e2
      exact ih rfl hp' h2 (Nat.lt_trans h2 (sz_arg_lt F G))

/-- From `v F G` with `|F| < |G|`: the last two arguments are untouched, or the second-to-last
has become larger than `F`. -/
theorem last2 {t w : Term} (h : Steps t w) : ∀ {v F G : Term}, t = v ⬝ F ⬝ G → PureS t →
    sz F < sz G →
    ∃ v' F' G', w = v' ⬝ F' ⬝ G' ∧ ((F' = F ∧ G' = G ∧ Steps v v') ∨ sz F < sz F') := by
  induction h with
  | refl => intro v F G e _ _; exact ⟨v, F, G, e, .inl ⟨rfl, rfl, .refl _⟩⟩
  | step s rest ih =>
    intro v F G e hp hFG
    subst e
    have hp' := (wstep_pure s.weak hp).1
    rcases step_inv hp.app_inv.1 s with ⟨u', s', rfl⟩ | ⟨f, g, e, rfl⟩
    · rcases step_inv hp.app_inv.1.app_inv.1 s' with ⟨v', s'', rfl⟩ | ⟨f, g, rfl, rfl⟩
      · obtain ⟨v₁, F', G', e, hr⟩ := ih rfl hp' hFG
        rcases hr with ⟨e1, e2, h3⟩ | h3
        · exact ⟨v₁, F', G', e, .inl ⟨e1, e2, .step s'' h3⟩⟩
        · exact ⟨v₁, F', G', e, .inr h3⟩
      · obtain ⟨v₁, F', G', e, h3, _⟩ := last2_grown rest rfl hp' (sz_arg_lt g F) hFG
        exact ⟨v₁, F', G', e, .inr h3⟩
    · injection e with _ e2
      subst e2
      obtain ⟨v₁, F', G', e, h3, _⟩ :=
        last2_grown rest rfl hp' hFG (Nat.lt_trans hFG (sz_arg_lt F G))
      exact ⟨v₁, F', G', e, .inr h3⟩

/-- No closed S-term head-reduces to a head normal form `S p c` whose second argument is the
term itself. -/
theorem no_snd_self : ∀ {c : Term}, PureS c → ∀ (p : Term), ¬ Steps c (S ⬝ p ⬝ c) := by
  intro c hc
  induction hc with
  | S => intro p h; cases steps_S h
  | @app e l he hl ihe _ =>
    intro p h
    rcases split h rfl (.app he hl) with ⟨e', h1, _⟩ | ⟨f, g, h1, h2⟩
    · injection h1 with _ e2
      exact ne_app_arg e l e2.symm
    · have hS := steps_pure he h1
      have hp2 : PureS (f ⬝ l ⬝ (g ⬝ l)) :=
        .app (.app hS.app_inv.1.app_inv.2 hl) (.app hS.app_inv.2 hl)
      obtain ⟨u', G', e, hw⟩ := last_wrap h2 rfl hp2
      injection e with _ e2
      subst e2
      have := hw.app_eq
      subst this
      exact ihe f h1

/-- No closed S-term head-reduces to a head normal form `S x y` whose first argument is the
term itself. -/
theorem no_fst_self {x : Term} (hx : PureS x) (y : Term) : ¬ Steps x (S ⬝ x ⬝ y) := by
  intro h
  cases hx with
  | S => cases steps_S h
  | @app c a hc ha =>
    rcases split h rfl (.app hc ha) with ⟨e', h1, h2⟩ | ⟨f, g, h1, h2⟩
    · injection h1 with e1 _
      subst e1
      rcases steps_last h2 with e | ⟨t', h3, s⟩
      · have : sz c < sz c := by
          have h' := sz_fun_lt c a
          have h'' := sz_arg_lt S (c ⬝ a)
          rw [← e] at h''
          exact Nat.lt_trans h' h''
        exact Nat.lt_irrefl _ this
      · obtain ⟨_, _, _, e⟩ := step_two (steps_pure hc h3) s
        injection e with e' _
        cases e'
    · have hS := steps_pure hc h1
      have hp2 : PureS (f ⬝ a ⬝ (g ⬝ a)) :=
        .app (.app hS.app_inv.1.app_inv.2 ha) (.app hS.app_inv.2 ha)
      rcases steps_last h2 with e | ⟨t', h3, s⟩
      · injection e with e1 _
        injection e1 with _ e2
        exact ne_app_arg c a e2
      · obtain ⟨y', rfl, _⟩ := step_to_S2 (steps_pure hp2 h3) s
        obtain ⟨u', G', e, hw⟩ := last_wrap h3 rfl hp2
        injection e with _ e2
        subst e2
        have := hw.app_eq
        subst this
        exact no_snd_self hc f h1

/-- No closed S-term returns to itself by head reduction. -/
theorem no_head_cycle : ∀ {t : Term}, PureS t → ∀ {t' : Term}, Step t t' → ¬ Steps t' t := by
  intro t ht
  induction ht with
  | S => intro t' s; cases s
  | @app u a hu ha ihu _ =>
    intro t' s h
    have key : ∀ {f g : Term}, PureS f → PureS g → ¬ Steps (f ⬝ a ⬝ (g ⬝ a)) (u ⬝ a) := by
      intro f g hf hg h2
      obtain ⟨u', G', e, hw⟩ := last_wrap h2 rfl (.app (.app hf ha) (.app hg ha))
      injection e with _ e2
      subst e2
      exact absurd hw.sz_le (Nat.not_le_of_lt (sz_arg_lt g _))
    rcases step_inv hu s with ⟨u', s', rfl⟩ | ⟨f, g, rfl, rfl⟩
    · have hu' := (wstep_pure s'.weak hu).1
      rcases split h rfl (.app hu' ha) with ⟨e', h1, h2⟩ | ⟨f, g, h1, h2⟩
      · injection h1 with e1 _
        subst e1
        exact ihu s' h2
      · have hS := steps_pure hu' h1
        exact key hS.app_inv.1.app_inv.2 hS.app_inv.2 h2
    · exact key hu.app_inv.1.app_inv.2 hu.app_inv.2 h

/-- Reflexive form of the one-argument case; `t = t X` is impossible, so the reduction is
nonempty. -/
theorem no_steps_self_app : ∀ {t : Term}, PureS t → ∀ (X : Term), ¬ Steps t (t ⬝ X) := by
  intro t ht
  induction ht with
  | S => intro X h; cases steps_S h
  | @app u a hu ha ihu _ =>
    intro X h
    rcases split h rfl (.app hu ha) with ⟨e', h1, h2⟩ | ⟨f, g, h1, h2⟩
    · injection h1 with e1 e2
      subst e1 e2
      exact ihu _ h2
    · have hS := steps_pure hu h1
      have hf := hS.app_inv.1.app_inv.2
      have hp2 : PureS (f ⬝ a ⬝ (g ⬝ a)) := .app (.app hf ha) (.app hS.app_inv.2 ha)
      have h3 : Steps (f ⬝ a ⬝ (g ⬝ a)) (S ⬝ f ⬝ g ⬝ a ⬝ X) :=
        h2.trans (Steps.left X (Steps.left a h1))
      obtain ⟨v', F', G', e, hr⟩ := last2 h3 rfl hp2 (sz_arg_lt g a)
      injection e with e1 _
      injection e1 with e3 e4
      subst e3 e4
      rcases hr with ⟨_, _, h4⟩ | h4
      · exact no_fst_self hf g h4
      · exact Nat.lt_irrefl _ h4

/-- **No head recurrence with one emitted argument.**  No closed S-term `t` head-reduces, in
one or more steps, to `t X`. -/
theorem no_head_recurrence_one {t t' X : Term} (ht : PureS t) (s : Step t t')
    (h : Steps t' (t ⬝ X)) : False :=
  no_steps_self_app ht X (.step s h)

end HeadRec
