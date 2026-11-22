import Ski.HnfS
open Term

/-!
# No head recurrence in pure S

A *head recurrence* is a closed S-term `t` with `t →h⁺ t X₁ … X_k` by head reduction (`Step`).
Such a term has no head normal form and emits `X₁ … X_k` forever.  This module proves, for
closed pure-S terms, that there is none with `k = 0` and none with `k = 1`:

* `no_head_cycle`: no `t` with `t →h⁺ t`;
* `no_head_recurrence_one`: no `t`, `X` with `t →h⁺ t X`.

Those two proofs are elementary and self-contained.  The general case, every `k`, is proved in
the last section by Waldmann's labelling argument (*The combinator S*, Inf. & Comput. 159, 2000,
Thm 8 – Cor. 17), which gives more: no closed S-term reduces to a term that contains it.

* `bsn`: weak reduction restricted to redexes `S f g x` whose `x` has right depth `< N` terminates;
* `no_ground_loop`: no `t →⁺ C[t]` (weak reduction, any context);
* `no_head_recurrence`, `nhr`, `efr`, `sfr`: no `t →h⁺ t X⃗`; no exact or self front return.

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

Frame lemmas and reductions between the statements (independent of the last section):

* `steps_blex`: bottom-lex monotonicity, the run-level form of `last_wrap` for every position;
* `last_root`, `efr_of_recurrence`: the normal form of a recurrence;
* `nhr_iff_efr`: no recurrence with `k ≥ 1` iff no exact front return `x z →h⁺ S x y z Y⃗`;
* `recurrence_of_sfr`, `sfr_of_efr`: a self front return `x →h* S x A⃗` with `|A⃗| ≥ 2` is a
  recurrence, so it follows from `EFR` (`efr`, last section).
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

/-! ## Bottom-lex monotonicity

Number the spine positions from the bottom: position 1 is the last argument.  A head step on a
spine of length `m` keeps positions `1 … m-3`, replaces the item `z` at position `m-2` by `y z`,
and rebuilds everything above.  So the lowest position that changes, changes by a proper wrap.
`BLex` states this for whole runs, directly on terms. -/

/-- `BLex u v`: reading the arguments of `u` and `v` from the last one upward, they agree up to
some position, and there `u` has `G` and `v` has a proper wrap `dₙ (… (d₁ (d G)))` of `G`.
Nothing is said about the positions above. -/
inductive BLex : Term → Term → Prop
  | here (d : Term) {u u' G G' : Term} : Wrap (d ⬝ G) G' → BLex (u ⬝ G) (u' ⬝ G')
  | up {u u' : Term} (G : Term) : BLex u u' → BLex (u ⬝ G) (u' ⬝ G)

theorem BLex.trans {a b c : Term} (h1 : BLex a b) (h2 : BLex b c) : BLex a c := by
  induction h1 generalizing c with
  | here d w =>
    cases h2 with
    | here d' w' => exact .here d (Wrap.trans w (Wrap.trans (.wrap d' .refl) w'))
    | up _ _ => exact .here d w
  | up G _ ih =>
    cases h2 with
    | here d' w' => exact .here d' w'
    | up _ h' => exact .up G (ih h')

theorem BLex.ne {t w : Term} (h : BLex t w) : t ≠ w := by
  induction h with
  | @here d u u' G G' w =>
    intro e
    injection e with _ e2
    subst e2
    exact absurd w.sz_le (Nat.not_le_of_lt (sz_arg_lt d G))
  | up G _ ih =>
    intro e
    injection e with e1 _
    exact ih e1

/-- The last argument of a `BLex`-larger term is a wrap of the last argument. -/
theorem BLex.last {u G w : Term} (h : BLex (u ⬝ G) w) : ∃ u' G', w = u' ⬝ G' ∧ Wrap G G' := by
  cases h with
  | here d w' => exact ⟨_, _, rfl, Wrap.trans (.wrap d .refl) w'⟩
  | up _ _ => exact ⟨_, _, rfl, .refl⟩

/-- Inversion: the last argument is properly wrapped, or it is unchanged and the function parts
are `BLex`-related. -/
theorem BLex.inv {u G w : Term} (h : BLex (u ⬝ G) w) :
    ∃ u' G', w = u' ⬝ G' ∧ ((∃ d, Wrap (d ⬝ G) G') ∨ (G' = G ∧ BLex u u')) := by
  cases h with
  | here d w' => exact ⟨_, _, rfl, .inl ⟨d, w'⟩⟩
  | up _ h' => exact ⟨_, _, rfl, .inr ⟨rfl, h'⟩⟩

/-- A head step of a closed S-term is a bottom-lex increase. -/
theorem step_blex {t t' : Term} (ht : PureS t) (s : Step t t') : BLex t t' := by
  induction s with
  | S f g x => exact .here g .refl
  | K => cases ht with | app h _ => cases h with | app h _ => cases h
  | I => cases ht with | app h _ => cases h
  | left x _ ih => exact .up x (ih ht.app_inv.1)

/-- **Bottom-lex monotonicity.**  Along a head reduction of a closed S-term, either nothing
happened, or the lowest spine position that was touched holds a proper wrap of its original
item and everything below it is unchanged. -/
theorem steps_blex {t w : Term} (h : Steps t w) (ht : PureS t) : t = w ∨ BLex t w := by
  induction h with
  | refl => exact .inl rfl
  | step s _ ih =>
    have hb := step_blex ht s
    rcases ih (wstep_pure s.weak ht).1 with rfl | h'
    · exact .inr hb
    · exact .inr (hb.trans h')

/-- The arguments of a term, last one first. -/
def rargs : Term → List Term
  | .app f x => x :: rargs f
  | _ => []

/-- `BLex` on reversed argument lists: a common part `B` below, then `G` against a proper wrap
of `G`. -/
theorem BLex.rargs {u v : Term} (h : BLex u v) : ∃ B G G' T T' d,
    rargs u = B ++ G :: T ∧ rargs v = B ++ G' :: T' ∧ Wrap (d ⬝ G) G' := by
  induction h with
  | here d w => exact ⟨[], _, _, _, _, d, rfl, rfl, w⟩
  | @up u u' G _ ih =>
    obtain ⟨B, G₀, G', T, T', d, e1, e2, w⟩ := ih
    refine ⟨G :: B, G₀, G', T, T', d, ?_, ?_, w⟩
    · show G :: HeadRec.rargs u = G :: (B ++ G₀ :: T)
      rw [e1]
    · show G :: HeadRec.rargs u' = G :: (B ++ G' :: T')
      rw [e2]

/-- Bottom-lex monotonicity, on reversed argument lists. -/
theorem steps_rargs {t w : Term} (h : Steps t w) (ht : PureS t) : t = w ∨ ∃ B G G' T T' d,
    rargs t = B ++ G :: T ∧ rargs w = B ++ G' :: T' ∧ Wrap (d ⬝ G) G' :=
  (steps_blex h ht).imp id BLex.rargs

/-- `last_wrap` again, as a corollary of bottom-lex monotonicity. -/
theorem last_wrap_of_blex {u G w : Term} (h : Steps (u ⬝ G) w) (hp : PureS (u ⬝ G)) :
    ∃ u' G', w = u' ⬝ G' ∧ Wrap G G' := by
  rcases steps_blex h hp with rfl | hb
  · exact ⟨u, G, rfl, .refl⟩
  · exact hb.last

/-- `no_head_cycle` again, as a corollary of bottom-lex monotonicity. -/
theorem no_head_cycle_of_blex {t t' : Term} (ht : PureS t) (s : Step t t') : ¬ Steps t' t := by
  intro h
  have hb := step_blex ht s
  rcases steps_blex h (wstep_pure s.weak ht).1 with e | h'
  · exact hb.ne e.symm
  · exact (hb.trans h').ne rfl

/-! ## Exact Front Return ⟺ no head recurrence with `k ≥ 1`

Argument vectors are `List Term`, applied left to right by `apps`:
`apps h [a₁, …, aₙ] = h a₁ … aₙ`.  `Plus` is one or more head steps. -/

/-- `apps h [a₁, …, aₙ] = h a₁ … aₙ`. -/
def apps (h : Term) : List Term → Term
  | [] => h
  | a :: L => apps (h ⬝ a) L

/-- One or more head steps. -/
def Plus (t w : Term) : Prop := ∃ t', Step t t' ∧ Steps t' w

theorem Plus.steps {t w : Term} (h : Plus t w) : Steps t w :=
  let ⟨_, s, r⟩ := h; .step s r

theorem plus_of_steps_ne {t w : Term} (h : Steps t w) (hne : t ≠ w) : Plus t w := by
  cases h with
  | refl => exact absurd rfl hne
  | step s r => exact ⟨_, s, r⟩

theorem apps_snoc (h : Term) (L : List Term) (a : Term) : apps h (L ++ [a]) = apps h L ⬝ a := by
  induction L generalizing h with
  | nil => rfl
  | cons b L ih => exact ih (h ⬝ b)

theorem steps_apps {f f' : Term} (L : List Term) (h : Steps f f') :
    Steps (apps f L) (apps f' L) := by
  induction L generalizing f f' with
  | nil => exact h
  | cons a L ih => exact ih (Steps.left a h)

theorem sz_le_apps (h : Term) (L : List Term) : sz h ≤ sz (apps h L) := by
  induction L generalizing h with
  | nil => exact Nat.le_refl _
  | cons a L ih => exact Nat.le_trans (Nat.le_of_lt (sz_fun_lt h a)) (ih (h ⬝ a))

theorem sz_lt_apps (h : Term) {L : List Term} (hL : L ≠ []) : sz h < sz (apps h L) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a L => exact Nat.lt_of_lt_of_le (sz_fun_lt h a) (sz_le_apps (h ⬝ a) L)

theorem pure_apps {h : Term} {L : List Term} (hp : PureS (apps h L)) : PureS h := by
  induction L generalizing h with
  | nil => exact hp
  | cons a L ih => exact (ih hp).app_inv.1

/-- If `h a₁ … aₙ` is `e a`, then `n = 0`, or `a = aₙ` and `e = h a₁ … aₙ₋₁`. -/
theorem apps_eq_app {h e a : Term} {L : List Term} (heq : apps h L = e ⬝ a) :
    (L = [] ∧ h = e ⬝ a) ∨ ∃ L₀, L = L₀ ++ [a] ∧ e = apps h L₀ := by
  induction L generalizing h with
  | nil => exact .inl ⟨rfl, heq⟩
  | cons b L ih =>
    rcases ih heq with ⟨rfl, e1⟩ | ⟨L₀, rfl, e1⟩
    · injection e1 with e2 e3
      subst e2 e3
      exact .inr ⟨[], rfl, rfl⟩
    · exact .inr ⟨b :: L₀, rfl, e1⟩

/-- **Root redex with an untouched tail.**  A head reduction from `e l` never touches `l`, or it
passes through a root redex `S x y z` after which the new last argument `y z` is not touched,
and the rest is a head reduction of `x z`.  (The statement does not assert that this redex is
the last root redex; nothing downstream needs that.) -/
theorem last_root {t w : Term} (h : Steps t w) : ∀ {e l : Term}, t = e ⬝ l → PureS t →
    (∃ e', w = e' ⬝ l ∧ Steps e e') ∨
    (∃ x y z e', Steps t (S ⬝ x ⬝ y ⬝ z) ∧ w = e' ⬝ (y ⬝ z) ∧ Steps (x ⬝ z) e') := by
  induction h with
  | refl => intro e l h _; exact .inl ⟨e, h, .refl _⟩
  | step s rest ih =>
    intro e l h hp
    subst h
    have hp' := (wstep_pure s.weak hp).1
    rcases step_inv hp.app_inv.1 s with ⟨u', s', rfl⟩ | ⟨f, g, rfl, rfl⟩
    · rcases ih rfl hp' with ⟨e', h1, h2⟩ | ⟨x, y, z, e', h1, h2, h3⟩
      · exact .inl ⟨e', h1, .step s' h2⟩
      · exact .inr ⟨x, y, z, e', .step s h1, h2, h3⟩
    · rcases ih rfl hp' with ⟨e', h1, h2⟩ | ⟨x, y, z, e', h1, h2, h3⟩
      · exact .inr ⟨f, g, l, e', .refl _, h1, h2⟩
      · exact .inr ⟨x, y, z, e', .step s h1, h2, h3⟩

/-- **Normal form of a recurrence.**  From a recurrence `t →h* t X⃗` with `|X⃗| ≥ 1` one gets an
exact front return `x z →h* S x y z Y⃗`.  By induction on `t`: strip the last argument while it
is untouched; otherwise rotate to the last root redex. -/
theorem efr_of_recurrence : ∀ {t : Term}, PureS t → ∀ (L : List Term), L ≠ [] →
    Steps t (apps t L) →
    ∃ x y z Ys, PureS (S ⬝ x ⬝ y ⬝ z) ∧ Steps (x ⬝ z) (apps (S ⬝ x ⬝ y ⬝ z) Ys) := by
  intro t ht
  induction ht with
  | S =>
    intro L hL h
    have h1 := sz_lt_apps S hL
    rw [steps_S h] at h1
    exact absurd h1 (Nat.lt_irrefl _)
  | @app e l he hl ihe _ =>
    intro L hL h
    rcases last_root h rfl (.app he hl) with ⟨e', h1, h2⟩ | ⟨x, y, z, e', h1, h2, h3⟩
    · rcases apps_eq_app h1 with ⟨e1, _⟩ | ⟨L₀, _, rfl⟩
      · exact absurd e1 hL
      · exact ihe (l :: L₀) (fun e => nomatch e) h2
    · rcases apps_eq_app h2 with ⟨e1, _⟩ | ⟨L₀, _, rfl⟩
      · exact absurd e1 hL
      · exact ⟨x, y, z, L₀, steps_pure (.app he hl) h1, h3.trans (steps_apps L₀ h1)⟩

/-- The converse construction: an exact front return gives a recurrence of the root redex
`S x y z`, emitting `Y⃗ (y z)`. -/
theorem recurrence_of_efr {x y z : Term} {Ys : List Term}
    (h : Steps (x ⬝ z) (apps (S ⬝ x ⬝ y ⬝ z) Ys)) :
    Plus (S ⬝ x ⬝ y ⬝ z) (apps (S ⬝ x ⬝ y ⬝ z) (Ys ++ [y ⬝ z])) := by
  refine ⟨x ⬝ z ⬝ (y ⬝ z), .S x y z, ?_⟩
  rw [apps_snoc]
  exact Steps.left _ h

theorem app_ne_S3_apps (x y z : Term) (Ys : List Term) : x ⬝ z ≠ apps (S ⬝ x ⬝ y ⬝ z) Ys := by
  intro e
  have h1 := sz_le_apps (S ⬝ x ⬝ y ⬝ z) Ys
  rw [← e] at h1
  have h2 : sz (S ⬝ x ⬝ y ⬝ z) = 1 + sz x + sz y + sz z := rfl
  have h3 : sz (x ⬝ z) = sz x + sz z := rfl
  have := sz_pos y
  omega

theorem ne_apps (t : Term) {L : List Term} (hL : L ≠ []) : t ≠ apps t L := by
  intro e
  have h1 := sz_lt_apps t hL
  rw [← e] at h1
  exact Nat.lt_irrefl _ h1

/-- No head recurrence with at least one emitted argument: no closed S-term `t` and nonempty
`X⃗` with `t →h⁺ t X⃗`. -/
def NHR : Prop := ∀ (t : Term) (L : List Term), PureS t → L ≠ [] → ¬ Plus t (apps t L)

/-- Exact Front Return: no closed `x`, `z` and no `y`, `Y⃗` with `x z →h⁺ S x y z Y⃗`.  (`y` and
`Y⃗` are then closed S-terms as well, being parts of a reduct of `x z`.) -/
def EFR : Prop := ∀ (x y z : Term) (Ys : List Term), PureS x → PureS z →
  ¬ Plus (x ⬝ z) (apps (S ⬝ x ⬝ y ⬝ z) Ys)

/-- **EFR ⟺ NHR(k ≥ 1).** -/
theorem nhr_iff_efr : NHR ↔ EFR := by
  constructor
  · intro hN x y z Ys hx hz hP
    have hp : PureS (S ⬝ x ⬝ y ⬝ z) := pure_apps (steps_pure (.app hx hz) hP.steps)
    exact hN _ (Ys ++ [y ⬝ z]) hp (fun e => by cases Ys <;> cases e)
      (recurrence_of_efr hP.steps)
  · intro hE t L ht hL hP
    obtain ⟨x, y, z, Ys, hp, h⟩ := efr_of_recurrence ht L hL hP.steps
    exact hE x y z Ys hp.app_inv.1.app_inv.1.app_inv.2 hp.app_inv.2
      (plus_of_steps_ne h (app_ne_S3_apps x y z Ys))

/-! ## Self Front Return

`x →h* S x A⃗` with `|A⃗| ≥ 1`.  One argument is `no_fst_self`.  Two or more arguments give, after
one more step, a recurrence of `x` with `|A⃗|` emitted arguments; `sfr_of_efr` derives it from
`EFR`, which is proved unconditionally below (`efr`, from `no_ground_loop`). -/

/-- A self front return with two or more arguments is a head recurrence of `x`. -/
theorem recurrence_of_sfr {x A₁ A₂ : Term} {As : List Term}
    (h : Steps x (apps (S ⬝ x) (A₁ :: A₂ :: As))) :
    Steps x (apps x (A₂ :: (A₁ ⬝ A₂) :: As)) :=
  h.trans (steps_apps As (Steps.single (.S x A₁ A₂)))

/-- Self Front Return, conditional on `EFR` (unconditional for one argument: `no_fst_self`). -/
theorem sfr_of_efr (hE : EFR) {x : Term} (hx : PureS x) {A : List Term} (hA : A ≠ []) :
    ¬ Steps x (apps (S ⬝ x) A) := by
  intro h
  match A, hA, h with
  | [A₁], _, h => exact no_fst_self hx A₁ h
  | A₁ :: A₂ :: As, _, h =>
    have hne : A₂ :: (A₁ ⬝ A₂) :: As ≠ [] := fun e => nomatch e
    exact nhr_iff_efr.mpr hE x (A₂ :: (A₁ ⬝ A₂) :: As) hx hne
      (plus_of_steps_ne (recurrence_of_sfr h) (ne_apps x hne))

/-! ## No ground loops (Waldmann 2000, Thm 8 – Cor. 17), hence no head recurrence

Waldmann's labelling argument.  The *right depth* `rd` of a term is the length of its right
spine.  Label every application node with a number that is at most the right depth of its
argument, and let a redex `S x y ·ₖ z` fire only if `k < N`:

    S x y ·ₖ z  ⟶  (x ·ₖ z) ·ₖ₊₁ (y ·ₖ z).

The labelled system terminates for every `N` (`acc_all`; Waldmann uses a recursive path order,
here it is a direct accessibility induction on `N - k`, then on the function part, then on the
argument).  Labels stay below the right depths (`lift`), so unlabelled weak reduction restricted
to redexes `S f g x` with `rd x < N` terminates (`bsn`).  A ground loop `t →⁺ C[t]` repeats
finitely many redexes forever, inside ever deeper contexts; so there is none (`no_ground_loop`).
A head recurrence `t →h⁺ t X⃗` is a ground loop (`nhr`). -/

/-- Right depth: the length of the right spine. -/
def rd : Term → Nat
  | _ ⬝ x => rd x + 1
  | _ => 0

/-- Pure S-terms with a number on every application node. -/
inductive LT
  | S : LT
  | app : Nat → LT → LT → LT

/-- Erase the labels. -/
def LT.forget : LT → Term
  | .S => Term.S
  | .app _ l r => l.forget ⬝ r.forget

/-- Label every application node with the right depth of its argument. -/
def tag : Term → LT
  | f ⬝ x => .app (rd x) (tag f) (tag x)
  | _ => .S

/-- Every label is at most the right depth of the argument below it. -/
def Cons : LT → Prop
  | .S => True
  | .app k l r => k ≤ rd r.forget ∧ Cons l ∧ Cons r

/-- Labelled weak reduction with bound `N`: a redex fires only if its label is below `N`. -/
inductive LStep (N : Nat) : LT → LT → Prop
  | root {i j k : Nat} {x y z : LT} : k < N →
      LStep N (.app k (.app j (.app i .S x) y) z) (.app (k + 1) (.app k x z) (.app k y z))
  | left {k : Nat} {u u' r : LT} : LStep N u u' → LStep N (.app k u r) (.app k u' r)
  | right {k : Nat} {u r r' : LT} : LStep N r r' → LStep N (.app k u r) (.app k u r')

/-- `Rel N a b`: `a` is a one-step reduct of `b`, a child of `b`, or the argument of `b`'s
function part. -/
inductive Rel (N : Nat) : LT → LT → Prop
  | step {a b : LT} : LStep N b a → Rel N a b
  | fn {k : Nat} {l r : LT} : Rel N l (.app k l r)
  | arg {k : Nat} {l r : LT} : Rel N r (.app k l r)
  | arg2 {i k : Nat} {l x r : LT} : Rel N x (.app k (.app i l x) r)

theorem acc_app_aux {N k : Nat}
    (hroot : ∀ x y r : LT, k < N → Acc (Rel N) (.app k x r) → Acc (Rel N) (.app k y r) →
      Acc (Rel N) (.app (k + 1) (.app k x r) (.app k y r)))
    {u : LT} (hu : Acc (Rel N) u) : ∀ {r : LT}, Acc (Rel N) r → Acc (Rel N) (.app k u r) := by
  induction hu with
  | intro u hu ihu =>
    intro r hr
    induction hr with
    | intro r hr ihr =>
      constructor
      intro a h
      cases h with
      | step s =>
        cases s with
        | root hk => exact hroot _ _ _ hk (ihu _ .arg2 (Acc.intro r hr)) (ihu _ .arg (Acc.intro r hr))
        | left s' => exact ihu _ (.step s') (Acc.intro r hr)
        | right s' => exact ihr _ (.step s')
      | fn => exact Acc.intro u hu
      | arg => exact Acc.intro r hr
      | arg2 => exact hu _ .arg

theorem acc_app (N : Nat) : ∀ (d k : Nat), N ≤ k + d → ∀ {u r : LT},
    Acc (Rel N) u → Acc (Rel N) r → Acc (Rel N) (.app k u r) := by
  intro d
  induction d with
  | zero =>
    intro k hk u r hu hr
    exact acc_app_aux (fun _ _ _ h => absurd h (Nat.not_lt.mpr hk)) hu hr
  | succ d ih =>
    intro k hk u r hu hr
    exact acc_app_aux (fun _ _ _ _ hx hy => ih (k + 1) (by omega) hx hy) hu hr

/-- **The labelled system terminates** (Waldmann 2000, Thm 8), together with the subterm order. -/
theorem acc_all (N : Nat) : ∀ T : LT, Acc (Rel N) T := by
  intro T
  induction T with
  | S =>
    constructor
    intro a h
    cases h with
    | step s => cases s
  | app k l r ihl ihr => exact acc_app N N k (Nat.le_add_left N k) ihl ihr

/-- Weak reduction of pure terms, restricted to redexes `S f g x` with `rd x < N`. -/
inductive BStep (N : Nat) : Term → Term → Prop
  | S (f g x : Term) : rd x < N → BStep N (S ⬝ f ⬝ g ⬝ x) (f ⬝ x ⬝ (g ⬝ x))
  | left {f f' : Term} (x : Term) : BStep N f f' → BStep N (f ⬝ x) (f' ⬝ x)
  | right (f : Term) {x x' : Term} : BStep N x x' → BStep N (f ⬝ x) (f ⬝ x')

/-- Zero or more bounded steps. -/
inductive BSteps (N : Nat) : Term → Term → Prop
  | refl (t : Term) : BSteps N t t
  | step {t t' u : Term} : BStep N t t' → BSteps N t' u → BSteps N t u

theorem BStep.mono {N M : Nat} (h : N ≤ M) {t u : Term} (s : BStep N t u) : BStep M t u := by
  induction s with
  | S f g x hx => exact .S f g x (Nat.lt_of_lt_of_le hx h)
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

theorem BSteps.mono {N M : Nat} (h : N ≤ M) {t u : Term} (s : BSteps N t u) : BSteps M t u := by
  induction s with
  | refl => exact .refl _
  | step s _ ih => exact .step (s.mono h) ih

theorem BStep.weak {N : Nat} {t u : Term} (s : BStep N t u) : WStep t u := by
  induction s with
  | S f g x _ => exact .S f g x
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

/-- Every weak step of a pure term is bounded by some `N`. -/
theorem bstep_of_wstep {t u : Term} (ht : PureS t) (s : WStep t u) : ∃ N, BStep N t u := by
  induction s with
  | S f g x => exact ⟨rd x + 1, .S f g x (Nat.lt_succ_self _)⟩
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih => obtain ⟨N, h⟩ := ih ht.app_inv.1; exact ⟨N, .left x h⟩
  | right f _ ih => obtain ⟨N, h⟩ := ih ht.app_inv.2; exact ⟨N, .right f h⟩

theorem bsteps_of_wsteps {t u : Term} (ht : PureS t) (s : WSteps t u) : ∃ N, BSteps N t u := by
  induction s with
  | refl => exact ⟨0, .refl _⟩
  | step s _ ih =>
    obtain ⟨N, h⟩ := bstep_of_wstep ht s
    obtain ⟨M, hs⟩ := ih (wstep_pure s ht).1
    exact ⟨N + M, .step (h.mono (Nat.le_add_right N M)) (hs.mono (Nat.le_add_left M N))⟩

theorem forget_app_inv {T : LT} {a b : Term} (h : T.forget = a ⬝ b) :
    ∃ k L R, T = .app k L R ∧ L.forget = a ∧ R.forget = b := by
  cases T with
  | S => cases h
  | app k L R =>
    simp only [LT.forget] at h
    injection h with h1 h2
    exact ⟨k, L, R, rfl, h1, h2⟩

theorem forget_S_inv {T : LT} (h : T.forget = Term.S) : T = .S := by
  cases T with
  | S => rfl
  | app k L R => simp only [LT.forget] at h; cases h

theorem forget_tag {t : Term} (ht : PureS t) : (tag t).forget = t := by
  induction ht with
  | S => rfl
  | app _ _ ihf ihx => simp only [tag, LT.forget, ihf, ihx]

theorem cons_tag {t : Term} (ht : PureS t) : Cons (tag t) := by
  induction ht with
  | S => trivial
  | app _ hx ihf ihx =>
    simp only [tag, Cons]
    exact ⟨by rw [forget_tag hx]; exact Nat.le_refl _, ihf, ihx⟩

/-- Reduction never lowers the right depth. -/
theorem rd_bstep {N : Nat} {t u : Term} (s : BStep N t u) : rd t ≤ rd u := by
  induction s with
  | S f g x _ => simp only [rd]; omega
  | left x _ _ => exact Nat.le_refl _
  | right f _ ih => simp only [rd]; omega

/-- A bounded step lifts to any consistent labelling, and consistency is kept
(Waldmann 2000, Prop. 11 and Prop. 15). -/
theorem lift {N : Nat} {t u : Term} (s : BStep N t u) : ∀ {T : LT}, T.forget = t → Cons T →
    ∃ U, LStep N T U ∧ U.forget = u ∧ Cons U := by
  induction s with
  | S f g x hx =>
    intro T hT hc
    obtain ⟨k, T1, X, rfl, h1, hX⟩ := forget_app_inv hT
    obtain ⟨j, T2, G, rfl, h2, hG⟩ := forget_app_inv h1
    obtain ⟨i, T3, F, rfl, h3, hF⟩ := forget_app_inv h2
    cases forget_S_inv h3
    simp only [Cons] at hc
    obtain ⟨hk, ⟨_, ⟨_, _, cF⟩, cG⟩, cX⟩ := hc
    rw [hX] at hk
    refine ⟨.app (k + 1) (.app k F X) (.app k G X), .root (Nat.lt_of_le_of_lt hk hx), ?_, ?_⟩
    · simp only [LT.forget, hF, hG, hX]
    · simp only [Cons, LT.forget, hX, rd]
      exact ⟨Nat.succ_le_succ hk, ⟨hk, cF, cX⟩, hk, cG, cX⟩
  | left x _ ih =>
    intro T hT hc
    obtain ⟨k, L, R, rfl, hL, hR⟩ := forget_app_inv hT
    simp only [Cons] at hc
    obtain ⟨U, sU, eU, cU⟩ := ih hL hc.2.1
    refine ⟨.app k U R, .left sU, by simp only [LT.forget, eU, hR], ?_⟩
    simp only [Cons]
    exact ⟨hc.1, cU, hc.2.2⟩
  | right f s' ih =>
    intro T hT hc
    obtain ⟨k, L, R, rfl, hL, hR⟩ := forget_app_inv hT
    simp only [Cons] at hc
    obtain ⟨U, sU, eU, cU⟩ := ih hR hc.2.2
    refine ⟨.app k L U, .right sU, by simp only [LT.forget, eU, hL], ?_⟩
    simp only [Cons]
    refine ⟨?_, hc.2.1, cU⟩
    rw [eU]
    have h1 := hc.1
    rw [hR] at h1
    exact Nat.le_trans h1 (rd_bstep s')

/-- **Bounded reduction terminates** (Waldmann 2000, Thm 16): for every `N`, weak reduction of
pure S-terms restricted to redexes `S f g x` with `rd x < N` is well founded. -/
theorem bsn (N : Nat) {t : Term} (ht : PureS t) : Acc (fun a b => BStep N b a) t := by
  have key : ∀ T : LT, Acc (Rel N) T → Cons T → Acc (fun a b => BStep N b a) T.forget := by
    intro T hT
    induction hT with
    | intro T _ ih =>
      intro hc
      constructor
      intro w hw
      obtain ⟨U, sU, eU, cU⟩ := lift hw rfl hc
      rw [← eU]
      exact ih U (.step sU) cU
  have h := key (tag t) (acc_all N _) (cons_tag ht)
  rw [forget_tag ht] at h
  exact h

/-- `Sub t w`: `t` occurs in `w` as a subterm. -/
inductive Sub (t : Term) : Term → Prop
  | refl : Sub t t
  | left {f : Term} (x : Term) : Sub t f → Sub t (f ⬝ x)
  | right (f : Term) {x : Term} : Sub t x → Sub t (f ⬝ x)

theorem Sub.trans {a b c : Term} (h1 : Sub a b) (h2 : Sub b c) : Sub a c := by
  induction h2 with
  | refl => exact h1
  | left x _ ih => exact .left x ih
  | right f _ ih => exact .right f ih

theorem BSteps.left {N : Nat} {f f' : Term} (x : Term) (h : BSteps N f f') :
    BSteps N (f ⬝ x) (f' ⬝ x) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.left x s) ih

theorem BSteps.right {N : Nat} (f : Term) {x x' : Term} (h : BSteps N x x') :
    BSteps N (f ⬝ x) (f ⬝ x') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.right f s) ih

/-- A bounded loop `t → t' →* u ∋ t` can be replayed at any occurrence of `t`. -/
theorem sub_replay {N : Nat} {t t' u : Term} (s : BStep N t t') (r : BSteps N t' u)
    (hu : Sub t u) {w : Term} (hw : Sub t w) :
    ∃ w' w'', BStep N w w' ∧ BSteps N w' w'' ∧ Sub t w'' := by
  induction hw with
  | refl => exact ⟨t', u, s, r, hu⟩
  | left x _ ih =>
    obtain ⟨w', w'', s', r', h'⟩ := ih
    exact ⟨w' ⬝ x, w'' ⬝ x, .left x s', r'.left x, .left x h'⟩
  | right f _ ih =>
    obtain ⟨w', w'', s', r', h'⟩ := ih
    exact ⟨f ⬝ w', f ⬝ w'', .right f s', r'.right f, .right f h'⟩

/-- **No ground loops** (Waldmann 2000, Cor. 17): no closed S-term `t` has `t →⁺ C[t]` under
weak reduction (any redex, any context `C`, the empty one included). -/
theorem no_ground_loop {t t' u : Term} (ht : PureS t) (s : WStep t t') (r : WSteps t' u)
    (hu : Sub t u) : False := by
  obtain ⟨N1, s1⟩ := bstep_of_wstep ht s
  obtain ⟨N2, r2⟩ := bsteps_of_wsteps (wstep_pure s ht).1 r
  have sN := s1.mono (Nat.le_add_right N1 N2)
  have rN := r2.mono (Nat.le_add_left N2 N1)
  have key : ∀ w : Term, Acc (fun a b => BStep (N1 + N2) b a) w →
      ∀ w', BSteps (N1 + N2) w w' → Sub t w' → False := by
    intro w hw
    induction hw with
    | intro w _ ih =>
      intro w' hr hs
      cases hr with
      | refl =>
        obtain ⟨w1, w2, s', r', h'⟩ := sub_replay sN rN hu hs
        exact ih w1 s' w2 r' h'
      | step s' r' => exact ih _ s' w' r' hs
  exact key t (bsn (N1 + N2) ht) t (.refl t) .refl

theorem sub_apps (t : Term) (L : List Term) : Sub t (apps t L) := by
  induction L generalizing t with
  | nil => exact .refl
  | cons a L ih => exact Sub.trans (.left a .refl) (ih (t ⬝ a))

/-- **No head recurrence**: no closed S-term `t` has `t →h⁺ t X⃗` (`X⃗` empty or not). -/
theorem no_head_recurrence {t : Term} (ht : PureS t) (L : List Term) : ¬ Plus t (apps t L) := by
  intro ⟨t', s, r⟩
  exact no_ground_loop ht s.weak r.weak (sub_apps t L)

theorem nhr : NHR := fun _ L ht _ => no_head_recurrence ht L

/-- Exact Front Return holds: no `x z →h⁺ S x y z Y⃗`. -/
theorem efr : EFR := nhr_iff_efr.mp nhr

/-- Self Front Return holds: no closed `x` with `x →h* S x A⃗`, `|A⃗| ≥ 1`. -/
theorem sfr {x : Term} (hx : PureS x) {A : List Term} (hA : A ≠ []) :
    ¬ Steps x (apps (S ⬝ x) A) := sfr_of_efr efr hx hA

/-- A reduct of a closed S-term never contains it: `t →⁺ u` implies `t` is not a subterm of `u`.
In particular no head run of `x` mints `x`, puts `x B⃗` at the front, or has `x B⃗` inside an
argument of its head normal form. -/
theorem no_self_subterm {t t' u : Term} (ht : PureS t) (s : Step t t') (r : Steps t' u) :
    ¬ Sub t u := fun h => no_ground_loop ht s.weak r.weak h

end HeadRec
