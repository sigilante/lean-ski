import Ski.HeadRec
open Term

/-!
# Theorem H: no loop with one function-position leg (pure S)

An *f-step* is a weak S-step whose contracted redex is not the argument of an application: the
redex is the whole term, or the function part of its parent (`FStep`).  Head steps are f-steps.

**Theorem H** (`theorem_H`).  For a closed S-term `t`: if `t ↠_f u` by f-steps and `t ↠ w` by
weak reduction, and `u` occurs in `w` as a subterm, then `w = u`.  That is, there are no `t`,
`u` and context `C ≠ [ ]` with `t ↠_f u` and `t ↠ C[u]`.

The proof uses the labelled system of `Ski/HeadRec.lean` (Waldmann's labelling: `LT`, `LStep N`,
`tag`, `Cons`, `acc_all`, `lift`) and adds:

* `local_confluent`, `confluent`: for every `N` the labelled `N`-steps are confluent (local
  confluence by cases, no overlaps; then Newman's lemma by induction on `acc_all`);
* `nf_exists`, `nf_unique`: every labelled term has exactly one `N`-normal form;
* `lsz_lstep`: a labelled step never lowers the leaf count;
* `fstep_tag`: an f-step `t → t'` is a labelled step `tag t → tag t'`, exactly, where `tag`
  labels every application with the right depth of its argument;
* `le_sim`: labelled steps are monotone in the labels (`Le`, pointwise `≤`);
* `h_core`: the labelled form of the theorem.

Everything is constructive (axiom gate: `propext`, `Quot.sound` only).

Corollaries: `no_head_reduct_inside` (no term reduces to a term that properly contains one of
its head reducts), `no_proper_ground_loop` (the case `u = t`: the part `C ≠ [ ]` of
`no_ground_loop`, here without `bsn`), `nhr_of_theorem_H` (`NHR` again).
-/

namespace HeadRec
open HnfS

/-! ## f-steps -/

/-- `IStep t t'`: `t → t'` contracts one S-redex occurrence that is the function part of its
parent application (at any depth in `t`).  In particular the redex is not `t` itself. -/
inductive IStep : Term → Term → Prop
  | fn (f g x a : Term) : IStep (S ⬝ f ⬝ g ⬝ x ⬝ a) (f ⬝ x ⬝ (g ⬝ x) ⬝ a)
  | left {f f' : Term} (a : Term) : IStep f f' → IStep (f ⬝ a) (f' ⬝ a)
  | right (f : Term) {x x' : Term} : IStep x x' → IStep (f ⬝ x) (f ⬝ x')

/-- An *f-step*: `t → t'` contracts one S-redex occurrence that is not the argument of an
application.  Either the redex is the whole term (`root`), or it is the function part of its
parent (`inner`, see `IStep`).  Only S-redexes are contracted; on pure S-terms the weak steps
left out are exactly those whose redex occurrence is the argument child of its parent. -/
inductive FStep : Term → Term → Prop
  | root (f g x : Term) : FStep (S ⬝ f ⬝ g ⬝ x) (f ⬝ x ⬝ (g ⬝ x))
  | inner {t t' : Term} : IStep t t' → FStep t t'

/-- Zero or more f-steps. -/
inductive FSteps : Term → Term → Prop
  | refl (t : Term) : FSteps t t
  | step {t t' u : Term} : FStep t t' → FSteps t' u → FSteps t u

theorem IStep.weak {t u : Term} (s : IStep t u) : WStep t u := by
  induction s with
  | fn f g x a => exact .left a (.S f g x)
  | left a _ ih => exact .left a ih
  | right f _ ih => exact .right f ih

/-- An f-step is a weak step. -/
theorem FStep.weak {t u : Term} (s : FStep t u) : WStep t u := by
  cases s with
  | root f g x => exact .S f g x
  | inner s => exact s.weak

theorem FSteps.weak {t u : Term} (s : FSteps t u) : WSteps t u := by
  induction s with
  | refl => exact .refl _
  | step s _ ih => exact .step s.weak ih

/-- An f-step of the function part is an f-step of the application. -/
theorem FStep.left {f f' : Term} (a : Term) (s : FStep f f') : FStep (f ⬝ a) (f' ⬝ a) := by
  cases s with
  | root f g x => exact .inner (.fn f g x a)
  | inner s => exact .inner (.left a s)

/-- A head step of a closed S-term is an f-step. -/
theorem fstep_of_step {t t' : Term} (ht : PureS t) (s : Step t t') : FStep t t' := by
  induction s with
  | S f g x => exact .root f g x
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih => exact (ih ht.app_inv.1).left x

/-- A head reduction of a closed S-term is a sequence of f-steps. -/
theorem fsteps_of_steps {t u : Term} (ht : PureS t) (s : Steps t u) : FSteps t u := by
  induction s with
  | refl => exact .refl _
  | step s _ ih => exact .step (fstep_of_step ht s) (ih (wstep_pure s.weak ht).1)

/-! ## Labelled reduction sequences and leaf count -/

/-- Leaf count of a labelled term. -/
def lsz : LT → Nat
  | .S => 1
  | .app _ l r => lsz l + lsz r

theorem lsz_pos : ∀ T : LT, 0 < lsz T
  | .S => Nat.lt_succ_self 0
  | .app _ l _ => Nat.lt_of_lt_of_le (lsz_pos l) (Nat.le_add_right _ _)

/-- Zero or more labelled steps with bound `N`. -/
inductive LSteps (N : Nat) : LT → LT → Prop
  | refl (T : LT) : LSteps N T T
  | step {T T' U : LT} : LStep N T T' → LSteps N T' U → LSteps N T U

theorem LSteps.single {N : Nat} {T U : LT} (s : LStep N T U) : LSteps N T U := .step s (.refl U)

theorem LSteps.trans {N : Nat} {T U V : LT} (h₁ : LSteps N T U) (h₂ : LSteps N U V) :
    LSteps N T V := by
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact .step s (ih h₂)

theorem LSteps.left {N k : Nat} {u u' : LT} (r : LT) (h : LSteps N u u') :
    LSteps N (.app k u r) (.app k u' r) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.left s) ih

theorem LSteps.right {N k : Nat} (u : LT) {r r' : LT} (h : LSteps N r r') :
    LSteps N (.app k u r) (.app k u r') := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.right s) ih

theorem LStep.mono {N M : Nat} (h : N ≤ M) {T U : LT} (s : LStep N T U) : LStep M T U := by
  induction s with
  | root hk => exact .root (Nat.lt_of_lt_of_le hk h)
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem LSteps.mono {N M : Nat} (h : N ≤ M) {T U : LT} (s : LSteps N T U) : LSteps M T U := by
  induction s with
  | refl => exact .refl _
  | step s _ ih => exact .step (s.mono h) ih

/-- A labelled step never lowers the leaf count. -/
theorem lsz_lstep {N : Nat} {T U : LT} (s : LStep N T U) : lsz T ≤ lsz U := by
  induction s with
  | @root i j k x y z _ =>
    have hz := lsz_pos z
    show 1 + lsz x + lsz y + lsz z ≤ lsz x + lsz z + (lsz y + lsz z)
    omega
  | @left k u u' r _ ih =>
    show lsz u + lsz r ≤ lsz u' + lsz r
    omega
  | @right k u r r' _ ih =>
    show lsz u + lsz r ≤ lsz u + lsz r'
    omega

theorem lsz_lsteps {N : Nat} {T U : LT} (s : LSteps N T U) : lsz T ≤ lsz U := by
  induction s with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans (lsz_lstep s) ih

/-! ## Normal forms -/

/-- `T` has no labelled step with bound `N`. -/
def Normal (N : Nat) (T : LT) : Prop := ∀ U, ¬ LStep N T U

theorem s2_dec : ∀ l : LT, (∃ i j x y, l = .app j (.app i .S x) y) ∨
    (∀ i j x y, l ≠ .app j (.app i .S x) y)
  | .S => .inr (fun _ _ _ _ h => by cases h)
  | .app _ .S _ => .inr (fun _ _ _ _ h => by cases h)
  | .app j (.app i .S x) y => .inl ⟨i, j, x, y, rfl⟩
  | .app _ (.app _ (.app _ _ _) _) _ => .inr (fun _ _ _ _ h => by cases h)

/-- Whether a labelled term has a step is decidable. -/
theorem lstep_dec (N : Nat) : ∀ T : LT, (∃ U, LStep N T U) ∨ Normal N T := by
  intro T
  induction T with
  | S => exact .inr (fun U s => by cases s)
  | app k l r ihl ihr =>
    rcases ihl with ⟨l', sl⟩ | hl
    · exact .inl ⟨_, .left sl⟩
    · rcases ihr with ⟨r', sr⟩ | hr
      · exact .inl ⟨_, .right sr⟩
      · rcases Nat.lt_or_ge k N with hk | hk
        · rcases s2_dec l with ⟨i, j, x, y, rfl⟩ | hs
          · exact .inl ⟨_, .root hk⟩
          · refine .inr (fun U s => ?_)
            cases s with
            | root _ => exact hs _ _ _ _ rfl
            | left s' => exact hl _ s'
            | right s' => exact hr _ s'
        · refine .inr (fun U s => ?_)
          cases s with
          | root h => exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hk)
          | left s' => exact hl _ s'
          | right s' => exact hr _ s'

/-- Every labelled term reduces to an `N`-normal form. -/
theorem nf_exists (N : Nat) (T : LT) : ∃ V, LSteps N T V ∧ Normal N V := by
  have h := acc_all N T
  induction h with
  | intro T _ ih =>
    rcases lstep_dec N T with ⟨U, s⟩ | hn
    · obtain ⟨V, r, hV⟩ := ih U (.step s)
      exact ⟨V, .step s r, hV⟩
    · exact ⟨T, .refl T, hn⟩

theorem Normal.steps_eq {N : Nat} {V D : LT} (hV : Normal N V) (r : LSteps N V D) : D = V := by
  cases r with
  | refl => rfl
  | step s _ => exact absurd s (hV _)

/-! ## Confluence -/

/-- A root step joins with any other step from the same term (the rule is left-linear and has
no overlaps: the function part `S x y` of a redex contains no redex at or above `x`, `y`). -/
theorem root_join {N i j k : Nat} {x y z B : LT} (hk : k < N)
    (s : LStep N (.app k (.app j (.app i .S x) y) z) B) :
    ∃ D, LSteps N (.app (k + 1) (.app k x z) (.app k y z)) D ∧ LSteps N B D := by
  cases s with
  | root _ => exact ⟨_, .refl _, .refl _⟩
  | left s1 =>
    cases s1 with
    | left s2 =>
      cases s2 with
      | left s3 => cases s3
      | right s3 => exact ⟨_, .single (.left (.left s3)), .single (.root hk)⟩
    | right s2 => exact ⟨_, .single (.right (.left s2)), .single (.root hk)⟩
  | right s1 =>
    exact ⟨_, .step (.left (.right s1)) (.single (.right (.right s1))), .single (.root hk)⟩

/-- Labelled steps are locally confluent. -/
theorem local_confluent {N : Nat} {T A : LT} (s1 : LStep N T A) :
    ∀ {B : LT}, LStep N T B → ∃ D, LSteps N A D ∧ LSteps N B D := by
  induction s1 with
  | root hk => intro B s2; exact root_join hk s2
  | @left k u u' r s ih =>
    intro B s2
    cases s2 with
    | root hk =>
      obtain ⟨D, h1, h2⟩ := root_join hk (.left s)
      exact ⟨D, h2, h1⟩
    | left s' =>
      obtain ⟨D, h1, h2⟩ := ih s'
      exact ⟨.app k D r, h1.left r, h2.left r⟩
    | right s' => exact ⟨_, .single (.right s'), .single (.left s)⟩
  | @right k u r r' s ih =>
    intro B s2
    cases s2 with
    | root hk =>
      obtain ⟨D, h1, h2⟩ := root_join hk (.right s)
      exact ⟨D, h2, h1⟩
    | left s' => exact ⟨_, .single (.left s'), .single (.right s)⟩
    | right s' =>
      obtain ⟨D, h1, h2⟩ := ih s'
      exact ⟨.app k u D, h1.right u, h2.right u⟩

/-- **Labelled reduction is confluent**, for every bound `N` (Newman's lemma, by induction on
the accessibility `acc_all` of the labelled system). -/
theorem confluent (N : Nat) {T : LT} : ∀ {A B : LT}, LSteps N T A → LSteps N T B →
    ∃ D, LSteps N A D ∧ LSteps N B D := by
  have h := acc_all N T
  induction h with
  | intro T _ ih =>
    intro A B rA rB
    cases rA with
    | refl => exact ⟨B, rB, .refl B⟩
    | step s1 r1 =>
      cases rB with
      | refl => exact ⟨A, .refl A, .step s1 r1⟩
      | step s2 r2 =>
        obtain ⟨D0, d1, d2⟩ := local_confluent s1 s2
        obtain ⟨E1, e1, e2⟩ := ih _ (.step s1) r1 d1
        obtain ⟨E2, f1, f2⟩ := ih _ (.step s2) r2 (d2.trans e2)
        exact ⟨E2, e1.trans f2, f1⟩

/-- Normal forms are unique. -/
theorem nf_unique {N : Nat} {T V V' : LT} (r : LSteps N T V) (hV : Normal N V)
    (r' : LSteps N T V') (hV' : Normal N V') : V = V' := by
  obtain ⟨D, d1, d2⟩ := confluent N r r'
  exact (hV.steps_eq d1).symm.trans (hV'.steps_eq d2)

/-! ## Monotonicity in the labels -/

/-- `Le T T'`: `T` and `T'` label the same term, and every label of `T` is at most the
corresponding label of `T'`. -/
inductive Le : LT → LT → Prop
  | S : Le .S .S
  | app {k k' : Nat} {l l' r r' : LT} : k ≤ k' → Le l l' → Le r r' →
      Le (.app k l r) (.app k' l' r')

theorem Le.lsz_eq {T T' : LT} (h : Le T T') : lsz T = lsz T' := by
  induction h with
  | S => rfl
  | @app k k' l l' r r' _ _ _ ihl ihr =>
    show lsz l + lsz r = lsz l' + lsz r'
    rw [ihl, ihr]

/-- A step of the larger labelling is matched, at the same redex, by a step of the smaller. -/
theorem le_sim {N : Nat} {T' U' : LT} (s : LStep N T' U') :
    ∀ {T : LT}, Le T T' → ∃ U, LStep N T U ∧ Le U U' := by
  induction s with
  | root hk =>
    intro T h
    cases h with
    | app hk' h1 hz =>
      cases h1 with
      | app _ h2 hy =>
        cases h2 with
        | app _ h3 hx =>
          cases h3
          exact ⟨_, .root (Nat.lt_of_le_of_lt hk' hk),
            .app (Nat.succ_le_succ hk') (.app hk' hx hz) (.app hk' hy hz)⟩
  | left _ ih =>
    intro T h
    cases h with
    | app hk hl hr =>
      obtain ⟨U, sU, hU⟩ := ih hl
      exact ⟨_, .left sU, .app hk hU hr⟩
  | right _ ih =>
    intro T h
    cases h with
    | app hk hl hr =>
      obtain ⟨U, sU, hU⟩ := ih hr
      exact ⟨_, .right sU, .app hk hl hU⟩

theorem le_sims {N : Nat} {T' U' : LT} (s : LSteps N T' U') :
    ∀ {T : LT}, Le T T' → ∃ U, LSteps N T U ∧ Le U U' := by
  induction s with
  | refl => intro T h; exact ⟨T, .refl T, h⟩
  | step s _ ih =>
    intro T h
    obtain ⟨U, sU, hU⟩ := le_sim s h
    obtain ⟨V, rV, hV⟩ := ih hU
    exact ⟨V, .step sU rV, hV⟩

/-- A consistent labelling is pointwise below the right-depth labelling of the same term. -/
theorem cons_le_tag {R : LT} : Cons R → Le R (tag R.forget) := by
  induction R with
  | S => intro _; exact .S
  | app k l r ihl ihr =>
    intro h
    simp only [Cons] at h
    show Le (.app k l r) (.app (rd r.forget) (tag l.forget) (tag r.forget))
    exact .app h.1 (ihl h.2.1) (ihr h.2.2)

/-! ## f-steps are labelled steps between right-depth labellings -/

/-- A step at a function position does not change the right depth. -/
theorem rd_istep {t t' : Term} (s : IStep t t') : rd t = rd t' := by
  induction s with
  | fn f g x a => rfl
  | left a _ _ => rfl
  | @right f x x' _ ih =>
    show rd x + 1 = rd x' + 1
    rw [ih]

theorem istep_tag {t t' : Term} (s : IStep t t') : ∃ N, LStep N (tag t) (tag t') := by
  induction s with
  | fn f g x a =>
    refine ⟨rd x + 1, ?_⟩
    show LStep (rd x + 1)
      (.app (rd a) (.app (rd x) (.app (rd g) (.app (rd f) .S (tag f)) (tag g)) (tag x)) (tag a))
      (.app (rd a) (.app (rd x + 1) (.app (rd x) (tag f) (tag x)) (.app (rd x) (tag g) (tag x)))
        (tag a))
    exact .left (.root (Nat.lt_succ_self _))
  | @left f f' a _ ih =>
    obtain ⟨N, h⟩ := ih
    refine ⟨N, ?_⟩
    show LStep N (.app (rd a) (tag f) (tag a)) (.app (rd a) (tag f') (tag a))
    exact .left h
  | @right f x x' s ih =>
    obtain ⟨N, h⟩ := ih
    refine ⟨N, ?_⟩
    show LStep N (.app (rd x) (tag f) (tag x)) (.app (rd x') (tag f) (tag x'))
    rw [← rd_istep s]
    exact .right h

/-- **An f-step lifts exactly**: if `t → t'` is an f-step then `tag t → tag t'` is a labelled
step (for some bound `N`, hence for every larger one by `LStep.mono`), where `tag` labels each
application with the right depth of its argument.  (`tag` reads every leaf as `S`; no purity
hypothesis is needed.) -/
theorem fstep_tag {t t' : Term} (s : FStep t t') : ∃ N, LStep N (tag t) (tag t') := by
  cases s with
  | root f g x =>
    refine ⟨rd x + 1, ?_⟩
    show LStep (rd x + 1)
      (.app (rd x) (.app (rd g) (.app (rd f) .S (tag f)) (tag g)) (tag x))
      (.app (rd x + 1) (.app (rd x) (tag f) (tag x)) (.app (rd x) (tag g) (tag x)))
    exact .root (Nat.lt_succ_self _)
  | inner s => exact istep_tag s

theorem fsteps_tag {t u : Term} (s : FSteps t u) : ∃ N, LSteps N (tag t) (tag u) := by
  induction s with
  | refl => exact ⟨0, .refl _⟩
  | step s _ ih =>
    obtain ⟨N, h⟩ := fstep_tag s
    obtain ⟨M, hs⟩ := ih
    exact ⟨N + M, .step (h.mono (Nat.le_add_right N M)) (hs.mono (Nat.le_add_left M N))⟩

/-! ## Lifting the unrestricted leg -/

/-- A bounded reduction lifts to any consistent labelling, and ends in a consistent one. -/
theorem lifts {N : Nat} {t w : Term} (s : BSteps N t w) : ∀ {T : LT}, T.forget = t → Cons T →
    ∃ W, LSteps N T W ∧ W.forget = w ∧ Cons W := by
  induction s with
  | refl => intro T hT hc; exact ⟨T, .refl T, hT, hc⟩
  | step s _ ih =>
    intro T hT hc
    obtain ⟨U, sU, eU, cU⟩ := lift s hT hc
    obtain ⟨W, rW, eW, cW⟩ := ih eU cU
    exact ⟨W, .step sU rW, eW, cW⟩

/-- An occurrence of `u` in `w` gives, in any consistent labelling `W` of `w`, a consistent
labelling `R` of `u` every reduct `R'` of which sits inside a reduct of `W`. -/
theorem sub_lift {N : Nat} {u w : Term} (hs : Sub u w) : ∀ {W : LT}, W.forget = w → Cons W →
    ∃ R, R.forget = u ∧ Cons R ∧
      ∀ R', LSteps N R R' → ∃ W', LSteps N W W' ∧ lsz R' ≤ lsz W' := by
  induction hs with
  | refl => intro W hW hc; exact ⟨W, hW, hc, fun R' r => ⟨R', r, Nat.le_refl _⟩⟩
  | left x _ ih =>
    intro W hW hc
    obtain ⟨k, L, X, rfl, hL, hX⟩ := forget_app_inv hW
    simp only [Cons] at hc
    obtain ⟨R, eR, cR, hR⟩ := ih hL hc.2.1
    refine ⟨R, eR, cR, fun R' r => ?_⟩
    obtain ⟨L', rL, hle⟩ := hR R' r
    refine ⟨.app k L' X, rL.left X, ?_⟩
    show lsz R' ≤ lsz L' + lsz X
    omega
  | right f _ ih =>
    intro W hW hc
    obtain ⟨k, L, X, rfl, hL, hX⟩ := forget_app_inv hW
    simp only [Cons] at hc
    obtain ⟨R, eR, cR, hR⟩ := ih hX hc.2.2
    refine ⟨R, eR, cR, fun R' r => ?_⟩
    obtain ⟨X', rX, hle⟩ := hR R' r
    refine ⟨.app k L X', rX.right L, ?_⟩
    show lsz R' ≤ lsz L + lsz X'
    omega

/-! ## Theorem H -/

/-- The labelled core of Theorem H.  If `A` reduces to `Tu` and to `W`, `R` is pointwise below
`Tu`, and every reduct `R'` of `R` is strictly smaller than some reduct of `W` (as when `R`
is a proper subterm of `W`), there is a contradiction: the normal form of `A` would have more
leaves than itself. -/
theorem h_core {N : Nat} {A Tu W R : LT} (h1 : LSteps N A Tu) (h2 : LSteps N A W)
    (hle : Le R Tu)
    (hctx : ∀ R', LSteps N R R' → ∃ W', LSteps N W W' ∧ lsz R' < lsz W') : False := by
  obtain ⟨V, rV, nV⟩ := nf_exists N Tu
  obtain ⟨V0, r0, le0⟩ := le_sims rV hle
  obtain ⟨W', rW, hlt⟩ := hctx V0 r0
  obtain ⟨V', rV', nV'⟩ := nf_exists N W'
  have e : V = V' := nf_unique (h1.trans rV) nV (h2.trans (rW.trans rV')) nV'
  have b := lsz_lsteps rV'
  rw [← e] at b
  rw [le0.lsz_eq] at hlt
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt b)

/-- **Theorem H.**  Let `t` be a closed S-term.  If `t ↠_f u` by f-steps (`FSteps`: no
contracted redex is the argument of an application), `t ↠ w` by weak reduction (`WSteps`), and
`u` occurs in `w` as a subterm (`Sub u w`), then `w = u`.  Equivalently: there are no `t`, `u`
and one-hole context `C ≠ [ ]` with `t ↠_f u` and `t ↠ C[u]`. -/
theorem theorem_H {t u w : Term} (ht : PureS t) (hf : FSteps t u) (hw : WSteps t w)
    (hs : Sub u w) : w = u := by
  obtain ⟨N1, l1⟩ := fsteps_tag hf
  obtain ⟨N2, b2⟩ := bsteps_of_wsteps ht hw
  obtain ⟨W, l2, eW, cW⟩ := lifts b2 (forget_tag ht) (cons_tag ht)
  have l1' := l1.mono (Nat.le_add_right N1 N2)
  have l2' := l2.mono (Nat.le_add_left N2 N1)
  cases hs with
  | refl => rfl
  | left x hs' =>
    exfalso
    obtain ⟨k, L, X, rfl, hL, hX⟩ := forget_app_inv eW
    simp only [Cons] at cW
    obtain ⟨R, eR, cR, hR⟩ := sub_lift (N := N1 + N2) hs' hL cW.2.1
    have hle : Le R (tag u) := by
      have h := cons_le_tag cR
      rw [eR] at h
      exact h
    refine h_core l1' l2' hle (fun R' r => ?_)
    obtain ⟨L', rL, hl⟩ := hR R' r
    refine ⟨.app k L' X, rL.left X, ?_⟩
    have hp := lsz_pos X
    show lsz R' < lsz L' + lsz X
    omega
  | right f hs' =>
    exfalso
    obtain ⟨k, L, X, rfl, hL, hX⟩ := forget_app_inv eW
    simp only [Cons] at cW
    obtain ⟨R, eR, cR, hR⟩ := sub_lift (N := N1 + N2) hs' hX cW.2.2
    have hle : Le R (tag u) := by
      have h := cons_le_tag cR
      rw [eR] at h
      exact h
    refine h_core l1' l2' hle (fun R' r => ?_)
    obtain ⟨X', rX, hl⟩ := hR R' r
    refine ⟨.app k L X', rX.right L, ?_⟩
    have hp := lsz_pos L
    show lsz R' < lsz L + lsz X'
    omega

/-- Theorem H in negative form: no `t ↠_f u` and `t ↠ w` with `u` a proper subterm of `w`. -/
theorem no_f_loop {t u w : Term} (ht : PureS t) (hf : FSteps t u) (hw : WSteps t w)
    (hs : Sub u w) (hne : w ≠ u) : False := hne (theorem_H ht hf hw hs)

/-- (H1) No closed S-term reduces to a term that properly contains one of its head reducts:
`t →h* u`, `t ↠ w` and `u` a subterm of `w` force `w = u`. -/
theorem no_head_reduct_inside {t u w : Term} (ht : PureS t) (h : Steps t u) (hw : WSteps t w)
    (hs : Sub u w) : w = u := theorem_H ht (fsteps_of_steps ht h) hw hs

/-- Theorem H with `u = t`: if a closed S-term `t` reduces to `w` and `t` occurs in `w`,
then `w = t`.  This is the part `C ≠ [ ]` of `no_ground_loop`
(which also excludes `t →⁺ t`), proved here from confluence instead of `bsn`. -/
theorem no_proper_ground_loop {t w : Term} (ht : PureS t) (hw : WSteps t w) (hs : Sub t w) :
    w = t := theorem_H ht (.refl t) hw hs

/-- `NHR` (no head recurrence `t →h⁺ t X⃗` with `X⃗` nonempty) from Theorem H; `nhr` proves the
same statement from `no_ground_loop`. -/
theorem nhr_of_theorem_H : NHR := fun t L ht hL h =>
  ne_apps t hL (no_proper_ground_loop ht h.steps.weak (sub_apps t L)).symm

end HeadRec
