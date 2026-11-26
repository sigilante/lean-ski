import Ski.InfNF
open Term

/-!
# Tree equality is a congruence on closed S-terms (Lock 1, Theorem C)

`Eqv t u` (written `t ≈ u` in `notes/LOCK1-CONG.md`): `t` and `u` have the same prefixes in the
sense of the `InfNF.NF` relation, `∀ d P, NF d t P ↔ NF d u P`.  Reading this as equality of the
infinitary normal forms `t^∞ = u^∞` uses S3's identification of `NF` prefixes with the strongly
convergent limit, which is not formalized here.

`Cong t t'` with base pairs of different fillers is the many-filler form of the theorem
(`cong_eqv`); `eqv_ctx` is the single-filler corollary.

The note proves Theorem C with open terms and `≈`-substitutions.  Here the simulation runs on
closed terms instead.  `Cong t t'` is the least relation that contains `≈` on pure S-terms and is
closed under application; a pair `(Dσ, Dσ′)` for an open `D` and an `≈`-pair `(σ, σ′)` is a `Cong`
pair (copied variables are copied `base` pairs).

* `factK`: Fact K in NF form (WC.2): if `x ≈ x'` and `x ↠h` an hnf, then `x' ↠h` an hnf of the
  same kind with `≈` items; `eqv_parts`: stable roots of `≈` terms have `≈` parts (WC.3).
* `cong_step`, `cong_steps`: a head step on the left is mirrored by head steps on the right,
  keeping `Cong` (expansions are Fact K; the open head step is the `S` case).
* `cong_fold` (Lemma 1): `Cong t t'` and `t` has an hnf give `t'` has an hnf.
* `cong_split` (Lemma 2): both sides reach `≈` terms, or stable roots `E r`, `E' r'` with `Cong`
  parts.
* `cong_nf` (Theorem C, by induction on `d`), `cong_eqv`, `eqv_app`, `eqv_ctx`.

Every case split on kinds is on the decidable `fold f = 36`; no `Classical.choice`.
-/

namespace Congruence
open HnfS HnfSound TopTerm InfNF

/-- Tree equality: equal `NF` prefixes at every depth.  Meaningful only on pure S-terms (`PureS`):
off `PureS` it collapses (e.g. `Eqv K I` holds, since neither has a prefix beyond depth 0), and
every theorem below that needs it assumes `PureS`. -/
def Eqv (t u : Term) : Prop := ∀ d P, NF d t P ↔ NF d u P

theorem Eqv.refl (t : Term) : Eqv t t := fun _ _ => Iff.rfl

theorem Eqv.symm {t u : Term} (h : Eqv t u) : Eqv u t := fun d P => (h d P).symm

theorem Eqv.trans {t u v : Term} (h1 : Eqv t u) (h2 : Eqv u v) : Eqv t v :=
  fun d P => (h1 d P).trans (h2 d P)

/-- Head reduction does not change the tree. -/
theorem eqv_steps {t s : Term} (ht : PureS t) (h : Steps t s) : Eqv t s := fun _ _ =>
  ⟨fun hP => nf_wsteps ht hP h.weak, fun hP => nf_bwd ht h hP⟩

/-- The prefix at a stable root is the root node of the prefixes of its parts. -/
theorem node_inv {d : Nat} {t f w : Term} {P : PT} (ht : PureS t) (hs : Steps t (f ⬝ w))
    (st : Stable f w) (h : NF (d + 1) t P) :
    ∃ Pf Pw, P = .app Pf Pw ∧ NF d f Pf ∧ NF d w Pw := by
  have hp := steps_pure ht hs
  obtain ⟨Pf, hf⟩ := nf_exists d hp.app_inv.1
  obtain ⟨Pw, hw⟩ := nf_exists d hp.app_inv.2
  exact ⟨Pf, Pw, nf_unique ht h (.node hs st hf hw), hf, hw⟩

theorem parts_dir {t t' f w f' w' : Term} (ht' : PureS t') (h : Eqv t t')
    (hs : Steps t (f ⬝ w)) (st : Stable f w) (hs' : Steps t' (f' ⬝ w')) (st' : Stable f' w')
    {d : Nat} {P Q : PT} (hP : NF d f P) (hQ : NF d w Q) : NF d f' P ∧ NF d w' Q := by
  have := (h (d + 1) _).1 (.node hs st hP hQ)
  obtain ⟨Pf, Pw, e, h1, h2⟩ := node_inv ht' hs' st' this
  injection e with e1 e2
  subst e1 e2
  exact ⟨h1, h2⟩

/-- **WC.3.**  Stable roots on the head paths of `≈` terms have `≈` parts. -/
theorem eqv_parts {t t' f w f' w' : Term} (ht : PureS t) (ht' : PureS t') (h : Eqv t t')
    (hs : Steps t (f ⬝ w)) (st : Stable f w) (hs' : Steps t' (f' ⬝ w')) (st' : Stable f' w') :
    Eqv f f' ∧ Eqv w w' := by
  have hp := steps_pure ht hs
  have hp' := steps_pure ht' hs'
  refine ⟨fun d P => ⟨fun hP => ?_, fun hP => ?_⟩, fun d Q => ⟨fun hQ => ?_, fun hQ => ?_⟩⟩
  · obtain ⟨Q, hQ⟩ := nf_exists d hp.app_inv.2
    exact (parts_dir ht' h hs st hs' st' hP hQ).1
  · obtain ⟨Q, hQ⟩ := nf_exists d hp'.app_inv.2
    exact (parts_dir ht h.symm hs' st' hs st hP hQ).1
  · obtain ⟨P, hP⟩ := nf_exists d hp.app_inv.1
    exact (parts_dir ht' h hs st hs' st' hP hQ).2
  · obtain ⟨P, hP⟩ := nf_exists d hp'.app_inv.1
    exact (parts_dir ht h.symm hs' st' hs st hP hQ).2

/-- `≈` preserves having no hnf (`leftInf_iff`). -/
theorem eqv_bot {t t' : Term} (ht : PureS t) (ht' : PureS t') (h : Eqv t t') (hb : fold t = 36) :
    fold t' = 36 :=
  (leftInf_iff ht').1 (fun d P hP => (leftInf_iff ht).2 hb d P ((h d P).2 hP))

/-! ## Fact K in NF form -/

/-- Number of items of an hnf. -/
def nargs : Term → Nat
  | .app (.app _ _) _ => 2
  | .app _ _ => 1
  | _ => 0

/-- The kind shown by a depth-2 prefix. -/
def ptKind : PT → Nat
  | .S => 0
  | .app .S _ => 1
  | .app (.app _ _) _ => 2
  | _ => 3

/-- The depth-2 prefix of an hnf shows its number of items. -/
theorem nf2_kind {u : Term} {P : PT} (hp : PureS u) (hu : IsHnf u) (h : NF 2 u P) :
    ptKind P = nargs u := by
  rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  · rw [nf_unique hp h (.leaf 1)]; rfl
  · obtain ⟨Pf, Pw, rfl, hf, _⟩ := node_inv hp (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) h
    rw [nf_unique .S hf (.leaf 0)]; rfl
  · obtain ⟨Pf, Pw, rfl, hf, _⟩ := node_inv hp (.refl _) (.inr (.inr (.inr ⟨a, b, rfl⟩))) h
    obtain ⟨Q1, Q2, rfl, _, _⟩ :=
      node_inv hp.app_inv.1 (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩))) hf
    rfl

/-- Two hnfs of the same kind with `≈` items. -/
def HnfMatch (u u' : Term) : Prop :=
  (u = S ∧ u' = S) ∨ (∃ a a', u = S ⬝ a ∧ u' = S ⬝ a' ∧ Eqv a a') ∨
    ∃ a b a' b', u = S ⬝ a ⬝ b ∧ u' = S ⬝ a' ⬝ b' ∧ Eqv a a' ∧ Eqv b b'

/-- **Fact K** (NF form, WC.2).  If `x ≈ x'` and `x ↠h u` with `u` an hnf, then `x' ↠h u'`
with `u'` an hnf of the same kind and `≈` items. -/
theorem factK {x x' u : Term} (hx : PureS x) (hx' : PureS x') (h : Eqv x x') (hs : Steps x u)
    (hu : IsHnf u) : ∃ u', Steps x' u' ∧ HnfMatch u u' := by
  have hup := steps_pure hx hs
  have hb' : fold x' ≠ 36 := fun hb' =>
    fold_hnf hup hu ((steps_fold hx hs).trans (eqv_bot hx' hx h.symm hb'))
  obtain ⟨u', hc, _, hu'⟩ := sound_head x' hx' hb'
  have hs' := headChain_steps hc
  refine ⟨u', hs', ?_⟩
  have hup' := steps_pure hx' hs'
  obtain ⟨P, hP⟩ := nf_exists 2 hx
  have k := (nf2_kind hup hu (nf_wsteps hx hP hs.weak)).symm.trans
    (nf2_kind hup' hu' (nf_wsteps hx' ((h 2 P).1 hP) hs'.weak))
  have ex := (eqv_steps hx hs).symm.trans (h.trans (eqv_steps hx' hs'))
  rcases hu with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩ <;>
    rcases hu' with rfl | ⟨a', rfl⟩ | ⟨a', b', rfl⟩ <;> simp only [nargs] at k <;>
    (try exact absurd k (by decide))
  · exact .inl ⟨rfl, rfl⟩
  · refine .inr (.inl ⟨a, a', rfl, rfl, ?_⟩)
    exact (eqv_parts hup (steps_pure hx' hs') ex (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩)))
      (.refl _) (.inr (.inr (.inl ⟨a', rfl⟩)))).2
  · have e1 := eqv_parts hup hup' ex (.refl _) (.inr (.inr (.inr ⟨a, b, rfl⟩)))
      (.refl _) (.inr (.inr (.inr ⟨a', b', rfl⟩)))
    have e2 := eqv_parts hup.app_inv.1 hup'.app_inv.1 e1.1 (.refl _) (.inr (.inr (.inl ⟨a, rfl⟩)))
      (.refl _) (.inr (.inr (.inl ⟨a', rfl⟩)))
    exact .inr (.inr ⟨a, b, a', b', rfl, rfl, e2.2, e1.2⟩)

/-! ## The congruence closure of `≈` -/

/-- `≈` on pure S-terms, closed under application.  `(Dσ, Dσ′)` for an open `D` and an
`≈`-pair `(σ, σ′)` is a `Cong` pair. -/
inductive Cong : Term → Term → Prop
  | base {t t' : Term} : PureS t → PureS t' → Eqv t t' → Cong t t'
  | app {a a' b b' : Term} : Cong a a' → Cong b b' → Cong (a ⬝ b) (a' ⬝ b')

theorem Cong.pure {t t' : Term} (h : Cong t t') : PureS t ∧ PureS t' := by
  induction h with
  | base h1 h2 _ => exact ⟨h1, h2⟩
  | app _ _ ih1 ih2 => exact ⟨.app ih1.1 ih2.1, .app ih1.2 ih2.2⟩

theorem Cong.symm {t t' : Term} (h : Cong t t') : Cong t' t := by
  induction h with
  | base h1 h2 h => exact .base h2 h1 h.symm
  | app _ _ ih1 ih2 => exact .app ih1 ih2

theorem Cong.S : Cong .S .S := .base .S .S (Eqv.refl _)

theorem cong_S_inv {t' : Term} (h : Cong S t') : t' = S := by
  cases h with
  | base _ _ h =>
    have h1 := (h 1 .S).1 (.leaf 0)
    cases h1 with
    | leaf => rfl

/-- An hnf on the left: the right side head-reduces to an hnf, both `S` or both roots with
`Cong` parts. -/
theorem cong_hnf {u u' : Term} (h : Cong u u') (hu : IsHnf u) :
    ∃ u'', Steps u' u'' ∧ IsHnf u'' ∧ ((u = S ∧ u'' = S) ∨
      ∃ E r E' r', u = E ⬝ r ∧ u'' = E' ⬝ r' ∧ Cong E E' ∧ Cong r r') := by
  cases h with
  | base hp hp' e =>
    obtain ⟨u'', hs, hm⟩ := factK hp hp' e (.refl _) hu
    have hp'' := steps_pure hp' hs
    rcases hm with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ea⟩ | ⟨a, b, a', b', rfl, rfl, ea, eb⟩
    · exact ⟨S, hs, .inl rfl, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hs, .inr (.inl ⟨a', rfl⟩), .inr ⟨S, a, S, a', rfl, rfl, Cong.S,
        .base hp.app_inv.2 hp''.app_inv.2 ea⟩⟩
    · exact ⟨_, hs, .inr (.inr ⟨a', b', rfl⟩), .inr ⟨S ⬝ a, b, S ⬝ a', b', rfl, rfl,
        .app Cong.S (.base hp.app_inv.1.app_inv.2 hp''.app_inv.1.app_inv.2 ea),
        .base hp.app_inv.2 hp''.app_inv.2 eb⟩⟩
  | @app x x' y y' hx hy =>
    rcases hu with e | ⟨a, e⟩ | ⟨a, b, e⟩
    · cases e
    · injection e with e1 e2
      subst e1 e2
      rw [cong_S_inv hx]
      exact ⟨_, .refl _, .inr (.inl ⟨y', rfl⟩), .inr ⟨S, _, S, y', rfl, rfl, Cong.S, hy⟩⟩
    · injection e with e1 e2
      subst e1 e2
      cases hx with
      | base hp hp' e =>
        obtain ⟨u1, hs, hm⟩ := factK hp hp' e (.refl _) (.inr (.inl ⟨a, rfl⟩))
        have hp1 := steps_pure hp' hs
        rcases hm with ⟨h1, _⟩ | ⟨a1, a', h1, rfl, ea⟩ | ⟨_, _, _, _, h1, _⟩
        · cases h1
        · injection h1 with _ h2
          subst h2
          exact ⟨_, Steps.left y' hs, .inr (.inr ⟨a', y', rfl⟩), .inr ⟨_, _, S ⬝ a', y', rfl,
            rfl, .app Cong.S (.base hp.app_inv.2 hp1.app_inv.2 ea), hy⟩⟩
        · cases h1
      | @app p p' q q' hp hq =>
        rw [cong_S_inv hp]
        exact ⟨_, .refl _, .inr (.inr ⟨q', y', rfl⟩), .inr ⟨_, _, S ⬝ q', y', rfl, rfl,
          .app Cong.S hq, hy⟩⟩

/-! ## Simulating head steps -/

/-- **One head step on the left is mirrored by head steps on the right.** -/
theorem cong_step {t t₁ : Term} (s : Step t t₁) : ∀ {t' : Term}, Cong t t' →
    ∃ t'₁, Steps t' t'₁ ∧ Cong t₁ t'₁ := by
  induction s with
  | S f g x =>
    intro t' h
    have hp := h.pure.1
    have hp1 := (HnfS.wstep_pure (Step.S f g x).weak hp).1
    cases h with
    | base _ ht' e =>
      exact ⟨t', .refl _, .base hp1 ht' ((eqv_steps hp (.single (.S f g x))).symm.trans e)⟩
    | @app A A' _ x' hA hx =>
      cases hA with
      | base hA hA' e =>
        obtain ⟨u1, hs, hm⟩ := factK hA hA' e (.refl _) (.inr (.inr ⟨f, g, rfl⟩))
        have hu1 := steps_pure hA' hs
        rcases hm with ⟨h1, _⟩ | ⟨_, _, h1, _⟩ | ⟨a, b, f', g', h1, rfl, ef, eg⟩
        · cases h1
        · injection h1 with h2; cases h2
        · injection h1 with h2 h3; injection h2 with _ h4; subst h3 h4
          exact ⟨_, (Steps.left x' hs).trans (.single (.S f' g' x')),
            .app (.app (.base hA.app_inv.1.app_inv.2 hu1.app_inv.1.app_inv.2 ef) hx)
              (.app (.base hA.app_inv.2 hu1.app_inv.2 eg) hx)⟩
      | @app B B' _ g' hB hg =>
        cases hB with
        | base hB hB' e =>
          obtain ⟨u1, hs, hm⟩ := factK hB hB' e (.refl _) (.inr (.inl ⟨f, rfl⟩))
          have hu1 := steps_pure hB' hs
          rcases hm with ⟨h1, _⟩ | ⟨a, f', h1, rfl, ef⟩ | ⟨_, _, _, _, h1, _⟩
          · cases h1
          · injection h1 with _ h3; subst h3
            exact ⟨_, (Steps.left x' (Steps.left g' hs)).trans (.single (.S f' g' x')),
              .app (.app (.base hB.app_inv.2 hu1.app_inv.2 ef) hx) (.app hg hx)⟩
          · cases h1
        | @app C C' _ f' hC hf =>
          rw [cong_S_inv hC]
          exact ⟨_, .single (.S f' g' x'), .app (.app hf hx) (.app hg hx)⟩
  | K a b =>
    intro t' h
    have hp := h.pure.1
    cases hp with | app h1 _ => cases h1 with | app h2 _ => cases h2
  | I a =>
    intro t' h
    have hp := h.pure.1
    cases hp with | app h1 _ => cases h1
  | @left f f₁ x s ih =>
    intro t' h
    have hp := h.pure.1
    cases h with
    | base _ ht' e =>
      have hp1 := (HnfS.wstep_pure (Step.left x s).weak hp).1
      exact ⟨t', .refl _, .base hp1 ht' ((eqv_steps hp (.single (.left x s))).symm.trans e)⟩
    | @app _ f' _ x' hf hx =>
      obtain ⟨f'₁, hs, hc⟩ := ih hf
      exact ⟨_, Steps.left x' hs, .app hc hx⟩

theorem cong_steps {t s : Term} (hs : Steps t s) : ∀ {t' : Term}, Cong t t' →
    ∃ s', Steps t' s' ∧ Cong s s' := by
  induction hs with
  | refl => intro t' h; exact ⟨t', .refl _, h⟩
  | step s _ ih =>
    intro t' h
    obtain ⟨t'₁, h1, c1⟩ := cong_step s h
    obtain ⟨s', h2, c2⟩ := ih c1
    exact ⟨s', h1.trans h2, c2⟩

/-! ## Lemma 1 and Lemma 2 -/

/-- **Lemma 1.**  Having an hnf transfers along `Cong`. -/
theorem cong_fold {t t' : Term} (h : Cong t t') (hb : fold t ≠ 36) : fold t' ≠ 36 := by
  have ⟨ht, ht'⟩ := h.pure
  obtain ⟨u, hc, _, hu⟩ := sound_head t ht hb
  obtain ⟨s', hs', hc'⟩ := cong_steps (headChain_steps hc) h
  obtain ⟨u'', hs'', hu'', _⟩ := cong_hnf hc' hu
  have hst := hs'.trans hs''
  rw [← steps_fold ht' hst]
  exact fold_hnf (steps_pure ht' hst) hu''

/-- The head path reaches an hnf or a root whose function part has no hnf. -/
theorem head_target {t : Term} (ht : PureS t) :
    ∃ s, Steps t s ∧ (IsHnf s ∨ ∃ f w, s = f ⬝ w ∧ fold f = 36) := by
  induction reach_all ht with
  | hnf hu => exact ⟨_, .refl _, .inl hu⟩
  | @bot f w _ hb => exact ⟨_, .refl _, .inr ⟨f, w, rfl, hb⟩⟩
  | step s _ ih =>
    obtain ⟨u, hs, hu⟩ := ih (HnfS.wstep_pure s.weak ht).1
    exact ⟨u, .step s hs, hu⟩

/-- **Lemma 2.**  Both sides head-reduce to `≈` terms, or to stable roots with `Cong` parts. -/
theorem cong_split {t t' : Term} (h : Cong t t') :
    ∃ s s', Steps t s ∧ Steps t' s' ∧ ((PureS s ∧ PureS s' ∧ Eqv s s') ∨
      ∃ E r E' r', s = E ⬝ r ∧ s' = E' ⬝ r' ∧ Cong E E' ∧ Cong r r' ∧ Stable E r ∧
        Stable E' r') := by
  have ⟨ht, _⟩ := h.pure
  obtain ⟨s, hs, hk⟩ := head_target ht
  obtain ⟨s', hs', hc⟩ := cong_steps hs h
  rcases hk with hu | ⟨f, w, rfl, hb⟩
  · obtain ⟨u'', hs'', hu'', hm⟩ := cong_hnf hc hu
    refine ⟨s, u'', hs, hs'.trans hs'', ?_⟩
    rcases hm with ⟨rfl, rfl⟩ | ⟨E, r, E', r', rfl, rfl, hE, hr⟩
    · exact .inl ⟨.S, .S, Eqv.refl _⟩
    · exact .inr ⟨E, r, E', r', rfl, rfl, hE, hr, .inr hu, .inr hu''⟩
  · refine ⟨_, s', hs, hs', ?_⟩
    cases hc with
    | base h1 h2 e => exact .inl ⟨h1, h2, e⟩
    | @app _ f' _ w' hf hw =>
      have hb' : fold f' = 36 :=
        if hb' : fold f' = 36 then hb' else absurd hb (cong_fold hf.symm hb')
      exact .inr ⟨f, w, f', w', rfl, rfl, hf, hw, .inl hb, .inl hb'⟩

/-! ## Theorem C -/

/-- **Theorem C** (prefix form): `Cong` pairs have the same prefixes. -/
theorem cong_nf : ∀ (d : Nat) {t t' : Term} {P : PT}, Cong t t' → NF d t P → NF d t' P := by
  intro d
  induction d with
  | zero => intro t t' P _ hP; cases hP; exact .zero t'
  | succ d ih =>
    intro t t' P h hP
    have ⟨ht, ht'⟩ := h.pure
    obtain ⟨s, s', hs, hs', hk⟩ := cong_split h
    have hPs := nf_wsteps ht hP hs.weak
    rcases hk with ⟨_, _, e⟩ | ⟨E, r, E', r', rfl, rfl, hE, hr, st, st'⟩
    · exact nf_bwd ht' hs' ((e (d + 1) P).1 hPs)
    · obtain ⟨Pf, Pw, rfl, hf, hw⟩ := node_inv (steps_pure ht hs) (.refl _) st hPs
      exact .node hs' st' (ih hE hf) (ih hr hw)

/-- **Theorem C.**  `≈` contains its congruence closure. -/
theorem cong_eqv {t t' : Term} (h : Cong t t') : Eqv t t' :=
  fun d _ => ⟨cong_nf d h, cong_nf d h.symm⟩

/-- **Theorem C, application form.**  `t ≈ t'` and `u ≈ u'` give `t u ≈ t' u'`. -/
theorem eqv_app {t t' u u' : Term} (ht : PureS t) (ht' : PureS t') (hu : PureS u)
    (hu' : PureS u') (h1 : Eqv t t') (h2 : Eqv u u') : Eqv (t ⬝ u) (t' ⬝ u') :=
  cong_eqv (.app (.base ht ht' h1) (.base hu hu' h2))

/-- Closed contexts over `S`, any number of holes. -/
inductive Ctx
  | hole
  | S
  | app (l r : Ctx)

/-- Fill every hole with `t`. -/
def Ctx.plug : Ctx → Term → Term
  | .hole, t => t
  | .S, _ => .S
  | .app l r, t => (l.plug t) ⬝ (r.plug t)

theorem cong_ctx {t t' : Term} (ht : PureS t) (ht' : PureS t') (h : Eqv t t') :
    ∀ C : Ctx, Cong (C.plug t) (C.plug t')
  | .hole => .base ht ht' h
  | .S => Cong.S
  | .app l r => .app (cong_ctx ht ht' h l) (cong_ctx ht ht' h r)

/-- **Theorem C, context form.**  `t ≈ t'` gives `C[t] ≈ C[t']` for every closed context. -/
theorem eqv_ctx {t t' : Term} (ht : PureS t) (ht' : PureS t') (h : Eqv t t') (C : Ctx) :
    Eqv (C.plug t) (C.plug t') :=
  cong_eqv (cong_ctx ht ht' h C)

end Congruence
