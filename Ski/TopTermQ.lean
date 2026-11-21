import Ski.TopTermFin
open Term

/-!
# Waldmann §7.5: from `Q Q Q`, boundedly many root steps

`Qt t`: `t` is not a right comb (Waldmann's `Q`), read off its block.  `QQ t`: `t` is an
application of two `Q`-terms.  The lemmas follow Waldmann's thesis (1998), §7.5, in block
language; each "finitely often" there is a structural induction here.

* `fin_rc`  (7.5.3): a right comb `W` in front of two `QQ`-terms and a `Q`-term;
* `fin_q2`  (7.5.4): `W B C D` with `W ∉ {S, S S}` and `B, C, D ∈ Q`;
* `fin_R1`, `fin_R2` (7.5.5): the hnf `S h₁ h₂` in Waldmann's set `R`;
* `fin_qqq_qq` (7.5.7): `X E F` with `X ∈ Q` and `E, F ∈ QQ`;
* `fin_T` (7.5.9, its `T` case) and `fin_hnf2`: any hnf `S h₁ h₂` in front of two `Q`-terms;
* `fin_qqq` (7.5.10): `A B C` with `A, B, C ∈ Q`.
-/

namespace TopTerm
open HnfS HnfSound HnfB0

def Qt (t : Term) : Prop := qB (fold t) = true

/-- Decidable through `qB` (without this instance, `if` on `Qt` would fall back to classical
decidability). -/
instance (t : Term) : Decidable (Qt t) := inferInstanceAs (Decidable (qB (fold t) = true))

def QQ (t : Term) : Prop := ∃ a b, t = a ⬝ b ∧ PureS a ∧ PureS b ∧ Qt a ∧ Qt b

theorem qt_S : ¬ Qt S := by
  intro h
  have h0 : qB (fold S) = false := by decide
  unfold Qt at h; rw [h0] at h; cases h

theorem ne_S_of_qt {t : Term} (h : Qt t) : t ≠ S := fun e => qt_S (e ▸ h)

theorem qt_app_ne {a b : Term} (ha : PureS a) (hb : PureS b) (h : a ≠ S) : Qt (a ⬝ b) := by
  have hq := q_app (fold_lt ha) (fold_lt hb)
  have h0 : fold a ≠ 0 := fun e => h (fold_eq_zero ha e)
  show qB (β (fold a) (fold b)) = true
  rw [hq]
  have : (fold a != 0) = true := bne_iff_ne.mpr h0
  rw [this]; rfl

theorem qt_app_right {a b : Term} (ha : PureS a) (hb : PureS b) (h : Qt b) : Qt (a ⬝ b) := by
  have hq := q_app (fold_lt ha) (fold_lt hb)
  show qB (β (fold a) (fold b)) = true
  rw [hq, show qB (fold b) = true from h, Bool.or_true]

theorem qt_app_left {a b : Term} (ha : PureS a) (hb : PureS b) (h : Qt a) : Qt (a ⬝ b) :=
  qt_app_ne ha hb (ne_S_of_qt h)

theorem qt_of_S_app {h : Term} (hh : PureS h) (q : Qt (S ⬝ h)) : Qt h := by
  have hq : qB (β 0 (fold h)) = ((0 : Nat) != 0 || qB (fold h)) := q_app (by decide) (fold_lt hh)
  have q' : qB (β 0 (fold h)) = true := q
  rw [hq] at q'
  exact q'

theorem qq_qt {t : Term} (h : QQ t) : Qt t := by
  obtain ⟨a, b, rfl, ha, hb, qa, _⟩ := h
  exact qt_app_left ha hb qa

theorem qq_pure {t : Term} (h : QQ t) : PureS t := by
  obtain ⟨a, b, rfl, ha, hb, _, _⟩ := h
  exact .app ha hb

theorem qq_mk {a b : Term} (ha : PureS a) (hb : PureS b) (qa : Qt a) (qb : Qt b) : QQ (a ⬝ b) :=
  ⟨a, b, rfl, ha, hb, qa, qb⟩

/-- Right combs `S`, `S S`, `S (S S)`, … -/
inductive RC : Term → Prop
  | S : RC S
  | app {w : Term} : RC w → RC (S ⬝ w)

theorem RC.pure : ∀ {w : Term}, RC w → PureS w
  | _, .S => .S
  | _, .app h => .app .S h.pure

/-- A term that is not in `Q` is a right comb. -/
theorem rc_of_not_qt : ∀ {t : Term}, PureS t → ¬ Qt t → RC t := by
  intro t ht
  induction ht with
  | S => intro _; exact .S
  | @app f x hf hx _ ihx =>
    intro hq
    if hfS : f = S then
      subst hfS
      exact .app (ihx fun q => hq (qt_app_right .S hx q))
    else exact absurd (qt_app_ne hf hx hfS) hq

/-! ## Head steps used below -/

theorem fin_qqq_app {A B C D : Term} (hA : PureS A) (hB : PureS B) (hC : PureS C)
    (qa : Qt A) (qb : Qt B) (qc : Qt C) : Fin (A ⬝ B ⬝ C ⬝ D) :=
  fin_of_bot_fun (.app (.app hA hB) hC) (qqq_bot hA hB hC qa qb qc)

/-- A `QQ`-term in front of two `Q`-terms: its function part has no hnf. -/
theorem fin_qq_head {V E F : Term} (hV : QQ V) (hE : PureS E) (qe : Qt E) : Fin (V ⬝ E ⬝ F) := by
  obtain ⟨a, b, rfl, ha, hb, qa, qb⟩ := hV
  exact fin_qqq_app ha hb hE qa qb qe

theorem fin_bot_head {X B C : Term} (hX : PureS X) (hB : PureS B) (hb : fold X = 36) :
    Fin (X ⬝ B ⬝ C) :=
  fin_of_bot_fun (.app hX hB) (by show β (fold X) (fold B) = 36; rw [hb]; exact absorb (fold_lt hB))

/-! ## 7.5.3, 7.5.4 -/

/-- 7.5.3: a right comb in front of two `QQ`-terms and a `Q`-term. -/
theorem fin_rc : ∀ {W : Term}, RC W → ∀ {B C D : Term}, QQ B → QQ C → PureS D → Qt D →
    Fin (W ⬝ B ⬝ C ⬝ D) := by
  intro W hW
  induction hW with
  | S =>
    intro B C D hB hC hD qd
    refine fin_of_step (.S B C D) ?_
    exact fin_qq_head hB hD qd
  | @app w hw ih =>
    intro B C D hB hC hD qd
    refine fin_of_step (.left D (.S w B C)) ?_
    exact ih hC (qq_mk (qq_pure hB) (qq_pure hC) (qq_qt hB) (qq_qt hC)) hD qd

/-- 7.5.4: `W B C D` with `W ∉ {S, S S}` and `B, C, D ∈ Q`. -/
theorem fin_q2 {W B C D : Term} (hW : PureS W) (h1 : W ≠ S) (h2 : W ≠ S ⬝ S)
    (hB : PureS B) (hC : PureS C) (hD : PureS D) (qb : Qt B) (qc : Qt C) (qd : Qt D) :
    Fin (W ⬝ B ⬝ C ⬝ D) := by
  if qw : Qt W then exact fin_qqq_app hW hB hC qw qb qc
  else
    have hr := rc_of_not_qt hW qw
    cases hr with
    | S => exact absurd rfl h1
    | @app w hw =>
      cases hw with
      | S => exact absurd rfl h2
      | @app w2 hw2 =>
        -- S (S w2) B C D → S w2 C (B C) D → w2 (B C) (C (B C)) D
        refine fin_of_step (.left D (.S (S ⬝ w2) B C)) ?_
        refine fin_of_step (.left D (.S w2 C (B ⬝ C))) ?_
        have qbc : QQ (B ⬝ C) := qq_mk hB hC qb qc
        exact fin_rc hw2 qbc (qq_mk hC (qq_pure qbc) qc (qq_qt qbc)) hD qd

/-! ## 7.5.5: the set `R` -/

theorem fin_R1 {h₁ h₂ B C : Term} (h1p : PureS h₁) (h2p : PureS h₂) (n1 : h₁ ≠ S)
    (n2 : h₁ ≠ S ⬝ S) (hB : PureS B) (hC : PureS C) (qb : Qt B) (qc : Qt C) :
    Fin (S ⬝ h₁ ⬝ h₂ ⬝ B ⬝ C) := by
  refine fin_of_step (.left C (.S h₁ h₂ B)) ?_
  exact fin_q2 h1p n1 n2 hB (.app h2p hB) hC qb (qt_app_right h2p hB qb) qc

theorem fin_R2 {h₂ B C : Term} (h2p : PureS h₂) (n1 : h₂ ≠ S) (n2 : h₂ ≠ S ⬝ S)
    (hB : PureS B) (hC : PureS C) (qb : Qt B) (qc : Qt C) :
    Fin (S ⬝ (S ⬝ S) ⬝ h₂ ⬝ B ⬝ C) := by
  -- S (S S) h₂ B C → S S B (h₂ B) C → S (h₂ B) (B (h₂ B)) C → h₂ B C (B (h₂ B) C)
  refine fin_of_step (.left C (.S (S ⬝ S) h₂ B)) ?_
  refine fin_of_step (.left C (.S S B (h₂ ⬝ B))) ?_
  refine fin_of_step (.S (h₂ ⬝ B) (B ⬝ (h₂ ⬝ B)) C) ?_
  have hb2 : PureS (B ⬝ (h₂ ⬝ B) ⬝ C) := .app (.app hB (.app h2p hB)) hC
  exact fin_q2 h2p n1 n2 hB hC hb2 qb qc (qt_app_right (.app hB (.app h2p hB)) hC qc)

/-! ## Steps from a term to a one-item head normal form are trivial (law L0) -/

theorem step_two {t t' : Term} (ht : PureS t) (s : Step t t') : ∃ a b c, t' = a ⬝ b ⬝ c := by
  induction s with
  | S f g x => exact ⟨f, x, g ⬝ x, rfl⟩
  | K => cases ht with | app h _ => cases h with | app h _ => cases h
  | I => cases ht with | app h _ => cases h
  | left x _ ih =>
    obtain ⟨a, b, c, rfl⟩ := ih ht.app_inv.1
    exact ⟨a ⬝ b, c, x, rfl⟩

theorem steps_two {t u : Term} (ht : PureS t) (h : Steps t u) : t = u ∨ ∃ a b c, u = a ⬝ b ⬝ c := by
  induction h with
  | refl => exact .inl rfl
  | step s _ ih =>
    rcases ih (HnfS.wstep_pure s.weak ht).1 with rfl | h
    · exact .inr (step_two ht s)
    · exact .inr h

theorem steps_S1 {t h : Term} (ht : PureS t) (hs : Steps t (S ⬝ h)) : t = S ⬝ h := by
  rcases steps_two ht hs with e | ⟨a, b, c, e⟩
  · exact e
  · cases e

/-- The head normal form of a non-⊥ term, with its block. -/
theorem hnf_of {X : Term} (hX : PureS X) (hb : fold X ≠ 36) :
    ∃ Kh, Steps X Kh ∧ IsHnf Kh ∧ PureS Kh ∧ fold Kh = fold X := by
  obtain ⟨Kh, hc, _, hK⟩ := sound_head X hX hb
  have ⟨hKp, hf⟩ := HnfS.fold_wsteps (HnfProd.headChain_wsteps hc hX) hX
  exact ⟨Kh, headChain_steps hc, hK, hKp, hf⟩

/-! ## 7.5.6 / 7.5.8: the complement `R̄` -/

/-- `S T S Y Z ↠ Y E F` with `E, F ∈ QQ`. -/
theorem steps_STS {Y Z : Term} : Steps (S ⬝ (S ⬝ S) ⬝ S ⬝ Y ⬝ Z)
    (Y ⬝ (Y ⬝ (S ⬝ Y) ⬝ Z) ⬝ (Z ⬝ (Y ⬝ (S ⬝ Y) ⬝ Z))) :=
  .step (.left Z (.S (S ⬝ S) S Y)) <|
  .step (.left Z (.S S Y (S ⬝ Y))) <|
  .step (.S (S ⬝ Y) (Y ⬝ (S ⬝ Y)) Z) <|
  .step (.S Y Z (Y ⬝ (S ⬝ Y) ⬝ Z)) (.refl _)

/-- `S T T Y Z ↠ Z W (Y Z W)` with `W = Y (T Y) Z`. -/
theorem steps_STT {Y Z : Term} : Steps (S ⬝ (S ⬝ S) ⬝ (S ⬝ S) ⬝ Y ⬝ Z)
    (Z ⬝ (Y ⬝ (S ⬝ S ⬝ Y) ⬝ Z) ⬝ (Y ⬝ Z ⬝ (Y ⬝ (S ⬝ S ⬝ Y) ⬝ Z))) :=
  .step (.left Z (.S (S ⬝ S) (S ⬝ S) Y)) <|
  .step (.left Z (.S S Y (S ⬝ S ⬝ Y))) <|
  .step (.S (S ⬝ S ⬝ Y) (Y ⬝ (S ⬝ S ⬝ Y)) Z) <|
  .step (.left (Y ⬝ (S ⬝ S ⬝ Y) ⬝ Z) (.S S Y Z)) <|
  .step (.S Z (Y ⬝ Z) (Y ⬝ (S ⬝ S ⬝ Y) ⬝ Z)) (.refl _)

/-- `T x Y Z ↠ Y Z (x Y Z)`. -/
theorem steps_T {x Y Z : Term} : Steps (S ⬝ S ⬝ x ⬝ Y ⬝ Z) (Y ⬝ Z ⬝ (x ⬝ Y ⬝ Z)) :=
  .step (.left Z (.S S x Y)) <| .step (.S Y (x ⬝ Y) Z) (.refl _)

/-- The two `S T P₂` cases: `X Y Z ↠ V E F` with `V ∈ {Y, Z}` and `E, F ∈ QQ`. -/
theorem stp2 {h₂ Y Z : Term} (hh : h₂ = S ∨ h₂ = S ⬝ S) (hY : PureS Y) (hZ : PureS Z)
    (qy : Qt Y) (qz : Qt Z) :
    ∃ V E F, Steps (S ⬝ (S ⬝ S) ⬝ h₂ ⬝ Y ⬝ Z) (V ⬝ E ⬝ F) ∧ (V = Y ∨ V = Z) ∧ QQ E ∧ QQ F := by
  rcases hh with rfl | rfl
  · have hE : PureS (Y ⬝ (S ⬝ Y)) := .app hY (.app .S hY)
    have qE : QQ (Y ⬝ (S ⬝ Y) ⬝ Z) := qq_mk hE hZ (qt_app_left hY (.app .S hY) qy) qz
    exact ⟨_, _, _, steps_STS, .inl rfl, qE, qq_mk hZ (qq_pure qE) qz (qq_qt qE)⟩
  · have hE : PureS (Y ⬝ (S ⬝ S ⬝ Y)) := .app hY (.app (.app .S .S) hY)
    have qE : QQ (Y ⬝ (S ⬝ S ⬝ Y) ⬝ Z) := qq_mk hE hZ (qt_app_left hY (.app (.app .S .S) hY) qy) qz
    have qF : QQ (Y ⬝ Z ⬝ (Y ⬝ (S ⬝ S ⬝ Y) ⬝ Z)) :=
      qq_mk (.app hY hZ) (qq_pure qE) (qt_app_left hY hZ qy) (qq_qt qE)
    exact ⟨_, _, _, steps_STT, .inr rfl, qE, qF⟩

/-- The five shapes of a two-item head normal form `S h₁ h₂`. -/
theorem hnf2_cases (h₁ h₂ : Term) :
    (h₁ ≠ S ∧ h₁ ≠ S ⬝ S) ∨ (h₁ = S ⬝ S ∧ h₂ ≠ S ∧ h₂ ≠ S ⬝ S) ∨ h₁ = S ∨
      (h₁ = S ⬝ S ∧ (h₂ = S ∨ h₂ = S ⬝ S)) := by
  if a : h₁ = S then exact .inr (.inr (.inl a))
  else if b : h₁ = S ⬝ S then
    if c : h₂ = S then exact .inr (.inr (.inr ⟨b, .inl c⟩))
    else if d : h₂ = S ⬝ S then exact .inr (.inr (.inr ⟨b, .inr d⟩))
    else exact .inr (.inl ⟨b, c, d⟩)
  else exact .inl ⟨a, b⟩

/-! ## 7.5.7 -/

/-- 7.5.7: `X E F` with `X ∈ Q` and `E, F ∈ QQ`. -/
theorem fin_qqq_qq : ∀ {X : Term}, PureS X → Qt X → ∀ {E F : Term}, QQ E → QQ F →
    Fin (X ⬝ E ⬝ F) := by
  intro X hX
  induction hX with
  | S => intro q; exact absurd q qt_S
  | @app f x hf hx _ ihx =>
    intro qX E F hE hF
    have hEp := qq_pure hE; have hFp := qq_pure hF
    if hb : fold (f ⬝ x) = 36 then exact fin_bot_head (.app hf hx) hEp hb
    else
      obtain ⟨Kh, hs, hK, hKp, hKf⟩ := hnf_of (.app hf hx) hb
      have qK : Qt Kh := by unfold Qt; rw [hKf]; exact qX
      refine fin_of_steps (Steps.left F (Steps.left E hs)) ?_
      rcases hK with rfl | ⟨h, rfl⟩ | ⟨h₁, h₂, rfl⟩
      · exact absurd qK qt_S
      · -- f x = S h, so f = S and h = x: S x E F → x F (E F)
        have e := steps_S1 (.app hf hx) hs
        injection e with ef ex
        subst ef ex
        refine fin_of_step (.S x E F) ?_
        exact ihx (qt_of_S_app hx qX) hF (qq_mk hEp hFp (qq_qt hE) (qq_qt hF))
      · have h1p := hKp.app_inv.1.app_inv.2
        have h2p := hKp.app_inv.2
        rcases hnf2_cases h₁ h₂ with ⟨n1, n2⟩ | ⟨rfl, n1, n2⟩ | rfl | ⟨rfl, hh⟩
        · exact fin_R1 h1p h2p n1 n2 hEp hFp (qq_qt hE) (qq_qt hF)
        · exact fin_R2 h2p n1 n2 hEp hFp (qq_qt hE) (qq_qt hF)
        · -- T h₂ E F ↠ E F (h₂ E F), and E ∈ QQ
          exact fin_of_steps steps_T (fin_qq_head hE hFp (qq_qt hF))
        · obtain ⟨V, E', F', hs', hV, qE', _⟩ := stp2 hh hEp hFp (qq_qt hE) (qq_qt hF)
          refine fin_of_steps hs' ?_
          rcases hV with rfl | rfl
          · exact fin_qq_head hE (qq_pure qE') (qq_qt qE')
          · exact fin_qq_head hF (qq_pure qE') (qq_qt qE')

/-! ## 7.5.9 -/

/-- `Y C G` with `Y, C ∈ Q` and `G ∈ QQ` (the `T` case of 7.5.9). -/
theorem fin_T {Y C G : Term} (hY : PureS Y) (hC : PureS C) (qy : Qt Y) (qc : Qt C) (hG : QQ G) :
    Fin (Y ⬝ C ⬝ G) := by
  have hGp := qq_pure hG
  if hb : fold Y = 36 then exact fin_bot_head hY hC hb
  else
    obtain ⟨Kh, hs, hK, hKp, hKf⟩ := hnf_of hY hb
    have qK : Qt Kh := by unfold Qt; rw [hKf]; exact qy
    refine fin_of_steps (Steps.left G (Steps.left C hs)) ?_
    rcases hK with rfl | ⟨h, rfl⟩ | ⟨h₁, h₂, rfl⟩
    · exact absurd qK qt_S
    · have hp := hKp.app_inv.2
      refine fin_of_step (.S h C G) ?_
      exact fin_qqq_qq hp (qt_of_S_app hp qK) hG (qq_mk hC hGp qc (qq_qt hG))
    · have h1p := hKp.app_inv.1.app_inv.2
      have h2p := hKp.app_inv.2
      rcases hnf2_cases h₁ h₂ with ⟨n1, n2⟩ | ⟨rfl, n1, n2⟩ | rfl | ⟨rfl, hh⟩
      · exact fin_R1 h1p h2p n1 n2 hC hGp qc (qq_qt hG)
      · exact fin_R2 h2p n1 n2 hC hGp qc (qq_qt hG)
      · refine fin_of_steps steps_T ?_
        exact fin_qqq_qq hC qc hG (qq_mk (.app h2p hC) hGp (qt_app_right h2p hC qc) (qq_qt hG))
      · obtain ⟨V, E', F', hs', hV, qE', qF'⟩ := stp2 hh hC hGp qc (qq_qt hG)
        refine fin_of_steps hs' ?_
        rcases hV with rfl | rfl
        · exact fin_qqq_qq hC qc qE' qF'
        · exact fin_qqq_qq hGp (qq_qt hG) qE' qF'

/-- Any two-item hnf `S h₁ h₂` in front of two `Q`-terms (7.5.5 and 7.5.9). -/
theorem fin_hnf2 {h₁ h₂ B C : Term} (h1p : PureS h₁) (h2p : PureS h₂) (hB : PureS B)
    (hC : PureS C) (qb : Qt B) (qc : Qt C) : Fin (S ⬝ h₁ ⬝ h₂ ⬝ B ⬝ C) := by
  rcases hnf2_cases h₁ h₂ with ⟨n1, n2⟩ | ⟨rfl, n1, n2⟩ | rfl | ⟨rfl, hh⟩
  · exact fin_R1 h1p h2p n1 n2 hB hC qb qc
  · exact fin_R2 h2p n1 n2 hB hC qb qc
  · refine fin_of_steps steps_T ?_
    exact fin_T hB hC qb qc (qq_mk (.app h2p hB) hC (qt_app_right h2p hB qb) qc)
  · obtain ⟨V, E', F', hs', hV, qE', qF'⟩ := stp2 hh hB hC qb qc
    refine fin_of_steps hs' ?_
    rcases hV with rfl | rfl
    · exact fin_qqq_qq hB qb qE' qF'
    · exact fin_qqq_qq hC qc qE' qF'

/-! ## 7.5.10 -/

/-- **Waldmann 7.5.10.**  `A B C` with `A, B, C ∈ Q` makes boundedly many root steps. -/
theorem fin_qqq : ∀ {A : Term}, PureS A → Qt A → ∀ {B C : Term}, PureS B → PureS C → Qt B → Qt C →
    Fin (A ⬝ B ⬝ C) := by
  intro A hA
  induction hA with
  | S => intro q; exact absurd q qt_S
  | @app f x hf hx _ ihx =>
    intro qA B C hB hC qb qc
    if hb : fold (f ⬝ x) = 36 then exact fin_bot_head (.app hf hx) hB hb
    else
      obtain ⟨Kh, hs, hK, hKp, hKf⟩ := hnf_of (.app hf hx) hb
      have qK : Qt Kh := by unfold Qt; rw [hKf]; exact qA
      refine fin_of_steps (Steps.left C (Steps.left B hs)) ?_
      rcases hK with rfl | ⟨h, rfl⟩ | ⟨h₁, h₂, rfl⟩
      · exact absurd qK qt_S
      · have e := steps_S1 (.app hf hx) hs
        injection e with ef ex
        subst ef ex
        refine fin_of_step (.S x B C) ?_
        exact ihx (qt_of_S_app hx qA) hC (.app hB hC) qc (qt_app_left hB hC qb)
      · exact fin_hnf2 hKp.app_inv.1.app_inv.2 hKp.app_inv.2 hB hC qb qc

end TopTerm
