import Ski.OracleFan

open Term

/-!
# A universal machine on codes, component 1: one head step

`stepC` performs one head step on the code of a term, mirroring the
computable contraction `step?` of `Ski/Fuel.lean` case for case:

    stepC ⟨t⟩ ↠ nothing        when step? t = none  (t is a whnf)
    stepC ⟨t⟩ ↠ just ⟨u⟩       when step? t = some u

(`stepC_spec`).  It is the first component of a mechanized Kleene tree
(`notes/mech-kleene.md`), which needs a step-bounded universal evaluator inside
the calculus.
-/

namespace Univ

open NoLift Requote

-- ---------------------------------------------------------------------------
-- Scott Maybe
-- ---------------------------------------------------------------------------

/-- `nothing = λ n j. n`. -/
def nothingT : Term := toTerm (absN [0, 1] (.var 0))
/-- `just c = λ n j. j c`. -/
def justT : Term := toTerm (absN [0, 1, 2] (.var 2 ⬝ₒ .var 0))

theorem nothing_sel (n j : Term) : WSteps (nothingT ⬝ n ⬝ j) n := by
  have h := absN_beta_close [0, 1] (.var 0) (fun _ => K) [n, j] rfl
  simp only [OTerm.close, appT] at h; exact h

theorem just_sel (c n j : Term) : WSteps (justT ⬝ c ⬝ n ⬝ j) (j ⬝ c) := by
  have h := absN_beta_close [0, 1, 2] (.var 2 ⬝ₒ .var 0) (fun _ => K) [c, n, j] rfl
  simp only [OTerm.close, appT] at h; exact h

/-- A Lean option of terms, as a Scott Maybe of codes. -/
def mcode : Option Term → Term
  | none => nothingT
  | some u => justT ⬝ quoteT u

-- ---------------------------------------------------------------------------
-- The step
-- ---------------------------------------------------------------------------

/-- The fallback when `f` does not step, over `f` (0), `x` (1), and inner
    binders `g` (2), `z` (3), `g'` (4), `y` (5), `a` (6), `b` (7):

      f nothing nothing (just x)
        (λ g z. g nothing (just z) nothing
          (λ g' y. g' (just (App (App y x) (App z x))) nothing nothing (λ a b. nothing))) -/
def fbInner2 : OTerm :=
  absN [4, 5] (.var 4 ⬝ₒ
    (justT.toO ⬝ₒ (appC.toO ⬝ₒ (appC.toO ⬝ₒ .var 5 ⬝ₒ .var 1) ⬝ₒ (appC.toO ⬝ₒ .var 3 ⬝ₒ .var 1)))
    ⬝ₒ nothingT.toO ⬝ₒ nothingT.toO ⬝ₒ absN [6, 7] nothingT.toO)

def fbInner1 : OTerm :=
  absN [2, 3] (.var 2 ⬝ₒ nothingT.toO ⬝ₒ (justT.toO ⬝ₒ .var 3) ⬝ₒ nothingT.toO ⬝ₒ fbInner2)

def fbBody : OTerm :=
  .var 0 ⬝ₒ nothingT.toO ⬝ₒ nothingT.toO ⬝ₒ (justT.toO ⬝ₒ .var 1) ⬝ₒ fbInner1

/-- `fb f x`. -/
def fbT : Term := toTerm (absN [0, 1] fbBody)

/-- The step function's body, over `r` (0), `q` (1), and `f` (2), `x` (3), `f'` (4):

      q nothing nothing nothing
        (λ f x. r f (fb f x) (λ f'. just (App f' x))) -/
def stepBodyC : OTerm :=
  .var 1 ⬝ₒ nothingT.toO ⬝ₒ nothingT.toO ⬝ₒ nothingT.toO ⬝ₒ
    absN [2, 3] (.var 0 ⬝ₒ .var 2 ⬝ₒ (fbT.toO ⬝ₒ .var 2 ⬝ₒ .var 3) ⬝ₒ
      absN [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3)))

def stepStepC : Term := toTerm (absN [0, 1] stepBodyC)

/-- **`stepC`**, the fixpoint of `stepStepC`. -/
def stepC : Term := fixSelf stepStepC (fixB stepStepC)

theorem stepC_unroll : WSteps stepC (stepStepC ⬝ stepC) := by
  have h := (fixSelf_unroll (F := stepStepC) (Steps.refl (fixB stepStepC))).weak
  have hI : WSteps (fixSelf stepStepC (I ⬝ fixB stepStepC)) stepC := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

-- ---------------------------------------------------------------------------
-- Unfolding the closures
-- ---------------------------------------------------------------------------

/-- The environments of the fallback's closures. -/
def σ1 (qf qx : Term) : Nat → Term := overrideC (fun _ => K) [0, 1] [qf, qx]
def σ2 (qf qx qg qz : Term) : Nat → Term := overrideC (σ1 qf qx) [2, 3] [qg, qz]
def σ3 (qf qx qg qz qg' qy : Term) : Nat → Term := overrideC (σ2 qf qx qg qz) [4, 5] [qg', qy]

theorem fb_unfold (qf qx : Term) :
    WSteps (fbT ⬝ qf ⬝ qx) (qf ⬝ nothingT ⬝ nothingT ⬝ (justT ⬝ qx) ⬝ fbInner1.close (σ1 qf qx)) := by
  have h := absN_beta_close [0, 1] fbBody (fun _ => K) [qf, qx] rfl
  simp only [fbBody, OTerm.close, close_toO, appT] at h
  exact h

theorem in1_unfold (qf qx qg qz : Term) :
    WSteps (fbInner1.close (σ1 qf qx) ⬝ qg ⬝ qz)
      (qg ⬝ nothingT ⬝ (justT ⬝ qz) ⬝ nothingT ⬝ fbInner2.close (σ2 qf qx qg qz)) := by
  have h := absN_beta_close [2, 3]
    (.var 2 ⬝ₒ nothingT.toO ⬝ₒ (justT.toO ⬝ₒ .var 3) ⬝ₒ nothingT.toO ⬝ₒ fbInner2) (σ1 qf qx) [qg, qz] rfl
  simp only [OTerm.close, close_toO, appT] at h
  exact h

theorem in2_unfold (qf qx qg qz qg' qy : Term) :
    WSteps (fbInner2.close (σ2 qf qx qg qz) ⬝ qg' ⬝ qy)
      (qg' ⬝ (justT ⬝ (appC ⬝ (appC ⬝ qy ⬝ qx) ⬝ (appC ⬝ qz ⬝ qx))) ⬝ nothingT ⬝ nothingT
        ⬝ (absN [6, 7] nothingT.toO).close (σ3 qf qx qg qz qg' qy)) := by
  have h := absN_beta_close [4, 5]
    (.var 4 ⬝ₒ
      (justT.toO ⬝ₒ (appC.toO ⬝ₒ (appC.toO ⬝ₒ .var 5 ⬝ₒ .var 1) ⬝ₒ (appC.toO ⬝ₒ .var 3 ⬝ₒ .var 1)))
      ⬝ₒ nothingT.toO ⬝ₒ nothingT.toO ⬝ₒ absN [6, 7] nothingT.toO) (σ2 qf qx qg qz) [qg', qy] rfl
  simp only [OTerm.close, close_toO, appT] at h
  exact h

theorem in3_unfold (σ : Nat → Term) (a b : Term) :
    WSteps ((absN [6, 7] nothingT.toO).close σ ⬝ a ⬝ b) nothingT := by
  have h := absN_beta_close [6, 7] nothingT.toO σ [a, b] rfl
  simp only [OTerm.close, close_toO, appT] at h
  exact h

/-- One unrolling: `stepC q ↠ q nothing nothing nothing (λ f x. …)`. -/
theorem stepC_case (q : Term) :
    WSteps (stepC ⬝ q) (q ⬝ nothingT ⬝ nothingT ⬝ nothingT ⬝
      (absN [2, 3] (.var 0 ⬝ₒ .var 2 ⬝ₒ (fbT.toO ⬝ₒ .var 2 ⬝ₒ .var 3) ⬝ₒ
        absN [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3)))).close
          (overrideC (fun _ => K) [0, 1] [stepC, q])) := by
  have h := absN_beta_close [0, 1] stepBodyC (fun _ => K) [stepC, q] rfl
  simp only [stepBodyC, OTerm.close, close_toO, appT] at h
  exact (WSteps.left _ stepC_unroll).trans h

theorem app_case (q qf qx : Term) :
    WSteps ((absN [2, 3] (.var 0 ⬝ₒ .var 2 ⬝ₒ (fbT.toO ⬝ₒ .var 2 ⬝ₒ .var 3) ⬝ₒ
        absN [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3)))).close
          (overrideC (fun _ => K) [0, 1] [stepC, q]) ⬝ qf ⬝ qx)
      (stepC ⬝ qf ⬝ (fbT ⬝ qf ⬝ qx) ⬝
        (absN [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3))).close
          (overrideC (overrideC (fun _ => K) [0, 1] [stepC, q]) [2, 3] [qf, qx])) := by
  have h := absN_beta_close [2, 3] (.var 0 ⬝ₒ .var 2 ⬝ₒ (fbT.toO ⬝ₒ .var 2 ⬝ₒ .var 3) ⬝ₒ
        absN [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3)))
    (overrideC (fun _ => K) [0, 1] [stepC, q]) [qf, qx] rfl
  simp only [OTerm.close, close_toO, appT] at h
  exact h

theorem just_case (σ : Nat → Term) (qf' : Term) (_hx : σ 3 = σ 3) :
    WSteps ((absN [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3))).close σ ⬝ qf')
      (justT ⬝ (appC ⬝ qf' ⬝ σ 3)) := by
  have h := absN_beta_close [4] (justT.toO ⬝ₒ (appC.toO ⬝ₒ .var 4 ⬝ₒ .var 3)) σ [qf'] rfl
  simp only [OTerm.close, close_toO, appT] at h
  exact h

-- ---------------------------------------------------------------------------
-- The specification
-- ---------------------------------------------------------------------------

/-- **The fallback**: when `f` does not step, `fb ⟨f⟩ ⟨x⟩` gives the step of
    `f x` that `step?` takes at the root. -/
theorem fb_spec (f x : Term) (hf : step? f = none) :
    WSteps (fbT ⬝ quoteT f ⬝ quoteT x) (mcode (step? (f ⬝ x))) := by
  refine (fb_unfold _ _).trans ?_
  cases f with
  | S => simpa [step?, mcode] using quoteS_elim _ _ _ _
  | K => simpa [step?, mcode] using quoteK_elim _ _ _ _
  | I => simpa [step?, mcode] using quoteI_elim _ _ _ _
  | app g z =>
    refine (quoteApp_elim g z _ _ _ _).trans ((in1_unfold _ _ _ _).trans ?_)
    cases g with
    | S => simpa [step?, mcode] using quoteS_elim _ _ _ _
    | K => simpa [step?, mcode] using quoteK_elim _ _ _ _
    | I => simp [step?] at hf
    | app g' y =>
      refine (quoteApp_elim g' y _ _ _ _).trans ((in2_unfold _ _ _ _ _ _).trans ?_)
      cases g' with
      | S =>
        have e := quoteS_elim (justT ⬝ (appC ⬝ (appC ⬝ quoteT y ⬝ quoteT x) ⬝ (appC ⬝ quoteT z ⬝ quoteT x)))
          nothingT nothingT ((absN [6, 7] nothingT.toO).close (σ3 (quoteT (S ⬝ y ⬝ z)) (quoteT x)
            (quoteT (S ⬝ y)) (quoteT z) (quoteT S) (quoteT y)))
        simpa [step?, mcode, quoteT_app] using e
      | K => simp [step?] at hf
      | I => simp [step?] at hf
      | app a b =>
        refine (quoteApp_elim a b _ _ _ _).trans ?_
        have e := in3_unfold (σ3 (quoteT (a ⬝ b ⬝ y ⬝ z)) (quoteT x) (quoteT (a ⬝ b ⬝ y)) (quoteT z)
          (quoteT (a ⬝ b)) (quoteT y)) (quoteT a) (quoteT b)
        have hn : step? (a ⬝ b ⬝ y ⬝ z ⬝ x) = none := by
          cases a <;> simp_all [step?]
        simpa [mcode, hn] using e

/-- **`stepC` is one head step on codes.** -/
theorem stepC_spec : ∀ t : Term, WSteps (stepC ⬝ quoteT t) (mcode (step? t))
  | .S => (stepC_case _).trans (by simpa [step?, mcode] using quoteS_elim _ _ _ _)
  | .K => (stepC_case _).trans (by simpa [step?, mcode] using quoteK_elim _ _ _ _)
  | .I => (stepC_case _).trans (by simpa [step?, mcode] using quoteI_elim _ _ _ _)
  | .app f x => by
    refine (stepC_case _).trans ((quoteApp_elim f x _ _ _ _).trans ((app_case _ _ _).trans ?_))
    have ih := stepC_spec f
    cases hf : step? f with
    | none =>
      rw [hf] at ih
      refine (WSteps.left _ (WSteps.left _ ih)).trans ((nothing_sel _ _).trans ?_)
      exact fb_spec f x hf
    | some f' =>
      rw [hf] at ih
      refine (WSteps.left _ (WSteps.left _ ih)).trans ((just_sel _ _ _).trans ?_)
      have e := just_case (overrideC (overrideC (fun _ => K) [0, 1] [stepC, quoteT (f ⬝ x)]) [2, 3]
        [quoteT f, quoteT x]) (quoteT f') rfl
      rw [show step? (f ⬝ x) = some (f' ⬝ x) by simp [step?, hf]]
      exact e

-- ---------------------------------------------------------------------------
-- Component 2: at most N head steps
-- ---------------------------------------------------------------------------

/-- The Lean model: the whnf `t` reaches within `N` head steps, if any. -/
def bnd : Nat → Term → Option Term
  | N, t => match step? t with
    | none => some t
    | some u => match N with
      | 0 => none
      | N + 1 => bnd N u

theorem bnd_mono : ∀ (N : Nat) (t v : Term), bnd N t = some v → bnd (N + 1) t = some v := by
  intro N
  induction N with
  | zero =>
    intro t v h
    unfold bnd at h ⊢
    cases hs : step? t with
    | none => rw [hs] at h; exact h
    | some u => rw [hs] at h; simp at h
  | succ N ih =>
    intro t v h
    unfold bnd at h ⊢
    cases hs : step? t with
    | none => rw [hs] at h; exact h
    | some u => rw [hs] at h; simp only at h ⊢; exact ih u v h

theorem bnd_mono_le {N M : Nat} (hNM : N ≤ M) {t v : Term} (h : bnd N t = some v) : bnd M t = some v := by
  induction hNM with
  | refl => exact h
  | step _ ih => exact bnd_mono _ _ _ ih

/-- A head run to a whnf in `k ≤ N` steps is found. -/
theorem bnd_of_run : ∀ (k : Nat) {t v : Term}, StepsN k t v → Whnf v → ∀ N, k ≤ N → bnd N t = some v := by
  intro k
  induction k with
  | zero =>
    intro t v h hv N _
    cases h
    unfold bnd
    rw [whnf_iff_step?_none.1 hv]
  | succ k ih =>
    intro t v h hv N hN
    cases h with
    | step h1 hs =>
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      unfold bnd
      rw [step?_complete h1]
      exact ih hs hv N' (by omega)

/-- What `bnd` returns is a whnf that `t` head-reduces to. -/
theorem bnd_sound : ∀ (N : Nat) {t v : Term}, bnd N t = some v → Steps t v ∧ Whnf v := by
  intro N
  induction N with
  | zero =>
    intro t v h
    unfold bnd at h
    cases hs : step? t with
    | none => rw [hs] at h; cases h; exact ⟨.refl _, step?_none hs⟩
    | some u => rw [hs] at h; simp at h
  | succ N ih =>
    intro t v h
    unfold bnd at h
    cases hs : step? t with
    | none => rw [hs] at h; cases h; exact ⟨.refl _, step?_none hs⟩
    | some u =>
      rw [hs] at h; simp only at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨.step (step?_sound hs) h1, h2⟩

/-- `ev r n q = stepC q (just q) (λ q'. n nothing (λ n'. r n' q'))`,
    over `r` (0), `n` (1), `q` (2), `q'` (3), `n'` (4). -/
def evIn : OTerm := absN [3] (.var 1 ⬝ₒ nothingT.toO ⬝ₒ absN [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 3))
def evBody : OTerm := stepC.toO ⬝ₒ .var 2 ⬝ₒ (justT.toO ⬝ₒ .var 2) ⬝ₒ evIn
def evStep : Term := toTerm (absN [0, 1, 2] evBody)

/-- **`evalC`**, the fixpoint of `evStep`. -/
def evalC : Term := fixSelf evStep (fixB evStep)

theorem evalC_unroll : WSteps evalC (evStep ⬝ evalC) := by
  have h := (fixSelf_unroll (F := evStep) (Steps.refl (fixB evStep))).weak
  have hI : WSteps (fixSelf evStep (I ⬝ fixB evStep)) evalC := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem evalC_case (n q : Term) : ∃ Y,
    WSteps (evalC ⬝ n ⬝ q) (stepC ⬝ q ⬝ (justT ⬝ q) ⬝ Y) ∧
    ∀ q', ∃ Z, WSteps (Y ⬝ q') (n ⬝ nothingT ⬝ Z) ∧ ∀ n', WSteps (Z ⬝ n') (evalC ⬝ n' ⬝ q') := by
  have h := absN_beta_close [0, 1, 2] evBody (fun _ => K) [evalC, n, q] rfl
  simp only [evBody, OTerm.close, close_toO, appT] at h
  refine ⟨_, (WSteps.left _ (WSteps.left _ evalC_unroll)).trans h, fun q' => ?_⟩
  let σ := overrideC (fun _ => K) [0, 1, 2] [evalC, n, q]
  have h2 := absN_beta_close [3] (.var 1 ⬝ₒ nothingT.toO ⬝ₒ absN [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 3)) σ [q'] rfl
  simp only [OTerm.close, close_toO, appT] at h2
  refine ⟨_, h2, fun n' => ?_⟩
  have h3 := absN_beta_close [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 3) (overrideC σ [3] [q']) [n'] rfl
  simp only [OTerm.close, appT] at h3
  exact h3

/-- **`evalC` is the bounded run on codes.** -/
theorem evalC_spec : ∀ (N : Nat) (t : Term), WSteps (evalC ⬝ num N ⬝ quoteT t) (mcode (bnd N t)) := by
  intro N
  induction N with
  | zero =>
    intro t
    obtain ⟨Y, hY, hYs⟩ := evalC_case (num 0) (quoteT t)
    refine hY.trans ((WSteps.left _ (WSteps.left _ (stepC_spec t))).trans ?_)
    unfold bnd
    cases hs : step? t with
    | none => simpa [mcode] using nothing_sel _ _
    | some u =>
      obtain ⟨Z, hZ, _⟩ := hYs (quoteT u)
      simpa [mcode] using (just_sel _ _ _).trans (hZ.trans (.single (.K _ _)))
  | succ N ih =>
    intro t
    obtain ⟨Y, hY, hYs⟩ := evalC_case (num (N + 1)) (quoteT t)
    refine hY.trans ((WSteps.left _ (WSteps.left _ (stepC_spec t))).trans ?_)
    unfold bnd
    cases hs : step? t with
    | none => simpa [mcode] using nothing_sel _ _
    | some u =>
      obtain ⟨Z, hZ, hZs⟩ := hYs (quoteT u)
      have := (just_sel (quoteT u) (justT ⬝ quoteT t) Y).trans
        (hZ.trans ((succS_wsteps (num N) _ Z).trans ((hZs _).trans (ih u))))
      simpa [mcode] using this

-- ---------------------------------------------------------------------------
-- Component 3: enumeration of terms by numerals
-- ---------------------------------------------------------------------------

/-- One step of the diagonal walk through ℕ × ℕ. -/
def next : Nat × Nat → Nat × Nat
  | (x, 0) => (0, x + 1)
  | (x, y + 1) => (x + 1, y)

/-- The `k`-th pair. -/
def walk : Nat → Nat × Nat
  | 0 => (0, 0)
  | k + 1 => next (walk k)

theorem walk_le : ∀ k, (walk k).1 + (walk k).2 ≤ k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have ih := walk_le k
    simp only [walk]
    rcases h : walk k with ⟨x, y⟩
    rw [h] at ih
    cases y with
    | zero => simp [next]; omega
    | succ y => simp [next]; omega

theorem walk_diag {k d : Nat} (h : walk k = (0, d)) : ∀ j, j ≤ d → walk (k + j) = (j, d - j)
  | 0, _ => by simpa using h
  | j + 1, hj => by
    have ih := walk_diag h j (by omega)
    rw [← Nat.add_assoc, walk, ih]
    obtain ⟨e, he⟩ : ∃ e, d - j = e + 1 := ⟨d - j - 1, by omega⟩
    rw [he]; simp [next]; omega

theorem walk_zero : ∀ d, ∃ k, walk k = (0, d)
  | 0 => ⟨0, rfl⟩
  | d + 1 => by
    obtain ⟨k, hk⟩ := walk_zero d
    have h := walk_diag hk d (Nat.le_refl _)
    simp at h
    exact ⟨k + d + 1, by rw [walk, h]; rfl⟩

/-- **Every pair is visited.** -/
theorem walk_surj (x y : Nat) : ∃ k, walk k = (x, y) := by
  obtain ⟨k, hk⟩ := walk_zero (x + y)
  exact ⟨k + x, by rw [walk_diag hk x (by omega)]; simp⟩

/-- The term numbered `n`. -/
def dec : Nat → Term
  | 0 => S
  | 1 => K
  | 2 => I
  | k + 3 =>
    have h1 : (walk k).1 < k + 3 := by have := walk_le k; omega
    have h2 : (walk k).2 < k + 3 := by have := walk_le k; omega
    dec (walk k).1 ⬝ dec (walk k).2
termination_by n => n

/-- **Every term is numbered.** -/
theorem dec_surj : ∀ t : Term, ∃ n, dec n = t
  | .S => ⟨0, by simp [dec]⟩
  | .K => ⟨1, by simp [dec]⟩
  | .I => ⟨2, by simp [dec]⟩
  | .app f a => by
    obtain ⟨nf, hf⟩ := dec_surj f
    obtain ⟨na, ha⟩ := dec_surj a
    obtain ⟨k, hk⟩ := walk_surj nf na
    exact ⟨k + 3, by rw [dec, hk]; simp [hf, ha]⟩

-- The walk on Scott numerals

open Search in
/-- `next p = p (λ x y. y (pair 0 (succ x)) (λ y'. pair (succ x) y'))`,
    over `p` (0), `x` (1), `y` (2), `y'` (3). -/
def nextIn : OTerm :=
  absN [1, 2] (.var 2 ⬝ₒ (consC.toO ⬝ₒ (num 0).toO ⬝ₒ (succS.toO ⬝ₒ .var 1)) ⬝ₒ
    absN [3] (consC.toO ⬝ₒ (succS.toO ⬝ₒ .var 1) ⬝ₒ .var 3))
def nextT : Term := toTerm (absN [0] (.var 0 ⬝ₒ nextIn))

open Search in
theorem next_spec (x y : Nat) :
    WSteps (nextT ⬝ (consC ⬝ num x ⬝ num y)) (consC ⬝ num (next (x, y)).1 ⬝ num (next (x, y)).2) := by
  have h := absN_beta_close [0] (.var 0 ⬝ₒ nextIn) (fun _ => K) [consC ⬝ num x ⬝ num y] rfl
  simp only [OTerm.close, appT] at h
  refine h.trans ((cons_sel _ _ _).trans ?_)
  have h2 := absN_beta_close [1, 2] (.var 2 ⬝ₒ (consC.toO ⬝ₒ (num 0).toO ⬝ₒ (succS.toO ⬝ₒ .var 1)) ⬝ₒ
    absN [3] (consC.toO ⬝ₒ (succS.toO ⬝ₒ .var 1) ⬝ₒ .var 3))
    (overrideC (fun _ => K) [0] [consC ⬝ num x ⬝ num y]) [num x, num y] rfl
  simp only [OTerm.close, close_toO, appT] at h2
  refine h2.trans ?_
  cases y with
  | zero => exact .single (.K _ _)
  | succ y =>
    refine (succS_wsteps (num y) _ _).trans ?_
    have h3 := absN_beta_close [3] (consC.toO ⬝ₒ (succS.toO ⬝ₒ .var 1) ⬝ₒ .var 3)
      (overrideC (overrideC (fun _ => K) [0] [consC ⬝ num x ⬝ num (y + 1)]) [1, 2] [num x, num (y + 1)])
      [num y] rfl
    simp only [OTerm.close, close_toO, appT] at h3
    exact h3

open Search in
/-- `walk n = n (pair 0 0) (λ n'. next (walk n'))`, over `r` (0), `n` (1), `n'` (2). -/
def walkBody : OTerm :=
  .var 1 ⬝ₒ (consC ⬝ num 0 ⬝ num 0).toO ⬝ₒ absN [2] (nextT.toO ⬝ₒ (.var 0 ⬝ₒ .var 2))
def walkStep : Term := toTerm (absN [0, 1] walkBody)
/-- **`walkC`**. -/
def walkC : Term := fixSelf walkStep (fixB walkStep)

theorem walkC_unroll : WSteps walkC (walkStep ⬝ walkC) := by
  have h := (fixSelf_unroll (F := walkStep) (Steps.refl (fixB walkStep))).weak
  have hI : WSteps (fixSelf walkStep (I ⬝ fixB walkStep)) walkC := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

open Search in
theorem walkC_spec : ∀ k, WSteps (walkC ⬝ num k) (consC ⬝ num (walk k).1 ⬝ num (walk k).2) := by
  have hcase : ∀ n, ∃ Z, WSteps (walkC ⬝ n) (n ⬝ (consC ⬝ num 0 ⬝ num 0) ⬝ Z) ∧
      ∀ n', WSteps (Z ⬝ n') (nextT ⬝ (walkC ⬝ n')) := by
    intro n
    have h := absN_beta_close [0, 1] walkBody (fun _ => K) [walkC, n] rfl
    simp only [walkBody, OTerm.close, close_toO, appT] at h
    refine ⟨_, (WSteps.left _ walkC_unroll).trans h, fun n' => ?_⟩
    have h2 := absN_beta_close [2] (nextT.toO ⬝ₒ (.var 0 ⬝ₒ .var 2))
      (overrideC (fun _ => K) [0, 1] [walkC, n]) [n'] rfl
    simp only [OTerm.close, close_toO, appT] at h2
    exact h2
  intro k
  induction k with
  | zero =>
    obtain ⟨Z, hZ, _⟩ := hcase (num 0)
    exact hZ.trans (.single (.K _ _))
  | succ k ih =>
    obtain ⟨Z, hZ, hZs⟩ := hcase (num (k + 1))
    rcases hw : walk k with ⟨x, y⟩
    rw [hw] at ih
    have e : walk (k + 1) = next (x, y) := by simp [walk, hw]
    rw [e]
    exact (hZ.trans ((succS_wsteps (num k) _ Z).trans ((hZs _).trans (WSteps.right _ ih)))).trans
      (next_spec x y)

-- The decoder

/-- `dec n = n ⟨S⟩ (λ n1. n1 ⟨K⟩ (λ n2. n2 ⟨I⟩ (λ n3. walk n3 (λ x y. App (r x) (r y)))))`,
    over `r` (0), `n` (1), `n1` (2), `n2` (3), `n3` (4), `x` (5), `y` (6). -/
def decXY : OTerm := absN [5, 6] (appC.toO ⬝ₒ (.var 0 ⬝ₒ .var 5) ⬝ₒ (.var 0 ⬝ₒ .var 6))
def dec3 : OTerm := absN [4] (walkC.toO ⬝ₒ .var 4 ⬝ₒ decXY)
def dec2 : OTerm := absN [3] (.var 3 ⬝ₒ (quoteT I).toO ⬝ₒ dec3)
def dec1 : OTerm := absN [2] (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ dec2)
def decBody : OTerm := .var 1 ⬝ₒ (quoteT S).toO ⬝ₒ dec1
def decStep : Term := toTerm (absN [0, 1] decBody)
/-- **`decC`**: the code of the term a numeral numbers. -/
def decC : Term := fixSelf decStep (fixB decStep)

theorem decC_unroll : WSteps decC (decStep ⬝ decC) := by
  have h := (fixSelf_unroll (F := decStep) (Steps.refl (fixB decStep))).weak
  have hI : WSteps (fixSelf decStep (I ⬝ fixB decStep)) decC := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

open Search in
theorem decC_spec : ∀ fuel n, n < fuel → WSteps (decC ⬝ num n) (quoteT (dec n)) := by
  intro fuel
  induction fuel with
  | zero => intro n h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro n hn
    let σ0 := overrideC (fun _ => K) [0, 1] [decC, num n]
    have h0 := absN_beta_close [0, 1] decBody (fun _ => K) [decC, num n] rfl
    simp only [decBody, OTerm.close, close_toO, appT] at h0
    have start := (WSteps.left _ decC_unroll).trans h0
    match n with
    | 0 =>
      have e : dec 0 = S := by rw [dec]
      rw [e]
      exact start.trans (.single (.K _ _))
    | 1 =>
      have e : dec 1 = K := by rw [dec]
      rw [e]
      have h1 := absN_beta_close [2] (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ dec2) σ0 [num 0] rfl
      simp only [OTerm.close, close_toO, appT] at h1
      exact (start.trans (succS_wsteps (num 0) _ _)).trans (h1.trans (.single (.K _ _)))
    | 2 =>
      have e : dec 2 = I := by rw [dec]
      rw [e]
      have h1 := absN_beta_close [2] (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ dec2) σ0 [num 1] rfl
      simp only [OTerm.close, close_toO, appT] at h1
      have h2 := absN_beta_close [3] (.var 3 ⬝ₒ (quoteT I).toO ⬝ₒ dec3) (overrideC σ0 [2] [num 1]) [num 0] rfl
      simp only [OTerm.close, close_toO, appT] at h2
      exact (start.trans (succS_wsteps (num 1) _ _)).trans
        ((h1.trans (succS_wsteps (num 0) _ _)).trans (h2.trans (.single (.K _ _))))
    | k + 3 =>
      refine (start.trans (succS_wsteps (num (k + 2)) _ _)).trans ?_
      have h1 := absN_beta_close [2] (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ dec2) σ0 [num (k + 2)] rfl
      simp only [OTerm.close, close_toO, appT] at h1
      refine (h1.trans (succS_wsteps (num (k + 1)) _ _)).trans ?_
      have h2 := absN_beta_close [3] (.var 3 ⬝ₒ (quoteT I).toO ⬝ₒ dec3) (overrideC σ0 [2] [num (k + 2)])
        [num (k + 1)] rfl
      simp only [OTerm.close, close_toO, appT] at h2
      refine (h2.trans (succS_wsteps (num k) _ _)).trans ?_
      let σ3 := overrideC (overrideC σ0 [2] [num (k + 2)]) [3] [num (k + 1)]
      have h3 := absN_beta_close [4] (walkC.toO ⬝ₒ .var 4 ⬝ₒ decXY) σ3 [num k] rfl
      simp only [OTerm.close, close_toO, appT] at h3
      refine (h3.trans (WSteps.left _ (walkC_spec k))).trans ((cons_sel _ _ _).trans ?_)
      have h4 := absN_beta_close [5, 6] (appC.toO ⬝ₒ (.var 0 ⬝ₒ .var 5) ⬝ₒ (.var 0 ⬝ₒ .var 6))
        (overrideC σ3 [4] [num k]) [num (walk k).1, num (walk k).2] rfl
      simp only [OTerm.close, close_toO, appT] at h4
      refine h4.trans ?_
      have hx := ih (walk k).1 (by have := walk_le k; omega)
      have hy := ih (walk k).2 (by have := walk_le k; omega)
      have e : quoteT (dec (k + 3)) = appC ⬝ quoteT (dec (walk k).1) ⬝ quoteT (dec (walk k).2) := by
        rw [dec]; rfl
      rw [e]
      exact WSteps.app (WSteps.right _ hx) hy

theorem decC_num (n : Nat) : WSteps (decC ⬝ num n) (quoteT (dec n)) := decC_spec (n + 1) n (by omega)

-- The code of a numeral

/-- `lift n = n ⟨K⟩ (λ n'. App ⟨succ⟩ (lift n'))`, over `r` (0), `n` (1), `n'` (2). -/
def liftBody : OTerm :=
  .var 1 ⬝ₒ (quoteT K).toO ⬝ₒ absN [2] (appC.toO ⬝ₒ (quoteT succS).toO ⬝ₒ (.var 0 ⬝ₒ .var 2))
def liftStep : Term := toTerm (absN [0, 1] liftBody)
/-- **`liftN`**: lift at Nat. -/
def liftN : Term := fixSelf liftStep (fixB liftStep)

theorem liftN_unroll : WSteps liftN (liftStep ⬝ liftN) := by
  have h := (fixSelf_unroll (F := liftStep) (Steps.refl (fixB liftStep))).weak
  have hI : WSteps (fixSelf liftStep (I ⬝ fixB liftStep)) liftN := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem liftN_case (n : Term) : ∃ X, WSteps (liftN ⬝ n) (n ⬝ quoteT K ⬝ X) ∧
    ∀ n', WSteps (X ⬝ n') (appC ⬝ quoteT succS ⬝ (liftN ⬝ n')) := by
  have h := absN_beta_close [0, 1] liftBody (fun _ => K) [liftN, n] rfl
  simp only [liftBody, OTerm.close, close_toO, appT] at h
  refine ⟨_, (WSteps.left _ liftN_unroll).trans h, fun n' => ?_⟩
  have h2 := absN_beta_close [2] (appC.toO ⬝ₒ (quoteT succS).toO ⬝ₒ (.var 0 ⬝ₒ .var 2))
    (overrideC (fun _ => K) [0, 1] [liftN, n]) [n'] rfl
  simp only [OTerm.close, close_toO, appT] at h2
  exact h2

theorem liftN_spec : ∀ n, WSteps (liftN ⬝ num n) (quoteT (num n))
  | 0 => by
    obtain ⟨X, hX, _⟩ := liftN_case (num 0)
    exact hX.trans (.single (.K _ _))
  | n + 1 => by
    obtain ⟨X, hX, hXs⟩ := liftN_case (num (n + 1))
    exact (hX.trans (succS_wsteps (num n) _ X)).trans ((hXs _).trans (WSteps.right _ (liftN_spec n)))

end Univ
