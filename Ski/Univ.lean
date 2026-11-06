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

end Univ
