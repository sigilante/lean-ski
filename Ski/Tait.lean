/-!
# Strong normalization of the typed realizer language (Tait)

Part II's realizer language: simply typed λ-calculus with products and sums,
over opaque base types and opaque constants.  An atom's witness type is a
base type, and its verifier a constant, so neither needs a definition
here.  Terms use de Bruijn indices; reduction (`Step`) is full, under
binders too, with β for functions, projections for pairs, and case for
injections.  Case takes its branches as functions, so λ is the only binder.

**Every typed term is strongly normalizing** (`strong_normalization`), by
Tait's method as in Girard's *Proofs and Types*.  Reducibility `Red A t`
is defined by recursion on `A`:
- at a base type, strong normalization;
- at `A ⇒ B`, mapping every reducible argument to a reducible result;
- at `A × B`, reducible projections;
- at `A + B`, strong normalization, with every injection the term reduces
  to carrying a reducible term.

The candidate properties (`cr`) are:
1. reducible terms are strongly normalizing;
2. reducibility is closed under reduction;
3. a neutral term whose reducts are all reducible is reducible.

They are proved together by induction on the type.  The fundamental lemma
(`fundamental`) says a typed term under a substitution of reducible terms
is reducible.  The only facts about substitution it needs are fusion
lemmas; reducibility is never renamed.
-/

namespace Rz

variable {β γ : Type}

/-- Types, over base types `β`. -/
inductive Ty (β : Type) where
  | base (b : β)
  | arr (A B : Ty β)
  | prod (A B : Ty β)
  | sum (A B : Ty β)

/-- Terms, over constants `γ`; variables are de Bruijn indices. -/
inductive Tm (γ : Type) where
  | var (n : Nat)
  | const (c : γ)
  | app (f a : Tm γ)
  | lam (b : Tm γ)
  | pair (a b : Tm γ)
  | fst (t : Tm γ)
  | snd (t : Tm γ)
  | inl (a : Tm γ)
  | inr (b : Tm γ)
  | case (s f g : Tm γ)

namespace Tm

-- ---------------------------------------------------------------------------
-- Renaming and substitution
-- ---------------------------------------------------------------------------

def upr (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

def ren (ξ : Nat → Nat) : Tm γ → Tm γ
  | var n => var (ξ n)
  | const c => const c
  | app f a => app (ren ξ f) (ren ξ a)
  | lam b => lam (ren (upr ξ) b)
  | pair a b => pair (ren ξ a) (ren ξ b)
  | fst t => fst (ren ξ t)
  | snd t => snd (ren ξ t)
  | inl a => inl (ren ξ a)
  | inr b => inr (ren ξ b)
  | case s f g => case (ren ξ s) (ren ξ f) (ren ξ g)

def up (σ : Nat → Tm γ) : Nat → Tm γ
  | 0 => var 0
  | n + 1 => ren Nat.succ (σ n)

def sub (σ : Nat → Tm γ) : Tm γ → Tm γ
  | var n => σ n
  | const c => const c
  | app f a => app (sub σ f) (sub σ a)
  | lam b => lam (sub (up σ) b)
  | pair a b => pair (sub σ a) (sub σ b)
  | fst t => fst (sub σ t)
  | snd t => snd (sub σ t)
  | inl a => inl (sub σ a)
  | inr b => inr (sub σ b)
  | case s f g => case (sub σ s) (sub σ f) (sub σ g)

/-- `a` for the variable 0, the rest shifted down. -/
def beta1 (a : Tm γ) : Nat → Tm γ
  | 0 => a
  | n + 1 => var n

/-- `a` for the variable 0, `σ` for the rest. -/
def scons (a : Tm γ) (σ : Nat → Tm γ) : Nat → Tm γ
  | 0 => a
  | n + 1 => σ n

theorem upr_comp (ξ ζ : Nat → Nat) : upr ξ ∘ upr ζ = upr (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

theorem ren_ren : ∀ (t : Tm γ) (ξ ζ : Nat → Nat), ren ξ (ren ζ t) = ren (ξ ∘ ζ) t
  | var _, _, _ => rfl
  | const _, _, _ => rfl
  | app f a, ξ, ζ => by simp only [ren, ren_ren f, ren_ren a]
  | lam b, ξ, ζ => by simp only [ren, ren_ren b, upr_comp]
  | pair a b, ξ, ζ => by simp only [ren, ren_ren a, ren_ren b]
  | fst t, ξ, ζ => by simp only [ren, ren_ren t]
  | snd t, ξ, ζ => by simp only [ren, ren_ren t]
  | inl a, ξ, ζ => by simp only [ren, ren_ren a]
  | inr b, ξ, ζ => by simp only [ren, ren_ren b]
  | case s f g, ξ, ζ => by simp only [ren, ren_ren s, ren_ren f, ren_ren g]

theorem up_ren_comp (σ : Nat → Tm γ) (ξ : Nat → Nat) : up σ ∘ upr ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem sub_ren : ∀ (t : Tm γ) (σ : Nat → Tm γ) (ξ : Nat → Nat),
    sub σ (ren ξ t) = sub (σ ∘ ξ) t
  | var _, _, _ => rfl
  | const _, _, _ => rfl
  | app f a, σ, ξ => by simp only [ren, sub, sub_ren f, sub_ren a]
  | lam b, σ, ξ => by simp only [ren, sub, sub_ren b, up_ren_comp]
  | pair a b, σ, ξ => by simp only [ren, sub, sub_ren a, sub_ren b]
  | fst t, σ, ξ => by simp only [ren, sub, sub_ren t]
  | snd t, σ, ξ => by simp only [ren, sub, sub_ren t]
  | inl a, σ, ξ => by simp only [ren, sub, sub_ren a]
  | inr b, σ, ξ => by simp only [ren, sub, sub_ren b]
  | case s f g, σ, ξ => by simp only [ren, sub, sub_ren s, sub_ren f, sub_ren g]

theorem ren_up_comp (ξ : Nat → Nat) (σ : Nat → Tm γ) :
    ren (upr ξ) ∘ up σ = up (ren ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show ren (upr ξ) (ren Nat.succ (σ n)) = ren Nat.succ (ren ξ (σ n))
    rw [ren_ren, ren_ren]
    rfl

theorem ren_sub : ∀ (t : Tm γ) (ξ : Nat → Nat) (σ : Nat → Tm γ),
    ren ξ (sub σ t) = sub (ren ξ ∘ σ) t
  | var _, _, _ => rfl
  | const _, _, _ => rfl
  | app f a, ξ, σ => by simp only [ren, sub, ren_sub f, ren_sub a]
  | lam b, ξ, σ => by simp only [ren, sub, ren_sub b, ren_up_comp]
  | pair a b, ξ, σ => by simp only [ren, sub, ren_sub a, ren_sub b]
  | fst t, ξ, σ => by simp only [ren, sub, ren_sub t]
  | snd t, ξ, σ => by simp only [ren, sub, ren_sub t]
  | inl a, ξ, σ => by simp only [ren, sub, ren_sub a]
  | inr b, ξ, σ => by simp only [ren, sub, ren_sub b]
  | case s f g, ξ, σ => by simp only [ren, sub, ren_sub s, ren_sub f, ren_sub g]

theorem up_comp (σ τ : Nat → Tm γ) : sub (up σ) ∘ up τ = up (sub σ ∘ τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show sub (up σ) (ren Nat.succ (τ n)) = ren Nat.succ (sub σ (τ n))
    rw [sub_ren, ren_sub]
    rfl

theorem sub_sub : ∀ (t : Tm γ) (σ τ : Nat → Tm γ), sub σ (sub τ t) = sub (sub σ ∘ τ) t
  | var _, _, _ => rfl
  | const _, _, _ => rfl
  | app f a, σ, τ => by simp only [sub, sub_sub f, sub_sub a]
  | lam b, σ, τ => by simp only [sub, sub_sub b, up_comp]
  | pair a b, σ, τ => by simp only [sub, sub_sub a, sub_sub b]
  | fst t, σ, τ => by simp only [sub, sub_sub t]
  | snd t, σ, τ => by simp only [sub, sub_sub t]
  | inl a, σ, τ => by simp only [sub, sub_sub a]
  | inr b, σ, τ => by simp only [sub, sub_sub b]
  | case s f g, σ, τ => by simp only [sub, sub_sub s, sub_sub f, sub_sub g]

theorem up_var : up (var (γ := γ)) = var := by
  funext n; cases n <;> rfl

theorem sub_var : ∀ t : Tm γ, sub var t = t
  | var _ => rfl
  | const _ => rfl
  | app f a => by simp only [sub, sub_var f, sub_var a]
  | lam b => by simp only [sub, up_var, sub_var b]
  | pair a b => by simp only [sub, sub_var a, sub_var b]
  | fst t => by simp only [sub, sub_var t]
  | snd t => by simp only [sub, sub_var t]
  | inl a => by simp only [sub, sub_var a]
  | inr b => by simp only [sub, sub_var b]
  | case s f g => by simp only [sub, sub_var s, sub_var f, sub_var g]

/-- Substitution through a β-contractum. -/
theorem sub_beta1 (σ : Nat → Tm γ) (a b : Tm γ) :
    sub σ (sub (beta1 a) b) = sub (beta1 (sub σ a)) (sub (up σ) b) := by
  rw [sub_sub, sub_sub]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show σ n = sub (beta1 (sub σ a)) (ren Nat.succ (σ n))
    rw [sub_ren]
    exact (sub_var (σ n)).symm

/-- Renaming through a β-contractum. -/
theorem ren_beta1 (ξ : Nat → Nat) (a b : Tm γ) :
    ren ξ (sub (beta1 a) b) = sub (beta1 (ren ξ a)) (ren (upr ξ) b) := by
  rw [ren_sub, sub_ren]
  congr 1
  funext n
  cases n <;> rfl

/-- A β-contractum under a lifted substitution is a substitution of `scons`. -/
theorem beta1_up (a : Tm γ) (σ : Nat → Tm γ) (b : Tm γ) :
    sub (beta1 a) (sub (up σ) b) = sub (scons a σ) b := by
  rw [sub_sub]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show sub (beta1 a) (ren Nat.succ (σ n)) = σ n
    rw [sub_ren]
    exact sub_var (σ n)

-- ---------------------------------------------------------------------------
-- Reduction
-- ---------------------------------------------------------------------------

/-- One step, anywhere. -/
inductive Step : Tm γ → Tm γ → Prop
  | beta (b a : Tm γ) : Step (app (lam b) a) (sub (beta1 a) b)
  | fstβ (a b : Tm γ) : Step (fst (pair a b)) a
  | sndβ (a b : Tm γ) : Step (snd (pair a b)) b
  | inlβ (a f g : Tm γ) : Step (case (inl a) f g) (app f a)
  | inrβ (b f g : Tm γ) : Step (case (inr b) f g) (app g b)
  | appL {f f' : Tm γ} (a : Tm γ) : Step f f' → Step (app f a) (app f' a)
  | appR (f : Tm γ) {a a' : Tm γ} : Step a a' → Step (app f a) (app f a')
  | lam {b b' : Tm γ} : Step b b' → Step (lam b) (lam b')
  | pairL {a a' : Tm γ} (b : Tm γ) : Step a a' → Step (pair a b) (pair a' b)
  | pairR (a : Tm γ) {b b' : Tm γ} : Step b b' → Step (pair a b) (pair a b')
  | fst {t t' : Tm γ} : Step t t' → Step (fst t) (fst t')
  | snd {t t' : Tm γ} : Step t t' → Step (snd t) (snd t')
  | inl {a a' : Tm γ} : Step a a' → Step (inl a) (inl a')
  | inr {b b' : Tm γ} : Step b b' → Step (inr b) (inr b')
  | caseS {s s' : Tm γ} (f g : Tm γ) : Step s s' → Step (case s f g) (case s' f g)
  | caseF (s : Tm γ) {f f' : Tm γ} (g : Tm γ) : Step f f' → Step (case s f g) (case s f' g)
  | caseG (s f : Tm γ) {g g' : Tm γ} : Step g g' → Step (case s f g) (case s f g')

inductive Steps : Tm γ → Tm γ → Prop
  | refl (t : Tm γ) : Steps t t
  | step {t u v : Tm γ} : Step t u → Steps u v → Steps t v

theorem Steps.single {t u : Tm γ} (h : Step t u) : Steps t u := .step h (.refl u)

theorem Steps.trans {t u v : Tm γ} (h₁ : Steps t u) (h₂ : Steps u v) : Steps t v := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- Multi-step reduction under a context that single steps respect. -/
theorem Steps.map {F : Tm γ → Tm γ} (hF : ∀ {t u}, Step t u → Step (F t) (F u))
    {t u : Tm γ} (h : Steps t u) : Steps (F t) (F u) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (hF h) ih

theorem Step.ren (ξ : Nat → Nat) {t u : Tm γ} (h : Step t u) : Step (ren ξ t) (ren ξ u) := by
  induction h generalizing ξ with
  | beta b a => rw [ren_beta1]; exact .beta _ _
  | fstβ a b => exact .fstβ _ _
  | sndβ a b => exact .sndβ _ _
  | inlβ a f g => exact .inlβ _ _ _
  | inrβ b f g => exact .inrβ _ _ _
  | appL a _ ih => exact .appL _ (ih ξ)
  | appR f _ ih => exact .appR _ (ih ξ)
  | lam _ ih => exact .lam (ih _)
  | pairL b _ ih => exact .pairL _ (ih ξ)
  | pairR a _ ih => exact .pairR _ (ih ξ)
  | fst _ ih => exact .fst (ih ξ)
  | snd _ ih => exact .snd (ih ξ)
  | inl _ ih => exact .inl (ih ξ)
  | inr _ ih => exact .inr (ih ξ)
  | caseS f g _ ih => exact .caseS _ _ (ih ξ)
  | caseF s g _ ih => exact .caseF _ _ (ih ξ)
  | caseG s f _ ih => exact .caseG _ _ (ih ξ)

theorem Step.sub (σ : Nat → Tm γ) {t u : Tm γ} (h : Step t u) : Step (sub σ t) (sub σ u) := by
  induction h generalizing σ with
  | beta b a => rw [sub_beta1]; exact .beta _ _
  | fstβ a b => exact .fstβ _ _
  | sndβ a b => exact .sndβ _ _
  | inlβ a f g => exact .inlβ _ _ _
  | inrβ b f g => exact .inrβ _ _ _
  | appL a _ ih => exact .appL _ (ih σ)
  | appR f _ ih => exact .appR _ (ih σ)
  | lam _ ih => exact .lam (ih _)
  | pairL b _ ih => exact .pairL _ (ih σ)
  | pairR a _ ih => exact .pairR _ (ih σ)
  | fst _ ih => exact .fst (ih σ)
  | snd _ ih => exact .snd (ih σ)
  | inl _ ih => exact .inl (ih σ)
  | inr _ ih => exact .inr (ih σ)
  | caseS f g _ ih => exact .caseS _ _ (ih σ)
  | caseF s g _ ih => exact .caseF _ _ (ih σ)
  | caseG s f _ ih => exact .caseG _ _ (ih σ)

-- ---------------------------------------------------------------------------
-- Strong normalization
-- ---------------------------------------------------------------------------

/-- Strongly normalizing: every reduction sequence from `t` is finite. -/
inductive SN : Tm γ → Prop
  | intro {t : Tm γ} : (∀ u, Step t u → SN u) → SN t

theorem SN.step {t u : Tm γ} (h : SN t) (s : Step t u) : SN u := by
  cases h with
  | intro h => exact h u s

theorem SN.steps {t u : Tm γ} (h : SN t) (s : Steps t u) : SN u := by
  induction s with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

/-- Strong normalization is reflected by any map that respects steps. -/
theorem SN.of_map {F : Tm γ → Tm γ} (hF : ∀ {t u}, Step t u → Step (F t) (F u)) :
    ∀ {t : Tm γ}, SN (F t) → SN t := by
  suffices h : ∀ s : Tm γ, SN s → ∀ t, F t = s → SN t from fun {t} hs => h _ hs t rfl
  intro s hs
  induction hs with
  | @intro s _ ih =>
    intro t e
    exact .intro fun u hu => ih (F u) (e ▸ hF hu) u rfl

theorem SN.of_sub (σ : Nat → Tm γ) {t : Tm γ} (h : SN (sub σ t)) : SN t :=
  SN.of_map (F := sub σ) (fun h => h.sub σ) h

theorem SN.of_app {t a : Tm γ} (h : SN (app t a)) : SN t :=
  SN.of_map (F := fun t => app t a) (fun h => .appL a h) h

theorem SN.of_fst {t : Tm γ} (h : SN (fst t)) : SN t :=
  SN.of_map (F := fst) (fun h => .fst h) h

theorem inl_step_inv {a v : Tm γ} (h : Step (inl a) v) : ∃ a', Step a a' ∧ v = inl a' := by
  cases h with
  | inl h => exact ⟨_, h, rfl⟩

theorem inr_step_inv {b v : Tm γ} (h : Step (inr b) v) : ∃ b', Step b b' ∧ v = inr b' := by
  cases h with
  | inr h => exact ⟨_, h, rfl⟩

theorem sn_inl {a : Tm γ} (h : SN a) : SN (inl a) := by
  induction h with
  | intro _ ih =>
    exact .intro fun v hv => by
      cases inl_step_inv hv with
      | intro a' h => rw [h.2]; exact ih a' h.1

theorem sn_inr {b : Tm γ} (h : SN b) : SN (inr b) := by
  induction h with
  | intro _ ih =>
    exact .intro fun v hv => by
      cases inr_step_inv hv with
      | intro b' h => rw [h.2]; exact ih b' h.1

theorem inl_steps_inv {a w : Tm γ} (h : Steps (inl a) w) : ∃ a', Steps a a' ∧ w = inl a' := by
  generalize e : inl a = t at h
  induction h generalizing a with
  | refl => exact ⟨a, .refl a, e.symm⟩
  | step s _ ih =>
    subst e
    cases inl_step_inv s with
    | intro a1 h1 =>
      cases ih h1.2.symm with
      | intro a2 h2 => exact ⟨a2, .step h1.1 h2.1, h2.2⟩

theorem inr_steps_inv {b w : Tm γ} (h : Steps (inr b) w) : ∃ b', Steps b b' ∧ w = inr b' := by
  generalize e : inr b = t at h
  induction h generalizing b with
  | refl => exact ⟨b, .refl b, e.symm⟩
  | step s _ ih =>
    subst e
    cases inr_step_inv s with
    | intro b1 h1 =>
      cases ih h1.2.symm with
      | intro b2 h2 => exact ⟨b2, .step h1.1 h2.1, h2.2⟩

-- ---------------------------------------------------------------------------
-- Neutral terms
-- ---------------------------------------------------------------------------

/-- Neutral: not an introduction form, so no context can make it a redex. -/
def Neutral : Tm γ → Prop
  | lam _ => False
  | pair _ _ => False
  | inl _ => False
  | inr _ => False
  | _ => True

theorem app_step_neutral {t a v : Tm γ} (hn : Neutral t) (h : Step (app t a) v) :
    (∃ t', Step t t' ∧ v = app t' a) ∨ (∃ a', Step a a' ∧ v = app t a') := by
  cases h with
  | beta b _ => exact hn.elim
  | appL _ h => exact .inl ⟨_, h, rfl⟩
  | appR _ h => exact .inr ⟨_, h, rfl⟩

theorem fst_step_neutral {t v : Tm γ} (hn : Neutral t) (h : Step (fst t) v) :
    ∃ t', Step t t' ∧ v = fst t' := by
  cases h with
  | fstβ _ _ => exact hn.elim
  | fst h => exact ⟨_, h, rfl⟩

theorem snd_step_neutral {t v : Tm γ} (hn : Neutral t) (h : Step (snd t) v) :
    ∃ t', Step t t' ∧ v = snd t' := by
  cases h with
  | sndβ _ _ => exact hn.elim
  | snd h => exact ⟨_, h, rfl⟩

theorem neutral_steps_first {t w : Tm γ} (hn : Neutral t) (hw : ¬ Neutral w) (h : Steps t w) :
    ∃ t1, Step t t1 ∧ Steps t1 w := by
  cases h with
  | refl => exact absurd hn hw
  | step s h => exact ⟨_, s, h⟩

end Tm

open Tm

-- ---------------------------------------------------------------------------
-- Reducibility and the candidate properties
-- ---------------------------------------------------------------------------

/-- Reducibility. -/
def Red : Ty β → Tm γ → Prop
  | .base _, t => SN t
  | .arr A B, t => ∀ u, Red A u → Red B (Tm.app t u)
  | .prod A B, t => Red A (Tm.fst t) ∧ Red B (Tm.snd t)
  | .sum A B, t => SN t ∧ (∀ u, Steps t (Tm.inl u) → Red A u) ∧ (∀ u, Steps t (Tm.inr u) → Red B u)

/-- The three candidate properties, together, by induction on the type. -/
theorem cr : ∀ A : Ty β,
    (∀ t : Tm γ, Red A t → SN t) ∧
    (∀ t t' : Tm γ, Red A t → Step t t' → Red A t') ∧
    (∀ t : Tm γ, Neutral t → (∀ t', Step t t' → Red A t') → Red A t)
  | .base _ => ⟨fun _ h => h, fun _ _ h s => h.step s, fun _ _ h => .intro h⟩
  | .arr A B => by
    have ⟨a1, a2, a3⟩ := cr A
    have ⟨b1, b2, b3⟩ := cr B
    have rvar : Red A (Tm.var 0 : Tm γ) := a3 _ trivial fun _ s => by cases s
    refine ⟨fun t h => SN.of_app (b1 _ (h _ rvar)), fun t t' h s u hu => b2 _ _ (h u hu) (.appL u s),
      fun t hn h => ?_⟩
    intro u hu
    have hsn := a1 u hu
    induction hsn with
    | @intro u _ ih =>
      refine b3 _ trivial fun v hv => ?_
      cases app_step_neutral hn hv with
      | inl ht =>
        cases ht with
        | intro t' ht => rw [ht.2]; exact h t' ht.1 u hu
      | inr hu' =>
        cases hu' with
        | intro u' hu' => rw [hu'.2]; exact ih u' hu'.1 (a2 _ _ hu hu'.1)
  | .prod A B => by
    have ⟨a1, a2, a3⟩ := cr A
    have ⟨b1, b2, b3⟩ := cr B
    refine ⟨fun t h => SN.of_fst (a1 _ h.1), fun t t' h s => ⟨a2 _ _ h.1 (.fst s), b2 _ _ h.2 (.snd s)⟩,
      fun t hn h => ⟨a3 _ trivial fun v hv => ?_, b3 _ trivial fun v hv => ?_⟩⟩
    · cases fst_step_neutral hn hv with
      | intro t' ht => rw [ht.2]; exact (h t' ht.1).1
    · cases snd_step_neutral hn hv with
      | intro t' ht => rw [ht.2]; exact (h t' ht.1).2
  | .sum A B => by
    refine ⟨fun t h => h.1, fun t t' h s => ⟨h.1.step s, fun u hu => h.2.1 u (.step s hu),
      fun u hu => h.2.2 u (.step s hu)⟩, fun t hn h => ⟨.intro fun t' s => (h t' s).1, ?_, ?_⟩⟩
    · intro u hu
      cases neutral_steps_first hn (show ¬ Neutral (Tm.inl u) from fun e => e) hu with
      | intro t1 h1 => exact (h t1 h1.1).2.1 u h1.2
    · intro u hu
      cases neutral_steps_first hn (show ¬ Neutral (Tm.inr u) from fun e => e) hu with
      | intro t1 h1 => exact (h t1 h1.1).2.2 u h1.2

theorem Red.sn {A : Ty β} {t : Tm γ} (h : Red A t) : SN t := (cr A).1 t h

theorem Red.step {A : Ty β} {t t' : Tm γ} (h : Red A t) (s : Step t t') : Red A t' :=
  (cr A).2.1 t t' h s

theorem Red.steps {A : Ty β} {t t' : Tm γ} (h : Red A t) (s : Steps t t') : Red A t' := by
  induction s with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

theorem Red.neutral {A : Ty β} {t : Tm γ} (hn : Neutral t) (h : ∀ t', Step t t' → Red A t') :
    Red A t :=
  (cr A).2.2 t hn h

theorem Red.var (A : Ty β) (n : Nat) : Red A (Tm.var n : Tm γ) :=
  Red.neutral trivial fun _ s => by cases s

theorem Red.const (A : Ty β) (c : γ) : Red A (Tm.const c) :=
  Red.neutral trivial fun _ s => by cases s

-- ---------------------------------------------------------------------------
-- Reducibility of the introduction and elimination forms
-- ---------------------------------------------------------------------------

/-- β-expansion: a λ whose body is reducible under every reducible
    argument is reducible. -/
theorem Red.lam {A B : Ty β} {b : Tm γ} (hb : ∀ u, Red A u → Red B (sub (beta1 u) b)) :
    Red (.arr A B) (Tm.lam b) := by
  have hsnb : SN b := SN.of_sub _ (hb (Tm.var 0) (Red.var A 0)).sn
  suffices key : ∀ b : Tm γ, SN b → (∀ u, Red A u → Red B (sub (beta1 u) b)) →
      ∀ u, SN u → Red A u → Red B (Tm.app (Tm.lam b) u) from
    fun u hu => key b hsnb hb u hu.sn hu
  intro b hsn
  induction hsn with
  | @intro b hsb ihb =>
    intro hb u hsu
    induction hsu with
    | @intro u hsu' ihu =>
      intro hu
      refine Red.neutral trivial fun v hv => ?_
      cases hv with
      | beta _ _ => exact hb u hu
      | appL _ hl =>
        cases hl with
        | lam hb' =>
          exact ihb _ hb' (fun w hw => (hb w hw).step (hb'.sub _)) u (.intro hsu') hu
      | appR _ hr => exact ihu _ hr (hu.step hr)

theorem Red.fst_pair {A : Ty β} {a b : Tm γ} (ha : Red A a) (hb : SN b) :
    Red A (Tm.fst (Tm.pair a b)) := by
  have hsa := ha.sn
  induction hsa generalizing b with
  | @intro a hsa' iha =>
    induction hb with
    | @intro b hsb' ihb =>
      refine Red.neutral trivial fun v hv => ?_
      cases hv with
      | fstβ _ _ => exact ha
      | fst hp =>
        cases hp with
        | pairL _ h => exact iha _ h (ha.step h) (.intro hsb')
        | pairR _ h => exact ihb _ h

theorem Red.snd_pair {B : Ty β} {a b : Tm γ} (ha : SN a) (hb : Red B b) :
    Red B (Tm.snd (Tm.pair a b)) := by
  have hsb := hb.sn
  induction hsb generalizing a with
  | @intro b hsb' ihb =>
    induction ha with
    | @intro a hsa' iha =>
      refine Red.neutral trivial fun v hv => ?_
      cases hv with
      | sndβ _ _ => exact hb
      | snd hp =>
        cases hp with
        | pairL _ h => exact iha _ h
        | pairR _ h => exact ihb _ h (.intro hsa') (hb.step h)

theorem Red.inl {A B : Ty β} {a : Tm γ} (ha : Red A a) : Red (.sum A B) (Tm.inl a) := by
  refine ⟨sn_inl ha.sn, fun u hu => ?_, fun u hu => ?_⟩
  · cases inl_steps_inv hu with
    | intro a' h =>
      cases h.2
      exact ha.steps h.1
  · cases inl_steps_inv hu with
    | intro a' h => cases h.2

theorem Red.inr {A B : Ty β} {b : Tm γ} (hb : Red B b) : Red (.sum A B) (Tm.inr b) := by
  refine ⟨sn_inr hb.sn, fun u hu => ?_, fun u hu => ?_⟩
  · cases inr_steps_inv hu with
    | intro b' h => cases h.2
  · cases inr_steps_inv hu with
    | intro b' h =>
      cases h.2
      exact hb.steps h.1

theorem Red.case {A B C : Ty β} {s f g : Tm γ} (hs : Red (.sum A B) s)
    (hf : Red (.arr A C) f) (hg : Red (.arr B C) g) : Red C (Tm.case s f g) := by
  have hss := hs.1
  induction hss generalizing f g with
  | @intro s hss' ihs =>
    have hsf := hf.sn
    induction hsf generalizing g with
    | @intro f hsf' ihf =>
      have hsg := hg.sn
      induction hsg with
      | @intro g hsg' ihg =>
        refine Red.neutral trivial fun v hv => ?_
        cases hv with
        | inlβ a _ _ => exact hf a (hs.2.1 a (.refl _))
        | inrβ b _ _ => exact hg b (hs.2.2 b (.refl _))
        | caseS _ _ h => exact ihs _ h (hs.step h) hf hg
        | caseF _ _ h => exact ihf _ h (hf.step h) hg
        | caseG _ _ h => exact ihg _ h (hg.step h)

-- ---------------------------------------------------------------------------
-- Typing and the fundamental lemma
-- ---------------------------------------------------------------------------

/-- `A` for the variable 0, `Γ` for the rest. -/
def Ty.cons (A : Ty β) (Γ : Nat → Ty β) : Nat → Ty β
  | 0 => A
  | n + 1 => Γ n

/-- Typing, over a signature `sig` for the constants. -/
inductive Typed (sig : γ → Ty β) : (Nat → Ty β) → Tm γ → Ty β → Prop
  | var (Γ : Nat → Ty β) (n : Nat) : Typed sig Γ (Tm.var n) (Γ n)
  | const (Γ : Nat → Ty β) (c : γ) : Typed sig Γ (Tm.const c) (sig c)
  | lam {Γ : Nat → Ty β} {A B : Ty β} {b : Tm γ} :
      Typed sig (Ty.cons A Γ) b B → Typed sig Γ (Tm.lam b) (.arr A B)
  | app {Γ : Nat → Ty β} {A B : Ty β} {f a : Tm γ} :
      Typed sig Γ f (.arr A B) → Typed sig Γ a A → Typed sig Γ (Tm.app f a) B
  | pair {Γ : Nat → Ty β} {A B : Ty β} {a b : Tm γ} :
      Typed sig Γ a A → Typed sig Γ b B → Typed sig Γ (Tm.pair a b) (.prod A B)
  | fst {Γ : Nat → Ty β} {A B : Ty β} {t : Tm γ} :
      Typed sig Γ t (.prod A B) → Typed sig Γ (Tm.fst t) A
  | snd {Γ : Nat → Ty β} {A B : Ty β} {t : Tm γ} :
      Typed sig Γ t (.prod A B) → Typed sig Γ (Tm.snd t) B
  | inl {Γ : Nat → Ty β} {A B : Ty β} {a : Tm γ} :
      Typed sig Γ a A → Typed sig Γ (Tm.inl a) (.sum A B)
  | inr {Γ : Nat → Ty β} {A B : Ty β} {b : Tm γ} :
      Typed sig Γ b B → Typed sig Γ (Tm.inr b) (.sum A B)
  | case {Γ : Nat → Ty β} {A B C : Ty β} {s f g : Tm γ} :
      Typed sig Γ s (.sum A B) → Typed sig Γ f (.arr A C) → Typed sig Γ g (.arr B C) →
        Typed sig Γ (Tm.case s f g) C

/-- **The fundamental lemma**: a typed term, under a substitution of
    reducible terms for its variables, is reducible. -/
theorem fundamental {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) : ∀ σ : Nat → Tm γ, (∀ n, Red (Γ n) (σ n)) → Red A (sub σ t) := by
  induction h with
  | var Γ n => intro σ hσ; exact hσ n
  | const Γ c => intro σ _; exact Red.const _ c
  | @lam Γ A B b _ ih =>
    intro σ hσ
    refine Red.lam fun u hu => ?_
    rw [beta1_up]
    refine ih (scons u σ) fun n => ?_
    cases n with
    | zero => exact hu
    | succ n => exact hσ n
  | app _ _ ihf iha => intro σ hσ; exact ihf σ hσ _ (iha σ hσ)
  | pair _ _ iha ihb =>
    intro σ hσ
    exact ⟨Red.fst_pair (iha σ hσ) (ihb σ hσ).sn, Red.snd_pair (iha σ hσ).sn (ihb σ hσ)⟩
  | fst _ ih => intro σ hσ; exact (ih σ hσ).1
  | snd _ ih => intro σ hσ; exact (ih σ hσ).2
  | inl _ ih => intro σ hσ; exact Red.inl (ih σ hσ)
  | inr _ ih => intro σ hσ; exact Red.inr (ih σ hσ)
  | case _ _ _ ihs ihf ihg => intro σ hσ; exact Red.case (ihs σ hσ) (ihf σ hσ) (ihg σ hσ)

/-- **Strong normalization**: every typed term of the realizer language is
    strongly normalizing. -/
theorem strong_normalization {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) : SN t := by
  have hr := fundamental h Tm.var fun n => Red.var (Γ n) n
  rw [sub_var] at hr
  exact hr.sn

/-- `λx. x x`. -/
def omegaT : Tm γ := Tm.lam (Tm.app (Tm.var 0) (Tm.var 0))

/-- `SN` is not vacuous: `(λx. x x) (λx. x x)` steps to itself, so it is not
    strongly normalizing, and so it has no type. -/
theorem omega_not_sn : ¬ SN (Tm.app (omegaT : Tm γ) omegaT) := by
  have hs : Step (Tm.app (omegaT : Tm γ) omegaT) (Tm.app omegaT omegaT) := Step.beta _ _
  suffices h : ∀ t : Tm γ, SN t → t ≠ Tm.app omegaT omegaT from fun hsn => h _ hsn rfl
  intro t ht
  induction ht with
  | intro _ ih => intro e; subst e; exact ih _ hs rfl

theorem omega_untyped {sig : γ → Ty β} {Γ : Nat → Ty β} {A : Ty β} :
    ¬ Typed sig Γ (Tm.app (omegaT : Tm γ) omegaT) A :=
  fun h => omega_not_sn (strong_normalization h)

end Rz
