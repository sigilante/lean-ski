/-!
# The untyped λ-calculus, and Church–Rosser

De Bruijn terms with renaming and parallel substitution (`ren`, `sub`),
whose fusion lemmas are proved once; full β-reduction (`LStep`, under
binders); parallel reduction (`LPar`) with Takahashi's complete development
(`ldev`), from which Church–Rosser follows (`lsteps_confluent`); and a
fuelled leftmost-outermost normalizer (`lnf`), sound for normal forms, so the
kernel can compute them.

Two uses: the translation of combinators into λ-terms, in which `S K X`
β-reduces to the identity for every `X` (`Ski/Quote.lean`, the
non-quotability of live terms), and the realizer language of the
combinatory logic of proofs.
-/

/-- λ-terms, variables as de Bruijn indices. -/
inductive Lam where
  | var (n : Nat)
  | app (f a : Lam)
  | lam (b : Lam)
  deriving DecidableEq, Repr

namespace Lam

/-- A renaming, lifted under a binder. -/
def upr (ξ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ξ n + 1

def ren (ξ : Nat → Nat) : Lam → Lam
  | var n => var (ξ n)
  | app f a => app (ren ξ f) (ren ξ a)
  | lam b => lam (ren (upr ξ) b)

/-- A substitution, lifted under a binder. -/
def up (σ : Nat → Lam) : Nat → Lam
  | 0 => var 0
  | n + 1 => ren Nat.succ (σ n)

def sub (σ : Nat → Lam) : Lam → Lam
  | var n => σ n
  | app f a => app (sub σ f) (sub σ a)
  | lam b => lam (sub (up σ) b)

/-- The substitution of `a` for the variable `0`, the rest shifted down. -/
def beta1 (a : Lam) : Nat → Lam
  | 0 => a
  | n + 1 => var n

-- ---------------------------------------------------------------------------
-- Fusion
-- ---------------------------------------------------------------------------

theorem upr_comp (ξ ζ : Nat → Nat) : upr ξ ∘ upr ζ = upr (ξ ∘ ζ) := by
  funext n; cases n <;> rfl

theorem ren_ren : ∀ (t : Lam) (ξ ζ : Nat → Nat), ren ξ (ren ζ t) = ren (ξ ∘ ζ) t
  | var _, _, _ => rfl
  | app f a, ξ, ζ => by
    show app (ren ξ (ren ζ f)) (ren ξ (ren ζ a)) = app (ren (ξ ∘ ζ) f) (ren (ξ ∘ ζ) a)
    rw [ren_ren f, ren_ren a]
  | lam b, ξ, ζ => by
    show lam (ren (upr ξ) (ren (upr ζ) b)) = lam (ren (upr (ξ ∘ ζ)) b)
    rw [ren_ren b, upr_comp]

theorem up_ren_comp (σ : Nat → Lam) (ξ : Nat → Nat) : up σ ∘ upr ξ = up (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem sub_ren : ∀ (t : Lam) (σ : Nat → Lam) (ξ : Nat → Nat), sub σ (ren ξ t) = sub (σ ∘ ξ) t
  | var _, _, _ => rfl
  | app f a, σ, ξ => by
    show app (sub σ (ren ξ f)) (sub σ (ren ξ a)) = app (sub (σ ∘ ξ) f) (sub (σ ∘ ξ) a)
    rw [sub_ren f, sub_ren a]
  | lam b, σ, ξ => by
    show lam (sub (up σ) (ren (upr ξ) b)) = lam (sub (up (σ ∘ ξ)) b)
    rw [sub_ren b, up_ren_comp]

theorem ren_up_comp (ξ : Nat → Nat) (σ : Nat → Lam) :
    ren (upr ξ) ∘ up σ = up (ren ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show ren (upr ξ) (ren Nat.succ (σ n)) = ren Nat.succ (ren ξ (σ n))
    rw [ren_ren, ren_ren]
    rfl

theorem ren_sub : ∀ (t : Lam) (ξ : Nat → Nat) (σ : Nat → Lam), ren ξ (sub σ t) = sub (ren ξ ∘ σ) t
  | var _, _, _ => rfl
  | app f a, ξ, σ => by
    show app (ren ξ (sub σ f)) (ren ξ (sub σ a)) = app (sub (ren ξ ∘ σ) f) (sub (ren ξ ∘ σ) a)
    rw [ren_sub f, ren_sub a]
  | lam b, ξ, σ => by
    show lam (ren (upr ξ) (sub (up σ) b)) = lam (sub (up (ren ξ ∘ σ)) b)
    rw [ren_sub b, ren_up_comp]

theorem up_comp (σ τ : Nat → Lam) : sub (up σ) ∘ up τ = up (sub σ ∘ τ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show sub (up σ) (ren Nat.succ (τ n)) = ren Nat.succ (sub σ (τ n))
    rw [sub_ren, ren_sub]
    rfl

theorem sub_sub : ∀ (t : Lam) (σ τ : Nat → Lam), sub σ (sub τ t) = sub (sub σ ∘ τ) t
  | var _, _, _ => rfl
  | app f a, σ, τ => by
    show app (sub σ (sub τ f)) (sub σ (sub τ a)) = app (sub (sub σ ∘ τ) f) (sub (sub σ ∘ τ) a)
    rw [sub_sub f, sub_sub a]
  | lam b, σ, τ => by
    show lam (sub (up σ) (sub (up τ) b)) = lam (sub (up (sub σ ∘ τ)) b)
    rw [sub_sub b, up_comp]

theorem up_var : up var = var := by
  funext n; cases n <;> rfl

theorem sub_var : ∀ t : Lam, sub var t = t
  | var _ => rfl
  | app f a => by
    show app (sub var f) (sub var a) = app f a
    rw [sub_var f, sub_var a]
  | lam b => by
    show lam (sub (up var) b) = lam b
    rw [up_var, sub_var b]

/-- Substitution through a β-contractum. -/
theorem sub_beta1 (σ : Nat → Lam) (a b : Lam) :
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
theorem ren_beta1 (ξ : Nat → Nat) (a b : Lam) :
    ren ξ (sub (beta1 a) b) = sub (beta1 (ren ξ a)) (ren (upr ξ) b) := by
  rw [ren_sub, sub_ren]
  congr 1
  funext n
  cases n <;> rfl

-- ---------------------------------------------------------------------------
-- β-reduction
-- ---------------------------------------------------------------------------

/-- One β-step, anywhere, under binders too. -/
inductive LStep : Lam → Lam → Prop
  | beta (b a : Lam) : LStep (app (lam b) a) (sub (beta1 a) b)
  | appL {f f' : Lam} (a : Lam) : LStep f f' → LStep (app f a) (app f' a)
  | appR (f : Lam) {a a' : Lam} : LStep a a' → LStep (app f a) (app f a')
  | lam {b b' : Lam} : LStep b b' → LStep (lam b) (lam b')

inductive LSteps : Lam → Lam → Prop
  | refl (t : Lam) : LSteps t t
  | step {t u v : Lam} : LStep t u → LSteps u v → LSteps t v

theorem LSteps.single {t u : Lam} (h : LStep t u) : LSteps t u := .step h (.refl u)

theorem LSteps.trans {t u v : Lam} (h₁ : LSteps t u) (h₂ : LSteps u v) : LSteps t v := by
  induction h₁ with
  | refl => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem LSteps.appL {f f' : Lam} (a : Lam) (h : LSteps f f') : LSteps (app f a) (app f' a) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.appL a h) ih

theorem LSteps.appR (f : Lam) {a a' : Lam} (h : LSteps a a') : LSteps (app f a) (app f a') := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.appR f h) ih

theorem LSteps.app {f f' a a' : Lam} (hf : LSteps f f') (ha : LSteps a a') :
    LSteps (app f a) (app f' a') :=
  (LSteps.appL a hf).trans (LSteps.appR f' ha)

theorem LSteps.lam {b b' : Lam} (h : LSteps b b') : LSteps (lam b) (lam b') := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (.lam h) ih

-- ---------------------------------------------------------------------------
-- Parallel reduction and Church–Rosser
-- ---------------------------------------------------------------------------

inductive LPar : Lam → Lam → Prop
  | var (n : Nat) : LPar (var n) (var n)
  | app {f f' a a' : Lam} : LPar f f' → LPar a a' → LPar (app f a) (app f' a')
  | lam {b b' : Lam} : LPar b b' → LPar (lam b) (lam b')
  | beta {b b' a a' : Lam} : LPar b b' → LPar a a' → LPar (app (lam b) a) (sub (beta1 a') b')

theorem LPar.refl : ∀ t : Lam, LPar t t
  | Lam.var n => .var n
  | Lam.app f a => .app (LPar.refl f) (LPar.refl a)
  | Lam.lam b => .lam (LPar.refl b)

theorem LStep.par {t u : Lam} (h : LStep t u) : LPar t u := by
  induction h with
  | beta b a => exact .beta (LPar.refl b) (LPar.refl a)
  | appL a _ ih => exact .app ih (LPar.refl a)
  | appR f _ ih => exact .app (LPar.refl f) ih
  | lam _ ih => exact .lam ih

theorem LPar.steps {t u : Lam} (h : LPar t u) : LSteps t u := by
  induction h with
  | var n => exact .refl _
  | app _ _ ihf iha => exact LSteps.app ihf iha
  | lam _ ih => exact LSteps.lam ih
  | @beta b b' a a' _ _ ihb iha =>
    exact (LSteps.app (LSteps.lam ihb) iha).trans (.single (.beta b' a'))

theorem LPar.ren {t u : Lam} (h : LPar t u) : ∀ ξ : Nat → Nat, LPar (Lam.ren ξ t) (Lam.ren ξ u) := by
  induction h with
  | var n => intro ξ; exact .var _
  | app _ _ ihf iha => intro ξ; exact .app (ihf ξ) (iha ξ)
  | lam _ ih => intro ξ; exact .lam (ih _)
  | @beta b b' a a' _ _ ihb iha =>
    intro ξ
    rw [ren_beta1]
    exact .beta (ihb _) (iha ξ)

theorem LPar.up {σ τ : Nat → Lam} (h : ∀ n, LPar (σ n) (τ n)) : ∀ n, LPar (Lam.up σ n) (Lam.up τ n)
  | 0 => .var 0
  | n + 1 => (h n).ren Nat.succ

theorem LPar.sub {t u : Lam} (h : LPar t u) :
    ∀ {σ τ : Nat → Lam}, (∀ n, LPar (σ n) (τ n)) → LPar (Lam.sub σ t) (Lam.sub τ u) := by
  induction h with
  | var n => intro σ τ hs; exact hs n
  | app _ _ ihf iha => intro σ τ hs; exact .app (ihf hs) (iha hs)
  | lam _ ih => intro σ τ hs; exact .lam (ih (LPar.up hs))
  | @beta b b' a a' _ _ ihb iha =>
    intro σ τ hs
    rw [sub_beta1]
    exact .beta (ihb (LPar.up hs)) (iha hs)

/-- Takahashi's complete development: every redex present, contracted. -/
def ldev : Lam → Lam
  | var n => var n
  | lam b => lam (ldev b)
  | app (lam b) a => sub (beta1 (ldev a)) (ldev b)
  | app (var n) a => app (var n) (ldev a)
  | app (app f g) a => app (ldev (app f g)) (ldev a)

theorem beta1_par {a a' : Lam} (h : LPar a a') : ∀ n, LPar (beta1 a n) (beta1 a' n)
  | 0 => h
  | _ + 1 => .var _

/-- **The triangle.**  Whatever a parallel step reaches, the complete
    development reaches from there. -/
theorem LPar.dev {t u : Lam} (h : LPar t u) : LPar u (ldev t) := by
  induction h with
  | var n => exact .var n
  | lam _ ih => exact .lam ih
  | @beta b b' a a' _ _ ihb iha => exact ihb.sub (beta1_par iha)
  | @app f f' a a' hf _ ihf iha =>
    cases f with
    | var n => cases hf; exact .app (.var n) iha
    | app g k => exact .app ihf iha
    | lam b =>
      cases hf with
      | lam hb =>
        cases ihf with
        | lam hdb => exact .beta hdb iha

theorem lpar_diamond {t u v : Lam} (hu : LPar t u) (hv : LPar t v) :
    ∃ w, LPar u w ∧ LPar v w :=
  ⟨ldev t, hu.dev, hv.dev⟩

/-- Reflexive-transitive parallel reduction is β-reduction. -/
inductive LPars : Lam → Lam → Prop
  | refl (t : Lam) : LPars t t
  | step {t u v : Lam} : LPar t u → LPars u v → LPars t v

theorem LSteps.pars {t u : Lam} (h : LSteps t u) : LPars t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h.par ih

theorem LPars.steps {t u : Lam} (h : LPars t u) : LSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact h.steps.trans ih

theorem lpar_strip {t u v : Lam} (hu : LPar t u) (hv : LPars t v) :
    ∃ w, LPars u w ∧ LPar v w := by
  induction hv generalizing u with
  | refl t => exact ⟨u, .refl u, hu⟩
  | @step t t' v ht' _ ih =>
    obtain ⟨w, hw1, hw2⟩ := lpar_diamond hu ht'
    obtain ⟨z, hz1, hz2⟩ := ih hw2
    exact ⟨z, .step hw1 hz1, hz2⟩

theorem lpars_confluent {t u v : Lam} (hu : LPars t u) (hv : LPars t v) :
    ∃ w, LPars u w ∧ LPars v w := by
  induction hu generalizing v with
  | refl t => exact ⟨v, hv, .refl v⟩
  | @step t t' u ht' _ ih =>
    obtain ⟨w, hw1, hw2⟩ := lpar_strip ht' hv
    obtain ⟨z, hz1, hz2⟩ := ih hw1
    exact ⟨z, hz1, .step hw2 hz2⟩

/-- **Church–Rosser.**  β-reduction is confluent. -/
theorem lsteps_confluent {t u v : Lam} (hu : LSteps t u) (hv : LSteps t v) :
    ∃ w, LSteps u w ∧ LSteps v w := by
  obtain ⟨w, h1, h2⟩ := lpars_confluent hu.pars hv.pars
  exact ⟨w, h1.steps, h2.steps⟩

-- ---------------------------------------------------------------------------
-- Normal forms, and a normalizer
-- ---------------------------------------------------------------------------

/-- No β-step applies. -/
def LNormal (t : Lam) : Prop := ∀ u, ¬ LStep t u

theorem LNormal.steps_eq {t u : Lam} (hn : LNormal t) (h : LSteps t u) : u = t := by
  cases h with
  | refl => rfl
  | step h _ => exact (hn _ h).elim

/-- Terms with a common reduct have at most one normal form between them. -/
theorem normal_unique {t u v : Lam} (hu : LSteps t u) (hv : LSteps t v)
    (nu : LNormal u) (nv : LNormal v) : u = v := by
  obtain ⟨w, hw1, hw2⟩ := lsteps_confluent hu hv
  rw [← nu.steps_eq hw1, ← nv.steps_eq hw2]

/-- Leftmost-outermost: the head redex if any, else the first reducible
    argument, and under a binder its body. -/
def lstep? : Lam → Option Lam
  | var _ => none
  | lam b => (lstep? b).map lam
  | app (lam b) a => some (sub (beta1 a) b)
  | app f a =>
    match lstep? f with
    | some f' => some (app f' a)
    | none => (lstep? a).map (app f)

theorem lstep?_sound : ∀ {t u : Lam}, lstep? t = some u → LStep t u
  | var _, _, h => by cases h
  | lam b, u, h => by
    have h' : (lstep? b).map lam = some u := h
    cases hb : lstep? b with
    | none => rw [hb] at h'; cases h'
    | some b' =>
      rw [hb] at h'
      cases h'
      exact .lam (lstep?_sound hb)
  | app (lam b) a, u, h => by
    cases h
    exact .beta b a
  | app (var n) a, u, h => by
    have h' : (match lstep? (var n) with
      | some f' => some (app f' a)
      | none => (lstep? a).map (app (var n))) = some u := h
    have e : lstep? (var n) = none := rfl
    rw [e] at h'
    cases ha : lstep? a with
    | none => rw [ha] at h'; cases h'
    | some a' =>
      rw [ha] at h'
      cases h'
      exact .appR _ (lstep?_sound ha)
  | app (app f g) a, u, h => by
    have h' : (match lstep? (app f g) with
      | some f' => some (app f' a)
      | none => (lstep? a).map (app (app f g))) = some u := h
    cases hf : lstep? (app f g) with
    | some f' =>
      rw [hf] at h'
      cases h'
      exact .appL a (lstep?_sound hf)
    | none =>
      rw [hf] at h'
      cases ha : lstep? a with
      | none => rw [ha] at h'; cases h'
      | some a' =>
        rw [ha] at h'
        cases h'
        exact .appR _ (lstep?_sound ha)

theorem lstep?_none : ∀ {t : Lam}, lstep? t = none → LNormal t
  | var n, _, u, hs => by cases hs
  | lam b, h, u, hs => by
    have h' : (lstep? b).map lam = none := h
    cases hb : lstep? b with
    | some b' => rw [hb] at h'; cases h'
    | none =>
      cases hs with
      | lam hs' => exact lstep?_none hb _ hs'
  | app (lam b) a, h, _, _ => by cases h
  | app (var n) a, h, u, hs => by
    have h' : (match lstep? (var n) with
      | some f' => some (app f' a)
      | none => (lstep? a).map (app (var n))) = none := h
    have e : lstep? (var n) = none := rfl
    rw [e] at h'
    cases ha : lstep? a with
    | some a' => rw [ha] at h'; cases h'
    | none =>
      cases hs with
      | appL _ hf => cases hf
      | appR _ ha' => exact lstep?_none ha _ ha'
  | app (app f g) a, h, u, hs => by
    have h' : (match lstep? (app f g) with
      | some f' => some (app f' a)
      | none => (lstep? a).map (app (app f g))) = none := h
    cases hf : lstep? (app f g) with
    | some f' => rw [hf] at h'; cases h'
    | none =>
      rw [hf] at h'
      cases ha : lstep? a with
      | some a' => rw [ha] at h'; cases h'
      | none =>
        cases hs with
        | appL _ hf' => exact lstep?_none hf _ hf'
        | appR _ ha' => exact lstep?_none ha _ ha'

/-- At most `k` leftmost-outermost steps, then the normal form if reached. -/
def lnf : Nat → Lam → Option Lam
  | 0, _ => none
  | k + 1, t =>
    match lstep? t with
    | none => some t
    | some t' => lnf k t'

theorem lnf_sound : ∀ {k : Nat} {t u : Lam}, lnf k t = some u → LSteps t u ∧ LNormal u
  | 0, _, _, h => by cases h
  | k + 1, t, u, h => by
    have h' : (match lstep? t with | none => some t | some t' => lnf k t') = some u := h
    cases hs : lstep? t with
    | none =>
      rw [hs] at h'
      cases h'
      exact ⟨.refl t, lstep?_none hs⟩
    | some t' =>
      rw [hs] at h'
      obtain ⟨h1, h2⟩ := lnf_sound h'
      exact ⟨.step (lstep?_sound hs) h1, h2⟩

end Lam
