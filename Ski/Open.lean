import Ski.Weak
open Term

/-!
# Open terms: probing at variables

`OTerm` is `Term` with variables.  Variables are inert: nothing contracts
them, so a term whose spine is headed by a variable, `ONeutral`, is stuck.
They exist for one purpose: to read a value by probing it at *fresh*
variables rather than at arbitrary closed continuations (`Ski/Decode.lean`).

A variable at the head of a probe's end has no internal structure, so an
internal parallel step cannot change it (`OParIs.var0` and its siblings).
That is what makes decoding closed under backward weak reduction, which
exact probing at closed continuations does not obviously give (`PLAN.md`
§3, G1b).  The closed facts are recovered by substitution: head reduction
commutes with substituting terms for variables (`OStep.subst`) and with
closing a term (`OStep.close`).

The module repeats, for `OTerm`, the parts of `Ski/Fuel.lean` and
`Ski/Weak.lean` that decoding needs: a computable contraction and its
iteration (`oiter_sound`, for kernel-checked symbolic runs), weak and
parallel reduction, and the split of a weak reduction into head steps and
internal parallel steps (`owsteps_split`).
-/

inductive OTerm
  | S | K | I
  | var (i : Nat)
  | app (f x : OTerm)
  deriving Inhabited, DecidableEq, Repr

infixl:70 " ⬝ₒ " => OTerm.app

/-- A closed term as an open one. -/
def Term.toO : Term → OTerm
  | .S => .S
  | .K => .K
  | .I => .I
  | .app f x => .app f.toO x.toO

-- ---------------------------------------------------------------------------
-- Head reduction
-- ---------------------------------------------------------------------------

/-- One contraction at the head of the spine, as `Step`. -/
inductive OStep : OTerm → OTerm → Prop
  | S (f g x : OTerm) : OStep (.S ⬝ₒ f ⬝ₒ g ⬝ₒ x) (f ⬝ₒ x ⬝ₒ (g ⬝ₒ x))
  | K (x y : OTerm) : OStep (.K ⬝ₒ x ⬝ₒ y) x
  | I (x : OTerm) : OStep (.I ⬝ₒ x) x
  | left {f f' : OTerm} (x : OTerm) (h : OStep f f') : OStep (f ⬝ₒ x) (f' ⬝ₒ x)

inductive OSteps : OTerm → OTerm → Prop
  | refl (t : OTerm) : OSteps t t
  | step {t t' u : OTerm} (h : OStep t t') (hs : OSteps t' u) : OSteps t u

theorem OSteps.single {t u : OTerm} (h : OStep t u) : OSteps t u := .step h (.refl u)

theorem OSteps.trans {t u v : OTerm} (h₁ : OSteps t u) (h₂ : OSteps u v) : OSteps t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem OSteps.left {f f' : OTerm} (x : OTerm) (h : OSteps f f') :
    OSteps (f ⬝ₒ x) (f' ⬝ₒ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

/-- A spine headed by a variable. -/
inductive ONeutral : OTerm → Prop
  | var (i : Nat) : ONeutral (.var i)
  | app {f : OTerm} (x : OTerm) : ONeutral f → ONeutral (f ⬝ₒ x)

theorem ONeutral.no_step {t u : OTerm} (hn : ONeutral t) (hs : OStep t u) : False := by
  induction hs with
  | S f g x =>
    cases hn with
    | app _ h1 =>
      cases h1 with
      | app _ h2 =>
        cases h2 with
        | app _ h3 => cases h3
  | K x y =>
    cases hn with
    | app _ h1 =>
      cases h1 with
      | app _ h2 => cases h2
  | I x =>
    cases hn with
    | app _ h1 => cases h1
  | left x _ ih =>
    cases hn with
    | app _ h1 => exact ih h1

theorem OStep.no_S2 {f g u : OTerm} (h : OStep (.S ⬝ₒ f ⬝ₒ g) u) : False := by
  cases h with
  | left _ h1 =>
    cases h1 with
    | left _ h2 => cases h2

theorem OStep.no_K1 {x u : OTerm} (h : OStep (.K ⬝ₒ x) u) : False := by
  cases h with
  | left _ h1 => cases h1

theorem OStep.no_I {u : OTerm} (h : OStep .I u) : False := by cases h

/-- Head reduction of open terms is deterministic. -/
theorem OStep.det {t u v : OTerm} (h₁ : OStep t u) (h₂ : OStep t v) : u = v := by
  induction h₁ generalizing v with
  | S f g x =>
    cases h₂ with
    | S => rfl
    | left _ h => exact (h.no_S2).elim
  | K x y =>
    cases h₂ with
    | K => rfl
    | left _ h => exact (h.no_K1).elim
  | I x =>
    cases h₂ with
    | I => rfl
    | left _ h => exact (h.no_I).elim
  | left x h ih =>
    cases h₂ with
    | S => exact (h.no_S2).elim
    | K => exact (h.no_K1).elim
    | I => exact (h.no_I).elim
    | left _ h' => rw [ih h']

/-- Two head reductions from one term to stuck terms end at the same term. -/
theorem osteps_neutral_det {t u v : OTerm} (hu : OSteps t u) (nu : ONeutral u)
    (hv : OSteps t v) (nv : ONeutral v) : u = v := by
  induction hu generalizing v with
  | refl t =>
    cases hv with
    | refl => rfl
    | step h _ => exact (nu.no_step h).elim
  | step h _ ih =>
    cases hv with
    | refl => exact (nv.no_step h).elim
    | step h' hs' =>
      apply ih nu _ nv
      rw [OStep.det h h']
      exact hs'

-- ---------------------------------------------------------------------------
-- Variables: occurrence, freshness, substitution, closing
-- ---------------------------------------------------------------------------

/-- `Occ i t`: the variable `i` occurs in `t`. -/
inductive Occ : Nat → OTerm → Prop
  | var (i : Nat) : Occ i (.var i)
  | left {i : Nat} {f : OTerm} (x : OTerm) : Occ i f → Occ i (f ⬝ₒ x)
  | right {i : Nat} (f : OTerm) {x : OTerm} : Occ i x → Occ i (f ⬝ₒ x)

/-- Every variable of `t` is below `b`. -/
def Fresh (b : Nat) (t : OTerm) : Prop := ∀ i, Occ i t → i < b

theorem fresh_toO (t : Term) (b : Nat) : Fresh b t.toO := by
  intro i h
  induction t with
  | S => cases h
  | K => cases h
  | I => cases h
  | app f x ihf ihx =>
    cases h with
    | left _ h => exact ihf h
    | right _ h => exact ihx h

theorem fresh_exists : ∀ t : OTerm, ∃ b, Fresh b t
  | .S => ⟨0, fun _ h => by cases h⟩
  | .K => ⟨0, fun _ h => by cases h⟩
  | .I => ⟨0, fun _ h => by cases h⟩
  | .var i => ⟨i + 1, fun _ h => by cases h; exact Nat.lt_succ_self _⟩
  | .app f x =>
    match fresh_exists f, fresh_exists x with
    | ⟨b1, h1⟩, ⟨b2, h2⟩ => ⟨b1 + b2, fun i h => by
        cases h with
        | left _ h => exact Nat.lt_of_lt_of_le (h1 i h) (Nat.le_add_right _ _)
        | right _ h => exact Nat.lt_of_lt_of_le (h2 i h) (Nat.le_add_left _ _)⟩

/-- Substitute a term for every variable. -/
def OTerm.subst (τ : Nat → OTerm) : OTerm → OTerm
  | .S => .S
  | .K => .K
  | .I => .I
  | .var i => τ i
  | .app f x => .app (f.subst τ) (x.subst τ)

theorem OStep.subst (τ : Nat → OTerm) {t u : OTerm} (h : OStep t u) :
    OStep (t.subst τ) (u.subst τ) := by
  induction h with
  | S f g x => exact .S _ _ _
  | K x y => exact .K _ _
  | I x => exact .I _
  | left x _ ih => exact .left _ ih

theorem OSteps.subst (τ : Nat → OTerm) {t u : OTerm} (h : OSteps t u) :
    OSteps (t.subst τ) (u.subst τ) := by
  induction h with
  | refl t => exact .refl _
  | step h _ ih => exact .step (h.subst τ) ih

theorem subst_agree {τ₁ τ₂ : Nat → OTerm} :
    ∀ {t : OTerm}, (∀ i, Occ i t → τ₁ i = τ₂ i) → t.subst τ₁ = t.subst τ₂
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var i, h => h i (.var i)
  | .app f x, h => by
    show OTerm.app (f.subst τ₁) (x.subst τ₁) = OTerm.app (f.subst τ₂) (x.subst τ₂)
    rw [subst_agree (fun i hi => h i (.left x hi)), subst_agree (fun i hi => h i (.right f hi))]

/-- Replace every variable by a closed term. -/
def OTerm.close (σ : Nat → Term) : OTerm → Term
  | .S => .S
  | .K => .K
  | .I => .I
  | .var i => σ i
  | .app f x => .app (f.close σ) (x.close σ)

theorem OStep.close (σ : Nat → Term) {t u : OTerm} (h : OStep t u) :
    Step (t.close σ) (u.close σ) := by
  induction h with
  | S f g x => exact .S _ _ _
  | K x y => exact .K _ _
  | I x => exact .I _
  | left x _ ih => exact .left _ ih

theorem OSteps.close (σ : Nat → Term) {t u : OTerm} (h : OSteps t u) :
    Steps (t.close σ) (u.close σ) := by
  induction h with
  | refl t => exact .refl _
  | step h _ ih => exact .step (h.close σ) ih

theorem close_toO (σ : Nat → Term) : ∀ t : Term, t.toO.close σ = t
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f x => by
    show Term.app (f.toO.close σ) (x.toO.close σ) = Term.app f x
    rw [close_toO σ f, close_toO σ x]

theorem toO_close (σ : Nat → Term) :
    ∀ t : OTerm, (t.close σ).toO = t.subst (fun i => (σ i).toO)
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .var _ => rfl
  | .app f x => by
    show OTerm.app ((f.close σ).toO) ((x.close σ).toO) = _
    rw [toO_close σ f, toO_close σ x]
    rfl

/-- `t` applied to the continuations `ks 0, …, ks (m - 1)`. -/
def appF (t : Term) (ks : Nat → Term) : Nat → Term
  | 0 => t
  | m + 1 => appF t ks m ⬝ ks m

/-- The same, for open terms. -/
def appO (t : OTerm) (ks : Nat → OTerm) : Nat → OTerm
  | 0 => t
  | m + 1 => appO t ks m ⬝ₒ ks m

theorem close_appO (σ : Nat → Term) (t : OTerm) (ks : Nat → OTerm) :
    ∀ m, (appO t ks m).close σ = appF (t.close σ) (fun i => (ks i).close σ) m
  | 0 => rfl
  | m + 1 => by
    show Term.app ((appO t ks m).close σ) ((ks m).close σ) = _
    rw [close_appO σ t ks m]
    rfl

theorem subst_appO (τ : Nat → OTerm) (t : OTerm) (ks : Nat → OTerm) :
    ∀ m, (appO t ks m).subst τ = appO (t.subst τ) (fun i => (ks i).subst τ) m
  | 0 => rfl
  | m + 1 => by
    show OTerm.app ((appO t ks m).subst τ) ((ks m).subst τ) = _
    rw [subst_appO τ t ks m]
    rfl

/-- The probe variables from `b` on: `vars b j` is the variable `j + b`. -/
def vars (b : Nat) : Nat → OTerm := fun j => .var (j + b)

/-- Below `b0` as `τ`; from `b0` on, the variables from `b` on.  Moves a
    probe made at the fresh variables `vars b0` to `vars b`. -/
def shiftAt (τ : Nat → OTerm) (b0 b : Nat) : Nat → OTerm :=
  fun j => if j < b0 then τ j else .var (j - b0 + b)

theorem shiftAt_at (τ : Nat → OTerm) (b0 b i : Nat) : shiftAt τ b0 b (i + b0) = .var (i + b) := by
  unfold shiftAt
  rw [if_neg (Nat.not_lt.mpr (Nat.le_add_left b0 i)), Nat.add_sub_cancel]

theorem subst_shiftAt {τ : Nat → OTerm} {b0 b : Nat} {t : OTerm} (ht : Fresh b0 t) :
    t.subst (shiftAt τ b0 b) = t.subst τ :=
  subst_agree (fun i hi => by simp [shiftAt, ht i hi])

-- ---------------------------------------------------------------------------
-- Kernel-checked symbolic runs of open terms
-- ---------------------------------------------------------------------------

/-- The computable contraction on open terms. -/
def ostep? : OTerm → Option OTerm
  | .app f x =>
    match ostep? f with
    | some f' => some (.app f' x)
    | none =>
      match f with
      | .I => some x
      | .app .K y => some y
      | .app (.app .S y) z => some (.app (.app y x) (.app z x))
      | _ => none
  | _ => none

theorem ostep?_sound : ∀ {t u : OTerm}, ostep? t = some u → OStep t u
  | .S, _, h => by simp [ostep?] at h
  | .K, _, h => by simp [ostep?] at h
  | .I, _, h => by simp [ostep?] at h
  | .var _, _, h => by simp [ostep?] at h
  | .app f x, u, h => by
    simp only [ostep?] at h
    split at h
    · rename_i f' hf
      cases h
      exact .left x (ostep?_sound hf)
    · split at h
      · cases h; exact .I _
      · cases h; exact .K _ _
      · cases h; exact .S _ _ _
      · simp at h

/-- Exactly `k` contractions, if they exist. -/
def oiter : Nat → OTerm → Option OTerm
  | 0, t => some t
  | k + 1, t => (ostep? t).bind (oiter k)

theorem oiter_sound : ∀ {k : Nat} {t u : OTerm}, oiter k t = some u → OSteps t u
  | 0, t, u, h => by cases h; exact .refl t
  | k + 1, t, u, h => by
    simp only [oiter] at h
    cases hs : ostep? t with
    | none => simp [hs] at h
    | some t' =>
      rw [hs] at h
      exact .step (ostep?_sound hs) (oiter_sound h)

-- ---------------------------------------------------------------------------
-- Weak and parallel reduction of open terms
-- ---------------------------------------------------------------------------

inductive OWStep : OTerm → OTerm → Prop
  | S (f g x : OTerm) : OWStep (.S ⬝ₒ f ⬝ₒ g ⬝ₒ x) (f ⬝ₒ x ⬝ₒ (g ⬝ₒ x))
  | K (x y : OTerm) : OWStep (.K ⬝ₒ x ⬝ₒ y) x
  | I (x : OTerm) : OWStep (.I ⬝ₒ x) x
  | left {f f' : OTerm} (x : OTerm) (h : OWStep f f') : OWStep (f ⬝ₒ x) (f' ⬝ₒ x)
  | right (f : OTerm) {x x' : OTerm} (h : OWStep x x') : OWStep (f ⬝ₒ x) (f ⬝ₒ x')

inductive OWSteps : OTerm → OTerm → Prop
  | refl (t : OTerm) : OWSteps t t
  | step {t t' u : OTerm} (h : OWStep t t') (hs : OWSteps t' u) : OWSteps t u

theorem OWSteps.trans {t u v : OTerm} (h₁ : OWSteps t u) (h₂ : OWSteps u v) : OWSteps t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

theorem OWSteps.left {f f' : OTerm} (x : OTerm) (h : OWSteps f f') :
    OWSteps (f ⬝ₒ x) (f' ⬝ₒ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

theorem OWSteps.right (f : OTerm) {x x' : OTerm} (h : OWSteps x x') :
    OWSteps (f ⬝ₒ x) (f ⬝ₒ x') := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.right f h) ih

theorem OWSteps.app {f f' x x' : OTerm} (hf : OWSteps f f') (hx : OWSteps x x') :
    OWSteps (f ⬝ₒ x) (f' ⬝ₒ x') :=
  (OWSteps.left x hf).trans (OWSteps.right f' hx)

theorem OWSteps.appO {t u : OTerm} (ks : Nat → OTerm) (h : OWSteps t u) :
    ∀ m, OWSteps (appO t ks m) (appO u ks m)
  | 0 => h
  | m + 1 => OWSteps.left (ks m) (OWSteps.appO ks h m)

theorem OStep.weak {t u : OTerm} (h : OStep t u) : OWStep t u := by
  induction h with
  | S f g x => exact .S f g x
  | K x y => exact .K x y
  | I x => exact .I x
  | left x _ ih => exact .left x ih

theorem OSteps.weak {t u : OTerm} (h : OSteps t u) : OWSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h.weak ih

/-- A weak step of closed terms is one of their open images. -/
theorem WStep.toO {t u : Term} (h : WStep t u) : OWStep t.toO u.toO := by
  induction h with
  | S f g x => exact .S _ _ _
  | K x y => exact .K _ _
  | I x => exact .I _
  | left x _ ih => exact .left _ ih
  | right f _ ih => exact .right _ ih

theorem WSteps.toO {t u : Term} (h : WSteps t u) : OWSteps t.toO u.toO := by
  induction h with
  | refl t => exact .refl _
  | step h _ ih => exact .step h.toO ih

/-- Weak reduction creates no variables. -/
theorem OWStep.occ {t u : OTerm} (h : OWStep t u) : ∀ {i}, Occ i u → Occ i t := by
  induction h with
  | S f g x =>
    intro i hi
    cases hi with
    | left _ h1 =>
      cases h1 with
      | left _ h2 => exact .left _ (.left _ (.right _ h2))
      | right _ h2 => exact .right _ h2
    | right _ h1 =>
      cases h1 with
      | left _ h2 => exact .left _ (.right _ h2)
      | right _ h2 => exact .right _ h2
  | K x y => exact fun hi => .left _ (.right _ hi)
  | I x => exact fun hi => .right _ hi
  | left x _ ih =>
    intro i hi
    cases hi with
    | left _ h1 => exact .left _ (ih h1)
    | right _ h1 => exact .right _ h1
  | right f _ ih =>
    intro i hi
    cases hi with
    | left _ h1 => exact .left _ h1
    | right _ h1 => exact .right _ (ih h1)

theorem Fresh.of_owsteps {b : Nat} {t u : OTerm} (ht : Fresh b t) (h : OWSteps t u) :
    Fresh b u := by
  induction h with
  | refl _ => exact ht
  | step h _ ih => exact ih (fun i hi => ht i (h.occ hi))

inductive OPar : OTerm → OTerm → Prop
  | S : OPar .S .S
  | K : OPar .K .K
  | I : OPar .I .I
  | var (i : Nat) : OPar (.var i) (.var i)
  | app {f f' x x' : OTerm} : OPar f f' → OPar x x' → OPar (f ⬝ₒ x) (f' ⬝ₒ x')
  | K2 {x x' : OTerm} (y : OTerm) : OPar x x' → OPar (.K ⬝ₒ x ⬝ₒ y) x'
  | I1 {x x' : OTerm} : OPar x x' → OPar (.I ⬝ₒ x) x'
  | S3 {f f' g g' x x' : OTerm} : OPar f f' → OPar g g' → OPar x x' →
      OPar (.S ⬝ₒ f ⬝ₒ g ⬝ₒ x) (f' ⬝ₒ x' ⬝ₒ (g' ⬝ₒ x'))

theorem OPar.refl : ∀ t : OTerm, OPar t t
  | .S => .S
  | .K => .K
  | .I => .I
  | .var i => .var i
  | .app f x => .app (OPar.refl f) (OPar.refl x)

theorem OWStep.par {t u : OTerm} (h : OWStep t u) : OPar t u := by
  induction h with
  | S f g x => exact .S3 (.refl f) (.refl g) (.refl x)
  | K x y => exact .K2 y (.refl x)
  | I x => exact .I1 (.refl x)
  | left x _ ih => exact .app ih (.refl x)
  | right f _ ih => exact .app (.refl f) ih

theorem OPar.wsteps {t u : OTerm} (h : OPar t u) : OWSteps t u := by
  induction h with
  | S => exact .refl _
  | K => exact .refl _
  | I => exact .refl _
  | var _ => exact .refl _
  | app _ _ ihf ihx => exact OWSteps.app ihf ihx
  | K2 y _ ih => exact .step (.K _ y) ih
  | I1 _ ih => exact .step (.I _) ih
  | S3 _ _ _ ihf ihg ihx =>
    exact .step (.S _ _ _) (OWSteps.app (OWSteps.app ihf ihx) (OWSteps.app ihg ihx))

/-- Parallel reduction that keeps the spine. -/
inductive OParI : OTerm → OTerm → Prop
  | S : OParI .S .S
  | K : OParI .K .K
  | I : OParI .I .I
  | var (i : Nat) : OParI (.var i) (.var i)
  | app {f f' x x' : OTerm} : OParI f f' → OPar x x' → OParI (f ⬝ₒ x) (f' ⬝ₒ x')

theorem OParI.par {t u : OTerm} (h : OParI t u) : OPar t u := by
  induction h with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | var i => exact .var i
  | app _ hx ih => exact .app ih hx

theorem opar_split {t u : OTerm} (h : OPar t u) : ∃ t', OSteps t t' ∧ OParI t' u := by
  induction h with
  | S => exact ⟨_, .refl _, .S⟩
  | K => exact ⟨_, .refl _, .K⟩
  | I => exact ⟨_, .refl _, .I⟩
  | var i => exact ⟨_, .refl _, .var i⟩
  | @app f f' x x' _ hx ihf _ =>
    cases ihf with
    | intro f1 h1 => exact ⟨f1 ⬝ₒ x, OSteps.left x h1.1, .app h1.2 hx⟩
  | @K2 x x' y _ ih =>
    cases ih with
    | intro x1 h1 => exact ⟨x1, .step (.K x y) h1.1, h1.2⟩
  | @I1 x x' _ ih =>
    cases ih with
    | intro x1 h1 => exact ⟨x1, .step (.I x) h1.1, h1.2⟩
  | @S3 f f' g g' x x' _ hg hx ihf _ _ =>
    cases ihf with
    | intro f1 h1 =>
      exact ⟨f1 ⬝ₒ x ⬝ₒ (g ⬝ₒ x),
        .step (.S f g x) (OSteps.left (g ⬝ₒ x) (OSteps.left x h1.1)),
        .app (.app h1.2 hx) (.app hg hx)⟩

theorem oparI_step {u w : OTerm} (hs : OStep u w) :
    ∀ {t : OTerm}, OParI t u → ∃ w', OStep t w' ∧ OPar w' w := by
  induction hs with
  | S f g x =>
    intro t hi
    cases hi with
    | app h1 hx =>
      cases h1 with
      | app h2 hg =>
        cases h2 with
        | app h3 hf =>
          cases h3
          exact ⟨_, .S _ _ _, .app (.app hf hx) (.app hg hx)⟩
  | K x y =>
    intro t hi
    cases hi with
    | app h1 _ =>
      cases h1 with
      | app h2 hx =>
        cases h2
        exact ⟨_, .K _ _, hx⟩
  | I x =>
    intro t hi
    cases hi with
    | app h1 hx =>
      cases h1
      exact ⟨_, .I _, hx⟩
  | left x _ ih =>
    intro t hi
    cases hi with
    | app hf hx =>
      cases ih hf with
      | intro w0 h0 => exact ⟨_, .left _ h0.1, .app h0.2 hx⟩

theorem opar_step {t u w : OTerm} (hp : OPar t u) (hs : OStep u w) :
    ∃ w', OSteps t w' ∧ OPar w' w := by
  cases opar_split hp with
  | intro t1 h1 =>
    cases oparI_step hs h1.2 with
    | intro w0 h0 => exact ⟨w0, h1.1.trans (.single h0.1), h0.2⟩

theorem opar_steps {u w : OTerm} (hs : OSteps u w) :
    ∀ {t : OTerm}, OPar t u → ∃ w', OSteps t w' ∧ OPar w' w := by
  induction hs with
  | refl _ => exact fun hp => ⟨_, .refl _, hp⟩
  | step h _ ih =>
    intro t hp
    cases opar_step hp h with
    | intro a ha =>
      cases ih ha.2 with
      | intro w' hw => exact ⟨w', ha.1.trans hw.1, hw.2⟩

inductive OParIs : OTerm → OTerm → Prop
  | refl (t : OTerm) : OParIs t t
  | step {t t' u : OTerm} (h : OParI t t') (hs : OParIs t' u) : OParIs t u

/-- Any weak reduction of open terms is head steps followed by internal
    parallel steps. -/
theorem owsteps_split {t v : OTerm} (h : OWSteps t v) : ∃ t', OSteps t t' ∧ OParIs t' v := by
  induction h with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | step s _ ih =>
    cases ih with
    | intro t1 h1 =>
      cases opar_steps h1.1 s.par with
      | intro w hw =>
        cases opar_split hw.2 with
        | intro w0 h0 => exact ⟨w0, hw.1.trans h0.1, .step h0.2 h1.2⟩

-- ---------------------------------------------------------------------------
-- An internal step cannot change a variable at the head
-- ---------------------------------------------------------------------------

theorem OParIs.var0 {w v : OTerm} (h : OParIs w v) : ∀ {c : Nat}, v = .var c → w = .var c := by
  induction h with
  | refl _ => exact fun e => e
  | step h _ ih =>
    intro c e
    have e' := ih e
    subst e'
    cases h
    rfl

theorem OParIs.var1 {w v : OTerm} (h : OParIs w v) :
    ∀ {c : Nat} {H : OTerm}, v = .var c ⬝ₒ H → ∃ H', w = .var c ⬝ₒ H' ∧ OWSteps H' H := by
  induction h with
  | refl _ => exact fun e => ⟨_, e, .refl _⟩
  | step h _ ih =>
    intro c H e
    cases ih e with
    | intro H'' h'' =>
      cases h''.1
      cases h with
      | app h1 hx =>
        cases h1
        exact ⟨_, rfl, hx.wsteps.trans h''.2⟩

theorem OParIs.var2 {w v : OTerm} (h : OParIs w v) :
    ∀ {c : Nat} {H G : OTerm}, v = .var c ⬝ₒ H ⬝ₒ G →
      ∃ H' G', w = .var c ⬝ₒ H' ⬝ₒ G' ∧ OWSteps H' H ∧ OWSteps G' G := by
  induction h with
  | refl _ => exact fun e => ⟨_, _, e, .refl _, .refl _⟩
  | step h _ ih =>
    intro c H G e
    cases ih e with
    | intro H'' h'' =>
      cases h'' with
      | intro G'' h'' =>
        cases h''.1
        cases h with
        | app h1 hg =>
          cases h1 with
          | app h2 hh =>
            cases h2
            exact ⟨_, _, rfl, hh.wsteps.trans h''.2.1, hg.wsteps.trans h''.2.2⟩

/-- A weak reduction ending in a variable-headed term is head steps to a
    term with the same variable at the head: `0`, `1` or `2` arguments. -/
theorem owsteps_var0 {t : OTerm} {c : Nat} (h : OWSteps t (.var c)) : OSteps t (.var c) := by
  cases owsteps_split h with
  | intro t' h' => exact (h'.2.var0 rfl) ▸ h'.1

theorem owsteps_var1 {t H : OTerm} {c : Nat} (h : OWSteps t (.var c ⬝ₒ H)) :
    ∃ H', OSteps t (.var c ⬝ₒ H') ∧ OWSteps H' H := by
  cases owsteps_split h with
  | intro t' h' =>
    cases h'.2.var1 rfl with
    | intro H' hH => exact ⟨H', hH.1 ▸ h'.1, hH.2⟩

theorem owsteps_var2 {t H G : OTerm} {c : Nat} (h : OWSteps t (.var c ⬝ₒ H ⬝ₒ G)) :
    ∃ H' G', OSteps t (.var c ⬝ₒ H' ⬝ₒ G') ∧ OWSteps H' H ∧ OWSteps G' G := by
  cases owsteps_split h with
  | intro t' h' =>
    cases h'.2.var2 rfl with
    | intro H' hH =>
      cases hH with
      | intro G' hG => exact ⟨H', G', hG.1 ▸ h'.1, hG.2.1, hG.2.2⟩
