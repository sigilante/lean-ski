import Ski.Abs
open Term

/-!
# Realizability: a combinatory logic of proofs

Part II's logic, over closed `SKI` terms.  A formula is an NP atom, a
conjunction, a disjunction, an implication, or an existential over
witnesses.  `Real φ r` reads "`r` realizes `φ`", with Kleene's clauses
stated for combinators:

- An atom `atom V x` is realized by a witness `w` exactly when the verifier
  accepts, `V ⬝ x ⬝ w` evaluating to `K` (true); see `real_atom_iff`.
- A conjunction is realized by a Scott pair.
- A disjunction is realized by a Scott injection.
- An implication is realized by a witness map.
- `∃ w. φ w` is realized by a pair of a witness and a realizer of `φ w`.

Realizability is closed under backward weak reduction (`Real.back`).  So a
realizer need not be a value, only something that weakly reduces to one.

**Soundness** (`soundness`): a term typed by the combinator rules realizes
its type.  `S`, `K` and `I` carry the Hilbert axioms, and application is
modus ponens.  Pairing, projection, injection, case and packing are
Scott-encoded constants, so the basis stays three combinators.

**Completeness** (`completeness`): a natural-deduction proof, with λ, is
compiled by `skijack`'s bracket abstraction (`abs`).  The compiled term
has the proof's type in the combinator system (`abs_types`).  This is
Curry's theorem, instantiated.

Existential elimination is not in this fragment.  In combinator form it
applies the pair to a function of type `∀ w. φ w → C`, and this logic has
no `∀` over witnesses; §logic of the paper records the choice.
-/

/-- Formulas. -/
inductive Form
  | atom (V x : Term)
  | and (A B : Form)
  | or (A B : Form)
  | imp (A B : Form)
  | ex (φ : Term → Form)

/-- `Real φ r`: `r` realizes `φ`. -/
def Real : Form → Term → Prop
  | .atom V x, r => WSteps (V ⬝ x ⬝ r) K
  | .and A B, r => ∃ a b, (∀ k, WSteps (r ⬝ k) (k ⬝ a ⬝ b)) ∧ Real A a ∧ Real B b
  | .or A B, r =>
    (∃ a, (∀ f g, WSteps (r ⬝ f ⬝ g) (f ⬝ a)) ∧ Real A a) ∨
    (∃ b, (∀ f g, WSteps (r ⬝ f ⬝ g) (g ⬝ b)) ∧ Real B b)
  | .imp A B, r => ∀ a, Real A a → Real B (r ⬝ a)
  | .ex φ, r => ∃ w b, (∀ k, WSteps (r ⬝ k) (k ⬝ w ⬝ b)) ∧ Real (φ w) b

/-- **Realizability is closed under backward weak reduction.** -/
theorem Real.back : ∀ (A : Form) {r r' : Term}, WSteps r r' → Real A r' → Real A r
  | .atom _ _, _, _, h, hr => (WSteps.right _ h).trans hr
  | .and _ _, _, _, h, hr => by
    cases hr with
    | intro a hr =>
      cases hr with
      | intro b hr => exact ⟨a, b, fun k => (WSteps.left k h).trans (hr.1 k), hr.2⟩
  | .or _ _, _, _, h, hr => by
    cases hr with
    | inl hl =>
      cases hl with
      | intro a ha =>
        exact .inl ⟨a, fun f g => (WSteps.left g (WSteps.left f h)).trans (ha.1 f g), ha.2⟩
    | inr hr =>
      cases hr with
      | intro b hb =>
        exact .inr ⟨b, fun f g => (WSteps.left g (WSteps.left f h)).trans (hb.1 f g), hb.2⟩
  | .imp _ B, _, _, h, hr => fun a ha => Real.back B (WSteps.left a h) (hr a ha)
  | .ex _, _, _, h, hr => by
    cases hr with
    | intro w hr =>
      cases hr with
      | intro b hr => exact ⟨w, b, fun k => (WSteps.left k h).trans (hr.1 k), hr.2⟩

-- ---------------------------------------------------------------------------
-- Atoms: the verifier accepts
-- ---------------------------------------------------------------------------

/-- A weak step from a weak head normal form stays one, and never reaches `K`. -/
theorem Whnf.wstep {v u : Term} (hv : Whnf v) (h : WStep v u) : Whnf u ∧ u ≠ Term.K := by
  cases hv with
  | S => cases h
  | K => cases h
  | I => cases h
  | S1 x =>
    cases h with
    | left _ h => cases h
    | right _ _ => exact ⟨.S1 _, fun e => by cases e⟩
  | S2 x y =>
    cases h with
    | left _ h =>
      cases h with
      | left _ h => cases h
      | right _ _ => exact ⟨.S2 _ _, fun e => by cases e⟩
    | right _ _ => exact ⟨.S2 _ _, fun e => by cases e⟩
  | K1 x =>
    cases h with
    | left _ h => cases h
    | right _ _ => exact ⟨.K1 _, fun e => by cases e⟩

/-- A weak head normal form that weakly reduces to `K` is `K`. -/
theorem Whnf.wsteps_K {v : Term} (hv : Whnf v) (h : WSteps v Term.K) : v = Term.K := by
  generalize hk : Term.K = k at h
  induction h with
  | refl => rfl
  | step s _ ih => exact absurd ((ih (hv.wstep s).1 hk).trans hk.symm) (hv.wstep s).2

/-- **An atom is realized by an accepted witness.**  Realizability of an atom
    is evaluation of its verifier to `K`, in normal order. -/
theorem real_atom_iff {V x w : Term} : Real (.atom V x) w ↔ Eval (V ⬝ x ⬝ w) K := by
  constructor
  · intro h
    cases eval_back h ⟨.refl K, .K⟩ with
    | intro v hv =>
      have e := hv.1.2.wsteps_K hv.2
      rw [e] at hv
      exact hv.1
  · intro h
    exact h.1.weak

/-- A witness on which the verifier diverges realizes nothing. -/
theorem real_atom_diverges {V x w : Term} (hd : Diverges (V ⬝ x ⬝ w)) :
    ¬ Real (.atom V x) w :=
  fun h => hd K (real_atom_iff.1 h)

-- ---------------------------------------------------------------------------
-- The Scott constants
-- ---------------------------------------------------------------------------

/-- A closed term by bracket abstraction over the formals `xs`. -/
def lam (xs : List Nat) (M : OTerm) : Term := (absN xs M).close (fun _ => I)

theorem lam_beta (xs : List Nat) (M : OTerm) (Ns : List Term) (hl : Ns.length = xs.length) :
    WSteps (appT (lam xs M) Ns) (M.close (overrideC (fun _ => I) xs Ns)) :=
  absN_beta_close xs M _ Ns hl

local notation "v0" => OTerm.var 0
local notation "v1" => OTerm.var 1
local notation "v2" => OTerm.var 2

/-- `λ a b k. k a b` -/
def pairT : Term := lam [0, 1, 2] (v2 ⬝ₒ v0 ⬝ₒ v1)
/-- `λ p. p K` -/
def fstT : Term := lam [0] (v0 ⬝ₒ .K)
/-- `λ p. p (K I)` -/
def sndT : Term := lam [0] (v0 ⬝ₒ (.K ⬝ₒ .I))
/-- `λ a f g. f a` -/
def inlT : Term := lam [0, 1, 2] (v1 ⬝ₒ v0)
/-- `λ b f g. g b` -/
def inrT : Term := lam [0, 1, 2] (v2 ⬝ₒ v0)
/-- `λ s f g. s f g` -/
def caseT : Term := lam [0, 1, 2] (v0 ⬝ₒ v1 ⬝ₒ v2)

theorem pairT_beta (a b k : Term) : WSteps (pairT ⬝ a ⬝ b ⬝ k) (k ⬝ a ⬝ b) :=
  lam_beta [0, 1, 2] _ [a, b, k] rfl

theorem fstT_beta (p : Term) : WSteps (fstT ⬝ p) (p ⬝ K) := lam_beta [0] _ [p] rfl

theorem sndT_beta (p : Term) : WSteps (sndT ⬝ p) (p ⬝ (K ⬝ I)) := lam_beta [0] _ [p] rfl

theorem inlT_beta (a f g : Term) : WSteps (inlT ⬝ a ⬝ f ⬝ g) (f ⬝ a) :=
  lam_beta [0, 1, 2] _ [a, f, g] rfl

theorem inrT_beta (b f g : Term) : WSteps (inrT ⬝ b ⬝ f ⬝ g) (g ⬝ b) :=
  lam_beta [0, 1, 2] _ [b, f, g] rfl

theorem caseT_beta (s f g : Term) : WSteps (caseT ⬝ s ⬝ f ⬝ g) (s ⬝ f ⬝ g) :=
  lam_beta [0, 1, 2] _ [s, f, g] rfl

-- ---------------------------------------------------------------------------
-- The combinator system and its soundness
-- ---------------------------------------------------------------------------

/-- Typing of closed proofs: the Hilbert axioms for `S`, `K`, `I`, modus
    ponens, the Scott constants, and an atom's accepted witness. -/
inductive Types : Term → Form → Prop
  | S {A B C : Form} :
      Types S (.imp (.imp A (.imp B C)) (.imp (.imp A B) (.imp A C)))
  | K {A B : Form} : Types K (.imp A (.imp B A))
  | I {A : Form} : Types I (.imp A A)
  | app {t u : Term} {A B : Form} : Types t (.imp A B) → Types u A → Types (t ⬝ u) B
  | pair {A B : Form} : Types pairT (.imp A (.imp B (.and A B)))
  | fst {A B : Form} : Types fstT (.imp (.and A B) A)
  | snd {A B : Form} : Types sndT (.imp (.and A B) B)
  | inl {A B : Form} : Types inlT (.imp A (.or A B))
  | inr {A B : Form} : Types inrT (.imp B (.or A B))
  | case {A B C : Form} :
      Types caseT (.imp (.or A B) (.imp (.imp A C) (.imp (.imp B C) C)))
  | pack {φ : Term → Form} (w : Term) : Types (pairT ⬝ w) (.imp (φ w) (.ex φ))
  | witness {V x w : Term} : WSteps (V ⬝ x ⬝ w) K → Types w (.atom V x)

theorem K_beta (a b : Term) : WSteps (K ⬝ a ⬝ b) a := .single (.K a b)

theorem KI_beta (a b : Term) : WSteps (K ⬝ I ⬝ a ⬝ b) b :=
  (WSteps.single (WStep.left b (.K I a))).trans (.single (.I b))

/-- **Soundness**: a typed closed term realizes its type. -/
theorem soundness {t : Term} {A : Form} (h : Types t A) : Real A t := by
  induction h with
  | S =>
    intro f hf g hg a ha
    exact Real.back _ (.single (.S f g a)) (hf a ha (g ⬝ a) (hg a ha))
  | K => intro a ha b _; exact Real.back _ (K_beta a b) ha
  | I => intro a ha; exact Real.back _ (.single (.I a)) ha
  | app _ _ iht ihu => exact iht _ ihu
  | pair => intro a ha b hb; exact ⟨a, b, fun k => pairT_beta a b k, ha, hb⟩
  | @fst A B =>
    intro p hp
    cases hp with
    | intro a hp =>
      cases hp with
      | intro b hp =>
        exact Real.back A ((fstT_beta p).trans ((hp.1 K).trans (K_beta a b))) hp.2.1
  | @snd A B =>
    intro p hp
    cases hp with
    | intro a hp =>
      cases hp with
      | intro b hp =>
        exact Real.back B ((sndT_beta p).trans ((hp.1 (K ⬝ I)).trans (KI_beta a b))) hp.2.2
  | inl => intro a ha; exact .inl ⟨a, fun f g => inlT_beta a f g, ha⟩
  | inr => intro b hb; exact .inr ⟨b, fun f g => inrT_beta b f g, hb⟩
  | @case A B C =>
    intro s hs f hf g hg
    cases hs with
    | inl hl =>
      cases hl with
      | intro a ha =>
        exact Real.back C ((caseT_beta s f g).trans (ha.1 f g)) (hf a ha.2)
    | inr hr =>
      cases hr with
      | intro b hb =>
        exact Real.back C ((caseT_beta s f g).trans (hb.1 f g)) (hg b hb.2)
  | pack w => intro b hb; exact ⟨w, b, fun k => pairT_beta w b k, hb⟩
  | witness h => exact h

-- ---------------------------------------------------------------------------
-- Open terms, and abstraction preserves types
-- ---------------------------------------------------------------------------

/-- `Γ` with `A` for `x`. -/
def extF (Γ : Nat → Form) (x : Nat) (A : Form) : Nat → Form :=
  fun y => if y = x then A else Γ y

/-- Typing of open combinator terms: variables typed by `Γ`, closed typed
    terms, and modus ponens. -/
inductive OTypes (Γ : Nat → Form) : OTerm → Form → Prop
  | var (n : Nat) : OTypes Γ (.var n) (Γ n)
  | closed {t : Term} {A : Form} : Types t A → OTypes Γ t.toO A
  | app {f a : OTerm} {A B : Form} : OTypes Γ f (.imp A B) → OTypes Γ a A →
      OTypes Γ (f ⬝ₒ a) B

/-- Typing depends on the context only at the variables that occur. -/
theorem OTypes.congr {Γ Γ' : Nat → Form} {M : OTerm} {B : Form} (h : OTypes Γ M B)
    (hc : ∀ y, M.mem y = true → Γ y = Γ' y) : OTypes Γ' M B := by
  induction h with
  | var n =>
    rw [hc n (mem_var.2 rfl)]
    exact .var n
  | closed ht => exact .closed ht
  | app _ _ ihf iha =>
    exact .app (ihf fun y hy => hc y (by simp [OTerm.mem, hy]))
      (iha fun y hy => hc y (by simp [OTerm.mem, hy]))

theorem toO_ne_var (t : Term) (y : Nat) : t.toO ≠ .var y := by
  cases t <;> intro e <;> cases e

theorem OTypes.var_inv {Γ : Nat → Form} {M : OTerm} {B : Form} (h : OTypes Γ M B) :
    ∀ {y}, M = .var y → B = Γ y := by
  cases h with
  | var n => intro y e; cases e; rfl
  | closed _ => intro y e; exact absurd e (toO_ne_var _ _)
  | app _ _ => intro y e; cases e

theorem OTypes.app_inv {Γ : Nat → Form} {M : OTerm} {B : Form} {x : Nat} (h : OTypes Γ M B)
    (hx : M.mem x = true) :
    ∀ {e f}, M = e ⬝ₒ f → ∃ A', OTypes Γ e (.imp A' B) ∧ OTypes Γ f A' := by
  cases h with
  | var n => intro e f h; cases h
  | @closed t _ _ => intro e f _; rw [mem_toO x t] at hx; cases hx
  | app hf ha => intro e f h; cases h; exact ⟨_, hf, ha⟩

/-- **Abstraction preserves types**: if `M : B` with `x : A`, then
    `[x] M : A → B`. -/
theorem abs_types {Γ : Nat → Form} {x : Nat} {A : Form} :
    ∀ (M : OTerm) {B : Form}, OTypes (extF Γ x A) M B → OTypes Γ (abs x M) (.imp A B)
  | M, B, h => by
    cases hm : M.mem x with
    | false =>
      rw [abs_of_not_mem hm]
      refine .app (.closed .K) (h.congr fun y hy => ?_)
      have hyx : y ≠ x := fun e => by rw [e, hm] at hy; cases hy
      exact if_neg hyx
    | true =>
      match M, h, hm with
      | .var y, h, hm =>
        have hyx : y = x := mem_var.1 hm
        subst hyx
        have hB : B = A := by rw [h.var_inv rfl]; exact if_pos rfl
        rw [hB, abs_var, if_pos rfl]
        exact .closed .I
      | .app e f, h, hm =>
        cases h.app_inv hm rfl with
        | intro A' hef =>
          by_cases he : f = .var x ∧ e.mem x = false
          · have hA : A' = A := by
              rw [hef.2.var_inv he.1]; exact if_pos rfl
            rw [abs_app, if_neg (by rw [hm]; decide), if_pos he]
            rw [hA] at hef
            refine hef.1.congr fun y hy => ?_
            have hyx : y ≠ x := fun e' => by rw [e', he.2] at hy; cases hy
            exact if_neg hyx
          · rw [abs_app, if_neg (by rw [hm]; decide), if_neg he]
            exact .app (.app (.closed .S) (abs_types e hef.1)) (abs_types f hef.2)

/-- Closing an open typed term with typed closed terms. -/
theorem OTypes.close {Γ : Nat → Form} {M : OTerm} {A : Form} (h : OTypes Γ M A)
    {γ : Nat → Term} (hγ : ∀ n, M.mem n = true → Types (γ n) (Γ n)) :
    Types (M.close γ) A := by
  induction h with
  | var n => exact hγ n (mem_var.2 rfl)
  | closed ht => rw [close_toO]; exact ht
  | app _ _ ihf iha =>
    exact .app (ihf fun n hn => hγ n (by simp [OTerm.mem, hn]))
      (iha fun n hn => hγ n (by simp [OTerm.mem, hn]))

/-- Realizers for the context make the closed term a realizer. -/
theorem OTypes.real {Γ : Nat → Form} {M : OTerm} {A : Form} (h : OTypes Γ M A)
    {γ : Nat → Term} (hγ : ∀ n, Real (Γ n) (γ n)) : Real A (M.close γ) := by
  induction h with
  | var n => exact hγ n
  | closed ht => rw [close_toO]; exact soundness ht
  | app _ _ ihf iha => exact ihf _ iha

-- ---------------------------------------------------------------------------
-- Natural deduction, compiled
-- ---------------------------------------------------------------------------

/-- Natural-deduction proof terms: variables, λ, application, and closed
    typed constants. -/
inductive PT
  | var (n : Nat)
  | lam (x : Nat) (b : PT)
  | app (f a : PT)
  | const (t : Term)

/-- Compilation by bracket abstraction. -/
def PT.compile : PT → OTerm
  | .var n => .var n
  | .lam x b => abs x b.compile
  | .app f a => f.compile ⬝ₒ a.compile
  | .const t => t.toO

/-- The natural-deduction rules: assumption, implication introduction,
    modus ponens, and constants. -/
inductive ND : (Nat → Form) → PT → Form → Prop
  | var (Γ : Nat → Form) (n : Nat) : ND Γ (.var n) (Γ n)
  | lam {Γ : Nat → Form} {x : Nat} {A B : Form} {b : PT} :
      ND (extF Γ x A) b B → ND Γ (.lam x b) (.imp A B)
  | app {Γ : Nat → Form} {f a : PT} {A B : Form} :
      ND Γ f (.imp A B) → ND Γ a A → ND Γ (.app f a) B
  | const {Γ : Nat → Form} {t : Term} {A : Form} : Types t A → ND Γ (.const t) A

theorem nd_compile {Γ : Nat → Form} {p : PT} {A : Form} (h : ND Γ p A) :
    OTypes Γ p.compile A := by
  induction h with
  | var Γ n => exact .var n
  | lam _ ih => exact abs_types _ ih
  | app _ _ ihf iha => exact .app ihf iha
  | const ht => exact .closed ht

/-- **Completeness**: a natural-deduction proof compiles, by bracket
    abstraction, to a combinator proof of the same formula, once its free
    assumptions are discharged by combinator proofs. -/
theorem completeness {Γ : Nat → Form} {p : PT} {A : Form} (h : ND Γ p A)
    {γ : Nat → Term} (hγ : ∀ n, p.compile.mem n = true → Types (γ n) (Γ n)) :
    Types (p.compile.close γ) A :=
  (nd_compile h).close hγ

/-- A closed natural-deduction proof compiles to a combinator proof. -/
theorem completeness_closed {Γ : Nat → Form} {p : PT} {A : Form} (h : ND Γ p A)
    (hc : ∀ n, p.compile.mem n = false) (γ : Nat → Term) : Types (p.compile.close γ) A :=
  completeness h fun n hn => by rw [hc n] at hn; cases hn

/-- A natural-deduction proof's compiled term realizes its formula, given
    realizers for its assumptions. -/
theorem nd_realizes {Γ : Nat → Form} {p : PT} {A : Form} (h : ND Γ p A)
    {γ : Nat → Term} (hγ : ∀ n, Real (Γ n) (γ n)) : Real A (p.compile.close γ) :=
  (nd_compile h).real hγ
