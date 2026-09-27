import Ski.Tait
import Ski.Simulation
import Ski.Converse
open Term

/-!
# Typed realizers compile to converging SKI terms

This is the bridge from Part II's realizer language (`Ski/Tait.lean`) to the
`SKI` term the prover runs.

**The source.**  `trS` writes a realizer as SKIjack source (`Src`), the
language `comp` compiles:
- a λ is a source λ, so `comp` λ-lifts it and chains consecutive λs;
- pairs and injections are the compiled Scott constructors `Pair a b`,
  `Inl a` and `Inr b` (`ctorO`, as globals);
- a projection lowers as SKIjack lowers a case: the scrutinee applied to
  the continuation `λ a b. a` (or `λ a b. b`);
- a case is the scrutinee applied to its two branches;
- constants are globals.

Variables are de Bruijn indices in the realizer, and named by binder depth
in the source.

**The theorem** (`compiled_converges`).  Let a realizer be typed and
closed, and let every constant realize its type.  Then its compiled term
converges: normal order reaches a weak head normal form.  Applied to
converging witnesses, its applications converge too
(`compiled_apply_converges`).

**The method.**  The relation `RS` is Tait's reducibility, stated on `SKI`
terms rather than realizers:
- at a base type, convergence;
- at `A ⇒ B`, mapping related arguments to related results;
- at a product, convergence and a Scott pair of related components;
- at a sum, convergence and a Scott injection of a related component.

It is closed under backward weak reduction (`RS.back`).  Every type is
inhabited, and every related term converges (`RS.inh_conv`).  The
fundamental lemma (`sem`) follows the typing derivation.  It is stated for
the body of the λ-chain that `comp` lifts, so that one induction covers
SKIjack's lifting of consecutive λs.  The proof never passes through the
realizer's own reduction: it reasons about the compiled term directly.
-/

namespace Rz

open Tm

variable {β γ : Type} (ι : γ → Term)

-- ---------------------------------------------------------------------------
-- The translation to SKIjack source
-- ---------------------------------------------------------------------------

/-- `Pair a b`, as SKIjack compiles the one constructor of a two-field type. -/
def pairG : Term := toTerm (ctorO 2 0 1)
/-- `Inl a`, the first constructor of a two-constructor sum. -/
def inlG : Term := toTerm (ctorO 1 0 2)
/-- `Inr b`, the second. -/
def inrG : Term := toTerm (ctorO 1 1 2)

/-- The case continuation `λ a b. a` (`first`) or `λ a b. b`, as source at
    depth `d`. -/
def projS (d : Nat) (first : Bool) : Src :=
  .lam d (.lam (d + 1) (.var (if first then d else d + 1)))

/-- A realizer as SKIjack source, at binder depth `d`; a constant is the
    global `ι` gives it. -/
def trS (d : Nat) : Tm γ → Src
  | .var i => .var (d - 1 - i)
  | .const c => .glob (ι c)
  | .app f a => trS d f ⬝ₛ trS d a
  | .lam b => .lam d (trS (d + 1) b)
  | .pair a b => .glob pairG ⬝ₛ trS d a ⬝ₛ trS d b
  | .fst t => trS d t ⬝ₛ projS d true
  | .snd t => trS d t ⬝ₛ projS d false
  | .inl a => .glob inlG ⬝ₛ trS d a
  | .inr b => .glob inrG ⬝ₛ trS d b
  | .case s f g => trS d s ⬝ₛ trS d f ⬝ₛ trS d g

/-- Every variable is bound: its index is below the binder depth. -/
def closedAt : Nat → Tm γ → Prop
  | d, .var i => i < d
  | _, .const _ => True
  | d, .app f a => closedAt d f ∧ closedAt d a
  | d, .lam b => closedAt (d + 1) b
  | d, .pair a b => closedAt d a ∧ closedAt d b
  | d, .fst t => closedAt d t
  | d, .snd t => closedAt d t
  | d, .inl a => closedAt d a
  | d, .inr b => closedAt d b
  | d, .case s f g => closedAt d s ∧ closedAt d f ∧ closedAt d g

/-- The compiled term of a closed realizer. -/
def compiled (t : Tm γ) : Term := toTerm (comp [] (trS ι 0 t))

-- ---------------------------------------------------------------------------
-- The relation
-- ---------------------------------------------------------------------------

/-- Reducibility on `SKI` terms. -/
def RS : Ty β → Term → Prop
  | .base _, r => Converges r
  | .arr A B, r => ∀ a, RS A a → RS B (r ⬝ a)
  | .prod A B, r => Converges r ∧
      ∃ a b, (∀ k, WSteps (r ⬝ k) (k ⬝ a ⬝ b)) ∧ RS A a ∧ RS B b
  | .sum A B, r => Converges r ∧
      ((∃ a, (∀ f g, WSteps (r ⬝ f ⬝ g) (f ⬝ a)) ∧ RS A a) ∨
       (∃ b, (∀ f g, WSteps (r ⬝ f ⬝ g) (g ⬝ b)) ∧ RS B b))

theorem Converges.back {r r' : Term} (h : WSteps r r') (hc : Converges r') : Converges r := by
  cases hc with
  | intro v hv =>
    cases eval_back h hv with
    | intro v' hv' => exact ⟨v', hv'.1⟩

/-- **Closed under backward weak reduction.** -/
theorem RS.back : ∀ (A : Ty β) {r r' : Term}, WSteps r r' → RS A r' → RS A r
  | .base _, _, _, h, hr => Converges.back h hr
  | .arr _ B, _, _, h, hr => fun a ha => RS.back B (WSteps.left a h) (hr a ha)
  | .prod _ _, _, _, h, hr => by
    cases hr with
    | intro hc hr =>
      cases hr with
      | intro a hr =>
        cases hr with
        | intro b hr =>
          exact ⟨Converges.back h hc, a, b, fun k => (WSteps.left k h).trans (hr.1 k), hr.2⟩
  | .sum _ _, _, _, h, hr => by
    cases hr with
    | intro hc hr =>
      refine ⟨Converges.back h hc, ?_⟩
      cases hr with
      | inl hl =>
        cases hl with
        | intro a ha =>
          exact .inl ⟨a, fun f g => (WSteps.left g (WSteps.left f h)).trans (ha.1 f g), ha.2⟩
      | inr hr =>
        cases hr with
        | intro b hb =>
          exact .inr ⟨b, fun f g => (WSteps.left g (WSteps.left f h)).trans (hb.1 f g), hb.2⟩

theorem converges_whnf {v : Term} (h : Whnf v) : Converges v := ⟨v, .refl v, h⟩

theorem pairG_beta (a b k : Term) : WSteps (pairG ⬝ a ⬝ b ⬝ k) (k ⬝ a ⬝ b) :=
  ctor_close_beta (a := 2) (j := 0) (m := 1) (fs := [a, b]) (ks := [k]) (by decide) rfl rfl

theorem inlG_beta (a f g : Term) : WSteps (inlG ⬝ a ⬝ f ⬝ g) (f ⬝ a) :=
  ctor_close_beta (a := 1) (j := 0) (m := 2) (fs := [a]) (ks := [f, g]) (by decide) rfl rfl

theorem inrG_beta (b f g : Term) : WSteps (inrG ⬝ b ⬝ f ⬝ g) (g ⬝ b) :=
  ctor_close_beta (a := 1) (j := 1) (m := 2) (fs := [b]) (ks := [f, g]) (by decide) rfl rfl

/-- **Every type is inhabited, and related terms converge.** -/
theorem RS.inh_conv : ∀ A : Ty β, (∃ r, RS A r) ∧ (∀ r, RS A r → Converges r)
  | .base _ => ⟨⟨K, converges_whnf .K⟩, fun _ h => h⟩
  | .arr A B => by
    have ⟨⟨a0, ha0⟩, _⟩ := RS.inh_conv A
    have ⟨⟨b0, hb0⟩, hB⟩ := RS.inh_conv B
    exact ⟨⟨K ⬝ b0, fun a _ => RS.back B (.single (.K b0 a)) hb0⟩,
      fun r h => Converges.app_left (hB _ (h a0 ha0))⟩
  | .prod A B => by
    have ⟨⟨a0, ha0⟩, hA⟩ := RS.inh_conv A
    have ⟨⟨b0, hb0⟩, _⟩ := RS.inh_conv B
    refine ⟨⟨pairG ⬝ a0 ⬝ b0, ?_, a0, b0, fun k => pairG_beta a0 b0 k, ha0, hb0⟩, fun _ h => h.1⟩
    exact Converges.app_left (Converges.back ((pairG_beta a0 b0 K).trans (.single (.K a0 b0)))
      (hA a0 ha0))
  | .sum A B => by
    have ⟨⟨a0, ha0⟩, _⟩ := RS.inh_conv A
    refine ⟨⟨inlG ⬝ a0, ?_, .inl ⟨a0, fun f g => inlG_beta a0 f g, ha0⟩⟩, fun _ h => h.1⟩
    exact Converges.app_left (Converges.app_left
      (Converges.back (inlG_beta a0 K K) (converges_whnf (.K1 a0))))

theorem RS.conv {A : Ty β} {r : Term} (h : RS A r) : Converges r := (RS.inh_conv A).2 r h

theorem RS.pair {A B : Ty β} {a b : Term} (ha : RS A a) (hb : RS B b) :
    RS (.prod A B) (pairG ⬝ a ⬝ b) :=
  ⟨Converges.app_left (Converges.back ((pairG_beta a b K).trans (.single (.K a b))) ha.conv),
    a, b, fun k => pairG_beta a b k, ha, hb⟩

theorem RS.inl {A B : Ty β} {a : Term} (ha : RS A a) : RS (.sum A B) (inlG ⬝ a) :=
  ⟨Converges.app_left (Converges.app_left
    (Converges.back (inlG_beta a K K) (converges_whnf (.K1 a)))),
    .inl ⟨a, fun f g => inlG_beta a f g, ha⟩⟩

theorem RS.inr {A B : Ty β} {b : Term} (hb : RS B b) : RS (.sum A B) (inrG ⬝ b) :=
  ⟨Converges.app_left (Converges.app_left
    (Converges.back (inrG_beta b K K) (converges_whnf (.K1 b)))),
    .inr ⟨b, fun f g => inrG_beta b f g, hb⟩⟩

-- ---------------------------------------------------------------------------
-- What `comp` does to a λ-chain
-- ---------------------------------------------------------------------------

theorem absN_append (xs ys : List Nat) (B : OTerm) : absN (xs ++ ys) B = absN xs (absN ys B) :=
  List.foldr_append

/-- A lifted combinator, applied to its captured binders, weakly reduces to the
    abstraction over its parameters alone. -/
theorem wrapLift_close (caps ps : List Nat) (B : OTerm) (γ : Nat → Term) :
    WSteps ((wrapLift caps ps B).close γ) ((absN ps B).close γ) := by
  have e1 : (wrapLift caps ps B).close γ = appT ((absN caps (absN ps B)).close γ) (caps.map γ) := by
    unfold wrapLift
    rw [close_appL, List.map_map, absN_append]
    rfl
  have h := absN_beta_close caps (absN ps B) γ (caps.map γ) (List.length_map _)
  rw [overrideC_self] at h
  rw [e1]
  exact h

/-- A compiled source λ weakly reduces to the abstraction of its chain's body
    over the chain's parameters. -/
theorem comp_lam_close (sc : List Nat) (x : Nat) (e : Src) (γ : Nat → Term) :
    ∃ sc', WSteps ((comp sc (.lam x e)).close γ)
      ((absN (Src.lam x e).peel.1 (comp sc' (Src.lam x e).peel.2)).close γ) := by
  refine ⟨(sc.filter fun s => (Src.lam x e).occurs s) ++ ([x] ++ e.peel.1), ?_⟩
  show WSteps ((compLam (sc.filter fun s => (Src.lam x e).occurs s) [x] e).close γ) _
  rw [compLam_chain]
  exact wrapLift_close _ _ _ γ

/-- The case continuation applied to two terms weakly reduces to the chosen one. -/
theorem projS_beta (sc : List Nat) (d : Nat) (first : Bool) (γ : Nat → Term) (a b : Term) :
    WSteps ((comp sc (projS d first)).close γ ⬝ a ⬝ b) (if first then a else b) := by
  cases comp_lam_close sc d (.lam (d + 1) (.var (if first then d else d + 1))) γ with
  | intro sc' h =>
    have h2 := absN_beta_close [d, d + 1] (comp sc' (.var (if first then d else d + 1))) γ [a, b] rfl
    refine (WSteps.left b (WSteps.left a h)).trans ?_
    refine h2.trans ?_
    cases first with
    | true =>
      show WSteps (overrideC γ [d, d + 1] [a, b] d) a
      have e : overrideC γ [d, d + 1] [a, b] d = a := by
        show updC (updC γ d a) (d + 1) b d = a
        unfold updC
        rw [if_neg (Nat.ne_of_lt (Nat.lt_succ_self d)), if_pos rfl]
      rw [e]
      exact .refl a
    | false =>
      show WSteps (overrideC γ [d, d + 1] [a, b] (d + 1)) b
      have e : overrideC γ [d, d + 1] [a, b] (d + 1) = b := by
        show updC (updC γ d a) (d + 1) b (d + 1) = b
        unfold updC
        rw [if_pos rfl]
      rw [e]
      exact .refl b

-- ---------------------------------------------------------------------------
-- The fundamental lemma
-- ---------------------------------------------------------------------------

/-- The environment realizes the context at depth `d`: the variable of index
    `i` is named `d - 1 - i`. -/
def EnvOK (d : Nat) (Γ : Nat → Ty β) (γ : Nat → Term) : Prop :=
  ∀ i, i < d → RS (Γ i) (γ (d - 1 - i))

theorem EnvOK.cons {d : Nat} {Γ : Nat → Ty β} {γ : Nat → Term} (h : EnvOK d Γ γ) {A : Ty β}
    {N : Term} (hN : RS A N) : EnvOK (d + 1) (Ty.cons A Γ) (updC γ d N) := by
  intro i hi
  cases i with
  | zero =>
    show RS A (updC γ d N (d + 1 - 1 - 0))
    rw [show d + 1 - 1 - 0 = d by omega]
    unfold updC
    rw [if_pos rfl]
    exact hN
  | succ i =>
    show RS (Γ i) (updC γ d N (d + 1 - 1 - (i + 1)))
    rw [show d + 1 - 1 - (i + 1) = d - 1 - i by omega]
    unfold updC
    rw [if_neg (by omega)]
    exact h i (by omega)

/-- The fundamental lemma, for the body of the λ-chain `comp` lifts: under an
    environment that realizes the context, the chain's body abstracted over
    its parameters is related to the realizer's type, in any scope. -/
theorem sem {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : ∀ c, RS (sig c) (ι c)) :
    ∀ d, closedAt d t → ∀ γ, EnvOK d Γ γ → ∀ sc,
      RS A ((absN (trS ι d t).peel.1 (comp sc (trS ι d t).peel.2)).close γ) := by
  -- the usual form, for a subterm: its compiled ι term in any scope
  have usual : ∀ {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β},
      (∀ d, closedAt d t → ∀ γ, EnvOK d Γ γ → ∀ sc,
        RS A ((absN (trS ι d t).peel.1 (comp sc (trS ι d t).peel.2)).close γ)) →
      ∀ d, closedAt d t → ∀ γ, EnvOK d Γ γ → ∀ sc, RS A ((comp sc (trS ι d t)).close γ) := by
    intro Γ t A ih d hd γ hγ sc
    cases t with
    | lam b =>
      cases comp_lam_close sc d (trS ι (d + 1) b) γ with
      | intro sc' hw => exact RS.back A hw (ih d hd γ hγ sc')
    | _ => exact ih d hd γ hγ sc
  induction h with
  | var Γ n =>
    intro d hd γ hγ sc
    exact hγ n hd
  | const Γ c =>
    intro d _ γ _ sc
    show RS (sig c) ((ι c).toO.close γ)
    rw [close_toO]
    exact hc c
  | @lam Γ A B b _ ih =>
    intro d hd γ hγ sc
    show RS (.arr A B) ((abs d (absN (trS ι (d + 1) b).peel.1 (comp sc (trS ι (d + 1) b).peel.2))).close γ)
    intro N hN
    exact RS.back B (abs_beta_close d _ γ N) (ih (d + 1) hd (updC γ d N) (hγ.cons hN) sc)
  | app _ _ ihf iha =>
    intro d hd γ hγ sc
    exact (usual ihf d hd.1 γ hγ sc) _ (usual iha d hd.2 γ hγ sc)
  | pair _ _ iha ihb =>
    intro d hd γ hγ sc
    show RS _ (pairG.toO.close γ ⬝ (comp sc (trS ι d _)).close γ ⬝ (comp sc (trS ι d _)).close γ)
    rw [close_toO]
    exact RS.pair (usual iha d hd.1 γ hγ sc) (usual ihb d hd.2 γ hγ sc)
  | @fst Γ A B t _ ih =>
    intro d hd γ hγ sc
    cases (usual ih d hd γ hγ sc).2 with
    | intro a hp =>
      cases hp with
      | intro b hp =>
        exact RS.back A ((hp.1 _).trans (projS_beta sc d true γ a b)) hp.2.1
  | @snd Γ A B t _ ih =>
    intro d hd γ hγ sc
    cases (usual ih d hd γ hγ sc).2 with
    | intro a hp =>
      cases hp with
      | intro b hp =>
        exact RS.back B ((hp.1 _).trans (projS_beta sc d false γ a b)) hp.2.2
  | inl _ ih =>
    intro d hd γ hγ sc
    show RS _ (inlG.toO.close γ ⬝ (comp sc (trS ι d _)).close γ)
    rw [close_toO]
    exact RS.inl (usual ih d hd γ hγ sc)
  | inr _ ih =>
    intro d hd γ hγ sc
    show RS _ (inrG.toO.close γ ⬝ (comp sc (trS ι d _)).close γ)
    rw [close_toO]
    exact RS.inr (usual ih d hd γ hγ sc)
  | @case Γ A B C s f g _ _ _ ihs ihf ihg =>
    intro d hd γ hγ sc
    have hf := usual ihf d hd.2.1 γ hγ sc
    have hg := usual ihg d hd.2.2 γ hγ sc
    cases (usual ihs d hd.1 γ hγ sc).2 with
    | inl hl =>
      cases hl with
      | intro a ha => exact RS.back C (ha.1 _ _) (hf a ha.2)
    | inr hr =>
      cases hr with
      | intro b hb => exact RS.back C (hb.1 _ _) (hg b hb.2)

/-- **A typed closed realizer compiles to a related term.** -/
theorem compiled_RS {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : ∀ c, RS (sig c) (ι c)) (ht : closedAt 0 t) :
    RS A (compiled ι t) := by
  have hs := sem ι h hc
  cases t with
  | lam b =>
    cases comp_lam_close [] 0 (trS ι 1 b) (fun _ => K) with
    | intro sc' hw =>
      exact RS.back A hw (hs 0 ht (fun _ => K) (fun _ h => absurd h (Nat.not_lt_zero _)) sc')
  | _ => exact hs 0 ht (fun _ => K) (fun _ h => absurd h (Nat.not_lt_zero _)) []

/-- **Typed realizers compile to converging terms**: the compiled ι term of a
    typed closed realizer, whose constants realize their types, reaches a
    weak head normal form in normal order. -/
theorem compiled_converges {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : ∀ c, RS (sig c) (ι c)) (ht : closedAt 0 t) :
    Converges (compiled ι t) :=
  (compiled_RS ι h hc ht).conv

/-- Applied to converging witnesses, a compiled realizer of type
    `W₁ ⇒ … ⇒ Wₖ ⇒ B`, over base types, converges. -/
theorem compiled_apply_converges {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ}
    {B : Ty β} (Ws : List β) (h : Typed sig Γ t (Ws.foldr (fun w C => .arr (.base w) C) B))
    (hc : ∀ c, RS (sig c) (ι c)) (ht : closedAt 0 t) (ws : List Term) (hl : ws.length = Ws.length)
    (hw : ∀ w ∈ ws, Converges w) : Converges (appT (compiled ι t) ws) := by
  have key : ∀ (Ws : List β) (ws : List Term) (r : Term), ws.length = Ws.length →
      (∀ w ∈ ws, Converges w) → RS (Ws.foldr (fun w C => .arr (.base w) C) B) r →
      RS B (appT r ws) := by
    intro Ws
    induction Ws with
    | nil => intro ws r hl _ hr; cases ws with
      | nil => exact hr
      | cons _ _ => cases hl
    | cons W Ws ih =>
      intro ws r hl hw hr
      cases ws with
      | nil => cases hl
      | cons w ws =>
        exact ih ws (r ⬝ w) (Nat.succ.inj hl) (fun v hv => hw v (.tail _ hv))
          (hr w (hw w (.head _)))
  exact (key Ws ws _ hl hw (compiled_RS ι h hc ht)).conv

/-- **The glue converges**: a typed closed realizer without constants (pairs,
    projections, injections, case, λ and application only) compiles to a
    converging term, with no hypothesis left. -/
theorem glue_converges {Γ : Nat → Ty β} {t : Tm Empty} {A : Ty β}
    (h : Typed Empty.elim Γ t A) (ht : closedAt 0 t) :
    Converges (compiled Empty.elim t) :=
  compiled_converges Empty.elim h (fun c => c.elim) ht

end Rz
