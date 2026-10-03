import Ski.Compose

set_option linter.unusedSectionVars false

open Term

/-!
# Composed statements with `∃` and knowledge implication

`Ski/Compose.lean` compiles atoms under `∧` and `∨` to one evaluation
statement.  This module extends the formula language with two
connectives, compiled to the same kind of statement, so the composed
circuit, its prover and `checkC_sound` apply unchanged.

**`∃` over a hidden witness** (`XF.ex B`): `∃ y. B`, the value `y` part of
the hidden witness.  An atom `atom V x` under binders `y₁ … yₖ` (outermost
first) reads the input `⟨…⟨x, y₁⟩ …, yₖ⟩` (`inp`), so its verifier sees
the bound values.  A realizer of `∃` is the pair of `y` and a realizer of
the body, as `Real (.ex φ)` asks.

**Knowledge implication** (`XF.mp f T A`): the formula `T A`, proved from
a hidden realizer of `A` through a public witness map `f`, certified in
Lean: every realizer `a` of `A` makes `f a` a realizer of `T A`
(`XF.Cert`).  This is knowledge implication as a typed, publicly checked
realizer, the only form it takes in a proof of knowledge: a hidden
realizer of `A → B` would have to be checked on every input, which no
finite evaluation does.  The statement is `A`'s; the conclusion is `T A`.

**The theorems.**
- `real_of_acceptedX`: bits and a witness the statement accepts read
  back as a realizer of the formula, given the certificates.
- `accepted_of_realX`: a realizer of the formula's *source*, which holds
  a realizer of `A` where the formula concludes `T A`, yields bits and a
  witness the statement accepts.
- `composeX`: over the assumed proof system for evaluation statements,
  the composed system is complete, knowledge-sound and zero knowledge.
-/

namespace Compose

-- ---------------------------------------------------------------------------
-- Formulas
-- ---------------------------------------------------------------------------

/-- Atoms under `∧`, `∨`, `∃` over a hidden witness, and knowledge
    implication through a public witness map. -/
inductive XF
  | atom (V x : Term)
  | and (A B : XF)
  | or (A B : XF)
  | ex (B : XF)
  | mp (f : Term) (T : Form → Form) (A : XF)

/-- An atom's input under bound values, innermost first: `x` paired with
    each, outermost first. -/
def inp (x : Term) : List Term → Term
  | [] => x
  | y :: ys => pairT (inp x ys) y

/-- **The formula proved**, under bound values `ys`. -/
def XF.form : XF → List Term → Form
  | .atom V x, ys => .atom V (inp x ys)
  | .and A B, ys => .and (A.form ys) (B.form ys)
  | .or A B, ys => .or (A.form ys) (B.form ys)
  | .ex B, ys => .ex fun y => B.form (y :: ys)
  | .mp _ T A, ys => T (A.form ys)

/-- **What the prover holds**: the formula with each implication's
    conclusion replaced by its hypothesis. -/
def XF.src : XF → List Term → Form
  | .atom V x, ys => .atom V (inp x ys)
  | .and A B, ys => .and (A.src ys) (B.src ys)
  | .or A B, ys => .or (A.src ys) (B.src ys)
  | .ex B, ys => .ex fun y => B.src (y :: ys)
  | .mp _ _ A, ys => A.src ys

/-- **The certificates**: each witness map takes every realizer of its
    hypothesis to one of its conclusion, for every bound value. -/
def XF.Cert : XF → List Term → Prop
  | .atom _ _, _ => True
  | .and A B, ys => A.Cert ys ∧ B.Cert ys
  | .or A B, ys => A.Cert ys ∧ B.Cert ys
  | .ex B, ys => ∀ y, B.Cert (y :: ys)
  | .mp f T A, ys => A.Cert ys ∧ ∀ a, Real (A.form ys) a → Real (T (A.form ys)) (f ⬝ a)

-- ---------------------------------------------------------------------------
-- Bits, paths, leaves
-- ---------------------------------------------------------------------------

/-- The bits have the formula's shape: a leaf per atom, and for `∃` a node
    whose first subtree is an unused leaf, aligning the bits' paths with
    the witness's. -/
def ShapeX : XF → BT → Prop
  | .atom _ _, .leaf _ => True
  | .and A B, .node l r => ShapeX A l ∧ ShapeX B r
  | .or A B, .node l r => ShapeX A l ∧ ShapeX B r
  | .ex B, .node (.leaf _) r => ShapeX B r
  | .mp _ _ A, β => ShapeX A β
  | _, _ => False

/-- The formula, over the bits. -/
def evalBX : XF → BT → Bool
  | .atom _ _, .leaf b => b
  | .and A B, .node l r => evalBX A l && evalBX B r
  | .or A B, .node l r => evalBX A l || evalBX B r
  | .ex B, .node _ r => evalBX B r
  | .mp _ _ A, β => evalBX A β
  | _, _ => false

/-- The atoms, each with its verifier, input, the paths of its bound
    values (innermost first) and its path. -/
def leavesX : XF → List Bool → List (List Bool) → List (Term × Term × List (List Bool) × List Bool)
  | .atom V x, p, bs => [(V, x, bs, p)]
  | .and A B, p, bs => leavesX A (p ++ [false]) bs ++ leavesX B (p ++ [true]) bs
  | .or A B, p, bs => leavesX A (p ++ [false]) bs ++ leavesX B (p ++ [true]) bs
  | .ex B, p, bs => leavesX B (p ++ [true]) ((p ++ [false]) :: bs)
  | .mp _ _ A, p, bs => leavesX A p bs

/-- The formula over the bits `ρ` (variable 0), as a Scott Boolean. -/
def fmX : XF → List Bool → OTerm
  | .atom _ _, p => appP (.var 0) p
  | .and A B, p => fmX A (p ++ [false]) ⬝ₒ fmX B (p ++ [true]) ⬝ₒ (.K ⬝ₒ .I)
  | .or A B, p => fmX A (p ++ [false]) ⬝ₒ .K ⬝ₒ fmX B (p ++ [true])
  | .ex B, p => fmX B (p ++ [true])
  | .mp _ _ A, p => fmX A p

/-- A Scott pair of open terms. -/
def pairXO (a b : OTerm) : OTerm := .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ a)) ⬝ₒ (.K ⬝ₒ b)

/-- An atom's input, read from the witness (variable 1) at the bound
    values' paths. -/
def inpO (x : Term) : List (List Bool) → OTerm
  | [] => x.toO
  | b :: bs => pairXO (inpO x bs) (appP (.var 1) b)

/-- The formula check: `[ρ w] (φ ρ) K (K I)`. -/
def phiStmtX (M : XF) : Term := toTerm (absN [0, 1] (fmX M [] ⬝ₒ .K ⬝ₒ (.K ⬝ₒ .I)))

/-- An atom's guard: `[ρ w] (ρ·q) (V ⟨x, w·b₁, …⟩ (w·q)) K`. -/
def leafStmtX (V x : Term) (bs : List (List Bool)) (q : List Bool) : Term :=
  toTerm (absN [0, 1] (appP (.var 0) q ⬝ₒ (V.toO ⬝ₒ inpO x bs ⬝ₒ appP (.var 1) q) ⬝ₒ .K))

/-- **The statement of a formula**: its formula check and its atoms'
    guards. -/
def stmtOfX (M : XF) : List Term :=
  phiStmtX M :: (leavesX M [] []).map fun (V, x, bs, q) => leafStmtX V x bs q

/-- A formula's statement, as an evaluation statement. -/
def evalStmtOfX (M : XF) : EvalStmt := (stmtOfX M, ShapeX M)

/-- **The relation of a formula**: its evaluation statement's. -/
def AcceptsX (M : XF) (β : BT) (w : Term) : Prop := EvalRel (evalStmtOfX M) β w

/-- The witness's component at a path. -/
def wAt (w : Term) (b : List Bool) : Term := appT w (projs b)

-- ---------------------------------------------------------------------------
-- Closing the statement's terms
-- ---------------------------------------------------------------------------

theorem close_pairXO (σ : Nat → Term) (a b : OTerm) : (pairXO a b).close σ = pairT (a.close σ) (b.close σ) := rfl

/-- An atom's input, closed, is its input under the witness's components. -/
theorem close_inpO (B W x : Term) : ∀ bs : List (List Bool),
    (inpO x bs).close (env B W) = inp x (bs.map (wAt W))
  | [] => close_toO _ x
  | b :: bs => by
    show pairT ((inpO x bs).close (env B W)) ((appP (.var 1) b).close (env B W)) = _
    rw [close_inpO B W x bs, close_appP, env1]
    rfl

/-- **The formula, applied to the literal bits, reduces to its value**, for
    bits of the formula's shape. -/
theorem fmX_red : ∀ (M : XF) (β : BT) (p : List Bool) (W : Term), ShapeX M (β.sub p) →
    WSteps (appT β.enc (projs p)) (β.sub p).enc →
    WSteps ((fmX M p).close (env β.enc W)) (boolT (evalBX M (β.sub p)))
  | .atom _ _, β, p, W, hs, hp => by
    unfold fmX
    rw [close_appP, env0]
    cases hb : β.sub p with
    | leaf b => rw [hb] at hp; exact hp
    | node _ _ => rw [hb] at hs; cases hs
  | .and A B, β, p, W, hs, hp => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      have ha := fmX_red A β (p ++ [false]) W (by rw [hl]; exact hs.1) (proj_sub β p ⟨l, r, hb⟩ hp false)
      have hbb := fmX_red B β (p ++ [true]) W (by rw [hr]; exact hs.2) (proj_sub β p ⟨l, r, hb⟩ hp true)
      rw [hl] at ha
      rw [hr] at hbb
      show WSteps ((fmX A (p ++ [false])).close _ ⬝ (fmX B (p ++ [true])).close _ ⬝ (K ⬝ I)) _
      refine (WSteps.left _ (WSteps.left _ ha)).trans ((boolT_sel _ _ _).trans ?_)
      show WSteps _ (boolT (evalBX A l && evalBX B r))
      cases evalBX A l with
      | true => exact hbb
      | false => exact .refl _
  | .or A B, β, p, W, hs, hp => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      have ha := fmX_red A β (p ++ [false]) W (by rw [hl]; exact hs.1) (proj_sub β p ⟨l, r, hb⟩ hp false)
      have hbb := fmX_red B β (p ++ [true]) W (by rw [hr]; exact hs.2) (proj_sub β p ⟨l, r, hb⟩ hp true)
      rw [hl] at ha
      rw [hr] at hbb
      show WSteps ((fmX A (p ++ [false])).close _ ⬝ K ⬝ (fmX B (p ++ [true])).close _) _
      refine (WSteps.left _ (WSteps.left _ ha)).trans ((boolT_sel _ _ _).trans ?_)
      show WSteps _ (boolT (evalBX A l || evalBX B r))
      cases evalBX A l with
      | true => exact .refl _
      | false => exact hbb
  | .ex B, β, p, W, hs, hp => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      cases l with
      | node _ _ => cases hs
      | leaf c =>
        have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
        have hbb := fmX_red B β (p ++ [true]) W (by rw [hr]; exact hs)
          (proj_sub β p ⟨_, r, hb⟩ hp true)
        rw [hr] at hbb
        exact hbb
  | .mp _ _ A, β, p, W, hs, hp => fmX_red A β p W hs hp

/-- **The formula check accepts exactly when the formula is true of the
    bits.** -/
theorem phi_iffX {M : XF} {β : BT} (hs : ShapeX M β) (W : Term) :
    Eval (phiStmtX M ⬝ β.enc ⬝ W) K ↔ evalBX M β = true := by
  have hr := fmX_red M β [] W hs (.refl _)
  have hred : WSteps (phiStmtX M ⬝ β.enc ⬝ W) (if evalBX M β then K else K ⬝ I) :=
    (stmt_beta _ _ _).trans ((WSteps.left _ (WSteps.left _ hr)).trans (boolT_sel _ _ _))
  rw [eval_K_iff, wsteps_K_iff hred]
  cases evalBX M β with
  | true => exact ⟨fun _ => rfl, fun _ => .refl _⟩
  | false => exact ⟨fun h => absurd h F_not_K, fun h => by cases h⟩

/-- **An atom's guard accepts exactly when its bit is clear or its verifier
    accepts the witness's component on its input under the bound
    values.** -/
theorem leaf_iffX {V x W : Term} {bs : List (List Bool)} {β : BT} {q : List Bool} {b : Bool}
    (hb : β.sub q = .leaf b) (hp : WSteps (appT β.enc (projs q)) (β.sub q).enc) :
    Eval (leafStmtX V x bs q ⬝ β.enc ⬝ W) K ↔
      (b = true → Real (.atom V (inp x (bs.map (wAt W)))) (wAt W q)) := by
  have hred : WSteps (leafStmtX V x bs q ⬝ β.enc ⬝ W)
      (boolT b ⬝ (V ⬝ inp x (bs.map (wAt W)) ⬝ wAt W q) ⬝ K) := by
    refine (stmt_beta _ _ _).trans ?_
    show WSteps ((appP (.var 0) q).close _ ⬝ (V.toO.close _ ⬝ (inpO x bs).close _ ⬝
      (appP (.var 1) q).close _) ⬝ K) _
    rw [close_appP, close_appP, env0, env1, close_toO, close_inpO]
    rw [hb] at hp
    exact WSteps.left _ (WSteps.left _ hp)
  rw [eval_K_iff, wsteps_K_iff (hred.trans (boolT_sel _ _ _))]
  cases b with
  | true =>
    simp only [if_true, forall_const]
    exact ⟨fun h => h, fun h => h⟩
  | false =>
    simp only [if_false, Bool.false_eq_true, false_implies, iff_true]
    exact .refl _

-- ---------------------------------------------------------------------------
-- Extraction: accepted bits and witness read back as a realizer
-- ---------------------------------------------------------------------------

/-- Each leaf's path leads to a leaf of bits of the formula's shape, and its
    projections reduce to it. -/
theorem leaf_pathX : ∀ (M : XF) (β : BT) (p : List Bool) (bs : List (List Bool)), ShapeX M (β.sub p) →
    WSteps (appT β.enc (projs p)) (β.sub p).enc →
    ∀ V x bs' q, (V, x, bs', q) ∈ leavesX M p bs →
      (∃ b, β.sub q = .leaf b) ∧ WSteps (appT β.enc (projs q)) (β.sub q).enc
  | .atom V' x', β, p, bs, hs, hp, V, x, bs', q, hm => by
    simp only [leavesX, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨_, _, _, rfl⟩ := hm
    refine ⟨?_, hp⟩
    cases hb : β.sub q with
    | leaf b => exact ⟨b, rfl⟩
    | node _ _ => rw [hb] at hs; cases hs
  | .and A B, β, p, bs, hs, hp, V, x, bs', q, hm => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [leavesX, List.mem_append] at hm
      rcases hm with hm | hm
      · exact leaf_pathX A β _ bs (by rw [hl]; exact hs.1) (proj_sub β p ⟨l, r, hb⟩ hp false) V x bs' q hm
      · exact leaf_pathX B β _ bs (by rw [hr]; exact hs.2) (proj_sub β p ⟨l, r, hb⟩ hp true) V x bs' q hm
  | .or A B, β, p, bs, hs, hp, V, x, bs', q, hm => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [leavesX, List.mem_append] at hm
      rcases hm with hm | hm
      · exact leaf_pathX A β _ bs (by rw [hl]; exact hs.1) (proj_sub β p ⟨l, r, hb⟩ hp false) V x bs' q hm
      · exact leaf_pathX B β _ bs (by rw [hr]; exact hs.2) (proj_sub β p ⟨l, r, hb⟩ hp true) V x bs' q hm
  | .ex B, β, p, bs, hs, hp, V, x, bs', q, hm => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      cases l with
      | node _ _ => cases hs
      | leaf c =>
        have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
        exact leaf_pathX B β _ _ (by rw [hr]; exact hs) (proj_sub β p ⟨_, r, hb⟩ hp true) V x bs' q hm
  | .mp _ _ A, β, p, bs, hs, hp, V, x, bs', q, hm => leaf_pathX A β p bs hs hp V x bs' q hm

/-- **The read-back**: a realizer of the formula from bits and a witness.
    An atom's realizer is the witness's component at its path; `∧` pairs;
    `∨` injects the side the bits make true; `∃` pairs the bound value,
    the component at the node's first path, with the body's realizer; a
    knowledge implication applies its witness map. -/
def readBackX : XF → BT → Term → List Bool → Term
  | .atom _ _, _, w, p => wAt w p
  | .and A B, β, w, p => pairT (readBackX A β w (p ++ [false])) (readBackX B β w (p ++ [true]))
  | .or A B, β, w, p =>
    if evalBX A (β.sub (p ++ [false])) then inlT (readBackX A β w (p ++ [false]))
    else inrT (readBackX B β w (p ++ [true]))
  | .ex B, β, w, p => pairT (wAt w (p ++ [false])) (readBackX B β w (p ++ [true]))
  | .mp f _ A, β, w, p => f ⬝ readBackX A β w p

theorem readBackX_real : ∀ (M : XF) (β : BT) (w : Term) (p : List Bool) (bs : List (List Bool)),
    ShapeX M (β.sub p) → evalBX M (β.sub p) = true →
    (∀ V x bs' q, (V, x, bs', q) ∈ leavesX M p bs → β.sub q = .leaf true →
      Real (.atom V (inp x (bs'.map (wAt w)))) (wAt w q)) →
    M.Cert (bs.map (wAt w)) →
    Real (M.form (bs.map (wAt w))) (readBackX M β w p)
  | .atom V x, β, w, p, bs, hs, he, hl, _ => by
    cases hb : β.sub p with
    | node _ _ => rw [hb] at hs; cases hs
    | leaf b =>
      rw [hb] at he
      cases he
      exact hl V x bs p (by simp [leavesX]) hb
  | .and A B, β, w, p, bs, hs, he, hl, hc => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs he
      have hl' : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr' : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [evalBX, Bool.and_eq_true] at he
      refine ⟨_, _, pairT_app _ _, ?_, ?_⟩
      · exact readBackX_real A β w _ bs (by rw [hl']; exact hs.1) (by rw [hl']; exact he.1)
          (fun V x bs' q hm => hl V x bs' q (by simp [leavesX, hm])) hc.1
      · exact readBackX_real B β w _ bs (by rw [hr']; exact hs.2) (by rw [hr']; exact he.2)
          (fun V x bs' q hm => hl V x bs' q (by simp [leavesX, hm])) hc.2
  | .or A B, β, w, p, bs, hs, he, hl, hc => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs he
      have hl' : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr' : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [evalBX, Bool.or_eq_true] at he
      unfold readBackX
      rw [hl']
      cases hA : evalBX A l with
      | true =>
        simp only [if_true]
        exact .inl ⟨_, inlT_app _, readBackX_real A β w _ bs (by rw [hl']; exact hs.1)
          (by rw [hl']; exact hA) (fun V x bs' q hm => hl V x bs' q (by simp [leavesX, hm])) hc.1⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hA] at he
        have hB : evalBX B r = true := he.resolve_left (by simp)
        exact .inr ⟨_, inrT_app _, readBackX_real B β w _ bs (by rw [hr']; exact hs.2)
          (by rw [hr']; exact hB) (fun V x bs' q hm => hl V x bs' q (by simp [leavesX, hm])) hc.2⟩
  | .ex B, β, w, p, bs, hs, he, hl, hc => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs he
      cases l with
      | node _ _ => cases hs
      | leaf c =>
        have hr' : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
        refine ⟨wAt w (p ++ [false]), _, pairT_app _ _, ?_⟩
        have := readBackX_real B β w (p ++ [true]) ((p ++ [false]) :: bs) (by rw [hr']; exact hs)
          (by rw [hr']; exact he) (fun V x bs' q hm => hl V x bs' q hm) (hc _)
        exact this
  | .mp f T A, β, w, p, bs, hs, he, hl, hc =>
    hc.2 _ (readBackX_real A β w p bs hs he (fun V x bs' q hm => hl V x bs' q hm) hc.1)

/-- **Knowledge soundness, composed**: bits and a witness the statement
    accepts read back as a realizer of the formula, given its
    certificates. -/
theorem real_of_acceptedX {M : XF} {β : BT} {w : Term} (h : AcceptsX M β w) (hc : M.Cert []) :
    Real (M.form []) (readBackX M β w []) := by
  obtain ⟨hs, hall⟩ := h
  have he : evalBX M β = true := (phi_iffX hs w).1 (hall _ (List.mem_cons_self))
  refine readBackX_real M β w [] [] hs he (fun V x bs q hm hq => ?_) hc
  obtain ⟨_, hp⟩ := leaf_pathX M β [] [] hs (.refl _) V x bs q hm
  have hacc := hall (leafStmtX V x bs q)
    (List.mem_cons_of_mem _ (List.mem_map.2 ⟨(V, x, bs, q), hm, rfl⟩))
  exact (leaf_iffX hq hp).1 hacc rfl

-- ---------------------------------------------------------------------------
-- Completeness: a realizer of the source yields accepted bits and witness
-- ---------------------------------------------------------------------------

theorem leaves_prefixX : ∀ (M : XF) (p : List Bool) (bs : List (List Bool)),
    leavesX M p bs = (leavesX M [] []).map fun (V, x, bs', q) => (V, x, bs'.map (p ++ ·) ++ bs, p ++ q)
  | .atom V x, p, bs => by simp [leavesX]
  | .and A B, p, bs => by
    simp only [leavesX, List.map_append]
    rw [leaves_prefixX A (p ++ [false]) bs, leaves_prefixX A ([] ++ [false]) [],
      leaves_prefixX B (p ++ [true]) bs, leaves_prefixX B ([] ++ [true]) []]
    simp [List.map_map, Function.comp_def, List.append_assoc]
  | .or A B, p, bs => by
    simp only [leavesX, List.map_append]
    rw [leaves_prefixX A (p ++ [false]) bs, leaves_prefixX A ([] ++ [false]) [],
      leaves_prefixX B (p ++ [true]) bs, leaves_prefixX B ([] ++ [true]) []]
    simp [List.map_map, Function.comp_def, List.append_assoc]
  | .ex B, p, bs => by
    simp only [leavesX]
    rw [leaves_prefixX B (p ++ [true]) ((p ++ [false]) :: bs),
      leaves_prefixX B ([] ++ [true]) [[] ++ [false]]]
    simp [List.map_map, Function.comp_def, List.append_assoc]
  | .mp _ _ A, p, bs => leaves_prefixX A p bs

/-- The bits that choose nothing, in a formula's shape. -/
def clearX : XF → BT
  | .atom _ _ => .leaf false
  | .and A B => .node (clearX A) (clearX B)
  | .or A B => .node (clearX A) (clearX B)
  | .ex B => .node (.leaf false) (clearX B)
  | .mp _ _ A => clearX A

theorem clear_shapeX : ∀ M : XF, ShapeX M (clearX M)
  | .atom _ _ => trivial
  | .and A B => ⟨clear_shapeX A, clear_shapeX B⟩
  | .or A B => ⟨clear_shapeX A, clear_shapeX B⟩
  | .ex B => clear_shapeX B
  | .mp _ _ A => clear_shapeX A

theorem clear_leavesX : ∀ (M : XF) (V x : Term) (bs : List (List Bool)) (q : List Bool),
    (V, x, bs, q) ∈ leavesX M [] [] → (clearX M).sub q = .leaf false
  | .atom _ _, V, x, bs, q, hm => by
    simp only [leavesX, List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨_, _, _, rfl⟩ := hm; rfl
  | .and A B, V, x, bs, q, hm => by
    rw [leavesX, leaves_prefixX A, leaves_prefixX B] at hm
    simp only [List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨V', x', bs', q'⟩, hm, e⟩ | ⟨⟨V', x', bs', q'⟩, hm, e⟩
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2.2]; exact clear_leavesX A V' x' bs' q' hm
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2.2]; exact clear_leavesX B V' x' bs' q' hm
  | .or A B, V, x, bs, q, hm => by
    rw [leavesX, leaves_prefixX A, leaves_prefixX B] at hm
    simp only [List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨V', x', bs', q'⟩, hm, e⟩ | ⟨⟨V', x', bs', q'⟩, hm, e⟩
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2.2]; exact clear_leavesX A V' x' bs' q' hm
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2.2]; exact clear_leavesX B V' x' bs' q' hm
  | .ex B, V, x, bs, q, hm => by
    rw [leavesX, leaves_prefixX B] at hm
    simp only [List.mem_map] at hm
    obtain ⟨⟨V', x', bs', q'⟩, hm, e⟩ := hm
    simp only [Prod.mk.injEq] at e; rw [← e.2.2.2]; exact clear_leavesX B V' x' bs' q' hm
  | .mp _ _ A, V, x, bs, q, hm => clear_leavesX A V x bs q hm

/-- Lists that reduce pointwise. -/
inductive Red2 : List Term → List Term → Prop
  | nil : Red2 [] []
  | cons {a a' : Term} {l l' : List Term} : WSteps a a' → Red2 l l' → Red2 (a :: l) (a' :: l')

theorem Red2.refl : ∀ l : List Term, Red2 l l
  | [] => .nil
  | a :: l => .cons (.refl a) (Red2.refl l)

theorem Red2.append {l l' m m' : List Term} (h : Red2 l l') (h' : Red2 m m') : Red2 (l ++ m) (l' ++ m') := by
  induction h with
  | nil => exact h'
  | cons ha _ ih => exact .cons ha ih

theorem Red2.map {α : Type} (f g : α → Term) (h : ∀ a, WSteps (f a) (g a)) : ∀ l : List α, Red2 (l.map f) (l.map g)
  | [] => .nil
  | a :: l => .cons (h a) (Red2.map f g h l)

theorem pairT_wsteps {a a' b b' : Term} (ha : WSteps a a') (hb : WSteps b b') :
    WSteps (pairT a b) (pairT a' b') :=
  WSteps.app (WSteps.right S (WSteps.right (S ⬝ I) (WSteps.right K ha))) (WSteps.right K hb)

/-- An atom's input reduces as its bound values do. -/
theorem inp_red (x : Term) : ∀ {es es' : List Term}, Red2 es es' → WSteps (inp x es) (inp x es')
  | [], [], .nil => .refl _
  | _ :: _, _ :: _, .cons ha hl => pairT_wsteps (inp_red x hl) ha

/-- An atom is realized whatever its input reduces to realizes it. -/
theorem real_atom_back {V X X' a : Term} (h : WSteps X X') (hr : Real (.atom V X') a) :
    Real (.atom V X) a :=
  (WSteps.left a (WSteps.right V h)).trans hr

/-- What completeness builds, under bound values `ys`: bits of the
    formula's shape that make it true, and a witness whose component at
    every set leaf is accepted on its input. -/
def GoodX (M : XF) (ys : List Term) (β : BT) (w : Term) : Prop :=
  ShapeX M β ∧ evalBX M β = true ∧
    ∀ V x bs q, (V, x, bs, q) ∈ leavesX M [] [] → β.sub q = .leaf true →
      Real (.atom V (inp x (bs.map (wAt w) ++ ys))) (wAt w q)

theorem wAt_cons (w : Term) (d : Bool) (b : List Bool) :
    wAt w (d :: b) = wAt (w ⬝ (if d then sndT else fstT)) b := rfl

/-- A leaf of a subformula, seen through a pair: its input and component
    reduce to the subformula's own. -/
theorem good_lift {V x : Term} {ys : List Term} {w w' : Term} {d : Bool} {bs : List (List Bool)} {q : List Bool}
    (hw : WSteps (w ⬝ (if d then sndT else fstT)) w')
    (h : Real (.atom V (inp x (bs.map (wAt w') ++ ys))) (wAt w' q)) :
    Real (.atom V (inp x ((bs.map ([d] ++ ·)).map (wAt w) ++ ys))) (wAt w ([d] ++ q)) := by
  have hq : WSteps (wAt w ([d] ++ q)) (wAt w' q) := WSteps.appT hw _
  refine Real.back (.atom V _) hq (real_atom_back (inp_red x ?_) h)
  rw [List.map_map]
  exact Red2.append (Red2.map _ _ (fun b => WSteps.appT hw _) bs) (Red2.refl ys)

/-- A realizer of the source gives good bits and witness. -/
theorem good_of_realX : ∀ (M : XF) (ys : List Term) (r : Term), Real (M.src ys) r → ∃ β w, GoodX M ys β w
  | .atom V x, ys, r, h => ⟨.leaf true, r, trivial, rfl, fun V' x' bs q hm _ => by
      simp only [leavesX, List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      exact h⟩
  | .and A B, ys, r, h => by
    obtain ⟨a, b, _, ha, hb⟩ := h
    obtain ⟨βa, wa, hsa, hea, hla⟩ := good_of_realX A ys a ha
    obtain ⟨βb, wb, hsb, heb, hlb⟩ := good_of_realX B ys b hb
    refine ⟨.node βa βb, pairT wa wb, ⟨hsa, hsb⟩, by simp [evalBX, hea, heb], ?_⟩
    intro V x bs q hm hq
    rw [leavesX, leaves_prefixX A, leaves_prefixX B] at hm
    simp only [List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨V', x', bs', q'⟩, hm, e⟩ | ⟨⟨V', x', bs', q'⟩, hm, e⟩
    · simp only [Prod.mk.injEq, List.append_nil] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      exact good_lift (d := false) (pairT_fst wa wb)
        (hla V' x' bs' q' hm (by simpa [BT.sub, BT.child] using hq))
    · simp only [Prod.mk.injEq, List.append_nil] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      exact good_lift (d := true) (pairT_snd wa wb)
        (hlb V' x' bs' q' hm (by simpa [BT.sub, BT.child] using hq))
  | .or A B, ys, r, h => by
    rcases h with ⟨a, _, ha⟩ | ⟨b, _, hb⟩
    · obtain ⟨βa, wa, hsa, hea, hla⟩ := good_of_realX A ys a ha
      refine ⟨.node βa (clearX B), pairT wa K, ⟨hsa, clear_shapeX B⟩, by simp [evalBX, hea], ?_⟩
      intro V x bs q hm hq
      rw [leavesX, leaves_prefixX A, leaves_prefixX B] at hm
      simp only [List.mem_append, List.mem_map] at hm
      rcases hm with ⟨⟨V', x', bs', q'⟩, hm, e⟩ | ⟨⟨V', x', bs', q'⟩, hm, e⟩
      · simp only [Prod.mk.injEq, List.append_nil] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact good_lift (d := false) (pairT_fst wa K)
          (hla V' x' bs' q' hm (by simpa [BT.sub, BT.child] using hq))
      · simp only [Prod.mk.injEq, List.append_nil] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        have hc := clear_leavesX B V' x' bs' q' hm
        simp [BT.sub, BT.child, hc] at hq
    · obtain ⟨βb, wb, hsb, heb, hlb⟩ := good_of_realX B ys b hb
      refine ⟨.node (clearX A) βb, pairT K wb, ⟨clear_shapeX A, hsb⟩, by simp [evalBX, heb], ?_⟩
      intro V x bs q hm hq
      rw [leavesX, leaves_prefixX A, leaves_prefixX B] at hm
      simp only [List.mem_append, List.mem_map] at hm
      rcases hm with ⟨⟨V', x', bs', q'⟩, hm, e⟩ | ⟨⟨V', x', bs', q'⟩, hm, e⟩
      · simp only [Prod.mk.injEq, List.append_nil] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        have hc := clear_leavesX A V' x' bs' q' hm
        simp [BT.sub, BT.child, hc] at hq
      · simp only [Prod.mk.injEq, List.append_nil] at e
        obtain ⟨rfl, rfl, rfl, rfl⟩ := e
        exact good_lift (d := true) (pairT_snd K wb)
          (hlb V' x' bs' q' hm (by simpa [BT.sub, BT.child] using hq))
  | .ex B, ys, r, h => by
    obtain ⟨y, b, _, hb⟩ := h
    obtain ⟨βb, wb, hsb, heb, hlb⟩ := good_of_realX B (y :: ys) b hb
    refine ⟨.node (.leaf false) βb, pairT y wb, hsb, heb, ?_⟩
    intro V x bs q hm hq
    rw [leavesX, leaves_prefixX B] at hm
    simp only [List.mem_map] at hm
    obtain ⟨⟨V', x', bs', q'⟩, hm, e⟩ := hm
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    have hl := hlb V' x' bs' q' hm (by simpa [BT.sub, BT.child] using hq)
    have hq' : WSteps (wAt (pairT y wb) ([] ++ [true] ++ q')) (wAt wb q') :=
      WSteps.appT (pairT_snd y wb) _
    refine Real.back (.atom V' _) hq' (real_atom_back (inp_red x' ?_) hl)
    rw [List.map_append, List.map_map, List.append_assoc]
    refine Red2.append (Red2.map _ _ (fun c => WSteps.appT (pairT_snd y wb) _) bs') ?_
    exact .cons (pairT_fst y wb) (Red2.refl ys)
  | .mp _ _ A, ys, r, h => good_of_realX A ys r h

/-- Good bits and witness are accepted. -/
theorem accepted_of_goodX {M : XF} {β : BT} {w : Term} (h : GoodX M [] β w) : AcceptsX M β w := by
  obtain ⟨hs, he, hl⟩ := h
  refine ⟨hs, fun P hP => ?_⟩
  rcases List.mem_cons.1 hP with rfl | hP
  · exact (phi_iffX hs w).2 he
  · obtain ⟨⟨V, x, bs, q⟩, hm, rfl⟩ := List.mem_map.1 hP
    obtain ⟨⟨b, hb⟩, hp⟩ := leaf_pathX M β [] [] hs (.refl _) V x bs q hm
    refine (leaf_iffX hb hp).2 fun hbt => ?_
    subst hbt
    have := hl V x bs q hm hb
    rw [List.append_nil] at this
    exact this

/-- **Completeness, composed**: a realizer of the formula's source yields
    bits and a witness the statement accepts. -/
theorem accepted_of_realX {M : XF} {r : Term} (h : Real (M.src []) r) : ∃ β w, AcceptsX M β w := by
  obtain ⟨β, w, hg⟩ := good_of_realX M [] r h
  exact ⟨β, w, accepted_of_goodX hg⟩

-- ---------------------------------------------------------------------------
-- The composition theorem
-- ---------------------------------------------------------------------------

/-- **The composition theorem, with `∃` and knowledge implication.**  Over
    a proof system for evaluation statements, the statement of a formula
    gives a proof system for it:
    - **complete**: a realizer of the formula's source yields bits and a
      witness with an honest proof, all of whose proofs verify;
    - **knowledge-sound**: given the certificates, from any proof that
      verifies the extractor's bits and witness read back as a realizer of
      the formula;
    - **zero knowledge** and so **witness-indistinguishable**, the
      interface's own, reindexed. -/
theorem composeX (ps : EvalPS EvalStmt EvalRel) (M : XF) :
    (∀ r, Real (M.src []) r → ∃ β w, AcceptsX M β w ∧
      (∃ π, ps.supp (ps.prove (evalStmtOfX M) β w) π) ∧
      ∀ π, ps.supp (ps.prove (evalStmtOfX M) β w) π → ps.verify (evalStmtOfX M) π) ∧
    (M.Cert [] → ∀ π, ps.verify (evalStmtOfX M) π →
      Real (M.form []) (readBackX M (ps.ext (evalStmtOfX M) π).1 (ps.ext (evalStmtOfX M) π).2 [])) ∧
    (∀ β w, AcceptsX M β w → ps.indist (ps.prove (evalStmtOfX M) β w) (ps.sim (evalStmtOfX M))) ∧
    (∀ β w β' w', AcceptsX M β w → AcceptsX M β' w' →
      ps.indist (ps.prove (evalStmtOfX M) β w) (ps.prove (evalStmtOfX M) β' w')) := by
  refine ⟨fun r hr => ?_, fun hc π hv => ?_, fun β w h => ps.zk _ β w h, fun β w β' w' h h' => ?_⟩
  · obtain ⟨β, w, hacc⟩ := accepted_of_realX hr
    exact ⟨β, w, hacc, ps.complete _ β w hacc⟩
  · exact real_of_acceptedX (ps.knowledge _ π hv) hc
  · exact ps.indist_equiv.trans (ps.zk _ β w h) (ps.indist_equiv.symm (ps.zk _ β' w' h'))

-- ---------------------------------------------------------------------------
-- A library of certified witness maps, and the formulas a statement names
-- ---------------------------------------------------------------------------

/-- `[a] a K`: the first component of a pair. -/
def fstMap : Term := S ⬝ I ⬝ (K ⬝ K)
/-- `[a] a (K I)`: the second. -/
def sndMap : Term := S ⬝ I ⬝ (K ⬝ (K ⬝ I))
/-- `[x y] ⟨y, x⟩`. -/
def flipT : Term := toTerm (absN [0, 1] (pairXO (.var 1) (.var 0)))
/-- `[a] a flipT`: a pair, swapped. -/
def swapMap : Term := S ⬝ I ⬝ (K ⬝ flipT)
/-- `[a] inl a`. -/
def inlMap : Term := toTerm (absN [0] (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .var 0))))
/-- `[a] inr a`. -/
def inrMap : Term := toTerm (absN [0] (.K ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .var 0))))

theorem sI_K (a k : Term) : WSteps (S ⬝ I ⬝ (K ⬝ k) ⬝ a) (a ⬝ k) :=
  (ws1 (.S _ _ _)).trans ((WSteps.left _ (ws1 (.I _))).trans (WSteps.right _ (ws1 (.K _ _))))

theorem flipT_app (x y : Term) : WSteps (flipT ⬝ x ⬝ y) (pairT y x) :=
  absN_beta_close [0, 1] (pairXO (.var 1) (.var 0)) (fun _ => K) [x, y] rfl

theorem inlMap_app (a : Term) : WSteps (inlMap ⬝ a) (inlT a) :=
  absN_beta_close [0] _ (fun _ => K) [a] rfl

theorem inrMap_app (a : Term) : WSteps (inrMap ⬝ a) (inrT a) :=
  absN_beta_close [0] _ (fun _ => K) [a] rfl

theorem fst_real {A B : Form} {a : Term} (h : Real (.and A B) a) : Real A (fstMap ⬝ a) := by
  obtain ⟨x, y, hk, hx, _⟩ := h
  exact Real.back A ((sI_K a K).trans ((hk K).trans (ws1 (.K _ _)))) hx

theorem snd_real {A B : Form} {a : Term} (h : Real (.and A B) a) : Real B (sndMap ⬝ a) := by
  obtain ⟨x, y, hk, _, hy⟩ := h
  exact Real.back B ((sI_K a (K ⬝ I)).trans ((hk (K ⬝ I)).trans
    ((ws1 (.left _ (.K _ _))).trans (ws1 (.I _))))) hy

theorem swap_real {A B : Form} {a : Term} (h : Real (.and A B) a) : Real (.and B A) (swapMap ⬝ a) := by
  obtain ⟨x, y, hk, hx, hy⟩ := h
  have hs : WSteps (swapMap ⬝ a) (pairT y x) := (sI_K a flipT).trans ((hk flipT).trans (flipT_app x y))
  exact ⟨y, x, fun k => (WSteps.left k hs).trans (pairT_app y x k), hy, hx⟩

theorem inl_real {A B : Form} {a : Term} (h : Real A a) : Real (.or A B) (inlMap ⬝ a) :=
  .inl ⟨a, fun f g => (WSteps.left g (WSteps.left f (inlMap_app a))).trans (inlT_app a f g), h⟩

theorem inr_real {A B : Form} {b : Term} (h : Real B b) : Real (.or A B) (inrMap ⬝ b) :=
  .inr ⟨b, fun f g => (WSteps.left g (WSteps.left f (inrMap_app b))).trans (inrT_app b f g), h⟩

/-- The conclusions of the library's maps. -/
def swapF : Form → Form
  | .and A B => .and B A
  | X => X

def fstF : Form → Form
  | .and A _ => A
  | X => X

def sndF : Form → Form
  | .and _ B => B
  | X => X

/-- **The formulas a statement names**: atoms, `∧`, `∨`, `∃`, and the
    library's knowledge implications: `swap A`, `fst A`, `snd A` from a
    proof of a conjunction `A`, and `inl A B` (`A ∨ B` from `A`), `inr A B`
    (`A ∨ B` from `B`). -/
inductive XS
  | atom (V x : Term)
  | and (A B : XS)
  | or (A B : XS)
  | ex (B : XS)
  | swap (A : XS)
  | fst (A : XS)
  | snd (A : XS)
  | inl (A B : XS)
  | inr (A B : XS)

/-- Its formula.  An injection's unproved side is read with no bound
    values. -/
def XS.toXF : XS → XF
  | .atom V x => .atom V x
  | .and A B => .and A.toXF B.toXF
  | .or A B => .or A.toXF B.toXF
  | .ex B => .ex B.toXF
  | .swap A => .mp swapMap swapF A.toXF
  | .fst A => .mp fstMap fstF A.toXF
  | .snd A => .mp sndMap sndF A.toXF
  | .inl A B => .mp inlMap (fun X => .or X (B.toXF.form [])) A.toXF
  | .inr A B => .mp inrMap (fun X => .or (A.toXF.form []) X) B.toXF

/-- A map from a conjunction applies to a conjunction. -/
def XS.isAnd : XS → Bool
  | .and _ _ => true
  | _ => false

/-- **Well-formed**: every projection or swap applies to a conjunction. -/
def XS.wf : XS → Bool
  | .atom _ _ => true
  | .and A B => A.wf && B.wf
  | .or A B => A.wf && B.wf
  | .ex B => B.wf
  | .swap A => A.isAnd && A.wf
  | .fst A => A.isAnd && A.wf
  | .snd A => A.isAnd && A.wf
  | .inl A _ => A.wf
  | .inr _ B => B.wf

/-- **The library's certificates**: a well-formed formula's maps are
    certified, under any bound values. -/
theorem XS.cert : ∀ (s : XS) (ys : List Term), s.wf = true → s.toXF.Cert ys
  | .atom _ _, _, _ => trivial
  | .and A B, ys, h => by
    simp only [XS.wf, Bool.and_eq_true] at h
    exact ⟨XS.cert A ys h.1, XS.cert B ys h.2⟩
  | .or A B, ys, h => by
    simp only [XS.wf, Bool.and_eq_true] at h
    exact ⟨XS.cert A ys h.1, XS.cert B ys h.2⟩
  | .ex B, ys, h => fun y => XS.cert B (y :: ys) h
  | .swap A, ys, h => by
    simp only [XS.wf, Bool.and_eq_true] at h
    refine ⟨XS.cert A ys h.2, fun a ha => ?_⟩
    cases A with
    | and A1 A2 => exact swap_real ha
    | _ => simp [XS.isAnd] at h
  | .fst A, ys, h => by
    simp only [XS.wf, Bool.and_eq_true] at h
    refine ⟨XS.cert A ys h.2, fun a ha => ?_⟩
    cases A with
    | and A1 A2 => exact fst_real ha
    | _ => simp [XS.isAnd] at h
  | .snd A, ys, h => by
    simp only [XS.wf, Bool.and_eq_true] at h
    refine ⟨XS.cert A ys h.2, fun a ha => ?_⟩
    cases A with
    | and A1 A2 => exact snd_real ha
    | _ => simp [XS.isAnd] at h
  | .inl A _, ys, h => ⟨XS.cert A ys h, fun _ ha => inl_real ha⟩
  | .inr _ B, ys, h => ⟨XS.cert B ys h, fun _ hb => inr_real hb⟩

/-- **Knowledge soundness for a named formula**: no certificate to supply;
    well-formedness, which the statement check decides, certifies it. -/
theorem real_of_acceptedXS {s : XS} {β : BT} {w : Term} (h : AcceptsX s.toXF β w) (hw : s.wf = true) :
    Real (s.toXF.form []) (readBackX s.toXF β w []) :=
  real_of_acceptedX h (XS.cert s [] hw)

end Compose
