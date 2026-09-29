import Ski.Realize
import Ski.Compile
import Ski.Weak

set_option linter.unusedSectionVars false

open Term

/-!
# Zero knowledge, composed: the monolithic composition theorem

Part II composes proofs of NP atoms with `∧` and `∨`: the Σ-protocol
algebra, threshold included, as nested connectives.  This module compiles
a composed formula to **one statement about evaluation** and proves that a
proof system for such statements, assumed, gives a proof system for the
formula with its completeness, knowledge soundness and zero knowledge.

**Why a list of evaluations, with bits.**  An atom is realized when its
verifier evaluates to the literal `K` (`real_atom_iff`).  That is
intensional: `S (K K) I` behaves as `K` whenever it is applied to two
arguments, and is not `K`.  So, we argue (this is an argument, not a
theorem), no combinator `C` conjoins two such evaluations exactly: the `K`
that `C a b` reaches descends from at most one of `a` and `b`, whether `C`
consumes its arguments or returns one; replacing the other by
`S (K K) I`, which weak reduction cannot tell from `K` once applied to two
arguments, leaves the result `K` while that argument no longer evaluates
to `K`.  The machine observes a literal `K` only where a run halts.  The
statement is therefore a list of public terms, each of which, applied to
the bits and the shared hidden witness, must evaluate to `K`; and the
choices of `∨` are hidden **bits**, literal Scott Booleans, so a formula
over them is exact.  The bits' literalness is load-bearing: with the bits
an arbitrary term, `K (K K)` in place of every bit passes every guard and
the formula check.

**The statement of a formula** (`stmtOf`), for a public tree of bits
`β` and a hidden term `w`:
- for each atom `atom V x` at a path `q` of the formula, the guard
  `[ρ w] (ρ·q) (V x (w·q)) K`: when the atom's bit is set, its verifier
  must accept the witness's component at `q`; when clear, nothing;
- the formula over the bits, `[ρ w] (φ ρ) K (K I)`, which must be true.

**The theorems.**
- `accepted_of_real`: a realizer of the formula yields bits and a witness
  the statement accepts (the composed prover is complete).
- `real_of_accepted`: bits and a witness the statement accepts read back
  as a realizer of the formula (`readBack`): the composed extractor.
- `compose`: over an assumed proof system for evaluation statements,
  any list of terms and any shape of bits (`EvalPS` for `EvalRel`), the
  composed system for a formula, reindexed along `stmtOf`, is complete
  (a proof exists and verifies), knowledge-sound (its extractor's output
  reads back as a realizer) and zero knowledge, and so
  witness-indistinguishable: `∨`'s hiding.

No cryptography is proved: `EvalPS`'s three properties are fields,
idealized (knowledge soundness as a deterministic extractor from any
accepted proof, zero knowledge as an abstract indistinguishability).  So
the zero-knowledge conclusions are the field, reindexed, and constrain
nothing beyond it; the content is the exactness lemmas.
-/

namespace Compose

-- ---------------------------------------------------------------------------
-- Scott pairs, injections and Booleans, as closed terms
-- ---------------------------------------------------------------------------

/-- `[k] k a b`. -/
def pairT (a b : Term) : Term := S ⬝ (S ⬝ I ⬝ (K ⬝ a)) ⬝ (K ⬝ b)

/-- `[f g] f a`. -/
def inlT (a : Term) : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ I ⬝ (K ⬝ a))

/-- `[f g] g b`. -/
def inrT (b : Term) : Term := K ⬝ (S ⬝ I ⬝ (K ⬝ b))

/-- A literal Scott Boolean. -/
def boolT : Bool → Term
  | true => K
  | false => K ⬝ I

/-- The first and second projections of a pair. -/
def fstT : Term := K
def sndT : Term := K ⬝ I

theorem ws1 {t u : Term} (h : WStep t u) : WSteps t u := .single h

theorem sI_app (a k : Term) : WSteps (S ⬝ I ⬝ (K ⬝ a) ⬝ k) (k ⬝ a) :=
  (ws1 (.S _ _ _)).trans ((WSteps.left _ (ws1 (.I _))).trans (WSteps.right _ (ws1 (.K _ _))))

theorem pairT_app (a b k : Term) : WSteps (pairT a b ⬝ k) (k ⬝ a ⬝ b) :=
  (ws1 (.S _ _ _)).trans ((WSteps.left _ (sI_app a k)).trans (WSteps.right _ (ws1 (.K _ _))))

theorem pairT_fst (a b : Term) : WSteps (pairT a b ⬝ fstT) a :=
  (pairT_app a b K).trans (ws1 (.K _ _))

theorem pairT_snd (a b : Term) : WSteps (pairT a b ⬝ sndT) b :=
  (pairT_app a b (K ⬝ I)).trans ((ws1 (.left _ (.K _ _))).trans (ws1 (.I _)))

theorem inlT_app (a f g : Term) : WSteps (inlT a ⬝ f ⬝ g) (f ⬝ a) :=
  (WSteps.left _ ((ws1 (.S _ _ _)).trans (ws1 (.left _ (.K _ _))))).trans
    ((ws1 (.K _ _)).trans (sI_app a f))

theorem inrT_app (b f g : Term) : WSteps (inrT b ⬝ f ⬝ g) (g ⬝ b) :=
  (WSteps.left _ (ws1 (.K _ _))).trans (sI_app b g)

-- ---------------------------------------------------------------------------
-- Evaluating to K
-- ---------------------------------------------------------------------------

/-- `K` takes no weak step. -/
theorem K_wsteps {u : Term} (h : WSteps K u) : u = K := by
  cases h with
  | refl => rfl
  | step s _ => cases s

/-- **Evaluating to `K` is weakly reducing to it.** -/
theorem eval_K_iff {t : Term} : Eval t K ↔ WSteps t K := by
  constructor
  · exact fun h => h.1.weak
  · intro h
    obtain ⟨v, hv, hvw⟩ := eval_back h ⟨.refl K, .K⟩
    rw [hv.2.wsteps_K hvw] at hv
    exact hv

/-- A weak reduct reaches `K` exactly when the term does (Church–Rosser,
    and `K` is normal). -/
theorem wsteps_K_iff {t u : Term} (h : WSteps t u) : WSteps t K ↔ WSteps u K := by
  constructor
  · intro hk
    obtain ⟨v, huv, hkv⟩ := church_rosser h hk
    rw [K_wsteps hkv] at huv
    exact huv
  · exact h.trans

/-- `F` never reaches `K`. -/
theorem F_not_K : ¬ WSteps (K ⬝ I) K := fun h => by
  have := (Whnf.K1 I).wsteps_K h
  cases this

theorem boolT_sel (b : Bool) (x y : Term) : WSteps (boolT b ⬝ x ⬝ y) (if b then x else y) := by
  cases b with
  | true => exact ws1 (.K _ _)
  | false => exact (ws1 (.left _ (.K _ _))).trans (ws1 (.I _))

-- ---------------------------------------------------------------------------
-- Formulas, bits, paths
-- ---------------------------------------------------------------------------

/-- The Σ-protocol algebra: atoms under `∧` and `∨`. -/
inductive MF
  | atom (V x : Term)
  | and (A B : MF)
  | or (A B : MF)

def MF.toForm : MF → Form
  | .atom V x => .atom V x
  | .and A B => .and A.toForm B.toForm
  | .or A B => .or A.toForm B.toForm

/-- A tree of bits, one per atom. -/
inductive BT
  | leaf (b : Bool)
  | node (l r : BT)

/-- The bits as a literal term: Scott Booleans in Scott pairs. -/
def BT.enc : BT → Term
  | .leaf b => boolT b
  | .node l r => pairT l.enc r.enc

/-- The bits have the formula's shape: a leaf per atom. -/
def Shape : MF → BT → Prop
  | .atom _ _, .leaf _ => True
  | .and A B, .node l r => Shape A l ∧ Shape B r
  | .or A B, .node l r => Shape A l ∧ Shape B r
  | _, _ => False

/-- The formula, over the bits. -/
def evalB : MF → BT → Bool
  | .atom _ _, .leaf b => b
  | .and A B, .node l r => evalB A l && evalB B r
  | .or A B, .node l r => evalB A l || evalB B r
  | _, _ => false

/-- A path's projections: `false` the first, `true` the second. -/
def projs (p : List Bool) : List Term := p.map fun d => if d then sndT else fstT

/-- The atoms of a formula, each with its verifier, input and path. -/
def leaves : MF → List Bool → List (Term × Term × List Bool)
  | .atom V x, p => [(V, x, p)]
  | .and A B, p => leaves A (p ++ [false]) ++ leaves B (p ++ [true])
  | .or A B, p => leaves A (p ++ [false]) ++ leaves B (p ++ [true])

/-- One step down: the first or second subtree; a leaf stays. -/
def BT.child : BT → Bool → BT
  | .node l _, false => l
  | .node _ r, true => r
  | .leaf b, _ => .leaf b

/-- The subtree of the bits at a path. -/
def BT.sub : BT → List Bool → BT
  | β, [] => β
  | β, d :: p => (β.child d).sub p

theorem BT.sub_append : ∀ (β : BT) (p q : List Bool), β.sub (p ++ q) = (β.sub p).sub q
  | _, [], _ => rfl
  | β, d :: p, q => BT.sub_append (β.child d) p q

theorem enc_proj_step (l r : BT) (d : Bool) :
    WSteps ((BT.node l r).enc ⬝ (if d then sndT else fstT)) ((BT.node l r).sub [d]).enc := by
  cases d with
  | true => exact pairT_snd _ _
  | false => exact pairT_fst _ _

-- ---------------------------------------------------------------------------
-- The statement's terms
-- ---------------------------------------------------------------------------

/-- `t` applied to a path's projections, as an open term. -/
def appP (t : OTerm) (p : List Bool) : OTerm := appL t ((projs p).map Term.toO)

/-- The formula over the bits `ρ` (variable 0), as a Scott Boolean. -/
def fm : MF → List Bool → OTerm
  | .atom _ _, p => appP (.var 0) p
  | .and A B, p => fm A (p ++ [false]) ⬝ₒ fm B (p ++ [true]) ⬝ₒ (.K ⬝ₒ .I)
  | .or A B, p => fm A (p ++ [false]) ⬝ₒ .K ⬝ₒ fm B (p ++ [true])

/-- The formula check: `[ρ w] (φ ρ) K (K I)`. -/
def phiStmt (M : MF) : Term := toTerm (absN [0, 1] (fm M [] ⬝ₒ .K ⬝ₒ (.K ⬝ₒ .I)))

/-- An atom's guard: `[ρ w] (ρ·q) (V x (w·q)) K`. -/
def leafStmt (V x : Term) (q : List Bool) : Term :=
  toTerm (absN [0, 1] (appP (.var 0) q ⬝ₒ (V.toO ⬝ₒ x.toO ⬝ₒ appP (.var 1) q) ⬝ₒ .K))

/-- **The statement of a formula**: its formula check and its atoms'
    guards, each to evaluate to `K` on the bits and the witness. -/
def stmtOf (M : MF) : List Term := phiStmt M :: (leaves M []).map fun (V, x, q) => leafStmt V x q

/-- **An evaluation statement**: public terms, and the shape the bits must
    have. -/
abbrev EvalStmt := List Term × (BT → Prop)

/-- **The evaluation relation**: the bits have the shape, and every term
    evaluates to `K` on the literal bits and the witness. -/
def EvalRel (s : EvalStmt) (β : BT) (w : Term) : Prop :=
  s.2 β ∧ ∀ P ∈ s.1, Eval (P ⬝ β.enc ⬝ w) K

/-- A formula's statement, as an evaluation statement. -/
def evalStmtOf (M : MF) : EvalStmt := (stmtOf M, Shape M)

/-- **The relation of a formula**: its evaluation statement's. -/
def Accepts (M : MF) (β : BT) (w : Term) : Prop := EvalRel (evalStmtOf M) β w

-- ---------------------------------------------------------------------------
-- Closing the statement's terms
-- ---------------------------------------------------------------------------

theorem close_appL (σ : Nat → Term) : ∀ (t : OTerm) (as : List OTerm),
    (appL t as).close σ = appT (t.close σ) (as.map (OTerm.close σ))
  | _, [] => rfl
  | t, a :: as => close_appL σ (t ⬝ₒ a) as

theorem close_appP (σ : Nat → Term) (i : Nat) (p : List Bool) :
    (appP (.var i) p).close σ = appT (σ i) (projs p) := by
  unfold appP
  rw [close_appL, List.map_map]
  congr 1
  have : ∀ l : List Term, List.map (OTerm.close σ ∘ Term.toO) l = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons, Function.comp_apply, close_toO]; rw [ih]
  exact this _

/-- The environment a statement closes under: the bits at 0, the witness
    at 1. -/
def env (B W : Term) : Nat → Term := overrideC (fun _ => K) [0, 1] [B, W]

theorem env0 (B W : Term) : env B W 0 = B := by simp [env, overrideC, updC]
theorem env1 (B W : Term) : env B W 1 = W := by simp [env, overrideC, updC]

theorem stmt_beta (body : OTerm) (B W : Term) :
    WSteps (toTerm (absN [0, 1] body) ⬝ B ⬝ W) (body.close (env B W)) :=
  absN_beta_close [0, 1] body (fun _ => K) [B, W] rfl

-- ---------------------------------------------------------------------------
-- The bits read back
-- ---------------------------------------------------------------------------

/-- Along a path that stays inside the tree, projections reduce to the
    subtree. -/
theorem proj_sub (β : BT) : ∀ (p : List Bool), (∃ l r, β.sub p = .node l r) →
    WSteps (appT β.enc (projs p)) (β.sub p).enc →
    ∀ e : Bool, WSteps (appT β.enc (projs (p ++ [e]))) (β.sub (p ++ [e])).enc
  | p, ⟨l, r, hlr⟩, h, e => by
    rw [projs, List.map_append, appT_append, BT.sub_append, hlr]
    have := WSteps.appT h [if e then sndT else fstT]
    rw [hlr] at this
    exact this.trans (enc_proj_step l r e)

/-- **The formula, applied to the literal bits, reduces to its value**, for
    bits of the formula's shape. -/
theorem fm_red : ∀ (M : MF) (β : BT) (p : List Bool) (W : Term), Shape M (β.sub p) →
    WSteps (appT β.enc (projs p)) (β.sub p).enc →
    WSteps ((fm M p).close (env β.enc W)) (boolT (evalB M (β.sub p)))
  | .atom _ _, β, p, W, hs, hp => by
    unfold fm
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
      have pa := proj_sub β p ⟨l, r, hb⟩ hp false
      have pb := proj_sub β p ⟨l, r, hb⟩ hp true
      have ha := fm_red A β (p ++ [false]) W (by rw [hl]; exact hs.1) pa
      have hbb := fm_red B β (p ++ [true]) W (by rw [hr]; exact hs.2) pb
      rw [hl] at ha
      rw [hr] at hbb
      show WSteps ((fm A (p ++ [false])).close _ ⬝ (fm B (p ++ [true])).close _ ⬝ (K ⬝ I)) _
      refine (WSteps.left _ (WSteps.left _ ha)).trans ((boolT_sel _ _ _).trans ?_)
      show WSteps _ (boolT (evalB A l && evalB B r))
      cases evalB A l with
      | true => exact hbb
      | false => exact .refl _
  | .or A B, β, p, W, hs, hp => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      have pa := proj_sub β p ⟨l, r, hb⟩ hp false
      have pb := proj_sub β p ⟨l, r, hb⟩ hp true
      have ha := fm_red A β (p ++ [false]) W (by rw [hl]; exact hs.1) pa
      have hbb := fm_red B β (p ++ [true]) W (by rw [hr]; exact hs.2) pb
      rw [hl] at ha
      rw [hr] at hbb
      show WSteps ((fm A (p ++ [false])).close _ ⬝ K ⬝ (fm B (p ++ [true])).close _) _
      refine (WSteps.left _ (WSteps.left _ ha)).trans ((boolT_sel _ _ _).trans ?_)
      show WSteps _ (boolT (evalB A l || evalB B r))
      cases evalB A l with
      | true => exact .refl _
      | false => exact hbb

/-- **The formula check accepts exactly when the formula is true of the
    bits.** -/
theorem phi_iff {M : MF} {β : BT} (hs : Shape M β) (W : Term) :
    Eval (phiStmt M ⬝ β.enc ⬝ W) K ↔ evalB M β = true := by
  have hr := fm_red M β [] W hs (.refl _)
  have hred : WSteps (phiStmt M ⬝ β.enc ⬝ W) (if evalB M β then K else K ⬝ I) :=
    (stmt_beta _ _ _).trans ((WSteps.left _ (WSteps.left _ hr)).trans (boolT_sel _ _ _))
  rw [eval_K_iff, wsteps_K_iff hred]
  cases evalB M β with
  | true => exact ⟨fun _ => rfl, fun _ => .refl _⟩
  | false => exact ⟨fun h => absurd h F_not_K, fun h => by cases h⟩

/-- **An atom's guard accepts exactly when its bit is clear or its verifier
    accepts the witness's component.** -/
theorem leaf_iff {V x W : Term} {β : BT} {q : List Bool} {b : Bool} (hb : β.sub q = .leaf b)
    (hp : WSteps (appT β.enc (projs q)) (β.sub q).enc) :
    Eval (leafStmt V x q ⬝ β.enc ⬝ W) K ↔ (b = true → Real (.atom V x) (appT W (projs q))) := by
  have hred : WSteps (leafStmt V x q ⬝ β.enc ⬝ W)
      (boolT b ⬝ (V ⬝ x ⬝ appT W (projs q)) ⬝ K) := by
    refine (stmt_beta _ _ _).trans ?_
    show WSteps ((appP (.var 0) q).close _ ⬝ (V.toO.close _ ⬝ x.toO.close _ ⬝
      (appP (.var 1) q).close _) ⬝ K) _
    rw [close_appP, close_appP, env0, env1, close_toO, close_toO]
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
-- Leaves and paths
-- ---------------------------------------------------------------------------

theorem leaves_prefix : ∀ (M : MF) (p : List Bool),
    leaves M p = (leaves M []).map fun (V, x, q) => (V, x, p ++ q)
  | .atom V x, p => by simp [leaves]
  | .and A B, p => by
    simp only [leaves, List.map_append]
    rw [leaves_prefix A (p ++ [false]), leaves_prefix A ([] ++ [false]),
      leaves_prefix B (p ++ [true]), leaves_prefix B ([] ++ [true])]
    simp [List.map_map, Function.comp_def, List.append_assoc]
  | .or A B, p => by
    simp only [leaves, List.map_append]
    rw [leaves_prefix A (p ++ [false]), leaves_prefix A ([] ++ [false]),
      leaves_prefix B (p ++ [true]), leaves_prefix B ([] ++ [true])]
    simp [List.map_map, Function.comp_def, List.append_assoc]

/-- Each leaf's path leads to a leaf of bits of the formula's shape, and its
    projections reduce to it. -/
theorem leaf_path : ∀ (M : MF) (β : BT) (p : List Bool), Shape M (β.sub p) →
    WSteps (appT β.enc (projs p)) (β.sub p).enc →
    ∀ V x q, (V, x, q) ∈ leaves M p →
      (∃ b, β.sub q = .leaf b) ∧ WSteps (appT β.enc (projs q)) (β.sub q).enc
  | .atom V' x', β, p, hs, hp, V, x, q, hm => by
    simp [leaves] at hm
    obtain ⟨_, _, rfl⟩ := hm
    refine ⟨?_, hp⟩
    cases hb : β.sub q with
    | leaf b => exact ⟨b, rfl⟩
    | node _ _ => rw [hb] at hs; cases hs
  | .and A B, β, p, hs, hp, V, x, q, hm => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [leaves, List.mem_append] at hm
      rcases hm with hm | hm
      · exact leaf_path A β _ (by rw [hl]; exact hs.1) (proj_sub β p ⟨l, r, hb⟩ hp false) V x q hm
      · exact leaf_path B β _ (by rw [hr]; exact hs.2) (proj_sub β p ⟨l, r, hb⟩ hp true) V x q hm
  | .or A B, β, p, hs, hp, V, x, q, hm => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs
      have hl : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [leaves, List.mem_append] at hm
      rcases hm with hm | hm
      · exact leaf_path A β _ (by rw [hl]; exact hs.1) (proj_sub β p ⟨l, r, hb⟩ hp false) V x q hm
      · exact leaf_path B β _ (by rw [hr]; exact hs.2) (proj_sub β p ⟨l, r, hb⟩ hp true) V x q hm

-- ---------------------------------------------------------------------------
-- Extraction: accepted bits and witness read back as a realizer
-- ---------------------------------------------------------------------------

/-- **The read-back**: a realizer of the formula from bits and a witness.
    An atom's realizer is the witness's component at its path; `∧` pairs;
    `∨` injects the side the bits make true. -/
def readBack : MF → BT → Term → List Bool → Term
  | .atom _ _, _, w, p => appT w (projs p)
  | .and A B, β, w, p => pairT (readBack A β w (p ++ [false])) (readBack B β w (p ++ [true]))
  | .or A B, β, w, p =>
    if evalB A (β.sub (p ++ [false])) then inlT (readBack A β w (p ++ [false]))
    else inrT (readBack B β w (p ++ [true]))

theorem readBack_real : ∀ (M : MF) (β : BT) (w : Term) (p : List Bool), Shape M (β.sub p) →
    evalB M (β.sub p) = true →
    (∀ V x q, (V, x, q) ∈ leaves M p → β.sub q = .leaf true → Real (.atom V x) (appT w (projs q))) →
    Real M.toForm (readBack M β w p)
  | .atom V x, β, w, p, hs, he, hl => by
    cases hb : β.sub p with
    | node _ _ => rw [hb] at hs; cases hs
    | leaf b =>
      rw [hb] at he
      cases he
      exact hl V x p (by simp [leaves]) hb
  | .and A B, β, w, p, hs, he, hl => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs he
      have hl' : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr' : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [evalB, Bool.and_eq_true] at he
      refine ⟨_, _, pairT_app _ _, ?_, ?_⟩
      · exact readBack_real A β w _ (by rw [hl']; exact hs.1) (by rw [hl']; exact he.1)
          (fun V x q hm => hl V x q (by simp [leaves, hm]))
      · exact readBack_real B β w _ (by rw [hr']; exact hs.2) (by rw [hr']; exact he.2)
          (fun V x q hm => hl V x q (by simp [leaves, hm]))
  | .or A B, β, w, p, hs, he, hl => by
    cases hb : β.sub p with
    | leaf _ => rw [hb] at hs; cases hs
    | node l r =>
      rw [hb] at hs he
      have hl' : β.sub (p ++ [false]) = l := by rw [BT.sub_append, hb]; rfl
      have hr' : β.sub (p ++ [true]) = r := by rw [BT.sub_append, hb]; rfl
      simp only [evalB, Bool.or_eq_true] at he
      unfold readBack
      rw [hl']
      cases hA : evalB A l with
      | true =>
        simp only [if_true]
        exact .inl ⟨_, inlT_app _, readBack_real A β w _ (by rw [hl']; exact hs.1)
          (by rw [hl']; exact hA) (fun V x q hm => hl V x q (by simp [leaves, hm]))⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        rw [hA] at he
        have hB : evalB B r = true := he.resolve_left (by simp)
        exact .inr ⟨_, inrT_app _, readBack_real B β w _ (by rw [hr']; exact hs.2)
          (by rw [hr']; exact hB) (fun V x q hm => hl V x q (by simp [leaves, hm]))⟩

/-- **Knowledge soundness, composed**: bits and a witness the statement
    accepts read back as a realizer of the formula. -/
theorem real_of_accepted {M : MF} {β : BT} {w : Term} (h : Accepts M β w) :
    Real M.toForm (readBack M β w []) := by
  obtain ⟨hs, hall⟩ := h
  have he : evalB M β = true := (phi_iff hs w).1 (hall _ (List.mem_cons_self))
  refine readBack_real M β w [] hs he fun V x q hm hq => ?_
  obtain ⟨_, hp⟩ := leaf_path M β [] hs (.refl _) V x q hm
  have hacc := hall (leafStmt V x q) (List.mem_cons_of_mem _ (List.mem_map.2 ⟨(V, x, q), hm, rfl⟩))
  exact (leaf_iff hq hp).1 hacc rfl

-- ---------------------------------------------------------------------------
-- Completeness: a realizer yields accepted bits and witness
-- ---------------------------------------------------------------------------

/-- The bits that choose nothing, in a formula's shape. -/
def clear : MF → BT
  | .atom _ _ => .leaf false
  | .and A B => .node (clear A) (clear B)
  | .or A B => .node (clear A) (clear B)

theorem clear_shape : ∀ M : MF, Shape M (clear M)
  | .atom _ _ => trivial
  | .and A B => ⟨clear_shape A, clear_shape B⟩
  | .or A B => ⟨clear_shape A, clear_shape B⟩

theorem clear_leaves : ∀ (M : MF) (q : List Bool) (V x : Term),
    (V, x, q) ∈ leaves M [] → (clear M).sub q = .leaf false
  | .atom _ _, q, V, x, hm => by simp [leaves] at hm; obtain ⟨_, _, rfl⟩ := hm; rfl
  | .and A B, q, V, x, hm => by
    rw [leaves, leaves_prefix A, leaves_prefix B] at hm
    simp only [List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨V', x', q'⟩, hm, e⟩ | ⟨⟨V', x', q'⟩, hm, e⟩
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2]; exact clear_leaves A q' V' x' hm
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2]; exact clear_leaves B q' V' x' hm
  | .or A B, q, V, x, hm => by
    rw [leaves, leaves_prefix A, leaves_prefix B] at hm
    simp only [List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨V', x', q'⟩, hm, e⟩ | ⟨⟨V', x', q'⟩, hm, e⟩
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2]; exact clear_leaves A q' V' x' hm
    · simp only [Prod.mk.injEq] at e; rw [← e.2.2]; exact clear_leaves B q' V' x' hm

/-- What completeness builds: bits of the formula's shape that make it
    true, and a witness whose component at every set leaf is accepted. -/
def Good (M : MF) (β : BT) (w : Term) : Prop :=
  Shape M β ∧ evalB M β = true ∧
    ∀ V x q, (V, x, q) ∈ leaves M [] → β.sub q = .leaf true → Real (.atom V x) (appT w (projs q))

/-- A realizer gives good bits and witness. -/
theorem good_of_real : ∀ (M : MF) (r : Term), Real M.toForm r → ∃ β w, Good M β w
  | .atom V x, r, h => ⟨.leaf true, r, trivial, rfl, fun V' x' q hm _ => by
      simp [leaves] at hm; obtain ⟨rfl, rfl, rfl⟩ := hm; exact h⟩
  | .and A B, r, h => by
    obtain ⟨a, b, _, ha, hb⟩ := h
    obtain ⟨βa, wa, hsa, hea, hla⟩ := good_of_real A a ha
    obtain ⟨βb, wb, hsb, heb, hlb⟩ := good_of_real B b hb
    refine ⟨.node βa βb, pairT wa wb, ⟨hsa, hsb⟩, by simp [evalB, hea, heb], ?_⟩
    intro V x q hm hq
    rw [leaves, leaves_prefix A, leaves_prefix B] at hm
    simp only [List.mem_append, List.mem_map] at hm
    rcases hm with ⟨⟨V', x', q'⟩, hm, e⟩ | ⟨⟨V', x', q'⟩, hm, e⟩
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      have := hla V' x' q' hm (by simpa [BT.sub, BT.child] using hq)
      refine Real.back (.atom V' x') ?_ this
      show WSteps (appT (pairT wa wb ⬝ fstT) (projs q')) _
      exact WSteps.appT (pairT_fst wa wb) _
    · simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      have := hlb V' x' q' hm (by simpa [BT.sub, BT.child] using hq)
      refine Real.back (.atom V' x') ?_ this
      show WSteps (appT (pairT wa wb ⬝ sndT) (projs q')) _
      exact WSteps.appT (pairT_snd wa wb) _
  | .or A B, r, h => by
    rcases h with ⟨a, _, ha⟩ | ⟨b, _, hb⟩
    · obtain ⟨βa, wa, hsa, hea, hla⟩ := good_of_real A a ha
      refine ⟨.node βa (clear B), pairT wa K, ⟨hsa, clear_shape B⟩, by simp [evalB, hea], ?_⟩
      intro V x q hm hq
      rw [leaves, leaves_prefix A, leaves_prefix B] at hm
      simp only [List.mem_append, List.mem_map] at hm
      rcases hm with ⟨⟨V', x', q'⟩, hm, e⟩ | ⟨⟨V', x', q'⟩, hm, e⟩
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        have := hla V' x' q' hm (by simpa [BT.sub, BT.child] using hq)
        refine Real.back (.atom V' x') ?_ this
        show WSteps (appT (pairT wa K ⬝ fstT) (projs q')) _
        exact WSteps.appT (pairT_fst wa K) _
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        have hc := clear_leaves B q' V' x' hm
        simp [BT.sub, BT.child, hc] at hq
    · obtain ⟨βb, wb, hsb, heb, hlb⟩ := good_of_real B b hb
      refine ⟨.node (clear A) βb, pairT K wb, ⟨clear_shape A, hsb⟩, by simp [evalB, heb], ?_⟩
      intro V x q hm hq
      rw [leaves, leaves_prefix A, leaves_prefix B] at hm
      simp only [List.mem_append, List.mem_map] at hm
      rcases hm with ⟨⟨V', x', q'⟩, hm, e⟩ | ⟨⟨V', x', q'⟩, hm, e⟩
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        have hc := clear_leaves A q' V' x' hm
        simp [BT.sub, BT.child, hc] at hq
      · simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        have := hlb V' x' q' hm (by simpa [BT.sub, BT.child] using hq)
        refine Real.back (.atom V' x') ?_ this
        show WSteps (appT (pairT K wb ⬝ sndT) (projs q')) _
        exact WSteps.appT (pairT_snd K wb) _

/-- Good bits and witness are accepted. -/
theorem accepted_of_good {M : MF} {β : BT} {w : Term} (h : Good M β w) : Accepts M β w := by
  obtain ⟨hs, he, hl⟩ := h
  refine ⟨hs, fun P hP => ?_⟩
  rcases List.mem_cons.1 hP with rfl | hP
  · exact (phi_iff hs w).2 he
  · obtain ⟨⟨V, x, q⟩, hm, rfl⟩ := List.mem_map.1 hP
    obtain ⟨⟨b, hb⟩, hp⟩ := leaf_path M β [] hs (.refl _) V x q hm
    refine (leaf_iff hb hp).2 fun hbt => ?_
    subst hbt
    exact hl V x q hm hb

/-- **Completeness, composed**: a realizer of the formula yields bits and a
    witness the statement accepts. -/
theorem accepted_of_real {M : MF} {r : Term} (h : Real M.toForm r) : ∃ β w, Accepts M β w := by
  obtain ⟨β, w, hg⟩ := good_of_real M r h
  exact ⟨β, w, accepted_of_good hg⟩

-- ---------------------------------------------------------------------------
-- The assumed interface, and the composition theorem
-- ---------------------------------------------------------------------------

/-- **The assumed interface**: a proof system for a relation, here the
    evaluation relation `EvalRel`.  A witness is literal bits and a hidden
    term.  Proving draws from a distribution the type `Dist` stands for.
    The three properties are assumed, idealized: completeness, that an
    honest proof exists and every one verifies; knowledge soundness as an
    extractor that reads a witness off any accepted proof; zero knowledge
    as a simulator whose output is indistinguishable from any honest
    proof. -/
structure EvalPS (Stmt : Type) (Rel : Stmt → BT → Term → Prop) where
  Proof : Type
  Dist : Type
  prove : Stmt → BT → Term → Dist
  supp : Dist → Proof → Prop
  verify : Stmt → Proof → Prop
  ext : Stmt → Proof → BT × Term
  sim : Stmt → Dist
  indist : Dist → Dist → Prop
  indist_equiv : Equivalence indist
  complete : ∀ s β w, Rel s β w → (∃ π, supp (prove s β w) π) ∧ ∀ π, supp (prove s β w) π → verify s π
  knowledge : ∀ s π, verify s π → Rel s (ext s π).1 (ext s π).2
  zk : ∀ s β w, Rel s β w → indist (prove s β w) (sim s)

/-- **The monolithic composition theorem.**  Over a proof system for
    evaluation statements, the statement of a formula of atoms under `∧`
    and `∨` gives a proof system for the formula:
    - **complete**: a realizer of the formula yields bits and a witness
      with an honest proof, all of whose proofs verify;
    - **knowledge-sound**: from any proof that verifies, the extractor's
      bits and witness read back as a realizer of the formula;
    - **zero knowledge**: an honest proof, for any accepted witness, is
      indistinguishable from the simulator's, which sees only the
      statement;
    - so **witness-indistinguishable**: proofs from two accepted
      witnesses, for instance two sides of an `∨`, are indistinguishable. -/
theorem compose (ps : EvalPS EvalStmt EvalRel) (M : MF) :
    (∀ r, Real M.toForm r → ∃ β w, Accepts M β w ∧
      (∃ π, ps.supp (ps.prove (evalStmtOf M) β w) π) ∧
      ∀ π, ps.supp (ps.prove (evalStmtOf M) β w) π → ps.verify (evalStmtOf M) π) ∧
    (∀ π, ps.verify (evalStmtOf M) π →
      Real M.toForm (readBack M (ps.ext (evalStmtOf M) π).1 (ps.ext (evalStmtOf M) π).2 [])) ∧
    (∀ β w, Accepts M β w → ps.indist (ps.prove (evalStmtOf M) β w) (ps.sim (evalStmtOf M))) ∧
    (∀ β w β' w', Accepts M β w → Accepts M β' w' →
      ps.indist (ps.prove (evalStmtOf M) β w) (ps.prove (evalStmtOf M) β' w')) := by
  refine ⟨fun r hr => ?_, fun π hv => ?_, fun β w h => ps.zk _ β w h, fun β w β' w' h h' => ?_⟩
  · obtain ⟨β, w, hacc⟩ := accepted_of_real hr
    exact ⟨β, w, hacc, ps.complete _ β w hacc⟩
  · exact real_of_accepted (ps.knowledge _ π hv)
  · exact ps.indist_equiv.trans (ps.zk _ β w h) (ps.indist_equiv.symm (ps.zk _ β' w' h'))

end Compose
