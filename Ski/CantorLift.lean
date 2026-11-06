import Ski.Search

open Term

/-!
# A behavioural lift at Stream → Bool, for m-local functionals

Theorem 6 of the B2 note `notes/B2-cantor-lift.md`, mechanized.  With
`Search.search` (Lemma 2) this module builds:

- `everyT p`: `p` holds everywhere, decided by searching for a
  counterexample (`every_spec`).
- `constT q`: `q` is constant, by `every` against `q` on the zero stream
  (`tab (K false)`) (`const_spec`, Corollary 3).
- `treeT q`: `q` tabulated as a decision tree; it reduces to the Lean-defined
  datum `D m φ`, which depends only on `φ`'s values on words of length `m`
  (`tree_spec`, Lemma 4; `D_congr`).
- `evalT d s`: the tree run on a stream (`eval_spec`, Lemma 5).
- `liftTreeT d`: the datum's own code (`liftTree_spec`).
- **`cantorL q = App ⟨evalT⟩ (liftTree (tree q))`**: for every `m`-local `q`,
  `cantorL q ↠ ⟨evalT ⬝ D m φ⟩`, and that code's term agrees with `q` on every
  stream with an `m`-prefix (`cantor_lift`); two `m`-local functionals with the
  same table get the same code (`cantor_canonical`).
- **`funL`**, the same for functionals of functions on Scott numerals that
  read their argument at `0 … m−1` only (`Search.FLocal`): `funL Φ` reduces
  to the code of `S (K (eval d)) tab`, which agrees with `Φ` on every `f`
  whose values there are booleans (`fun_lift`, `fun_canonical`).  This is the
  form comparable with `NoLift.no_lift_conv`, whose functions are the same.

The only quotations are of fixed closed terms (`evalT`, `leafT`, `nodeT` and
the booleans).  Taken with `NoLift.no_lift_conv` and `LiftBool.lift_bool`:
there is a lift at Bool → Bool and at m-local Stream → Bool, and none at
Nat → Bool.  The remaining hypothesis is m-locality itself; totality on all
points of Cantor space implies it by the fan theorem, which is not
mechanized (it needs an oracle semantics; over closed terms alone a Kleene
tree refutes it).
-/

namespace CantorLift

open NoLift LiftBool Search

-- ---------------------------------------------------------------------------
-- Boolean operations
-- ---------------------------------------------------------------------------

theorem not_spec (b : Bool) : WSteps (notT ⬝ boolT b) (boolT (!b)) := by
  cases b with
  | true => exact canon_spec false true true
  | false => exact canon_spec false true false

/-- `eqB x y = x y (not y)`. -/
def eqBT : Term := toTerm (absN [0, 1] (.var 0 ⬝ₒ .var 1 ⬝ₒ (notT.toO ⬝ₒ .var 1)))

theorem eqB_spec (a b : Bool) : WSteps (eqBT ⬝ boolT a ⬝ boolT b) (boolT (a == b)) := by
  have h := absN_beta_close [0, 1] (.var 0 ⬝ₒ .var 1 ⬝ₒ (notT.toO ⬝ₒ .var 1)) (fun _ => K)
    [boolT a, boolT b] rfl
  simp only [OTerm.close, close_toO, appT] at h
  refine h.trans ((sel a _ _).trans ?_)
  cases a <;> cases b
  · exact (not_spec false)
  · exact (not_spec true)
  · exact .refl _
  · exact .refl _

/-- `g ∘ q = S (K g) q`. -/
def comp (g q : Term) : Term := S ⬝ (K ⬝ g) ⬝ q

theorem comp_wsteps (g q s : Term) : WSteps (comp g q ⬝ s) (g ⬝ (q ⬝ s)) :=
  (WSteps.single (WStep.S _ _ _)).trans (WSteps.left _ (.single (.K _ _)))

theorem local_not {m : Nat} {φ : List Bool → Bool} {p : Term} (hp : Local m φ p) :
    Local m (fun w => !φ w) (comp notT p) := fun w hw s hs =>
  (comp_wsteps _ _ _).trans ((WSteps.right _ (hp w hw s hs)).trans (not_spec _))

-- ---------------------------------------------------------------------------
-- `every` and `const`
-- ---------------------------------------------------------------------------

/-- `every p = not (p' (find p'))`, `p' = not ∘ p`. -/
def everyT (p : Term) : Term := notT ⬝ (comp notT p ⬝ (findT ⬝ comp notT p))

/-- **`every` decides universality.** -/
theorem every_spec {m : Nat} {φ : List Bool → Bool} {p : Term} (hp : Local m φ p) :
    ∃ b : Bool, WSteps (everyT p) (boolT b) ∧
      (b = true ↔ ∀ w : List Bool, w.length = m → φ w = true) := by
  obtain ⟨u, _, hr, hiff⟩ := search_decides (local_not hp)
  refine ⟨φ u, (WSteps.right _ hr).trans (by simpa using not_spec (!φ u)), ?_⟩
  constructor
  · intro hu w hw
    cases hφ : φ w with
    | true => rfl
    | false =>
      have : (!φ u) = true := hiff.2 ⟨w, hw, by simp [hφ]⟩
      simp [hu] at this
  · intro hall
    cases h : φ u with
    | true => rfl
    | false =>
      obtain ⟨w, hw, hw'⟩ := hiff.1 (by simp [h])
      simp [hall w hw] at hw'

/-- The zero stream, `tab (K false)`. -/
def zerosT : Term := tabT ⬝ (K ⬝ boolT false)

theorem zeros_prefix (m : Nat) : HasPrefix (List.replicate m false) zerosT :=
  tab_spec _ _ fun i hi => by simpa using (WSteps.single (WStep.K (boolT false) (num i)))

/-- `λ a. eqB (q a) c`, as `S (S (K eqB) q) (K c)`. -/
def eqWith (q c : Term) : Term := S ⬝ (S ⬝ (K ⬝ eqBT) ⬝ q) ⬝ (K ⬝ c)

theorem local_eqWith {m : Nat} {φ : List Bool → Bool} {q c : Term} (hq : Local m φ q) {c0 : Bool}
    (hc : WSteps c (boolT c0)) : Local m (fun w => φ w == c0) (eqWith q c) := by
  intro w hw s hs
  have h0 : WSteps (eqWith q c ⬝ s) (eqBT ⬝ (q ⬝ s) ⬝ c) :=
    (iter_sound (k := 3) rfl : Steps (eqWith q c ⬝ s) (eqBT ⬝ (q ⬝ s) ⬝ (K ⬝ c ⬝ s))).weak.trans
      (WSteps.right _ (.single (.K c s)))
  exact h0.trans ((WSteps.app (WSteps.right _ (hq w hw s hs)) hc).trans (eqB_spec _ _))

/-- `const q = every (λ a. eqB (q a) (q zeros))`. -/
def constT (q : Term) : Term := everyT (eqWith q (q ⬝ zerosT))

/-- The value of a table on the zero word. -/
def zeroVal (m : Nat) (φ : List Bool → Bool) : Bool := φ (List.replicate m false)

/-- Every word of length `m`. -/
def words : Nat → List (List Bool)
  | 0 => [[]]
  | m + 1 => (words m).map (false :: ·) ++ (words m).map (true :: ·)

theorem mem_words : ∀ {m : Nat} {w : List Bool}, w.length = m → w ∈ words m
  | 0, [], _ => by simp [words]
  | m + 1, b :: w, hw => by
    have := mem_words (m := m) (w := w) (by simpa using hw)
    cases b <;> simp [words, this]

theorem length_of_mem_words : ∀ {m : Nat} {w : List Bool}, w ∈ words m → w.length = m
  | 0, w, h => by simp [words] at h; simp [h]
  | m + 1, w, h => by
    simp only [words, List.mem_append, List.mem_map] at h
    rcases h with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [length_of_mem_words hv]

/-- `φ` is constant on words of length `m`, as a computation. -/
def constB (m : Nat) (φ : List Bool → Bool) : Bool :=
  (words m).all fun w => φ w == zeroVal m φ

theorem constB_iff (m : Nat) (φ : List Bool → Bool) :
    constB m φ = true ↔ ∀ w : List Bool, w.length = m → φ w = zeroVal m φ := by
  simp only [constB, List.all_eq_true, beq_iff_eq]
  exact ⟨fun h w hw => h w (mem_words hw), fun h w hw => h w (length_of_mem_words hw)⟩

/-- **Corollary 3.** -/
theorem const_spec {m : Nat} {φ : List Bool → Bool} {q : Term} (hq : Local m φ q) :
    WSteps (constT q) (boolT (constB m φ)) := by
  have hc : WSteps (q ⬝ zerosT) (boolT (zeroVal m φ)) :=
    hq _ (by simp) _ (zeros_prefix m)
  obtain ⟨b, hb, hiff⟩ := every_spec (local_eqWith hq hc)
  have : b = constB m φ := by
    cases h : constB m φ with
    | true => exact hiff.2 fun w hw => by simpa using (constB_iff m φ).1 h w hw
    | false =>
      cases hb' : b with
      | false => rfl
      | true =>
        have := (constB_iff m φ).2 fun w hw => by simpa using hiff.1 hb' w hw
        simp [h] at this
  exact this ▸ hb

-- ---------------------------------------------------------------------------
-- Trees
-- ---------------------------------------------------------------------------

/-- `Leaf b = λ l n. l b`. -/
def leafT : Term := toTerm (absN [0, 1, 2] (.var 1 ⬝ₒ .var 0))
/-- `Node x y = λ l n. n x y`. -/
def nodeT : Term := toTerm (absN [0, 1, 2, 3] (.var 3 ⬝ₒ .var 0 ⬝ₒ .var 1))

theorem leaf_sel (b l n : Term) : WSteps (leafT ⬝ b ⬝ l ⬝ n) (l ⬝ b) := by
  have h := absN_beta_close [0, 1, 2] (.var 1 ⬝ₒ .var 0) (fun _ => K) [b, l, n] rfl
  simp only [OTerm.close, appT] at h; exact h

theorem node_sel (x y l n : Term) : WSteps (nodeT ⬝ x ⬝ y ⬝ l ⬝ n) (n ⬝ x ⬝ y) := by
  have h := absN_beta_close [0, 1, 2, 3] (.var 3 ⬝ₒ .var 0 ⬝ₒ .var 1) (fun _ => K) [x, y, l, n] rfl
  simp only [OTerm.close, appT] at h; exact h

/-- **The datum** a table tabulates to, by recursion in Lean. -/
def D : Nat → (List Bool → Bool) → Term
  | 0, φ => leafT ⬝ boolT (φ [])
  | m + 1, φ =>
    if constB (m + 1) φ then leafT ⬝ boolT (zeroVal (m + 1) φ)
    else nodeT ⬝ D m (fun w => φ (false :: w)) ⬝ D m (fun w => φ (true :: w))

/-- **`D` depends only on the table on words of length `m`.** -/
theorem D_congr : ∀ (m : Nat) (φ ψ : List Bool → Bool),
    (∀ w : List Bool, w.length = m → φ w = ψ w) → D m φ = D m ψ
  | 0, φ, ψ, h => by simp [D, h [] rfl]
  | m + 1, φ, ψ, h => by
    have hz : zeroVal (m + 1) φ = zeroVal (m + 1) ψ := h _ (by simp)
    have hc : constB (m + 1) φ = constB (m + 1) ψ := by
      apply Bool.eq_iff_iff.2
      rw [constB_iff, constB_iff]
      constructor
      · intro H w hw; rw [← h w hw, ← hz]; exact H w hw
      · intro H w hw; rw [h w hw, hz]; exact H w hw
    have h0 := D_congr m (fun w => φ (false :: w)) (fun w => ψ (false :: w))
      fun w hw => h _ (by simp [hw])
    have h1 := D_congr m (fun w => φ (true :: w)) (fun w => ψ (true :: w))
      fun w hw => h _ (by simp [hw])
    simp only [D, hc, hz, h0, h1]

-- The same constructions over a variable, for use inside combinators.

def compO (g q : OTerm) : OTerm := S.toO ⬝ₒ (K.toO ⬝ₒ g) ⬝ₒ q
def everyO (p : OTerm) : OTerm := notT.toO ⬝ₒ (compO notT.toO p ⬝ₒ (findT.toO ⬝ₒ compO notT.toO p))
def eqWithO (q c : OTerm) : OTerm := S.toO ⬝ₒ (S.toO ⬝ₒ (K.toO ⬝ₒ eqBT.toO) ⬝ₒ q) ⬝ₒ (K.toO ⬝ₒ c)
def constO (q : OTerm) : OTerm := everyO (eqWithO q (q ⬝ₒ zerosT.toO))

theorem close_constO (σ : Nat → Term) (x : Nat) : (constO (.var x)).close σ = constT (σ x) := by
  simp [constO, everyO, eqWithO, compO, OTerm.close, close_toO, constT, everyT, eqWith, comp]

/-- `tree q = const q (Leaf (q zeros)) (Node (tree (q ∘ cons false)) (tree (q ∘ cons true)))`,
    over `r` (0), `q` (1). -/
def treeBody : OTerm :=
  constO (.var 1) ⬝ₒ (leafT.toO ⬝ₒ (.var 1 ⬝ₒ zerosT.toO)) ⬝ₒ
    (nodeT.toO ⬝ₒ (.var 0 ⬝ₒ preO 1 false) ⬝ₒ (.var 0 ⬝ₒ preO 1 true))

def treeStep : Term := toTerm (absN [0, 1] treeBody)

/-- **`tree`**, the fixpoint of `treeStep`. -/
def treeT : Term := fixSelf treeStep (fixB treeStep)

theorem tree_unroll : WSteps treeT (treeStep ⬝ treeT) := by
  have h := (fixSelf_unroll (F := treeStep) (Steps.refl (fixB treeStep))).weak
  have hI : WSteps (fixSelf treeStep (I ⬝ fixB treeStep)) treeT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem tree_unfold (q : Term) :
    WSteps (treeT ⬝ q) (constT q ⬝ (leafT ⬝ (q ⬝ zerosT)) ⬝
      (nodeT ⬝ (treeT ⬝ pre q false) ⬝ (treeT ⬝ pre q true))) := by
  have h := absN_beta_close [0, 1] treeBody (fun _ => K) [treeT, q] rfl
  simp only [treeBody, OTerm.close, close_toO, appT, preO] at h
  rw [close_constO] at h
  exact (WSteps.left _ tree_unroll).trans h

/-- **Lemma 4 (tabulation).** -/
theorem tree_spec : ∀ (m : Nat) (φ : List Bool → Bool) (q : Term), Local m φ q →
    WSteps (treeT ⬝ q) (D m φ)
  | m, φ, q, hq => by
    have hu := tree_unfold q
    have hc := const_spec hq
    have hz : WSteps (q ⬝ zerosT) (boolT (zeroVal m φ)) := hq _ (by simp) _ (zeros_prefix m)
    have hsel := (hu.trans (WSteps.left _ (WSteps.left _ hc))).trans (sel _ _ _)
    cases m with
    | zero =>
      have h0 : constB 0 φ = true := by simp [constB, words, zeroVal]
      rw [h0] at hsel
      simpa [D, zeroVal] using hsel.trans (WSteps.right _ hz)
    | succ m =>
      cases h : constB (m + 1) φ with
      | true =>
        rw [h] at hsel
        simpa [D, h] using hsel.trans (WSteps.right _ hz)
      | false =>
        rw [h] at hsel
        have h0 := tree_spec m _ _ (local_pre hq false)
        have h1 := tree_spec m _ _ (local_pre hq true)
        simpa [D, h] using hsel.trans (WSteps.app (WSteps.right _ h0) h1)

-- ---------------------------------------------------------------------------
-- Evaluating a tree on a stream
-- ---------------------------------------------------------------------------

/-- `eval d s = d (λ b. b) (λ x y. hd s (eval y (tl s)) (eval x (tl s)))`,
    over `ev` (0), `d` (1), `s` (2), `x` (3), `y` (4). -/
def evalIn : OTerm :=
  absN [3, 4] ((.var 2 ⬝ₒ .K) ⬝ₒ (.var 0 ⬝ₒ .var 4 ⬝ₒ (.var 2 ⬝ₒ (K ⬝ I).toO)) ⬝ₒ
    (.var 0 ⬝ₒ .var 3 ⬝ₒ (.var 2 ⬝ₒ (K ⬝ I).toO)))

def evalBody : OTerm := .var 1 ⬝ₒ I.toO ⬝ₒ evalIn

def evalStep : Term := toTerm (absN [0, 1, 2] evalBody)

/-- **`eval`**, the fixpoint of `evalStep`. -/
def evalT : Term := fixSelf evalStep (fixB evalStep)

theorem eval_unroll : WSteps evalT (evalStep ⬝ evalT) := by
  have h := (fixSelf_unroll (F := evalStep) (Steps.refl (fixB evalStep))).weak
  have hI : WSteps (fixSelf evalStep (I ⬝ fixB evalStep)) evalT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem eval_unfold (d s : Term) : ∃ X, WSteps (evalT ⬝ d ⬝ s) (d ⬝ I ⬝ X) ∧
    ∀ x y, WSteps (X ⬝ x ⬝ y)
      (s ⬝ K ⬝ (evalT ⬝ y ⬝ (s ⬝ (K ⬝ I))) ⬝ (evalT ⬝ x ⬝ (s ⬝ (K ⬝ I)))) := by
  have h := absN_beta_close [0, 1, 2] evalBody (fun _ => K) [evalT, d, s] rfl
  simp only [evalBody, OTerm.close, close_toO, appT] at h
  refine ⟨_, (WSteps.left _ (WSteps.left _ eval_unroll)).trans h, fun x y => ?_⟩
  have h2 := absN_beta_close [3, 4]
    ((.var 2 ⬝ₒ .K) ⬝ₒ (.var 0 ⬝ₒ .var 4 ⬝ₒ (.var 2 ⬝ₒ (K ⬝ I).toO)) ⬝ₒ
      (.var 0 ⬝ₒ .var 3 ⬝ₒ (.var 2 ⬝ₒ (K ⬝ I).toO)))
    (overrideC (fun _ => K) [0, 1, 2] [evalT, d, s]) [x, y] rfl
  simp only [OTerm.close, close_toO, appT] at h2
  exact h2

theorem hd_cons {b : Bool} {s s' : Term} (h : WSteps s (consC ⬝ boolT b ⬝ s')) :
    WSteps (s ⬝ K) (boolT b) :=
  (WSteps.left K h).trans ((cons_sel _ _ _).trans (.single (.K _ _)))

theorem tl_cons {b : Bool} {s s' : Term} (h : WSteps s (consC ⬝ boolT b ⬝ s')) :
    WSteps (s ⬝ (K ⬝ I)) s' :=
  (WSteps.left _ h).trans ((cons_sel _ _ _).trans
    ((WSteps.left _ (.single (.K _ _))).trans (.single (.I _))))

/-- **Lemma 5 (evaluation).** -/
theorem eval_spec : ∀ (m : Nat) (φ : List Bool → Bool) (w : List Bool) (s : Term),
    w.length = m → HasPrefix w s → WSteps (evalT ⬝ D m φ ⬝ s) (boolT (φ w))
  | 0, φ, w, s, hw, _ => by
    rw [List.length_eq_zero_iff.1 hw]
    obtain ⟨X, hX, _⟩ := eval_unfold (D 0 φ) s
    exact (hX.trans (leaf_sel _ _ _)).trans (.single (.I _))
  | m + 1, φ, w, s, hw, hs => by
    cases h : constB (m + 1) φ with
    | true =>
      have hv : φ w = zeroVal (m + 1) φ := (constB_iff _ φ).1 h w hw
      have hD : D (m + 1) φ = leafT ⬝ boolT (zeroVal (m + 1) φ) := by simp [D, h]
      rw [hD, hv]
      obtain ⟨X, hX, _⟩ := eval_unfold (leafT ⬝ boolT (zeroVal (m + 1) φ)) s
      exact (hX.trans (leaf_sel _ _ _)).trans (.single (.I _))
    | false =>
      have hD : D (m + 1) φ =
          nodeT ⬝ D m (fun w => φ (false :: w)) ⬝ D m (fun w => φ (true :: w)) := by simp [D, h]
      rw [hD]
      obtain ⟨X, hX, hnode⟩ := eval_unfold
        (nodeT ⬝ D m (fun w => φ (false :: w)) ⬝ D m (fun w => φ (true :: w))) s
      match w, hw, hs with
      | b :: w', hw', ⟨s', h1, h2⟩ =>
        have hl : w'.length = m := by simpa using hw'
        refine (hX.trans (node_sel _ _ _ _)).trans ((hnode _ _).trans ?_)
        refine (WSteps.left _ (WSteps.left _ (hd_cons h1))).trans ((sel b _ _).trans ?_)
        cases b with
        | true =>
          exact (WSteps.right _ (tl_cons h1)).trans (eval_spec m _ w' s' hl h2)
        | false =>
          exact (WSteps.right _ (tl_cons h1)).trans (eval_spec m _ w' s' hl h2)

-- ---------------------------------------------------------------------------
-- Lifting a tree datum to its code
-- ---------------------------------------------------------------------------

/-- `lt d = d (λ b. App ⟨Leaf⟩ (b ⟨K⟩ ⟨K I⟩)) (λ x y. App (App ⟨Node⟩ (lt x)) (lt y))`,
    over `lt` (0), `d` (1), `b` (2), `x` (3), `y` (4). -/
def ltLeaf : OTerm :=
  absN [2] (Requote.appC.toO ⬝ₒ (quoteT leafT).toO ⬝ₒ (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ (quoteT (K ⬝ I)).toO))
def ltNode : OTerm :=
  absN [3, 4] (Requote.appC.toO ⬝ₒ (Requote.appC.toO ⬝ₒ (quoteT nodeT).toO ⬝ₒ (.var 0 ⬝ₒ .var 3)) ⬝ₒ
    (.var 0 ⬝ₒ .var 4))
def ltBody : OTerm := .var 1 ⬝ₒ ltLeaf ⬝ₒ ltNode

def ltStep : Term := toTerm (absN [0, 1] ltBody)

/-- **`liftTree`**, lift at the tree data type. -/
def liftTreeT : Term := fixSelf ltStep (fixB ltStep)

theorem lt_unroll : WSteps liftTreeT (ltStep ⬝ liftTreeT) := by
  have h := (fixSelf_unroll (F := ltStep) (Steps.refl (fixB ltStep))).weak
  have hI : WSteps (fixSelf ltStep (I ⬝ fixB ltStep)) liftTreeT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem lt_case (d : Term) : WSteps (liftTreeT ⬝ d)
    (d ⬝ ltLeaf.close (overrideC (fun _ => K) [0, 1] [liftTreeT, d])
       ⬝ ltNode.close (overrideC (fun _ => K) [0, 1] [liftTreeT, d])) := by
  have h := absN_beta_close [0, 1] ltBody (fun _ => K) [liftTreeT, d] rfl
  simp only [ltBody, OTerm.close, appT] at h
  exact (WSteps.left _ lt_unroll).trans h

theorem quote_bool (b : Bool) :
    WSteps (boolT b ⬝ quoteT K ⬝ quoteT (K ⬝ I)) (quoteT (boolT b)) := by
  cases b with
  | true => exact .single (.K _ _)
  | false => exact (WSteps.left _ (.single (.K _ _))).trans (.single (.I _))

/-- **`liftTree` sends a tree datum to its own code.** -/
theorem liftTree_spec : ∀ (m : Nat) (φ : List Bool → Bool),
    WSteps (liftTreeT ⬝ D m φ) (quoteT (D m φ)) := by
  have leaf : ∀ b : Bool, WSteps (liftTreeT ⬝ (leafT ⬝ boolT b)) (quoteT (leafT ⬝ boolT b)) := by
    intro b
    refine (lt_case _).trans ((leaf_sel _ _ _).trans ?_)
    have h := absN_beta_close [2]
      (Requote.appC.toO ⬝ₒ (quoteT leafT).toO ⬝ₒ (.var 2 ⬝ₒ (quoteT K).toO ⬝ₒ (quoteT (K ⬝ I)).toO))
      (overrideC (fun _ => K) [0, 1] [liftTreeT, leafT ⬝ boolT b]) [boolT b] rfl
    simp only [OTerm.close, close_toO, appT] at h
    exact h.trans (WSteps.right _ (quote_bool b))
  intro m
  induction m with
  | zero => intro φ; exact leaf _
  | succ m ih =>
    intro φ
    cases h : constB (m + 1) φ with
    | true => simp only [D, h, if_true]; exact leaf _
    | false =>
      simp only [D, h]
      refine (lt_case _).trans ((node_sel _ _ _ _).trans ?_)
      have h2 := absN_beta_close [3, 4]
        (Requote.appC.toO ⬝ₒ (Requote.appC.toO ⬝ₒ (quoteT nodeT).toO ⬝ₒ (.var 0 ⬝ₒ .var 3)) ⬝ₒ
          (.var 0 ⬝ₒ .var 4))
        (overrideC (fun _ => K) [0, 1] [liftTreeT, nodeT ⬝ D m (fun w => φ (false :: w)) ⬝ D m (fun w => φ (true :: w))])
        [D m (fun w => φ (false :: w)), D m (fun w => φ (true :: w))] rfl
      simp only [OTerm.close, close_toO, appT] at h2
      exact h2.trans (WSteps.app (WSteps.right _ (WSteps.right _ (ih _))) (ih _))

-- ---------------------------------------------------------------------------
-- The lift
-- ---------------------------------------------------------------------------

/-- **The lift at Stream → Bool**: `L q = App ⟨eval⟩ (liftTree (tree q))`. -/
def cantorL : Term :=
  toTerm (absN [0] (Requote.appC.toO ⬝ₒ (quoteT evalT).toO ⬝ₒ (liftTreeT.toO ⬝ₒ (treeT.toO ⬝ₒ .var 0))))

/-- **Theorem 6.**  For an `m`-local `q` with table `φ`, `L q` reduces to the
    code of `eval (D m φ)`, which agrees with `q` on every stream with an
    `m`-prefix. -/
theorem cantor_lift {m : Nat} {φ : List Bool → Bool} {q : Term} (hq : Local m φ q) :
    WSteps (cantorL ⬝ q) (quoteT (evalT ⬝ D m φ)) ∧
    ∀ (w : List Bool) (s : Term) (r : Bool), w.length = m → HasPrefix w s →
      WSteps (q ⬝ s) (boolT r) → WSteps (evalT ⬝ D m φ ⬝ s) (boolT r) := by
  refine ⟨?_, fun w s r hw hs hr => ?_⟩
  · have h := absN_beta_close [0]
      (Requote.appC.toO ⬝ₒ (quoteT evalT).toO ⬝ₒ (liftTreeT.toO ⬝ₒ (treeT.toO ⬝ₒ .var 0)))
      (fun _ => K) [q] rfl
    simp only [OTerm.close, close_toO, appT] at h
    exact h.trans (WSteps.right _ ((WSteps.right _ (tree_spec m φ q hq)).trans (liftTree_spec m φ)))
  · rw [bool_unique hr (hq w hw s hs)]
    exact eval_spec m φ w s hw hs

/-- **Canonicality.**  Two `m`-local functionals with the same table get the
    same code. -/
theorem cantor_canonical {m : Nat} {φ ψ : List Bool → Bool} {q q' : Term}
    (hq : Local m φ q) (hq' : Local m ψ q') (h : ∀ w : List Bool, w.length = m → φ w = ψ w) :
    ∃ c, WSteps (cantorL ⬝ q) (quoteT c) ∧ WSteps (cantorL ⬝ q') (quoteT c) :=
  ⟨evalT ⬝ D m φ, (cantor_lift hq).1, by rw [D_congr m φ ψ h]; exact (cantor_lift hq').1⟩

-- ---------------------------------------------------------------------------
-- The lift for functionals of functions on numerals
-- ---------------------------------------------------------------------------

/-- `λ Φ. App (App ⟨S⟩ (App ⟨K⟩ (L (Φ ∘ nth)))) ⟨tab⟩`: the code of
    `S (K (eval d)) tab`, `d` the tree of `Φ ∘ nth`. -/
def funL : Term :=
  toTerm (absN [0] (Requote.appC.toO ⬝ₒ
    (Requote.appC.toO ⬝ₒ (quoteT S).toO ⬝ₒ
      (Requote.appC.toO ⬝ₒ (quoteT K).toO ⬝ₒ
        (cantorL.toO ⬝ₒ (S.toO ⬝ₒ (K.toO ⬝ₒ .var 0) ⬝ₒ nthT.toO)))) ⬝ₒ
    (quoteT tabT).toO))

/-- **The lift at (Nat → Bool) → Bool, for functionals that read `f` at
    `0 … m−1` only.**  `funL Φ` reduces to the code of a term that agrees with
    `Φ` on every function whose values at `0 … m−1` are booleans. -/
theorem fun_lift {m : Nat} {φ : List Bool → Bool} {Φ : Term} (hΦ : FLocal m φ Φ) :
    WSteps (funL ⬝ Φ) (quoteT (S ⬝ (K ⬝ (evalT ⬝ D m φ)) ⬝ tabT)) ∧
    ∀ (w : List Bool) (hw : w.length = m) (f : Term),
      (∀ i (hi : i < m), WSteps (f ⬝ num i) (boolT (w.get ⟨i, hw ▸ hi⟩))) →
      ∀ r : Bool, WSteps (Φ ⬝ f) (boolT r) →
        WSteps (S ⬝ (K ⬝ (evalT ⬝ D m φ)) ⬝ tabT ⬝ f) (boolT r) := by
  have hloc := flocal_stream hΦ
  refine ⟨?_, fun w hw f hf r hr => ?_⟩
  · have h := absN_beta_close [0]
      (Requote.appC.toO ⬝ₒ
        (Requote.appC.toO ⬝ₒ (quoteT S).toO ⬝ₒ
          (Requote.appC.toO ⬝ₒ (quoteT K).toO ⬝ₒ
            (cantorL.toO ⬝ₒ (S.toO ⬝ₒ (K.toO ⬝ₒ .var 0) ⬝ₒ nthT.toO)))) ⬝ₒ
        (quoteT tabT).toO) (fun _ => K) [Φ] rfl
    simp only [OTerm.close, close_toO, appT] at h
    exact h.trans (WSteps.left _ (WSteps.right _ (WSteps.right _ (WSteps.right _ (cantor_lift hloc).1))))
  · have h0 : WSteps (S ⬝ (K ⬝ (evalT ⬝ D m φ)) ⬝ tabT ⬝ f) (evalT ⬝ D m φ ⬝ (tabT ⬝ f)) :=
      (WSteps.single (WStep.S _ _ _)).trans (WSteps.left _ (.single (.K _ _)))
    have hpre : HasPrefix w (tabT ⬝ f) := tab_spec w f fun i hi => hf i (hw ▸ hi)
    rw [bool_unique hr (hΦ w hw f hf)]
    exact h0.trans (eval_spec m φ w _ hw hpre)

/-- Canonicality for functionals of functions. -/
theorem fun_canonical {m : Nat} {φ ψ : List Bool → Bool} {Φ Ψ : Term}
    (hΦ : FLocal m φ Φ) (hΨ : FLocal m ψ Ψ) (h : ∀ w : List Bool, w.length = m → φ w = ψ w) :
    ∃ c, WSteps (funL ⬝ Φ) (quoteT c) ∧ WSteps (funL ⬝ Ψ) (quoteT c) :=
  ⟨_, (fun_lift hΦ).1, by rw [D_congr m φ ψ h]; exact (fun_lift hΨ).1⟩

end CantorLift
