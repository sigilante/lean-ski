import Ski.BExp
open Term

/-!
# Ψ skeleton: the finite table facts and the frame lemmas

Facts about S1's 38-block table `β` and about head runs that the Ψ-skeleton argument uses
(`notes/S4-bounded-exposure.md`, section R6).  A *root frame* is an hnf-less term `S x y z`.

* **Kinds** (`one_iff`, `one_item_of_fold`, `fold_one_item`, `fold_two_items`): the block decides
  whether a term is `S`, a one-item term `S v`, or a term of at least two items.  The one-item
  blocks are `oneBlocks`.
* **Heads of root frames** (`comb_alive`, `root_head_not_comb`): if `S x y z` is hnf-less then the
  block of `x` is not a right-comb block `0, 1, 2, 4, 8, 17`.
* **Inert blocks** (`inert_iff`): the blocks all of whose applications are ⊥ are `31` and `36`.
* **Last step** (`headChain_last`): a head run from a frame of at least three items to a frame
  of at most two ends with an atom step, so its end is `S z (y z)`.
* **Closure sets** (`Lz_self`, `Lz_closed`): `Lz z` contains `z` and is closed under `e ↦ β c e`; it bounds
  the block of the last frame item along a head run (`last_mem_Lz`).

The acyclicity of the root-to-root graph itself is computed by
`notes/checks/s4/psi/psiskel.py` and is not proved here.
-/

namespace PsiSkel
open HnfS HnfSound

/-! ## Kinds -/

/-- Blocks of the one-item terms `S v`. -/
def oneBlocks : List Nat := [1, 2, 4, 5, 8, 9, 10, 11, 17, 18, 19, 20, 27, 28]

def oneB : Bool := r38.all fun a => r38.all fun b => (oneBlocks.contains (β a b)) == (a == 0)
theorem oneB_eq : oneB = true := by decide +kernel

/-- A product lies in a one-item block exactly when its function part is `S`. -/
theorem one_iff {a b : Nat} (ha : a < 38) (hb : b < 38) : β a b ∈ oneBlocks ↔ a = 0 := by
  have h := oneB_eq
  simp only [oneB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h a ha b hb
  constructor
  · intro hm
    have hc : oneBlocks.contains (β a b) = true := by simpa using hm
    rw [hc] at this
    simpa using this.symm
  · intro h0
    have hc : (a == 0) = true := by simpa using h0
    rw [hc] at this
    simpa using this

/-- A term whose block is a one-item block is literally `S v`. -/
theorem one_item_of_fold {t : Term} (ht : PureS t) (h : fold t ∈ oneBlocks) : ∃ v, t = S ⬝ v := by
  cases ht with
  | S => simp [fold, oneBlocks] at h
  | @app f x hf hx =>
    have h0 := (one_iff (fold_lt hf) (fold_lt hx)).1 h
    exact ⟨x, by rw [fold_eq_zero hf h0]⟩

theorem fold_one_item {v : Term} (hv : PureS v) : fold (S ⬝ v) ∈ oneBlocks :=
  (one_iff (by decide) (fold_lt hv)).2 rfl

/-- A term of at least two items has a block outside the one-item blocks (and it is not `0`). -/
theorem fold_two_items {f a b : Term} (hf : PureS f) (ha : PureS a) (hb : PureS b) :
    fold (f ⬝ a ⬝ b) ∉ oneBlocks ∧ fold (f ⬝ a ⬝ b) ≠ 0 := by
  refine ⟨fun h => ?_, beta_ne_zero (fold_lt (.app hf ha)) (fold_lt hb)⟩
  have h0 := (one_iff (fold_lt (.app hf ha)) (fold_lt hb)).1 h
  exact beta_ne_zero (fold_lt hf) (fold_lt ha) h0

/-! ## Heads of root frames -/

/-- Right-comb blocks: `S`, `S S`, `S (S S)`, … -/
def combBlocks : List Nat := [0, 1, 2, 4, 8, 17]

def combB : Bool := combBlocks.all fun p => r38.all fun q => r38.all fun w =>
  β (β (β 0 p) q) w != 36
theorem combB_eq : combB = true := by decide +kernel

/-- `S p q w` with `p` a right comb has a head normal form, on blocks. -/
theorem comb_alive {p q w : Nat} (hp : p ∈ combBlocks) (hq : q < 38) (hw : w < 38) :
    β (β (β 0 p) q) w ≠ 36 := by
  have h := combB_eq
  simp only [combB, r38, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  exact h p hp q hq w hw

/-- The first item of an hnf-less root frame is not a right comb. -/
theorem root_head_not_comb {x y z : Term} (hy : PureS y) (hz : PureS z)
    (hb : fold (S ⬝ x ⬝ y ⬝ z) = 36) : fold x ∉ combBlocks :=
  fun hp => comb_alive hp (fold_lt hy) (fold_lt hz) hb

/-! ## Inert blocks -/

def inertB : Bool := r38.all fun a => (r38.all fun b => β a b == 36) == (a == 31 || a == 36)
theorem inertB_eq : inertB = true := by decide +kernel

/-- Every application of a block is ⊥ exactly for the blocks `31` and `36`. -/
theorem inert_iff {a : Nat} (ha : a < 38) : (∀ b, b < 38 → β a b = 36) ↔ (a = 31 ∨ a = 36) := by
  have h := inertB_eq
  simp only [inertB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h a ha
  constructor
  · intro hall
    have hc : ((List.range 38).all fun b => β a b == 36) = true := by
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq]; exact hall
    rw [hc] at this
    simpa using this.symm
  · intro h31
    have hc : (a == 31 || a == 36) = true := by simpa using h31
    rw [hc] at this
    have h2 : ((List.range 38).all fun b => β a b == 36) = true := this
    simpa only [List.all_eq_true, List.mem_range, beq_iff_eq] using h2

/-! ## The last step of a productive head run -/

/-- A head run from a frame of at least three items to a frame of at most two ends with an atom
step from a frame of exactly three: the end is `S z (y z)`. -/
theorem headChain_last {t u : Term} (h : HeadChain t u) (ht : PureS t)
    (hl : 3 ≤ (spine t).length) (hu : (spine u).length ≤ 2) : ∃ y z, u = S ⬝ z ⬝ (y ⬝ z) := by
  induction h with
  | refl t => exact absurd hl (Nat.not_le.mpr (Nat.lt_succ_of_le hu))
  | @step t v u₁ u₂ u₃ rest hs hS hc ih =>
    have hsp : spine (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) = spine u₁ ++ u₃ :: (u₂ ⬝ u₃) :: rest := by
      rw [spine_foldl]; simp [spine]
    have hstep : WStep t (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
      rw [hS]; exact wstep_foldl (WStep.S u₁ u₂ u₃) rest
    have hp' := (wstep_pure hstep ht).1
    have p₁ : PureS u₁ := spine_pure ht u₁ (by rw [hs]; exact List.mem_cons_self)
    match hsu : spine u₁, hr : rest with
    | a :: l, _ =>
      subst hr
      refine ih hp' ?_ hu
      rw [hsp, hsu]
      show 3 ≤ (a :: (l ++ u₃ :: (u₂ ⬝ u₃) :: rest)).length
      rw [List.length_cons, List.length_append, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (Nat.le_trans (Nat.le_add_left 2 rest.length) (Nat.le_add_left _ _))
    | [], r :: rest' =>
      subst hr
      refine ih hp' ?_ hu
      rw [hsp, hsu]
      show 3 ≤ (u₃ :: (u₂ ⬝ u₃) :: r :: rest').length
      rw [List.length_cons, List.length_cons, List.length_cons]
      exact Nat.le_add_left 3 rest'.length
    | [], [] =>
      subst hr
      have e₁ : u₁ = S := by have := pure_eq_foldl p₁; rw [hsu] at this; exact this
      subst e₁
      cases hc with
      | refl => exact ⟨u₂, u₃, rfl⟩
      | step hs' _ _ =>
        rw [hsp, hsu] at hs'
        exact absurd (congrArg List.length hs') (by
          show ¬ (2 = _ + 3)
          exact fun h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h)))

/-! ## Closure sets for the last frame item -/

/-- `Lz z` for `z = 0, …, 37`: the least set of blocks that contains `z` and is closed under
`e ↦ β c e` (computed; only the two properties below are used). -/
def LzTable : List (List Nat) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37],
  [1, 2, 4, 6, 8, 9, 10, 12, 13, 14, 17, 18, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [2, 4, 8, 9, 10, 12, 14, 17, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [3, 5, 9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [4, 8, 9, 10, 12, 17, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [5, 9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [6, 9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [7, 9, 10, 11, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [8, 9, 10, 12, 17, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 11, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 13, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 14, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 15, 18, 19, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 16, 18, 20, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 17, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 19, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 20, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 24, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36],
  [9, 10, 12, 18, 21, 22, 23, 25, 27, 28, 29, 30, 31, 32, 33, 34, 36, 37]]

def Lz (z : Nat) : List Nat := LzTable.getD z []

def lzSelfB : Bool := r38.all fun z => (Lz z).contains z
def lzClosedB : Bool := r38.all fun z => r38.all fun c => (Lz z).all fun e => (Lz z).contains (β c e)
theorem lzSelfB_eq : lzSelfB = true := by decide +kernel
theorem lzClosedB_eq : lzClosedB = true := by decide +kernel

theorem Lz_self {z : Nat} (hz : z < 38) : z ∈ Lz z := by
  have h := lzSelfB_eq
  simp only [lzSelfB, r38, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  exact h z hz

theorem Lz_closed {z c e : Nat} (hz : z < 38) (hc : c < 38) (he : e ∈ Lz z) : β c e ∈ Lz z := by
  have h := lzClosedB_eq
  simp only [lzClosedB, r38, List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  exact h z hz c hc e he

/-- The last frame item of an application. -/
def lastArg : Term → Term
  | .app _ x => x
  | t => t

theorem lastArg_foldl : ∀ (rest : List Term) (a b : Term), rest ≠ [] →
    lastArg (rest.foldl Term.app a) = lastArg (rest.foldl Term.app b) := by
  intro rest
  induction rest with
  | nil => intro a b h; exact absurd rfl h
  | cons x w ih =>
    intro a b _
    by_cases hw : w = []
    · subst hw; rfl
    · exact ih (a ⬝ x) (b ⬝ x) hw

/-- Along a head run the block of the last frame item stays in `Lz z`: the last item is only
ever replaced by `y z'` with `z'` the last item before. -/
theorem last_mem_Lz {t u : Term} (h : HeadChain t u) (ht : PureS t) {z : Nat} (hz : z < 38)
    (hm : fold (lastArg t) ∈ Lz z) : fold (lastArg u) ∈ Lz z := by
  induction h with
  | refl t => exact hm
  | @step t v u₁ u₂ u₃ rest hs hS hc ih =>
    have hstep : WStep t (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) := by
      rw [hS]; exact wstep_foldl (WStep.S u₁ u₂ u₃) rest
    have hp' := (wstep_pure hstep ht).1
    have p₂ : PureS u₂ := spine_pure ht u₂ (by rw [hs]; simp)
    apply ih hp'
    by_cases hr : rest = []
    · subst hr
      rw [hS] at hm
      exact Lz_closed hz (fold_lt p₂) hm
    · rw [lastArg_foldl rest _ (S ⬝ u₁ ⬝ u₂ ⬝ u₃) hr, ← hS]; exact hm

end PsiSkel
