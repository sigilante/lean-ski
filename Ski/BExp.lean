import Ski.HnfSound
open Term

/-!
# Bounded exposure: the finite table facts (S4, Item-Reading)

Finite facts about S1's 38-block table `β` that the Item-Reading analysis uses, each lifted to
closed S-terms.  See `notes/S4-bounded-exposure.md`.

* **Chain Lemma** (`C3_eq`, `C_ge4`, `chain_mem`, `chain4_emitter`): if the two-item first-item
  chain of `t` (`t ↠ S a b`, `a ↠ S a' b'`, …) has depth `d ≥ 1`, the block of `t` lies in `C d`;
  `C 3 = {31, 34}`, `C d = {31}` for `d ≥ 4`; row 31 is ⊥ and two applications of block 34 give ⊥.
* **Budgets** (`budStep`, `budConv`, `app_budget`, `long_app`): `A k` is the set of blocks that
  some `k` arguments keep out of ⊥; `A 6 = {0, 1, 3, 6, 12}` is the fixed point, and a term
  applied to seven or more arguments with an hnf has its first argument `S` unless it is `S S`.
* **Shapes** (`shape1`, `shape3`, `shape6`, `shape12`, `arity_blocks`): blocks 0, 1, 3 are
  `S`, `S S`, `S S S`; block 6 is `S S (S S)` or `S S S S`; block 12 reduces to `S S c`.
* **Skeleton** (`skeleton`): a head run from a term with an hnf has at most 10 steps whose first
  frame item is not `S` and not a tower of block 17 (from `HnfSound.root_step`).
* **Towers** (`tower_of_fold`, `exempt_shape`): blocks 1, 2, 4, 8, 17 are the literal terms
  `S^k (S S)`.
* **One-item chains** (`iterS_run`, `fib_dead`): `S^k u x y` head-reduces to `u P Q` with
  `(P, Q)` the `k`-th Fibonacci pair of `(x, y)`; from `k = 8` on both are hnf-less.
* **The Ψ counterexample** (`psi_cex`): for `k ≥ 8`, `S^k (S S c) x y` head-reduces to `f w` with
  `f` hnf-less and `w = c P Q`; for `c = S (S S)` the block of `w` is 31, for `c = S S S` it is
  36, while `S^j (S S c)` has the same block for both `c` and every `j`.
-/

namespace BExp
open HnfS HnfSound

/-! ## Chain sets -/

/-- The block of `S a b`. -/
def two (a b : Nat) : Nat := β (β 0 a) b

/-- Blocks of `S a b` with `a` in `l`. -/
def img (l : List Nat) : List Nat :=
  r38.filter fun c => l.any fun a => r38.any fun b => two a b == c

/-- `C d`: blocks of terms whose two-item first-item chain has depth `d + 1`. -/
def C : Nat → List Nat
  | 0 => img r38
  | d + 1 => img (C d)

theorem C1_eq : C 0 = [3, 6, 7, 12, 13, 14, 15, 16, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 33,
    34, 35, 37] := by decide +kernel
theorem C2_eq : img [3, 6, 7, 12, 13, 14, 15, 16, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32, 33,
    34, 35, 37] = [16, 23, 24, 25, 26, 31, 32, 33, 34, 35, 37] := by decide +kernel
theorem C3_img : img [16, 23, 24, 25, 26, 31, 32, 33, 34, 35, 37] = [31, 34] := by decide +kernel
theorem C4_img : img [31, 34] = [31] := by decide +kernel
theorem C5_img : img [31] = [31] := by decide +kernel

theorem C2_eq' : C 1 = [16, 23, 24, 25, 26, 31, 32, 33, 34, 35, 37] := by
  show img (C 0) = _; rw [C1_eq, C2_eq]
/-- `C₃ = {31, 34}`. -/
theorem C3_eq : C 2 = [31, 34] := by show img (C 1) = _; rw [C2_eq', C3_img]
theorem C4_eq : C 3 = [31] := by show img (C 2) = _; rw [C3_eq, C4_img]
/-- `C_d = {31}` for `d ≥ 4`. -/
theorem C_ge4 (d : Nat) : C (d + 3) = [31] := by
  induction d with
  | zero => exact C4_eq
  | succ d ih => show img (C (d + 3)) = _; rw [ih, C5_img]

def row31B : Bool := r38.all fun b => β 31 b == 36
def row34B : Bool := r38.all fun a => (β 34 a == 31 || β 34 a == 36) && r38.all fun b => β (β 34 a) b == 36
theorem row31B_eq : row31B = true := by decide +kernel
theorem row34B_eq : row34B = true := by decide +kernel

/-- Every application of a block-31 term is ⊥. -/
theorem row31 {b : Nat} (hb : b < 38) : β 31 b = 36 := by
  have h := row31B_eq
  simp only [row31B, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h b hb

/-- One application of block 34 gives 31 or ⊥; two give ⊥. -/
theorem row34 {a b : Nat} (ha : a < 38) (hb : b < 38) :
    (β 34 a = 31 ∨ β 34 a = 36) ∧ β (β 34 a) b = 36 := by
  have h := row34B_eq
  simp only [row34B, r38, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  exact ⟨(h a ha).1, (h a ha).2 b hb⟩

theorem mem_img {l : List Nat} {a b : Nat} (ha : a ∈ l) (ha38 : a < 38) (hb : b < 38) :
    two a b ∈ img l := by
  simp only [img, List.mem_filter, r38, List.mem_range, List.any_eq_true, beq_iff_eq]
  exact ⟨β_lt (β_lt (by decide) ha38) hb, a, ha, b, hb, rfl⟩

/-- Two-item first-item chains: `Chain d t` when `t ↠ S a b` and `Chain (d-1) a`. -/
inductive Chain : Nat → Term → Prop
  | zero (t : Term) : Chain 0 t
  | succ {d : Nat} {t a b : Term} : WSteps t (S ⬝ a ⬝ b) → Chain d a → Chain (d + 1) t

/-- **Chain Lemma** (one inclusion).  A chain of depth `d + 1` puts the block of `t` in `C d`.
`C d` is the exact image at the level of blocks; that every block of `C d` is the block of a term
with such a chain is not proved here. -/
theorem chain_mem : ∀ {d : Nat} {t : Term}, PureS t → Chain (d + 1) t → fold t ∈ C d := by
  intro d
  induction d with
  | zero =>
    intro t ht h
    cases h with
    | succ hs _ =>
      obtain ⟨hp, he⟩ := fold_wsteps hs ht
      obtain ⟨h1, hb⟩ := hp.app_inv
      have ha := h1.app_inv.2
      rw [← he]
      exact mem_img (l := r38) (by simp [r38, fold_lt ha]) (fold_lt ha) (fold_lt hb)
  | succ d ih =>
    intro t ht h
    cases h with
    | succ hs hc =>
      obtain ⟨hp, he⟩ := fold_wsteps hs ht
      obtain ⟨h1, hb⟩ := hp.app_inv
      have ha := h1.app_inv.2
      rw [← he]
      exact mem_img (ih ha hc) (fold_lt ha) (fold_lt hb)

/-- A chain of depth at least 4 is an emitter: block 31, and every application is ⊥. -/
theorem chain4_emitter {d : Nat} {t x : Term} (ht : PureS t) (hx : PureS x)
    (h : Chain (d + 4) t) : fold t = 31 ∧ fold (t ⬝ x) = 36 := by
  have hm := chain_mem ht h
  rw [C_ge4 d] at hm
  have e : fold t = 31 := by simpa using hm
  exact ⟨e, by show β (fold t) (fold x) = 36; rw [e]; exact row31 (fold_lt hx)⟩

/-- A chain of depth 3: block 31 or 34, and two applications give ⊥. -/
theorem chain3 {t x y : Term} (ht : PureS t) (hx : PureS x) (hy : PureS y) (h : Chain 3 t) :
    (fold t = 31 ∨ fold t = 34) ∧ fold (t ⬝ x ⬝ y) = 36 := by
  have hm := chain_mem ht h
  rw [C3_eq] at hm
  have e : fold t = 31 ∨ fold t = 34 := by simpa using hm
  refine ⟨e, ?_⟩
  show β (β (fold t) (fold x)) (fold y) = 36
  rcases e with e | e
  · rw [e, row31 (fold_lt hx)]; exact absorb (fold_lt hy)
  · rw [e]; exact (row34 (fold_lt hx) (fold_lt hy)).2

/-! ## Application budgets -/

/-- `A k`: the blocks that some `k` arguments keep out of ⊥ (`A 6` is the fixed point). -/
def A : Nat → List Nat
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37]
  | 1 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37]
  | 2 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
      24, 26, 28, 29, 32, 33, 35]
  | 3 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 15, 16, 19, 21, 24, 33]
  | 4 => [0, 1, 2, 3, 4, 5, 6, 12, 16, 24]
  | 5 => [0, 1, 3, 5, 6, 12]
  | _ => [0, 1, 3, 6, 12]

/-- `A 0` is the set of non-⊥ blocks. -/
def budZeroB : Bool := r38.all fun b => (A 0).contains b == (b != 36)
/-- `A (k+1) = {b : some x has β b x ∈ A k}`, for `k ≤ 6` (so `A 7 = A 6`). -/
def budStepB : Bool := (List.range 7).all fun k => r38.all fun b =>
  (A (k + 1)).contains b == r38.any fun x => (A k).contains (β b x)
/-- Staying in `A 6` after one argument: the function is `S S`, or the argument is `S`. -/
def longB : Bool := r38.all fun b => r38.all fun x =>
  !((A 6).contains (β b x)) || b == 1 || x == 0

theorem budZeroB_eq : budZeroB = true := by decide +kernel
theorem budStepB_eq : budStepB = true := by decide +kernel
theorem longB_eq : longB = true := by decide +kernel

theorem A_ge6 (k : Nat) : A (k + 6) = A 6 := rfl

theorem budZero {b : Nat} (hb : b < 38) (h : b ≠ 36) : b ∈ A 0 := by
  have h0 := budZeroB_eq
  simp only [budZeroB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h0
  have := h0 b hb
  rw [show (b != 36) = true from bne_iff_ne.mpr h] at this
  simpa using this

theorem budStep7 {k b x : Nat} (hk : k < 7) (hb : b < 38) (hx : x < 38) (h : β b x ∈ A k) :
    b ∈ A (k + 1) := by
  have h0 := budStepB_eq
  simp only [budStepB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h0
  have h1 := h0 k hk b hb
  have h2 : ((List.range 38).any fun x => (A k).contains (β b x)) = true := by
    simp only [List.any_eq_true, List.mem_range, List.contains_iff_mem]
    exact ⟨x, hx, h⟩
  rw [h2] at h1
  simpa using h1

/-- One argument costs one unit of budget. -/
theorem budStep {k b x : Nat} (hb : b < 38) (hx : x < 38) (h : β b x ∈ A k) : b ∈ A (k + 1) := by
  by_cases hk : k < 7
  · exact budStep7 hk hb hx h
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    rw [A_ge6] at h
    have := budStep7 (k := 6) (by decide) hb hx h
    rw [show j + 6 + 1 = (j + 1) + 6 by omega, A_ge6]
    exact this

/-- Conversely a block of `A (k+1)` has an argument block that leaves it in `A k` (`k ≤ 6`). -/
theorem budConv {k b : Nat} (hk : k < 7) (hb : b < 38) (h : b ∈ A (k + 1)) :
    ∃ x, x < 38 ∧ β b x ∈ A k := by
  have h0 := budStepB_eq
  simp only [budStepB, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h0
  have h1 := h0 k hk b hb
  rw [show (A (k + 1)).contains b = true by simpa using h] at h1
  have h2 := h1.symm
  simp only [List.any_eq_true, List.mem_range, List.contains_iff_mem] at h2
  exact h2

/-- **Budget.**  If `t x₁ … x_k` has block ≠ ⊥ then the block of `t` is in `A k`. -/
theorem app_budget : ∀ (xs : List Term) {t : Term}, PureS t → (∀ x ∈ xs, PureS x) →
    fold (xs.foldl Term.app t) ≠ 36 → fold t ∈ A xs.length := by
  intro xs
  induction xs with
  | nil => intro t ht _ h; exact budZero (fold_lt ht) h
  | cons x xs ih =>
    intro t ht hxs h
    have hx := hxs x (by simp)
    have := ih (t := t ⬝ x) (.app ht hx) (fun y hy => hxs y (by simp [hy])) h
    exact budStep (fold_lt ht) (fold_lt hx) this

/-- With six or more arguments and a block other than ⊥, the function part is in block 0, 1, 3,
6 or 12.  The converse is `unbounded_S`. -/
theorem unbounded_blocks {xs : List Term} {t : Term} (ht : PureS t) (hxs : ∀ x ∈ xs, PureS x)
    (h : fold (xs.foldl Term.app t) ≠ 36) (hl : 6 ≤ xs.length) :
    fold t = 0 ∨ fold t = 1 ∨ fold t = 3 ∨ fold t = 6 ∨ fold t = 12 := by
  have hm := app_budget xs ht hxs h
  obtain ⟨j, hj⟩ : ∃ j, xs.length = j + 6 := ⟨xs.length - 6, by omega⟩
  rw [hj, A_ge6] at hm
  simpa [A] using hm

/-! ## Shapes of the unbounded blocks -/

def shapeB : Bool := r38.all fun a => r38.all fun b =>
  (β a b != 1 || (a == 0 && b == 0)) &&
  (β a b != 3 || (a == 1 && b == 0)) &&
  (β a b != 6 || ((a == 1 && b == 1) || (a == 3 && b == 0))) &&
  (β a b != 12 || (a == 1 || (b == 0 && (a == 6 || a == 12))))
theorem shapeB_eq : shapeB = true := by decide +kernel

theorem shape_tab {a b : Nat} (ha : a < 38) (hb : b < 38) :
    (β a b = 1 → a = 0 ∧ b = 0) ∧ (β a b = 3 → a = 1 ∧ b = 0) ∧
    (β a b = 6 → (a = 1 ∧ b = 1) ∨ (a = 3 ∧ b = 0)) ∧
    (β a b = 12 → a = 1 ∨ (b = 0 ∧ (a = 6 ∨ a = 12))) := by
  have h := shapeB_eq
  simp only [shapeB, r38, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h3⟩, h6⟩, h12⟩ := h a ha b hb
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rcases h1 with h1 | h1
    · exact absurd e h1
    · exact h1
  · rcases h3 with h3 | h3
    · exact absurd e h3
    · exact h3
  · rcases h6 with h6 | h6
    · exact absurd e h6
    · exact h6
  · rcases h12 with h12 | h12
    · exact absurd e h12
    · exact h12

/-- Block 1 is `S S`. -/
theorem shape1 {t : Term} (ht : PureS t) (h : fold t = 1) : t = S ⬝ S := by
  cases ht with
  | S => cases h
  | app hf hx =>
    obtain ⟨e1, e2⟩ := (shape_tab (fold_lt hf) (fold_lt hx)).1 h
    rw [fold_eq_zero hf e1, fold_eq_zero hx e2]

/-- **Long applications.**  If the block of `t x x₁ … x_k` is not ⊥ and `k ≥ 6`, then `t` is the
literal term `S S` or `x` is the literal term `S`.  (One argument at a time: it says nothing about
`x₁ … x_k` directly; apply it to `t x`, `t x x₁`, … while six arguments remain.) -/
theorem long_app {xs : List Term} {t x : Term} (ht : PureS t) (hx : PureS x)
    (hxs : ∀ y ∈ xs, PureS y) (h : fold (xs.foldl Term.app (t ⬝ x)) ≠ 36) (hl : 6 ≤ xs.length) :
    t = S ⬝ S ∨ x = S := by
  have hm := app_budget xs (.app ht hx) hxs h
  obtain ⟨j, hj⟩ : ∃ j, xs.length = j + 6 := ⟨xs.length - 6, by omega⟩
  rw [hj, A_ge6] at hm
  have h0 := longB_eq
  simp only [longB, r38, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq] at h0
  rcases h0 (fold t) (fold_lt ht) (fold x) (fold_lt hx) with (h1 | h1) | h1
  · have hm' : β (fold t) (fold x) ∈ A 6 := hm
    have : (A 6).contains (β (fold t) (fold x)) = true := by simpa using hm'
    rw [this] at h1; cases h1
  · exact .inl (shape1 ht h1)
  · exact .inr (fold_eq_zero hx h1)

/-- Block 3 is `S S S`. -/
theorem shape3 {t : Term} (ht : PureS t) (h : fold t = 3) : t = S ⬝ S ⬝ S := by
  cases ht with
  | S => cases h
  | app hf hx =>
    obtain ⟨e1, e2⟩ := (shape_tab (fold_lt hf) (fold_lt hx)).2.1 h
    rw [shape1 hf e1, fold_eq_zero hx e2]

/-- Block 6 is `S S (S S)` or `S S S S` (which reduces to it). -/
theorem shape6 {t : Term} (ht : PureS t) (h : fold t = 6) :
    t = S ⬝ S ⬝ (S ⬝ S) ∨ t = S ⬝ S ⬝ S ⬝ S := by
  cases ht with
  | S => cases h
  | app hf hx =>
    rcases (shape_tab (fold_lt hf) (fold_lt hx)).2.2.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left; rw [shape1 hf e1, shape1 hx e2]
    · right; rw [shape3 hf e1, fold_eq_zero hx e2]

/-- Block 12 reduces to `S S c`: a head normal form whose first item is `S`. -/
theorem shape12 : ∀ {t : Term}, PureS t → fold t = 12 → ∃ c, WSteps t (S ⬝ S ⬝ c) := by
  intro t ht
  induction ht with
  | S => intro h; cases h
  | @app f x hf hx ihf _ =>
    intro h
    rcases (shape_tab (fold_lt hf) (fold_lt hx)).2.2.2 h with e1 | ⟨e2, e3⟩
    · exact ⟨x, by rw [shape1 hf e1]; exact .refl _⟩
    · have ex := fold_eq_zero hx e2
      subst ex
      rcases e3 with e3 | e3
      · rcases shape6 hf e3 with e | e
        · exact ⟨S ⬝ S ⬝ S, by rw [e]; exact .single (.S S (S ⬝ S) S)⟩
        · refine ⟨S ⬝ S ⬝ S, ?_⟩
          rw [e]
          exact .step (.left S (.S S S S)) (.single (.S S (S ⬝ S) S))
      · obtain ⟨c, hc⟩ := ihf e3
        exact ⟨c ⬝ S, (WSteps.left S hc).trans (.single (.S S c S))⟩

def arityB : Bool := r38.all fun a => r38.all fun b => r38.all fun c => β 0 a != two b c
theorem arityB_eq : arityB = true := by decide +kernel

/-- The block decides the arity of the hnf: `S`, `S a`, `S b c` have pairwise different blocks. -/
theorem arity_blocks {a b c : Nat} (ha : a < 38) (hb : b < 38) (hc : c < 38) :
    β 0 a ≠ two b c ∧ β 0 a ≠ 0 ∧ two b c ≠ 0 := by
  have h := arityB_eq
  simp only [arityB, r38, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  exact ⟨h a ha b hb c hc, beta_ne_zero (by decide) ha, beta_ne_zero (β_lt (by decide) hb) hc⟩

/-! ## Towers -/

/-- `iterS k u = S^k u`. -/
def iterS : Nat → Term → Term
  | 0, u => u
  | k + 1, u => S ⬝ iterS k u

/-- The tower `S^k (S S)`. -/
def tower (k : Nat) : Term := iterS k (S ⬝ S)

def towerShapeB : Bool := r38.all fun a => r38.all fun b =>
  !([2, 4, 8, 17].contains (β a b)) || (a == 0 && [1, 2, 4, 8, 17].contains b)
theorem towerShapeB_eq : towerShapeB = true := by decide +kernel

/-- A term of block 1, 2, 4, 8 or 17 is a literal tower.  The converse is `fold_tower`. -/
theorem tower_of_fold : ∀ {u : Term}, PureS u → fold u ∈ [1, 2, 4, 8, 17] → ∃ k, u = tower k := by
  intro u hu
  induction hu with
  | S => intro h; simp [fold] at h
  | @app f x hf hx _ ihx =>
    intro h
    by_cases h1 : fold (f ⬝ x) = 1
    · exact ⟨0, shape1 (.app hf hx) h1⟩
    · have h0 := towerShapeB_eq
      simp only [towerShapeB, r38, List.all_eq_true, List.mem_range, Bool.or_eq_true,
        Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h0
      have hm : β (fold f) (fold x) ∈ [2, 4, 8, 17] := by
        have : fold (f ⬝ x) ∈ [1, 2, 4, 8, 17] := h
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at this ⊢
        rcases this with e | e
        · exact absurd e h1
        · exact e
      rcases h0 (fold f) (fold_lt hf) (fold x) (fold_lt hx) with h2 | ⟨e1, e2⟩
      · have : ([2, 4, 8, 17].contains (β (fold f) (fold x))) = true := by simpa using hm
        rw [this] at h2; cases h2
      · obtain ⟨k, hk⟩ := ihx e2
        exact ⟨k + 1, by rw [fold_eq_zero hf e1, hk]; rfl⟩

/-- An exempt first item (`HnfSound.exempt`) is `S` or a tower `S^k (S S)` with `k ≥ 4`. -/
theorem exempt_shape {u : Term} (hu : PureS u) (h : exempt (fold u) = true) :
    u = S ∨ ∃ k, u = tower (k + 4) := by
  simp only [exempt, towerBlock, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact .inl (fold_eq_zero hu h)
  · obtain ⟨k, rfl⟩ := tower_of_fold hu (by rw [h]; decide)
    match k, h with
    | 0, h => exact absurd h (by decide)
    | 1, h => exact absurd h (by decide)
    | 2, h => exact absurd h (by decide)
    | 3, h => exact absurd h (by decide)
    | k + 4, _ => exact .inr ⟨k, rfl⟩

/-! ## The skeleton of a productive head run -/

/-- Head chains that count the steps whose first frame item is not exempt. -/
inductive HeadChainN : Nat → Term → Term → Prop
  | refl (t : Term) : HeadChainN 0 t t
  | step {n : Nat} {t v : Term} {u₁ u₂ u₃ : Term} {rest : List Term}
      (hs : spine t = u₁ :: u₂ :: u₃ :: rest)
      (hS : t = rest.foldl Term.app (S ⬝ u₁ ⬝ u₂ ⬝ u₃))
      (h : HeadChainN n (rest.foldl Term.app (u₁ ⬝ u₃ ⬝ (u₂ ⬝ u₃))) v) :
      HeadChainN (n + (if exempt (fold u₁) then 0 else 1)) t v

theorem headChainN_of {t u : Term} (h : HeadChain t u) : ∃ n, HeadChainN n t u := by
  induction h with
  | refl t => exact ⟨0, .refl t⟩
  | step hs hS _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨_, .step hs hS hn⟩

def piB : Bool := r38.all fun b => decide (pw b ≤ 10)
theorem piB_eq : piB = true := by decide +kernel

/-- The weight of a term with an hnf is at most 10. -/
theorem r1_le {t : Term} (ht : PureS t) (hb : fold t ≠ 36) : r₁ t ≤ 10 := by
  have h := wt_le_pot 0 (by decide) (spine t) (spine_pure ht) (allH_spine ht hb)
  rw [walk_spine ht] at h
  have hp := piB_eq
  simp only [piB, r38, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hp
  have := hp (fold t) (fold_lt ht)
  show wt 0 (spine t) ≤ 10
  omega

theorem skeleton_r1 : ∀ {n : Nat} {t v : Term}, HeadChainN n t v → PureS t → fold t ≠ 36 →
    n ≤ r₁ t := by
  intro n t v h
  induction h with
  | refl t => intro _ _; exact Nat.zero_le _
  | step hs hS _ ih =>
    intro ht hb
    obtain ⟨hstep, _, hr, _, _⟩ := root_step ht hb hs
    obtain ⟨hp', he⟩ := wstep_pure hstep ht
    have := ih hp' (by rw [he]; exact hb)
    omega

/-- **Skeleton.**  A head run from a term with an hnf has at most 10 steps whose first frame
item is neither `S` nor a tower of block 17. -/
theorem skeleton {n : Nat} {t v : Term} (h : HeadChainN n t v) (ht : PureS t)
    (hb : fold t ≠ 36) : n ≤ 10 :=
  Nat.le_trans (skeleton_r1 h ht hb) (r1_le ht hb)

/-! ## One-item chains and the Fibonacci map -/

/-- `k` Fibonacci steps on a pair of terms: `(x, y) ↦ (y, x y)`. -/
def fibT : Nat → Term × Term → Term × Term
  | 0, p => p
  | k + 1, p => fibT k (p.2, p.1 ⬝ p.2)

/-- The same on blocks. -/
def fibB : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | k + 1, p => fibB k (p.2, β p.1 p.2)

/-- `S^k u x y` head-reduces to `u P Q`, `(P, Q)` the `k`-th Fibonacci pair of `(x, y)`. -/
theorem iterS_run : ∀ (k : Nat) (u x y : Term),
    Steps (iterS k u ⬝ x ⬝ y) (u ⬝ (fibT k (x, y)).1 ⬝ (fibT k (x, y)).2) := by
  intro k
  induction k with
  | zero => intro u x y; exact .refl _
  | succ k ih => intro u x y; exact .step (.S (iterS k u) x y) (ih u y (x ⬝ y))

theorem fibT_pure : ∀ (k : Nat) {x y : Term}, PureS x → PureS y →
    PureS (fibT k (x, y)).1 ∧ PureS (fibT k (x, y)).2 := by
  intro k
  induction k with
  | zero => intro x y hx hy; exact ⟨hx, hy⟩
  | succ k ih => intro x y hx hy; exact ih hy (.app hx hy)

theorem fold_fibT : ∀ (k : Nat) (x y : Term),
    (fold (fibT k (x, y)).1, fold (fibT k (x, y)).2) = fibB k (fold x, fold y) := by
  intro k
  induction k with
  | zero => intro x y; rfl
  | succ k ih => intro x y; exact ih y (x ⬝ y)

def fib8B : Bool := r38.all fun p => r38.all fun q => fibB 8 (p, q) == (36, 36)
theorem fib8B_eq : fib8B = true := by decide +kernel

theorem fibB_add : ∀ (j k : Nat) (p : Nat × Nat), fibB (j + k) p = fibB k (fibB j p) := by
  intro j
  induction j with
  | zero => intro k p; rw [Nat.zero_add]; rfl
  | succ j ih => intro k p; rw [Nat.add_right_comm]; exact ih k _

theorem fibB_bot : ∀ k : Nat, fibB k (36, 36) = (36, 36) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- From step 8 on, both members of the Fibonacci pair are hnf-less, whatever the start. -/
theorem fib_dead (k : Nat) {x y : Term} (hx : PureS x) (hy : PureS y) :
    fold (fibT (k + 8) (x, y)).1 = 36 ∧ fold (fibT (k + 8) (x, y)).2 = 36 := by
  have h := fold_fibT (k + 8) x y
  have h8 := fib8B_eq
  simp only [fib8B, r38, List.all_eq_true, List.mem_range, beq_iff_eq] at h8
  have e : fibB (k + 8) (fold x, fold y) = (36, 36) := by
    rw [Nat.add_comm, fibB_add, h8 _ (fold_lt hx) _ (fold_lt hy), fibB_bot]
  rw [e] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## The Ψ counterexample to depth-bounded exposure (S1 labels) -/

theorem fold_iterS_congr : ∀ (j : Nat) {u v : Term}, fold u = fold v →
    fold (iterS j u) = fold (iterS j v) := by
  intro j
  induction j with
  | zero => intro u v h; exact h
  | succ j ih => intro u v h; show β 0 _ = β 0 _; rw [ih h]

/-- `S^k (S S c) x y` head-reduces to `f w` with `f = P Q` hnf-less and `w = c P Q`, where
`P`, `Q` are hnf-less (`k ≥ 8`). -/
theorem deep_item (k : Nat) (c : Term) {x y : Term} (hx : PureS x) (hy : PureS y) :
    ∃ P Q, Steps (iterS (k + 8) (S ⬝ S ⬝ c) ⬝ x ⬝ y) (P ⬝ Q ⬝ (c ⬝ P ⬝ Q)) ∧
      fold P = 36 ∧ fold Q = 36 ∧ fold (P ⬝ Q) = 36 := by
  obtain ⟨hP, hQ⟩ := fib_dead k hx hy
  refine ⟨(fibT (k + 8) (x, y)).1, (fibT (k + 8) (x, y)).2, ?_, hP, hQ, ?_⟩
  · refine (iterS_run (k + 8) (S ⬝ S ⬝ c) x y).trans ?_
    exact .step (.left _ (.S S c _)) (.single (.S _ _ _))
  · show β _ _ = 36; rw [hP]; exact absorb (by rw [hQ]; decide)

/-- **Counterexample (Ψ part, S1 labels): what is proved here.**  Let `t c = S^(k+8) (S S c)`,
`c₁ = S (S S)`, `c₂ = S S S`.  (1) Every `S^j (S S c)` has the same block for both `c`.  (2)
`t c x y` head-reduces to some `f w` with `fold f = 36`, where `fold w = 31` for `c₁` and `36` for
`c₂`.  `psi_cex_stable` adds that every such `f w` has this `w`.  That (1) makes the labelled
unfoldings `τ_D` equal for `D ≤ k + 7` is a pencil step (the hnf of `S^(j+1) u` is `S (S^j u)`),
not stated in Lean. -/
theorem psi_cex (k : Nat) {x y : Term} (hx : PureS x) (hy : PureS y) :
    (∀ j, fold (iterS j (S ⬝ S ⬝ (S ⬝ (S ⬝ S)))) = fold (iterS j (S ⬝ S ⬝ (S ⬝ S ⬝ S)))) ∧
    (∃ f w, Steps (iterS (k + 8) (S ⬝ S ⬝ (S ⬝ (S ⬝ S))) ⬝ x ⬝ y) (f ⬝ w) ∧ fold f = 36 ∧
      fold w = 31) ∧
    (∃ f w, Steps (iterS (k + 8) (S ⬝ S ⬝ (S ⬝ S ⬝ S)) ⬝ x ⬝ y) (f ⬝ w) ∧ fold f = 36 ∧
      fold w = 36) := by
  refine ⟨fun j => fold_iterS_congr j (by decide), ?_, ?_⟩
  · obtain ⟨P, Q, hs, hP, hQ, hPQ⟩ := deep_item k (S ⬝ (S ⬝ S)) hx hy
    refine ⟨_, _, hs, hPQ, ?_⟩
    show β (β (fold (S ⬝ (S ⬝ S))) (fold P)) (fold Q) = 31
    rw [hP, hQ]; decide
  · obtain ⟨P, Q, hs, hP, hQ, hPQ⟩ := deep_item k (S ⬝ S ⬝ S) hx hy
    refine ⟨_, _, hs, hPQ, ?_⟩
    show β (β (fold (S ⬝ S ⬝ S)) (fold P)) (fold Q) = 36
    rw [hP, hQ]; decide

/-! ## Converses and uniqueness (after the Wizard review, 2026-11-23) -/

theorem tower_pure : ∀ k : Nat, PureS (tower k) := by
  intro k
  induction k with
  | zero => exact .app .S .S
  | succ k ih => exact .app .S ih

/-- Every tower has block 1, 2, 4, 8 or 17 (converse of `tower_of_fold`). -/
theorem fold_tower : ∀ k : Nat, fold (tower k) ∈ [1, 2, 4, 8, 17] := by
  intro k
  induction k with
  | zero => decide
  | succ k ih =>
    have h : ∀ b ∈ [1, 2, 4, 8, 17], β 0 b ∈ [1, 2, 4, 8, 17] := by decide
    exact h _ ih

/-- The five unbounded blocks stay among themselves under any number of arguments `S`
(converse of `unbounded_blocks`): their budgets are unbounded. -/
theorem unbounded_S : ∀ (k : Nat) {t : Term}, fold t ∈ [0, 1, 3, 6, 12] →
    fold ((List.replicate k S).foldl Term.app t) ∈ [0, 1, 3, 6, 12] := by
  intro k
  induction k with
  | zero => intro t h; exact h
  | succ k ih =>
    intro t h
    have hs : ∀ b ∈ [0, 1, 3, 6, 12], β b 0 ∈ [0, 1, 3, 6, 12] := by decide
    exact ih (t := t ⬝ S) (hs _ h)

theorem unbounded_S_ne (k : Nat) {t : Term} (h : fold t ∈ [0, 1, 3, 6, 12]) :
    fold ((List.replicate k S).foldl Term.app t) ≠ 36 := by
  intro e
  have := unbounded_S k h
  rw [e] at this
  exact absurd this (by decide)

/-- A head step of `f w` with `f` hnf-less is a head step of `f`. -/
theorem stable_step {f w u : Term} (hf : PureS f) (hb : fold f = 36) (s : Step (f ⬝ w) u) :
    ∃ f', u = f' ⬝ w ∧ PureS f' ∧ fold f' = 36 := by
  cases s with
  | S a c x =>
    exfalso
    obtain ⟨h1, hc⟩ := hf.app_inv
    exact (hnf_blocks (fold_lt h1.app_inv.2) (fold_lt hc)).2 hb
  | K x y => exact absurd hf.app_inv.1 PureS.not_K
  | I x => exact absurd hf PureS.not_I
  | left _ h =>
    obtain ⟨hp, he⟩ := wstep_pure h.weak hf
    exact ⟨_, rfl, hp, he.trans hb⟩

theorem stable_steps {w : Term} : ∀ {t u : Term}, Steps t u → ∀ {f : Term}, t = f ⬝ w → PureS f →
    fold f = 36 → ∃ f', u = f' ⬝ w ∧ PureS f' ∧ fold f' = 36 := by
  intro t u h
  induction h with
  | refl t => intro f e hf hb; exact ⟨f, e, hf, hb⟩
  | step s _ ih =>
    intro f e hf hb
    subst e
    obtain ⟨f', e', hf', hb'⟩ := stable_step hf hb s
    exact ih e' hf' hb'

theorem steps_linear {t a : Term} (h₁ : Steps t a) : ∀ {b : Term}, Steps t b →
    Steps a b ∨ Steps b a := by
  induction h₁ with
  | refl t => intro b h₂; exact .inl h₂
  | step s hs ih =>
    intro b h₂
    cases h₂ with
    | refl => exact .inr (.step s hs)
    | step s' hs' =>
      have e := Step.det s s'
      subst e
      exact ih hs'

/-- **The stable decomposition is unique in its argument.**  If `t` head-reduces to `f w` and to
`f' w'` with `f`, `f'` hnf-less, then `w = w'` (and `f`, `f'` lie on one head run). -/
theorem stable_unique {t f w f' w' : Term} (ht : PureS t) (h : Steps t (f ⬝ w))
    (hb : fold f = 36) (h' : Steps t (f' ⬝ w')) (hb' : fold f' = 36) : w = w' := by
  have hf := (fold_wsteps h.weak ht).1.app_inv.1
  have hf' := (fold_wsteps h'.weak ht).1.app_inv.1
  rcases steps_linear h h' with hs | hs
  · obtain ⟨g, e, _, _⟩ := stable_steps hs rfl hf hb
    injection e with _ e2
    exact e2.symm
  · obtain ⟨g, e, _, _⟩ := stable_steps hs rfl hf' hb'
    injection e with _ e2

theorem iterS_pure : ∀ (k : Nat) {u : Term}, PureS u → PureS (iterS k u) := by
  intro k
  induction k with
  | zero => intro u hu; exact hu
  | succ k ih => intro u hu; exact .app .S (ih hu)

/-- **The Ψ counterexample, in terms of every stable decomposition.**  For `k ≥ 8`: whenever
`S^k (S S c) x y` head-reduces to `f w` with `f` hnf-less, the block of `w` is 31 for
`c = S (S S)` and 36 for `c = S S S`.  (Such `f w` exist: `psi_cex`.) -/
theorem psi_cex_stable (k : Nat) {x y f w : Term} (hx : PureS x) (hy : PureS y)
    (hb : fold f = 36) :
    (Steps (iterS (k + 8) (S ⬝ S ⬝ (S ⬝ (S ⬝ S))) ⬝ x ⬝ y) (f ⬝ w) → fold w = 31) ∧
    (Steps (iterS (k + 8) (S ⬝ S ⬝ (S ⬝ S ⬝ S)) ⬝ x ⬝ y) (f ⬝ w) → fold w = 36) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨P, Q, hs, hP, hQ, hPQ⟩ := deep_item k (S ⬝ (S ⬝ S)) hx hy
    have hp : PureS (iterS (k + 8) (S ⬝ S ⬝ (S ⬝ (S ⬝ S))) ⬝ x ⬝ y) :=
      .app (.app (iterS_pure _ (.app (.app .S .S) (.app .S (.app .S .S)))) hx) hy
    rw [stable_unique hp h hb hs hPQ]
    show β (β (fold (S ⬝ (S ⬝ S))) (fold P)) (fold Q) = 31
    rw [hP, hQ]; decide
  · obtain ⟨P, Q, hs, hP, hQ, hPQ⟩ := deep_item k (S ⬝ S ⬝ S) hx hy
    have hp : PureS (iterS (k + 8) (S ⬝ S ⬝ (S ⬝ S ⬝ S)) ⬝ x ⬝ y) :=
      .app (.app (iterS_pure _ (.app (.app .S .S) (.app (.app .S .S) .S))) hx) hy
    rw [stable_unique hp h hb hs hPQ]
    show β (β (fold (S ⬝ S ⬝ S)) (fold P)) (fold Q) = 36
    rw [hP, hQ]; decide

end BExp
