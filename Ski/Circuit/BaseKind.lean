import Ski.Circuit.BaseRow

/-!
# One CPU row: its kind, and its range checks, in numbers

From the row's equations (`Ski/Circuit/BaseRow.lean`):
- exactly one kind selector is `1`, the others `0`, and it is not the
  instantiation or a probe kind (`kind_of`);
- a range check's value is a number below `2^24` (`rangeVal_val`).
-/

namespace Circuit

open B

-- ---------------------------------------------------------------------------
-- Bits and their sums
-- ---------------------------------------------------------------------------

theorem val_of_bit {x : F} (h : x * (x - 1) = 0) : x.val = 0 ∨ x.val = 1 := by
  rcases bit_of h with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem val_add_of_lt {a b : F} (h : a.val + b.val < P) : (a + b).val = a.val + b.val := by
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

/-- A sum of bits, as a number: the number of ones. -/
theorem sum_bits_val : ∀ xs : List F, (∀ x ∈ xs, x.val ≤ 1) → xs.length < P →
    (xs.foldr (· + ·) 0).val = (xs.map Fin.val).sum ∧ (xs.map Fin.val).sum ≤ xs.length
  | [], _, _ => ⟨rfl, Nat.le_refl _⟩
  | x :: xs, h, hl => by
    have hx := h x (List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := sum_bits_val xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      (Nat.lt_of_le_of_lt (Nat.le_succ _) hl)
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, List.length_cons] at hl ⊢
    refine ⟨?_, by omega⟩
    rw [val_add_of_lt (by rw [ih1]; omega), ih1]

theorem le_sum_of_mem : ∀ {xs : List Nat} {y : Nat}, y ∈ xs → y ≤ xs.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; exact Nat.le_add_right _ _
  | x :: _, _, .tail _ h => by
    simp only [List.sum_cons]; exact Nat.le_trans (le_sum_of_mem h) (Nat.le_add_left _ x)

/-- **One-hot, in numbers**: bits summing to one have exactly one one. -/
theorem onehot : ∀ xs : List Nat, (∀ x ∈ xs, x ≤ 1) → xs.sum = 1 →
    ∃ k, k < xs.length ∧ xs.getD k 0 = 1 ∧ ∀ i, i < xs.length → i ≠ k → xs.getD i 0 = 0
  | [], _, h => by simp at h
  | x :: xs, hb, h => by
    have hx := hb x (List.mem_cons_self)
    simp only [List.sum_cons] at h
    rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
    · obtain ⟨k, hk, h1, h0⟩ := onehot xs (fun y hy => hb y (List.mem_cons_of_mem _ hy)) (by omega)
      refine ⟨k + 1, by simp; omega, by simpa using h1, fun i hi hne => ?_⟩
      cases i with
      | zero => rfl
      | succ i => simpa using h0 i (by simp at hi; omega) (by omega)
    · have hz : xs.sum = 0 := by omega
      have hall : ∀ y ∈ xs, y = 0 := fun y hy => by
        have := le_sum_of_mem hy
        omega
      refine ⟨0, by simp, rfl, fun i hi hne => ?_⟩
      cases i with
      | zero => exact absurd rfl hne
      | succ i =>
        simp only [List.getD_cons_succ]
        rw [List.getD_eq_getElem?_getD]
        rcases Nat.lt_or_ge i xs.length with h' | h'
        · rw [List.getElem?_eq_getElem h']
          exact hall _ (List.getElem_mem _)
        · rw [List.getElem?_eq_none h']; rfl

section Row

variable {hd0 stk0 ctr0 : Nat} {T : Table} (hs : Sat (cpuAir hd0 stk0 ctr0) T) {r : Nat} (hr : r < T.h)
include hs hr

/-- **The row's kind**: one selector is `1`, the others `0`; it is one of
    the machine's eleven kinds, not an instantiation or a probe. -/
theorem kind_of : ∃ k, k < 11 ∧ ∀ i, i < NKINDS → T.main r (SEL + i) = if i = k then 1 else 0 := by
  let xs := (List.range NKINDS).map fun i => T.main r (SEL + i)
  have hb : ∀ x ∈ xs, x.val ≤ 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rcases val_of_bit (sel_bit hs hr (List.mem_range.1 hi)) with h | h <;> omega
  obtain ⟨hv, _⟩ := sum_bits_val xs hb (by simp [xs, NKINDS, P])
  have hsum := sel_sum hs hr
  rw [show ((List.range NKINDS).map fun i => T.main r (SEL + i)) = xs from rfl, Fin.ext_iff] at hsum
  rw [hv] at hsum
  obtain ⟨k, hk, h1, h0⟩ := onehot (xs.map Fin.val) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hb x hx) hsum
  have hlen : (xs.map Fin.val).length = NKINDS := by simp [xs]
  have get : ∀ i, i < NKINDS → (xs.map Fin.val).getD i 0 = (T.main r (SEL + i)).val := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
    simp [xs]
  have hval : ∀ i, i < NKINDS → T.main r (SEL + i) = if i = k then 1 else 0 := by
    intro i hi
    apply Fin.ext
    by_cases hik : i = k
    · rw [if_pos hik]; subst hik; rw [← get i hi, h1]; rfl
    · rw [if_neg hik, ← get i hi, h0 i (by rw [hlen]; exact hi) hik]; rfl
  have hk11 : k < 11 := by
    rw [hlen] at hk
    have e11 := hval 11 (by decide)
    have e12 := hval 12 (by decide)
    have e13 := hval 13 (by decide)
    rw [inst_zero hs hr] at e11
    rw [pfirst_zero hs hr] at e12
    rw [plater_zero hs hr] at e13
    by_cases h11 : 11 = k
    · rw [if_pos h11] at e11; exact absurd e11 (by decide)
    · by_cases h12 : 12 = k
      · rw [if_pos h12] at e12; exact absurd e12 (by decide)
      · by_cases h13 : 13 = k
        · rw [if_pos h13] at e13; exact absurd e13 (by decide)
        · unfold NKINDS at hk; omega
  exact ⟨k, hk11, hval⟩

end Row

-- ---------------------------------------------------------------------------
-- Each kind's expressions, with its selectors substituted
-- ---------------------------------------------------------------------------

/-- Replace atoms by expressions. -/
def E.subst (σ : Atom → E) : E → E
  | .atom a => σ a
  | .const c => .const c
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .sub a b => .sub (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .neg a => .neg (a.subst σ)

theorem E.eval_subst (σ : Atom → E) (ρ : Atom → F) (hσ : ∀ a, (σ a).eval ρ = ρ a) :
    ∀ e : E, (e.subst σ).eval ρ = e.eval ρ
  | .atom a => hσ a
  | .const _ => rfl
  | .add a b => by simp only [E.subst, E.eval, E.eval_subst σ ρ hσ a, E.eval_subst σ ρ hσ b]
  | .sub a b => by simp only [E.subst, E.eval, E.eval_subst σ ρ hσ a, E.eval_subst σ ρ hσ b]
  | .mul a b => by simp only [E.subst, E.eval, E.eval_subst σ ρ hσ a, E.eval_subst σ ρ hσ b]
  | .neg a => by simp only [E.subst, E.eval, E.eval_subst σ ρ hσ a]

/-- Kind `k`'s selectors, as constants. -/
def selSub (k : Nat) : Atom → E
  | .main 0 i => if SEL ≤ i ∧ i < SEL + NKINDS then .const (if i - SEL = k then 1 else 0) else .atom (.main 0 i)
  | a => .atom a

/-- Whether a read is active, by kind. -/
def actOf (k j : Nat) : Nat :=
  match j with
  | 0 => 1
  | 1 => if k = 0 ∨ k = 10 then 0 else 1
  | 2 => if k = 2 ∨ k = 3 ∨ k = 6 ∨ k = 8 ∨ k = 9 then 1 else 0
  | _ => if k = 3 ∨ k = 9 then 1 else 0

/-- The tag a read requires, by kind. -/
def tagOf (k j : Nat) : Nat :=
  match j with
  | 0 => if k = 0 then 3 else if k = 1 ∨ k = 4 then 2 else if k = 2 ∨ k = 5 ∨ k = 6 then 1
    else if k = 10 then 6 else 0
  | 1 => if k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 6 ∨ k = 8 ∨ k = 9 then 5
    else if k = 4 ∨ k = 5 ∨ k = 7 then 4 else 0
  | 2 => if k = 2 ∨ k = 3 ∨ k = 9 then 5 else if k = 6 ∨ k = 8 then 4 else 0
  | _ => if k = 3 then 5 else if k = 9 then 4 else 0

def nextHdOf (k : Nat) : E := if k = 0 then fld 0 else if k < 4 then fld 2 else col HD

def nextStkOf (k : Nat) : E :=
  if k = 0 then col CTR else if k = 1 then fld 3 else if k = 2 then fld 5
  else if k = 3 then .add (col CTR) (c 2) else col STK

def nextCtrOf (k : Nat) : E :=
  if k = 0 then .add (col CTR) one else if k = 3 then .add (col CTR) (c 3) else col CTR

/-- Two expressions the same once kind `k`'s selectors are substituted. -/
def kindEq (k : Nat) (e e' : E) : Bool := (e.subst (selSub k)).norm == e'.norm

/-- **The kind table**: every expression the analysis needs, per kind. -/
def kindOK (k : Nat) : Bool :=
  (List.range 4).all (fun j => kindEq k (acts.getD j zero) (c (actOf k j)) &&
    kindEq k (tags.getD j zero) (c (tagOf k j))) &&
  kindEq k halt (c (if 4 ≤ k then 1 else 0)) &&
  kindEq k sApp (c (if k = 0 then 1 else 0)) && kindEq k sS (c (if k = 3 then 1 else 0)) &&
  kindEq k nextHd (nextHdOf k) && kindEq k nextStk (nextStkOf k) && kindEq k nextCtr (nextCtrOf k)

theorem kindOK_all : (List.range 11).all kindOK = true := by decide

theorem kindOK_of {k : Nat} (hk : k < 11) : kindOK k = true :=
  List.all_eq_true.1 kindOK_all k (List.mem_range.2 hk)

/-- **A row of kind `k`**: its selectors are kind `k`'s. -/
def IsKind (T : Table) (r k : Nat) : Prop :=
  k < 11 ∧ ∀ i, i < NKINDS → T.main r (SEL + i) = if i = k then 1 else 0

theorem selSub_eval {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKind T r k) (a : Atom) :
    (selSub k a).eval (T.env r) = T.env r a := by
  cases a with
  | main o i =>
    cases o with
    | zero =>
      simp only [selSub]
      split
      · next h =>
        rw [env_main0 hr]
        have e := hk.2 (i - SEL) (Nat.sub_lt_left_of_lt_add h.1 h.2)
        rw [Nat.add_sub_cancel' h.1] at e
        rw [e]; rfl
      · rfl
    | succ o => rfl
  | pre _ _ => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

theorem kind_eval {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKind T r k) {e e' : E}
    (h : kindEq k e e' = true) : e.eval (T.env r) = e'.eval (T.env r) := by
  rw [← E.eval_subst (selSub k) (T.env r) (selSub_eval hr hk) e]
  exact E.eval_eq_of_norm (beq_iff_eq.1 h) _

/-- **A row's kind, evaluated**: its reads' activity and tags, whether it
    halts, its writes, and its next registers, in the row's values. -/
theorem kind_facts {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKind T r k) :
    (∀ j, j < 4 → (acts.getD j zero).eval (T.env r) = ofN (actOf k j) ∧
      (tags.getD j zero).eval (T.env r) = ofN (tagOf k j)) ∧
    halt.eval (T.env r) = ofN (if 4 ≤ k then 1 else 0) ∧
    sApp.eval (T.env r) = ofN (if k = 0 then 1 else 0) ∧ sS.eval (T.env r) = ofN (if k = 3 then 1 else 0) ∧
    nextHd.eval (T.env r) = (nextHdOf k).eval (T.env r) ∧
    nextStk.eval (T.env r) = (nextStkOf k).eval (T.env r) ∧
    nextCtr.eval (T.env r) = (nextCtrOf k).eval (T.env r) := by
  have h := kindOK_of hk.1
  simp only [kindOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hj, hh⟩, ha⟩, hs⟩, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun j hj' => ⟨kind_eval hr hk (hj j hj').1, kind_eval hr hk (hj j hj').2⟩,
    kind_eval hr hk hh, kind_eval hr hk ha, kind_eval hr hk hs,
    kind_eval hr hk h1, kind_eval hr hk h2, kind_eval hr hk h3⟩

end Circuit
