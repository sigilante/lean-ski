import Ski.Circuit.CompRow

/-!
# One composed CPU row: its kind

Twelve kinds: the machine's eleven, and the restart (`11`), which reads
`K` at the head and a nil at the stack and jumps to the next root.  Each
kind's expressions are checked by substitution and normal forms, as in
`Ski/Circuit/BaseKind.lean` (`kindOKC_all`).
-/

namespace Circuit

open B

/-- **A composed row of kind `k`**: its selectors and restart selector. -/
def IsKindC (T : Table) (r k : Nat) : Prop :=
  k < 12 ∧ (∀ i, i < NKINDS → T.main r (SEL + i) = if i = k ∧ k < 11 then 1 else 0) ∧
    T.main r RS = if k = 11 then 1 else 0

section Row

variable {hd0 stk0 ctr0 n nilA : Nat} {T : Table} (hs : Sat (cpuAirC hd0 stk0 ctr0 n nilA) T)
  {r : Nat} (hr : r < T.h)
include hs hr

/-- **The row's kind**: one of the machine's eleven, or a restart. -/
theorem kind_ofC : ∃ k, IsKindC T r k := by
  let xs := (List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RS]
  have hb : ∀ x ∈ xs, x.val ≤ 1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      rcases val_of_bit (sel_bitC hs hr (List.mem_range.1 hi)) with h | h <;> omega
    · rw [List.mem_singleton.1 hx]
      rcases val_of_bit (rs_bit hs hr) with h | h <;> omega
  obtain ⟨hv, _⟩ := sum_bits_val xs hb (by simp [xs, NKINDS, P])
  have hsum := sel_sumC hs hr
  rw [show ((List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RS]) = xs from rfl,
    Fin.ext_iff, hv] at hsum
  obtain ⟨k, hk, h1, h0⟩ := onehot (xs.map Fin.val) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hb x hx) hsum
  have hlen : (xs.map Fin.val).length = 15 := by simp [xs, NKINDS]
  have get : ∀ i, i < 15 → (xs.map Fin.val).getD i 0 =
      (if i < NKINDS then T.main r (SEL + i) else T.main r RS).val := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
    simp only [xs, List.getElem_map, Option.getD_some]
    rcases Nat.lt_or_ge i NKINDS with h | h
    · rw [if_pos h, List.getElem_append_left (by simp; exact h)]; simp
    · rw [if_neg (by omega), List.getElem_append_right (by simp; omega)]
      have : i - ((List.range NKINDS).map fun i => T.main r (SEL + i)).length = 0 := by
        simp [NKINDS] at h ⊢; omega
      simp only [this]; rfl
  rw [hlen] at hk
  have val : ∀ i, i < 15 → (if i < NKINDS then T.main r (SEL + i) else T.main r RS) =
      if i = k then 1 else 0 := by
    intro i hi
    apply Fin.ext
    by_cases hik : i = k
    · rw [if_pos hik]; subst hik; rw [← get i hi, h1]; rfl
    · rw [if_neg hik, ← get i hi, h0 i (by rw [hlen]; exact hi) hik]; rfl
  have e11 := val 11 (by decide)
  have e12 := val 12 (by decide)
  have e13 := val 13 (by decide)
  rw [if_pos (by decide), inst_zeroC hs hr] at e11
  rw [if_pos (by decide), pfirst_zeroC hs hr] at e12
  rw [if_pos (by decide), plater_zeroC hs hr] at e13
  have n11 : k ≠ 11 := fun h => by rw [if_pos h.symm] at e11; exact absurd e11 (by decide)
  have n12 : k ≠ 12 := fun h => by rw [if_pos h.symm] at e12; exact absurd e12 (by decide)
  have n13 : k ≠ 13 := fun h => by rw [if_pos h.symm] at e13; exact absurd e13 (by decide)
  have e14 := val 14 (by decide)
  rw [if_neg (by decide)] at e14
  rcases Nat.lt_or_ge k 11 with hk11 | hk11
  · refine ⟨k, by omega, fun i hi => ?_, ?_⟩
    · have := val i (by unfold NKINDS at hi; omega)
      rw [if_pos hi] at this
      rw [this]
      by_cases e : i = k
      · rw [if_pos e, if_pos ⟨e, hk11⟩]
      · rw [if_neg e, if_neg (fun h => e h.1)]
    · rw [e14, if_neg (by omega), if_neg (by omega)]
  · have hk14 : k = 14 := by omega
    refine ⟨11, by decide, fun i hi => ?_, ?_⟩
    · have := val i (by unfold NKINDS at hi; omega)
      rw [if_pos hi, if_neg (by unfold NKINDS at hi; omega)] at this
      rw [this, if_neg (fun h => absurd h.2 (by decide))]
    · rw [e14, if_pos hk14.symm, if_pos rfl]

end Row

/-- Kind `k`'s selectors and restart selector, as constants. -/
def selSubC (k : Nat) : Atom → E
  | .main 0 i =>
    if SEL ≤ i ∧ i < SEL + NKINDS then .const (if i - SEL = k ∧ k < 11 then 1 else 0)
    else if i = RS then .const (if k = 11 then 1 else 0) else .atom (.main 0 i)
  | a => .atom a

def actOfC (k j : Nat) : Nat := if k = 11 then (if j < 2 then 1 else 0) else actOf k j
def tagOfC (k j : Nat) : Nat := if k = 11 then (if j = 0 then 1 else if j = 1 then 4 else 0) else tagOf k j
def haltOfC (k : Nat) : Nat := if 4 ≤ k ∧ k < 11 then 1 else 0
def nextHdOfC (k : Nat) : E := if k = 11 then zero else nextHdOf k
def nextStkOfC (k : Nat) : E := if k = 11 then zero else nextStkOf k
def nextCtrOfC (k : Nat) : E := if k = 11 then col CTR else nextCtrOf k

def kindEqC (k : Nat) (e e' : E) : Bool := (e.subst (selSubC k)).norm == e'.norm

/-- **The composed kind table.** -/
def kindOKC (k : Nat) : Bool :=
  (List.range 4).all (fun j => kindEqC k (acts.getD j zero) (c (actOfC k j)) &&
    kindEqC k (tagsC.getD j zero) (c (tagOfC k j))) &&
  kindEqC k halt (c (haltOfC k)) &&
  kindEqC k sApp (c (if k = 0 then 1 else 0)) && kindEqC k sS (c (if k = 3 then 1 else 0)) &&
  kindEqC k sHK1 (c (if k = 5 then 1 else 0)) && kindEqC k sRS (c (if k = 11 then 1 else 0)) &&
  kindEqC k nextHd (nextHdOfC k) && kindEqC k nextStk (nextStkOfC k) && kindEqC k nextCtr (nextCtrOfC k)

theorem kindOKC_all : (List.range 12).all kindOKC = true := by decide

theorem selSubC_eval {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindC T r k) (a : Atom) :
    (selSubC k a).eval (T.env r) = T.env r a := by
  cases a with
  | main o i =>
    cases o with
    | zero =>
      simp only [selSubC]
      split
      · next h =>
        rw [env_main0 hr]
        have e := hk.2.1 (i - SEL) (Nat.sub_lt_left_of_lt_add h.1 h.2)
        rw [Nat.add_sub_cancel' h.1] at e
        rw [e]; rfl
      · split
        · next h => subst h; rw [env_main0 hr, hk.2.2]; rfl
        · rfl
    | succ o => rfl
  | pre _ _ => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

theorem kind_evalC {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindC T r k) {e e' : E}
    (h : kindEqC k e e' = true) : e.eval (T.env r) = e'.eval (T.env r) := by
  rw [← E.eval_subst (selSubC k) (T.env r) (selSubC_eval hr hk) e]
  exact E.eval_eq_of_norm (beq_iff_eq.1 h) _

/-- **A composed row's kind, evaluated.** -/
theorem kind_factsC {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindC T r k) :
    (∀ j, j < 4 → (acts.getD j zero).eval (T.env r) = ofN (actOfC k j) ∧
      (tagsC.getD j zero).eval (T.env r) = ofN (tagOfC k j)) ∧
    halt.eval (T.env r) = ofN (haltOfC k) ∧
    sApp.eval (T.env r) = ofN (if k = 0 then 1 else 0) ∧ sS.eval (T.env r) = ofN (if k = 3 then 1 else 0) ∧
    sHK1.eval (T.env r) = ofN (if k = 5 then 1 else 0) ∧ sRS.eval (T.env r) = ofN (if k = 11 then 1 else 0) ∧
    nextHd.eval (T.env r) = (nextHdOfC k).eval (T.env r) ∧
    nextStk.eval (T.env r) = (nextStkOfC k).eval (T.env r) ∧
    nextCtr.eval (T.env r) = (nextCtrOfC k).eval (T.env r) := by
  have h := List.all_eq_true.1 kindOKC_all k (List.mem_range.2 hk.1)
  simp only [kindOKC, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hj, hh⟩, ha⟩, hs⟩, hk1⟩, hrs⟩, h1⟩, h2⟩, h3⟩ := h
  exact ⟨fun j hj' => ⟨kind_evalC hr hk (hj j hj').1, kind_evalC hr hk (hj j hj').2⟩,
    kind_evalC hr hk hh, kind_evalC hr hk ha, kind_evalC hr hk hs, kind_evalC hr hk hk1,
    kind_evalC hr hk hrs, kind_evalC hr hk h1, kind_evalC hr hk h2, kind_evalC hr hk h3⟩

end Circuit

#print axioms Circuit.kind_ofC
#print axioms Circuit.kindOKC_all
#print axioms Circuit.kind_factsC
