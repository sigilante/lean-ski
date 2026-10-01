import Ski.Circuit.CompJRow

/-!
# One row of the composed CPU with jets: its kind

Thirteen kinds: the machine's eleven (`0`–`10`), an instantiation (`11`,
the jet CPU's selector `11`), and the restart (`12`, the restart column
`RSJ`, outside the selectors).  Each kind's expressions are checked by
substitution and normal forms (`kindOKCJ_all`), as for the composed CPU
(`Ski/Circuit/CompKind.lean`).
-/

namespace Circuit

open B

/-- **A row of kind `k`**: its selectors and restart selector. -/
def IsKindCJ (T : Table) (r k : Nat) : Prop :=
  k < 13 ∧ (∀ i, i < NKINDS → T.main r (SEL + i) = if i = k ∧ k < 12 then 1 else 0) ∧
    T.main r RSJ = if k = 12 then 1 else 0

section Row

variable {hd0 stk0 ctr0 n nilA : Nat} {T : Table} (hs : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) T)
  {r : Nat} (hr : r < T.h)
include hs hr

/-- **The row's kind**: one of the machine's eleven, an instantiation, or a
    restart. -/
theorem kind_ofCJ : ∃ k, IsKindCJ T r k := by
  let xs := (List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RSJ]
  have hb : ∀ x ∈ xs, x.val ≤ 1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      rcases val_of_bit (sel_bitCJ hs hr (List.mem_range.1 hi)) with h | h <;> omega
    · rw [List.mem_singleton.1 hx]
      rcases val_of_bit (rs_bitCJ hs hr) with h | h <;> omega
  obtain ⟨hv, _⟩ := sum_bits_val xs hb (by simp [xs, NKINDS, P])
  have hsum := sel_sumCJ hs hr
  rw [show ((List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RSJ]) = xs from rfl,
    Fin.ext_iff, hv] at hsum
  obtain ⟨k, hk, h1, h0⟩ := onehot (xs.map Fin.val) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hb x hx) hsum
  have hlen : (xs.map Fin.val).length = 15 := by simp [xs, NKINDS]
  have get : ∀ i, i < 15 → (xs.map Fin.val).getD i 0 =
      (if i < NKINDS then T.main r (SEL + i) else T.main r RSJ).val := by
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
  have val : ∀ i, i < 15 → (if i < NKINDS then T.main r (SEL + i) else T.main r RSJ) =
      if i = k then 1 else 0 := by
    intro i hi
    apply Fin.ext
    by_cases hik : i = k
    · rw [if_pos hik]; subst hik; rw [← get i hi, h1]; rfl
    · rw [if_neg hik, ← get i hi, h0 i (by rw [hlen]; exact hi) hik]; rfl
  have e12 := val 12 (by decide)
  have e13 := val 13 (by decide)
  rw [if_pos (by decide), pfirst_zeroCJ hs hr] at e12
  rw [if_pos (by decide), plater_zeroCJ hs hr] at e13
  have n12 : k ≠ 12 := fun h => by rw [if_pos h.symm] at e12; exact absurd e12 (by decide)
  have n13 : k ≠ 13 := fun h => by rw [if_pos h.symm] at e13; exact absurd e13 (by decide)
  have e14 := val 14 (by decide)
  rw [if_neg (by decide)] at e14
  rcases Nat.lt_or_ge k 12 with hk12 | hk12
  · refine ⟨k, by omega, fun i hi => ?_, ?_⟩
    · have := val i (by unfold NKINDS at hi; omega)
      rw [if_pos hi] at this
      rw [this]
      by_cases e : i = k
      · rw [if_pos e, if_pos ⟨e, hk12⟩]
      · rw [if_neg e, if_neg (fun h => e h.1)]
    · rw [e14, if_neg (by omega), if_neg (by omega)]
  · have hk14 : k = 14 := by omega
    refine ⟨12, by decide, fun i hi => ?_, ?_⟩
    · have := val i (by unfold NKINDS at hi; omega)
      rw [if_pos hi, if_neg (by unfold NKINDS at hi; omega)] at this
      rw [this, if_neg (fun h => absurd h.2 (by decide))]
    · rw [e14, if_pos hk14.symm, if_pos rfl]

end Row

/-- Kind `k`'s selectors and restart selector, as constants. -/
def selSubCJ (k : Nat) : Atom → E
  | .main 0 i =>
    if SEL ≤ i ∧ i < SEL + NKINDS then .const (if i - SEL = k ∧ k < 12 then 1 else 0)
    else if i = RSJ then .const (if k = 12 then 1 else 0) else .atom (.main 0 i)
  | a => .atom a

def actOfCJ (k j : Nat) : Nat := if k = 12 then (if j < 2 then 1 else 0) else if k = 11 then 0 else actOf k j
def tagOfCJ (k j : Nat) : Nat :=
  if k = 12 then (if j = 0 then 1 else if j = 1 then 4 else 0) else if k = 11 then 0 else tagOf k j
def haltOfCJ (k : Nat) : Nat := if 4 ≤ k ∧ k < 11 then 1 else 0
def nextHdOfCJ (k : Nat) : E := if k = 11 ∨ k = 12 then zero else nextHdOf k
def nextStkOfCJ (k : Nat) : E := if k = 11 ∨ k = 12 then zero else nextStkOf k
def nextCtrOfCJ (k : Nat) : E := if k = 11 ∨ k = 12 then col CTR else nextCtrOf k

def kindEqCJ (k : Nat) (e e' : E) : Bool := (e.subst (selSubCJ k)).norm == e'.norm

/-- **The kind table.** -/
def kindOKCJ (k : Nat) : Bool :=
  (List.range 4).all (fun j => kindEqCJ k (acts.getD j zero) (c (actOfCJ k j)) &&
    kindEqCJ k (tagsCJ.getD j zero) (c (tagOfCJ k j))) &&
  kindEqCJ k halt (c (haltOfCJ k)) &&
  kindEqCJ k sApp (c (if k = 0 then 1 else 0)) && kindEqCJ k sS (c (if k = 3 then 1 else 0)) &&
  kindEqCJ k sHK1 (c (if k = 5 then 1 else 0)) && kindEqCJ k sRSJ (c (if k = 12 then 1 else 0)) &&
  kindEqCJ k sInst (c (if k = 11 then 1 else 0)) &&
  kindEqCJ k nextHd (nextHdOfCJ k) && kindEqCJ k nextStk (nextStkOfCJ k) && kindEqCJ k nextCtr (nextCtrOfCJ k)

theorem kindOKCJ_all : (List.range 13).all kindOKCJ = true := by decide

theorem selSubCJ_eval {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindCJ T r k) (a : Atom) :
    (selSubCJ k a).eval (T.env r) = T.env r a := by
  cases a with
  | main o i =>
    cases o with
    | zero =>
      simp only [selSubCJ]
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

theorem kind_evalCJ {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindCJ T r k) {e e' : E}
    (h : kindEqCJ k e e' = true) : e.eval (T.env r) = e'.eval (T.env r) := by
  rw [← E.eval_subst (selSubCJ k) (T.env r) (selSubCJ_eval hr hk) e]
  exact E.eval_eq_of_norm (beq_iff_eq.1 h) _

/-- **A row's kind, evaluated.** -/
theorem kind_factsCJ {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindCJ T r k) :
    (∀ j, j < 4 → (acts.getD j zero).eval (T.env r) = ofN (actOfCJ k j) ∧
      (tagsCJ.getD j zero).eval (T.env r) = ofN (tagOfCJ k j)) ∧
    halt.eval (T.env r) = ofN (haltOfCJ k) ∧
    sApp.eval (T.env r) = ofN (if k = 0 then 1 else 0) ∧ sS.eval (T.env r) = ofN (if k = 3 then 1 else 0) ∧
    sHK1.eval (T.env r) = ofN (if k = 5 then 1 else 0) ∧ sRSJ.eval (T.env r) = ofN (if k = 12 then 1 else 0) ∧
    sInst.eval (T.env r) = ofN (if k = 11 then 1 else 0) ∧
    nextHd.eval (T.env r) = (nextHdOfCJ k).eval (T.env r) ∧
    nextStk.eval (T.env r) = (nextStkOfCJ k).eval (T.env r) ∧
    nextCtr.eval (T.env r) = (nextCtrOfCJ k).eval (T.env r) := by
  have h := List.all_eq_true.1 kindOKCJ_all k (List.mem_range.2 hk.1)
  simp only [kindOKCJ, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hj, hh⟩, ha⟩, hs⟩, hk1⟩, hrs⟩, hin⟩, h1⟩, h2⟩, h3⟩ := h
  exact ⟨fun j hj' => ⟨kind_evalCJ hr hk (hj j hj').1, kind_evalCJ hr hk (hj j hj').2⟩,
    kind_evalCJ hr hk hh, kind_evalCJ hr hk ha, kind_evalCJ hr hk hs, kind_evalCJ hr hk hk1,
    kind_evalCJ hr hk hrs, kind_evalCJ hr hk hin, kind_evalCJ hr hk h1, kind_evalCJ hr hk h2, kind_evalCJ hr hk h3⟩

/-- A row of kind `k` has kind `k`'s jet selectors: `SelsAre` for an
    instantiation and the machine's kinds. -/
theorem IsKindCJ.sels {T : Table} {r k : Nat} (hk : IsKindCJ T r k) (hk12 : k < 12) : SelsAre T r k := by
  intro i hi
  rw [hk.2.1 i hi]
  by_cases e : i = k
  · rw [if_pos ⟨e, hk12⟩, if_pos e]
  · rw [if_neg (fun h => e h.1), if_neg e]

end Circuit
