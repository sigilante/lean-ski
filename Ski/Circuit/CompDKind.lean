import Ski.Circuit.CompDRow
import Ski.Circuit.CompKind

/-!
# One CPU row of the circuit with the `dec` jet: its kind

Thirteen kinds: the composed CPU's twelve (`Ski/Circuit/CompKind.lean`),
and the jet's (`12`), which reads the atom `J` at the head and one stack
cell.  Each kind's expressions are checked by substitution and normal
forms (`kindOKD_all`), as `Ski/Circuit/CompPKind.lean` checks the
Poseidon2 CPU's.
-/

namespace Circuit

open B

/-- **A row of kind `k`**: its selectors, restart selector and jet selector. -/
def IsKindD (T : Table) (r k : Nat) : Prop :=
  k < 13 ∧ (∀ i, i < NKINDS → T.main r (SEL + i) = if i = k ∧ k < 11 then 1 else 0) ∧
    T.main r RS = (if k = 11 then 1 else 0) ∧ T.main r DECSEL = if k = 12 then 1 else 0

section Row

variable {hd0 stk0 ctr0 n nilA J : Nat} {T : Table}
  (hs : Sat (cpuAirDec hd0 stk0 ctr0 n nilA J) T) {r : Nat} (hr : r < T.h)
include hs hr

/-- **The row's kind**: one of the machine's eleven, a restart, or the jet's. -/
theorem kind_ofD : ∃ k, IsKindD T r k := by
  let xs := (List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RS, T.main r DECSEL]
  have hb : ∀ x ∈ xs, x.val ≤ 1 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      rcases val_of_bit (sel_bitD hs hr (List.mem_range.1 hi)) with h | h <;> omega
    · rcases List.mem_cons.1 hx with hx | hx
      · rw [hx]; rcases val_of_bit (rs_bitD hs hr) with h | h <;> omega
      · rw [List.mem_singleton.1 hx]; rcases val_of_bit (dec_bitD hs hr) with h | h <;> omega
  obtain ⟨hv, _⟩ := sum_bits_val xs hb (by simp [xs, NKINDS, P])
  have hsum := sel_sumD hs hr
  rw [show ((List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RS, T.main r DECSEL]) = xs from rfl,
    Fin.ext_iff, hv] at hsum
  obtain ⟨k, hk, h1, h0⟩ := onehot (xs.map Fin.val) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hb x hx) hsum
  have hlen : (xs.map Fin.val).length = 16 := by simp [xs, NKINDS]
  have get : ∀ i, i < 16 → (xs.map Fin.val).getD i 0 =
      (if i < NKINDS then T.main r (SEL + i) else if i = NKINDS then T.main r RS else T.main r DECSEL).val := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
    simp only [xs, List.getElem_map, Option.getD_some]
    rcases Nat.lt_or_ge i NKINDS with h | h
    · rw [if_pos h, List.getElem_append_left (by simp; exact h)]; simp
    · rw [if_neg (by omega), List.getElem_append_right (by simp; omega)]
      have hl : ((List.range NKINDS).map fun i => T.main r (SEL + i)).length = NKINDS := by simp
      rcases (show i = NKINDS ∨ i = NKINDS + 1 by unfold NKINDS at h ⊢; omega) with e | e
      · rw [if_pos e]; simp only [hl, e, Nat.sub_self]; rfl
      · rw [if_neg (by omega)]; simp only [hl, e, Nat.add_sub_cancel_left]; rfl
  rw [hlen] at hk
  have val : ∀ i, i < 16 →
      (if i < NKINDS then T.main r (SEL + i) else if i = NKINDS then T.main r RS else T.main r DECSEL) =
      if i = k then 1 else 0 := by
    intro i hi
    apply Fin.ext
    by_cases hik : i = k
    · rw [if_pos hik]; subst hik; rw [← get i hi, h1]; rfl
    · rw [if_neg hik, ← get i hi, h0 i (by rw [hlen]; exact hi) hik]; rfl
  have e11 := val 11 (by decide)
  have e12 := val 12 (by decide)
  have e13 := val 13 (by decide)
  rw [if_pos (by decide), inst_zeroD hs hr] at e11
  rw [if_pos (by decide), pfirst_zeroD hs hr] at e12
  rw [if_pos (by decide), plater_zeroD hs hr] at e13
  have n11 : k ≠ 11 := fun h => by rw [if_pos h.symm] at e11; exact absurd e11 (by decide)
  have n12 : k ≠ 12 := fun h => by rw [if_pos h.symm] at e12; exact absurd e12 (by decide)
  have n13 : k ≠ 13 := fun h => by rw [if_pos h.symm] at e13; exact absurd e13 (by decide)
  have e14 := val 14 (by decide)
  rw [if_neg (by decide), if_pos (by decide)] at e14
  have e15 := val 15 (by decide)
  rw [if_neg (by decide), if_neg (by decide)] at e15
  rcases Nat.lt_or_ge k 11 with hk11 | hk11
  · refine ⟨k, by omega, fun i hi => ?_, ?_, ?_⟩
    · have := val i (by unfold NKINDS at hi; omega)
      rw [if_pos hi] at this
      rw [this]
      by_cases e : i = k
      · rw [if_pos e, if_pos ⟨e, hk11⟩]
      · rw [if_neg e, if_neg (fun h => e h.1)]
    · rw [e14, if_neg (by omega), if_neg (by omega)]
    · rw [e15, if_neg (by omega), if_neg (by omega)]
  · rcases (show k = 14 ∨ k = 15 by omega) with hk14 | hk15
    · refine ⟨11, by decide, fun i hi => ?_, ?_, ?_⟩
      · have := val i (by unfold NKINDS at hi; omega)
        rw [if_pos hi, if_neg (by unfold NKINDS at hi; omega)] at this
        rw [this, if_neg (fun h => absurd h.2 (by decide))]
      · rw [e14, if_pos hk14.symm, if_pos rfl]
      · rw [e15, if_neg (by omega), if_neg (by decide)]
    · refine ⟨12, by decide, fun i hi => ?_, ?_, ?_⟩
      · have := val i (by unfold NKINDS at hi; omega)
        rw [if_pos hi, if_neg (by unfold NKINDS at hi; omega)] at this
        rw [this, if_neg (fun h => absurd h.2 (by decide))]
      · rw [e14, if_neg (by omega), if_neg (by decide)]
      · rw [e15, if_pos hk15.symm, if_pos rfl]

end Row

/-- Kind `k`'s selectors, restart selector and jet selector, as constants. -/
def selSubD (k : Nat) : Atom → E
  | .main 0 i =>
    if SEL ≤ i ∧ i < SEL + NKINDS then .const (if i - SEL = k ∧ k < 11 then 1 else 0)
    else if i = RS then .const (if k = 11 then 1 else 0)
    else if i = DECSEL then .const (if k = 12 then 1 else 0) else .atom (.main 0 i)
  | a => .atom a

def actOfD (k j : Nat) : Nat := if k = 12 then (if j < 2 then 1 else 0) else actOfC k j
def tagOfD (k j : Nat) : Nat :=
  if k = 12 then (if j = 0 then 6 else if j = 1 then 5 else 0) else tagOfC k j
def nextHdOfD (k : Nat) : E := if k = 12 then zero else nextHdOfC k
def nextStkOfD (k : Nat) : E := if k = 12 then zero else nextStkOfC k
def nextCtrOfD (k : Nat) : E := if k = 12 then col CTR else nextCtrOfC k

def kindEqD (k : Nat) (e e' : E) : Bool := (e.subst (selSubD k)).norm == e'.norm

/-- **The kind table with the `dec` jet.** -/
def kindOKD (k : Nat) : Bool :=
  (List.range 4).all (fun j => kindEqD k (acts.getD j zero) (c (actOfD k j)) &&
    kindEqD k (tagsD.getD j zero) (c (tagOfD k j))) &&
  kindEqD k halt (c (haltOfC k)) &&
  kindEqD k sApp (c (if k = 0 then 1 else 0)) && kindEqD k sS (c (if k = 3 then 1 else 0)) &&
  kindEqD k sHK1 (c (if k = 5 then 1 else 0)) && kindEqD k sRS (c (if k = 11 then 1 else 0)) &&
  kindEqD k sDec (c (if k = 12 then 1 else 0)) &&
  kindEqD k nextHd (nextHdOfD k) && kindEqD k nextStk (nextStkOfD k) && kindEqD k nextCtr (nextCtrOfD k)

theorem kindOKD_all : (List.range 13).all kindOKD = true := by decide

theorem selSubD_eval {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindD T r k) (a : Atom) :
    (selSubD k a).eval (T.env r) = T.env r a := by
  cases a with
  | main o i =>
    cases o with
    | zero =>
      simp only [selSubD]
      split
      · next h =>
        rw [env_main0 hr]
        have e := hk.2.1 (i - SEL) (Nat.sub_lt_left_of_lt_add h.1 h.2)
        rw [Nat.add_sub_cancel' h.1] at e
        rw [e]; rfl
      · split
        · next h => subst h; rw [env_main0 hr, hk.2.2.1]; rfl
        · split
          · next h => subst h; rw [env_main0 hr, hk.2.2.2]; rfl
          · rfl
    | succ o => rfl
  | pre _ _ => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

theorem kind_evalD {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindD T r k) {e e' : E}
    (h : kindEqD k e e' = true) : e.eval (T.env r) = e'.eval (T.env r) := by
  rw [← E.eval_subst (selSubD k) (T.env r) (selSubD_eval hr hk) e]
  exact E.eval_eq_of_norm (beq_iff_eq.1 h) _

/-- **A row's kind, evaluated.** -/
theorem kind_factsD {T : Table} {r k : Nat} (hr : r < T.h) (hk : IsKindD T r k) :
    (∀ j, j < 4 → (acts.getD j zero).eval (T.env r) = ofN (actOfD k j) ∧
      (tagsD.getD j zero).eval (T.env r) = ofN (tagOfD k j)) ∧
    halt.eval (T.env r) = ofN (haltOfC k) ∧
    sApp.eval (T.env r) = ofN (if k = 0 then 1 else 0) ∧ sS.eval (T.env r) = ofN (if k = 3 then 1 else 0) ∧
    sHK1.eval (T.env r) = ofN (if k = 5 then 1 else 0) ∧ sRS.eval (T.env r) = ofN (if k = 11 then 1 else 0) ∧
    sDec.eval (T.env r) = ofN (if k = 12 then 1 else 0) ∧
    nextHd.eval (T.env r) = (nextHdOfD k).eval (T.env r) ∧
    nextStk.eval (T.env r) = (nextStkOfD k).eval (T.env r) ∧
    nextCtr.eval (T.env r) = (nextCtrOfD k).eval (T.env r) := by
  have h := List.all_eq_true.1 kindOKD_all k (List.mem_range.2 hk.1)
  simp only [kindOKD, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hj, hh⟩, ha⟩, hs⟩, hk1⟩, hrs⟩, hp2⟩, h1⟩, h2⟩, h3⟩ := h
  exact ⟨fun j hj' => ⟨kind_evalD hr hk (hj j hj').1, kind_evalD hr hk (hj j hj').2⟩,
    kind_evalD hr hk hh, kind_evalD hr hk ha, kind_evalD hr hk hs, kind_evalD hr hk hk1,
    kind_evalD hr hk hrs, kind_evalD hr hk hp2, kind_evalD hr hk h1, kind_evalD hr hk h2, kind_evalD hr hk h3⟩

end Circuit
