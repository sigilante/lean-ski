import Ski.Circuit.BaseTrace

/-!
# The honest CPU table

For a run the Lean AIR accepts (`Accepts M t k row`), the CPU table the
prover builds (`cpuTable`): each row's registers, its kind's selector, the
fields of the cells its reads find, and the bits of its range checks.
**`cpu_sat`**: it satisfies every constraint of the CPU AIR, provided the
counters stay within the range checks' `2^24`.
-/

namespace Circuit

open B Air

theorem ofN_add (a b : Nat) : ofN (a + b) = ofN a + ofN b := by
  apply Fin.ext
  rw [Fin.val_add]
  show (a + b) % P = (a % P + b % P) % P
  exact Nat.add_mod a b P

theorem ofN_mul (a b : Nat) : ofN (a * b) = ofN a * ofN b := by
  apply Fin.ext
  rw [Fin.val_mul]
  show (a * b) % P = (a % P * (b % P)) % P
  exact Nat.mul_mod a b P

theorem sub_self' (x : F) : x - x = 0 := by
  rw [sub_eq_add_neg', add_comm', neg_add_cancel']

/-- `x + y + 1 - y - 1 - x = 0`, by normal forms. -/
theorem range_identity (x y : F) : x + y + 1 - y - 1 - x = 0 :=
  E.eval_eq_of_norm
    (e := .sub (.sub (.sub (.add (.add (.atom (.main 0 0)) (.atom (.main 0 1))) (.const 1)) (.atom (.main 0 1)))
      (.const 1)) (.atom (.main 0 0)))
    (e' := .const 0) (by decide)
    (fun | .main 0 0 => x | .main 0 1 => y | _ => 0)

/-- A number's low `m + 1` bits: its low `m` bits and bit `m`. -/
theorem mod_two_pow_succ (n m : Nat) : n % 2 ^ (m + 1) = n % 2 ^ m + 2 ^ m * ((n / 2 ^ m) % 2) := by
  have h1 := Nat.div_add_mod n (2 ^ m)
  have h2 := Nat.div_add_mod (n / 2 ^ m) 2
  have hlt := Nat.mod_lt n (Nat.two_pow_pos m)
  have hq := Nat.mod_two_eq_zero_or_one (n / 2 ^ m)
  generalize n / 2 ^ m = q at *
  generalize n % 2 ^ m = rr at *
  have e : n = (rr + 2 ^ m * (q % 2)) + 2 ^ (m + 1) * (q / 2) := by
    rw [Nat.pow_succ, Nat.mul_assoc, ← h1]
    conv => lhs; rw [← h2]
    rw [Nat.mul_add]
    generalize 2 ^ m * (q % 2) = A
    generalize 2 ^ m * (2 * (q / 2)) = B
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  rw [Nat.pow_succ]
  rcases hq with h | h <;> rw [h] <;> omega

/-- A read's range value: the gap below the counter, when active. -/
def rangeValue (M : List Cell) (r : Row) (j : Nat) : Nat :=
  if actOf (kindOf M r) j = 1 then r.ctr - addrAt M r j - 1 else 0

/-- **The honest CPU row.** -/
def cpuCol (M : List Cell) (r : Row) (col : Nat) : F :=
  if col = HD then ofN r.hd
  else if col = STK then ofN r.stk
  else if col = CTR then ofN r.ctr
  else if col < FLD then (if col - SEL = kindOf M r then 1 else 0)
  else if col < BITS then
    (if (col - FLD) % 2 = 0 then ofN (fieldsAt M r ((col - FLD) / 2)).1 else ofN (fieldsAt M r ((col - FLD) / 2)).2)
  else ofN ((rangeValue M r ((col - BITS) / RANGE_BITS) / 2 ^ ((col - BITS) % RANGE_BITS)) % 2)

def cpuTable (M : List Cell) (row : Nat → Row) (k : Nat) : Table :=
  ⟨k, fun i col => cpuCol M (row i) col, fun _ _ => 0⟩

theorem cpuCol_hd (M : List Cell) (r : Row) : cpuCol M r HD = ofN r.hd := rfl
theorem cpuCol_stk (M : List Cell) (r : Row) : cpuCol M r STK = ofN r.stk := rfl
theorem cpuCol_ctr (M : List Cell) (r : Row) : cpuCol M r CTR = ofN r.ctr := rfl

theorem cpuCol_sel (M : List Cell) (r : Row) {i : Nat} (hi : i < NKINDS) :
    cpuCol M r (SEL + i) = if i = kindOf M r then 1 else 0 := by
  unfold cpuCol
  have e : SEL + i - SEL = i := Nat.add_sub_cancel_left SEL i
  rw [if_neg (by unfold HD SEL; omega), if_neg (by unfold STK SEL; omega), if_neg (by unfold CTR SEL; omega),
    if_pos (by unfold FLD; omega), e]

theorem cpuCol_fld (M : List Cell) (r : Row) {i : Nat} (hi : i < 8) :
    cpuCol M r (FLD + i) =
      if i % 2 = 0 then ofN (fieldsAt M r (i / 2)).1 else ofN (fieldsAt M r (i / 2)).2 := by
  unfold cpuCol
  have e : FLD + i - FLD = i := Nat.add_sub_cancel_left FLD i
  rw [if_neg (by unfold HD FLD SEL NKINDS; omega), if_neg (by unfold STK FLD SEL NKINDS; omega),
    if_neg (by unfold CTR FLD SEL NKINDS; omega), if_neg (by omega), if_pos (by unfold BITS; omega), e]

theorem cpuCol_bit (M : List Cell) (r : Row) {j i : Nat} (hj : j < 4) (hi : i < RANGE_BITS) :
    cpuCol M r (BITS + j * RANGE_BITS + i) = ofN ((rangeValue M r j / 2 ^ i) % 2) := by
  unfold cpuCol
  have e : BITS + j * RANGE_BITS + i - BITS = j * RANGE_BITS + i := by omega
  have e1 : (j * RANGE_BITS + i) / RANGE_BITS = j := by unfold RANGE_BITS at *; omega
  have e2 : (j * RANGE_BITS + i) % RANGE_BITS = i := by unfold RANGE_BITS at *; omega
  rw [if_neg (by unfold HD BITS FLD SEL NKINDS; omega), if_neg (by unfold STK BITS FLD SEL NKINDS; omega),
    if_neg (by unfold CTR BITS FLD SEL NKINDS; omega), if_neg (by unfold BITS; omega),
    if_neg (by omega), e, e1, e2]

/-- The kind selectors of every kind sum to one. -/
theorem kindSum_all :
    (List.range 11).all (fun k => kindEq k (sum ((List.range NKINDS).map fun i => col (SEL + i))) one) = true := by
  decide

/-- A range check's bits reassemble its value, below `2^24`. -/
theorem rangeVal_bits {T : Table} {r j n : Nat} (hr : r < T.h)
    (hb : ∀ i, i < RANGE_BITS → T.main r (BITS + j * RANGE_BITS + i) = ofN ((n / 2 ^ i) % 2)) (hn : n < 2 ^ 24) :
    (rangeVal j).eval (T.env r) = ofN n := by
  have step : ∀ m, m ≤ RANGE_BITS →
      ((List.range m).foldl (fun v i => E.add v (E.mul (col (BITS + j * RANGE_BITS + i)) (c (2 ^ i)))) zero).eval
        (T.env r) = ofN (n % 2 ^ m) := by
    intro m
    induction m with
    | zero => intro _; show ofN 0 = ofN (n % 1); rw [Nat.mod_one]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      show E.eval (T.env r) (List.foldl _ zero (List.range m)) +
        T.env r (.main 0 (BITS + j * RANGE_BITS + m)) * ofN (2 ^ m) = _
      rw [ih (Nat.le_of_succ_le hm), env_main0 hr, hb m hm, ← ofN_mul, ← ofN_add, mod_two_pow_succ,
        Nat.mul_comm]
  unfold rangeVal
  rw [step RANGE_BITS (Nat.le_refl _), Nat.mod_eq_of_lt (show n < 2 ^ RANGE_BITS from hn)]

section

variable {M : List Cell} {row : Nat → Row} {k : Nat}
  (hv : ∀ i, i < k → Valid M (row i))
  (htr : ∀ i, i + 1 < k → stepRow M (row i) = some (row (i + 1)) ∨ (haltRow M (row i) = true ∧ row (i + 1) = row i))
  (hfin : haltRow M (row (k - 1)) = true)
  (hb : ∀ i, i < k → (row i).ctr ≤ 2 ^ 24)

theorem cpu_env {i : Nat} (hi : i < k) (col : Nat) :
    (B.col col).eval ((cpuTable M row k).env i) = cpuCol M (row i) col := by
  show (cpuTable M row k).main ((i + 0) % k) col = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]; rfl

theorem cpu_kind {i : Nat} (hi : i < k) (hS : Shape M (row i) (kindOf M (row i))) :
    IsKind (cpuTable M row k) i (kindOf M (row i)) :=
  ⟨hS.lt, fun j hj => by
    show cpuCol M (row i) (SEL + j) = _
    rw [cpuCol_sel M (row i) hj]⟩

include hv in
/-- The next row's registers are what the kind computes, for a row that
    steps to the next or has halted and repeats. -/
theorem cpu_next {i : Nat} (hi1 : i + 1 < k)
    (hti : stepRow M (row i) = some (row (i + 1)) ∨ (haltRow M (row i) = true ∧ row (i + 1) = row i)) :
    ofN (row (i + 1)).hd = (nextHdOf (kindOf M (row i))).eval ((cpuTable M row k).env i) ∧
    ofN (row (i + 1)).stk = (nextStkOf (kindOf M (row i))).eval ((cpuTable M row k).env i) ∧
    ofN (row (i + 1)).ctr = (nextCtrOf (kindOf M (row i))).eval ((cpuTable M row k).env i) := by
  have hi : i < k := Nat.lt_of_succ_lt hi1
  have hS := shape (hv i hi)
  have cv := cpu_env (M := M) (row := row) hi
  generalize hK : kindOf M (row i) = K at hS
  rcases Nat.lt_or_ge K 4 with h4 | h4
  · have hstep : stepRow M (row i) = some (row (i + 1)) := by
      rcases hti with h | h
      · exact h
      · rw [hS.step h4] at h; cases h.1
    rcases (show K = 0 ∨ K = 1 ∨ K = 2 ∨ K = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [(hS.app rfl).2] at hstep
      rw [← Option.some.inj hstep]
      refine ⟨?_, ?_, ?_⟩
      · show _ = (fld 0).eval _; rw [fld, cv, cpuCol_fld M _ (by decide)]; rfl
      · show _ = (col CTR).eval _; rw [cv]; rfl
      · show _ = (E.add (col CTR) one).eval _
        simp only [E.eval, cv, cpuCol_ctr, B.one, B.c, ← ofN_add]
    · rw [hS.i rfl] at hstep
      rw [← Option.some.inj hstep]
      refine ⟨?_, ?_, ?_⟩
      · show _ = (fld 2).eval _; rw [fld, cv, cpuCol_fld M _ (by decide)]; rfl
      · show _ = (fld 3).eval _; rw [fld, cv, cpuCol_fld M _ (by decide)]; rfl
      · show _ = (col CTR).eval _; rw [cv]; rfl
    · rw [hS.k2 rfl] at hstep
      rw [← Option.some.inj hstep]
      refine ⟨?_, ?_, ?_⟩
      · show _ = (fld 2).eval _; rw [fld, cv, cpuCol_fld M _ (by decide)]; rfl
      · show _ = (fld 5).eval _; rw [fld, cv, cpuCol_fld M _ (by decide)]; rfl
      · show _ = (col CTR).eval _; rw [cv]; rfl
    · rw [(hS.s rfl).2.2.2] at hstep
      rw [← Option.some.inj hstep]
      refine ⟨?_, ?_, ?_⟩
      · show _ = (fld 2).eval _; rw [fld, cv, cpuCol_fld M _ (by decide)]; rfl
      · show _ = (E.add (col CTR) (c 2)).eval _
        simp only [E.eval, cv, cpuCol_ctr, B.c, ← ofN_add]
      · show _ = (E.add (col CTR) (c 3)).eval _
        simp only [E.eval, cv, cpuCol_ctr, B.c, ← ofN_add]
  · have hrep : row (i + 1) = row i := by
      rcases hti with h | h
      · rw [hS.none h4] at h; cases h
      · exact h.2
    rw [nextHdOf_halt h4, nextStkOf_halt h4, nextCtrOf_halt h4, cv, cv, cv, hrep]
    exact ⟨rfl, rfl, rfl⟩

theorem actOf_le (k j : Nat) : actOf k j ≤ 1 := by
  unfold actOf; split <;> (try split) <;> decide

theorem cpu_addr {i : Nat} (hi : i < k) {j : Nat} (hj : j < 4) :
    (addrs.getD j zero).eval ((cpuTable M row k).env i) = ofN (addrAt M (row i) j) := by
  have cv := cpu_env (M := M) (row := row) hi
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · show (col HD).eval _ = _; rw [cv]; rfl
  · show (col STK).eval _ = _; rw [cv]; rfl
  · show (col (FLD + 3)).eval _ = _; rw [cv, cpuCol_fld M _ (by decide)]; rfl
  · show (col (FLD + 5)).eval _ = _; rw [cv, cpuCol_fld M _ (by decide)]; rfl

include hv hb in
/-- A read's constraints: its bits are bits, and its range check holds. -/
theorem cpu_read {i : Nat} (hi : i < k) {j : Nat} (hj : j < 4) :
    ∀ e ∈ readCons j, e.eval ((cpuTable M row k).env i) = 0 := by
  have hS := shape (hv i hi)
  have hK := cpu_kind hi hS
  obtain ⟨hf, _⟩ := kind_facts hi hK
  have cv := cpu_env (M := M) (row := row) hi
  intro e he
  unfold readCons at he
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
  rcases he with ⟨b, hb', rfl⟩ | rfl
  · simp only [B.bool, E.eval, cv, cpuCol_bit M _ hj hb', B.one, B.c, ofN_one]
    rcases Nat.mod_two_eq_zero_or_one (rangeValue M (row i) j / 2 ^ b) with h | h <;> rw [h] <;> decide
  · simp only [E.eval, (hf j hj).1]
    rcases Nat.lt_or_ge (actOf (kindOf M (row i)) j) 1 with h0 | h1
    · rw [show actOf (kindOf M (row i)) j = 0 by omega, ofN_zero, zero_mul']
    · have ha : actOf (kindOf M (row i)) j = 1 := Nat.le_antisymm (actOf_le _ _) h1
      obtain ⟨cell, hrd, _⟩ := hS.reads j hj ha
      have hlt : addrAt M (row i) j < (row i).ctr := by
        unfold rd at hrd
        split at hrd
        · assumption
        · cases hrd
      have hrv : rangeValue M (row i) j = (row i).ctr - addrAt M (row i) j - 1 := by
        unfold rangeValue; rw [if_pos ha]
      have hbound := hb i hi
      have hr := rangeVal_bits (T := cpuTable M row k) (r := i) (j := j) (n := rangeValue M (row i) j) hi
        (fun b hb' => cpuCol_bit M (row i) hj hb') (by rw [hrv]; omega)
      rw [hr, hrv, cpu_addr hi hj, cv, cpuCol_ctr, ha, B.one, B.c]
      show ofN 1 * (_ - _ - ofN 1 - _) = 0
      have e : (row i).ctr = ((row i).ctr - addrAt M (row i) j - 1) + addrAt M (row i) j + 1 := by omega
      have e' : ofN (row i).ctr =
          ofN ((row i).ctr - addrAt M (row i) j - 1) + ofN (addrAt M (row i) j) + ofN 1 := by
        rw [← ofN_add, ← ofN_add]; exact congrArg ofN e
      rw [e', ofN_one, one_mul']
      exact range_identity _ _

/-- A transition constraint, from the next row's register. -/
theorem cpu_trans {i : Nat} (hi : i < k) {reg : Nat} {pr : Row → Nat} {nextE targ : E}
    (hreg : ∀ r, cpuCol M r reg = ofN (pr r))
    (hn : i + 1 < k → ofN (pr (row (i + 1))) = targ.eval ((cpuTable M row k).env i))
    (hf : nextE.eval ((cpuTable M row k).env i) = targ.eval ((cpuTable M row k).env i)) :
    (whenTrans (B.eq (nxt reg) nextE)).eval ((cpuTable M row k).env i) = 0 := by
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
  split
  · exact zero_mul' _
  · next hne =>
    have hne' : ¬ (i + 1 = k) := hne
    have hi1 : i + 1 < k := by omega
    show 1 * (cpuCol M (row ((i + 1) % k)) reg - _) = 0
    rw [Nat.mod_eq_of_lt hi1, one_mul', hreg, hn hi1, hf]
    exact sub_self' _

/-- A first-row constraint, from the first row's register. -/
theorem cpu_first {i : Nat} (hi : i < k) {reg v : Nat} (h : i = 0 → cpuCol M (row i) reg = ofN v) :
    (whenFirst (B.eq (col reg) (c v))).eval ((cpuTable M row k).env i) = 0 := by
  simp only [B.whenFirst, B.eq, B.c, E.eval, env_first, cpu_env hi]
  split
  · next h0 => rw [h h0, sub_self', mul_zero']
  · exact zero_mul' _

include hv htr hfin hb in
/-- **The honest CPU table satisfies the CPU AIR.** -/
theorem cpu_sat (hk0 : 0 < k) : Sat (cpuAir (row 0).hd (row 0).stk (row 0).ctr) (cpuTable M row k) := by
  refine ⟨hk0, fun e he i (hi : i < k) => ?_⟩
  have hS := shape (hv i hi)
  have hK := cpu_kind hi hS
  obtain ⟨_, hhalt, _⟩ := kind_facts hi hK
  have cv := cpu_env (M := M) (row := row) hi
  have hk11 := hS.lt
  simp only [cpuAir, cpuCons, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at he
  rcases he with (((((⟨j, hj, rfl⟩ | rfl) | he) | he) | he) | he) | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · simp only [B.bool, E.eval, cv, cpuCol_sel M _ hj, B.one, B.c, ofN_one]
    split <;> decide
  · have hsum := kind_eval hi hK (List.all_eq_true.1 kindSum_all _ (List.mem_range.2 hk11))
    simp only [B.eq, E.eval]
    rw [hsum]; exact sub_self' _
  · exact cpu_read hv hb hi (by decide) _ he
  · exact cpu_read hv hb hi (by decide) _ he
  · exact cpu_read hv hb hi (by decide) _ he
  · exact cpu_read hv hb hi (by decide) _ he
  · show (col (SEL + 11)).eval _ = 0; rw [cv, cpuCol_sel M _ (by decide), if_neg (by omega)]
  · show (col (SEL + 12)).eval _ = 0; rw [cv, cpuCol_sel M _ (by decide), if_neg (by omega)]
  · show (col (SEL + 13)).eval _ = 0; rw [cv, cpuCol_sel M _ (by decide), if_neg (by omega)]
  · exact cpu_trans hi (pr := Row.hd) (fun _ => rfl) (fun hi1 => (cpu_next hv hi1 (htr i hi1)).1) (kind_facts hi hK).2.2.2.2.1
  · exact cpu_trans hi (pr := Row.stk) (fun _ => rfl) (fun hi1 => (cpu_next hv hi1 (htr i hi1)).2.1)
      (kind_facts hi hK).2.2.2.2.2.1
  · exact cpu_trans hi (pr := Row.ctr) (fun _ => rfl) (fun hi1 => (cpu_next hv hi1 (htr i hi1)).2.2)
      (kind_facts hi hK).2.2.2.2.2.2
  · exact cpu_first hi (fun h0 => by subst h0; rfl)
  · exact cpu_first hi (fun h0 => by subst h0; rfl)
  · exact cpu_first hi (fun h0 => by subst h0; rfl)
  · simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = k := hl
      have hi' : i = k - 1 := by omega
      have h4 : 4 ≤ kindOf M (row i) := by
        rcases Nat.lt_or_ge (kindOf M (row i)) 4 with h | h
        · have := hS.step h; rw [hi', hfin] at this; cases this
        · exact h
      rw [hhalt, if_pos h4]
      show 1 * (ofN 1 - ofN 1) = 0
      rw [sub_self', mul_zero']
    · exact zero_mul' _

end

end Circuit
