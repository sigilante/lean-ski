import Ski.Circuit.Base

/-!
# One CPU row's constraints, as equations

A table that satisfies the CPU AIR (`Sat (cpuAir …) T`) satisfies, at each
row, the equations of `CpuEqs`: over BabyBear, in the row's own values.
This file only unfolds the constraint list (`cpu_eqs`); the reasoning is
in `Ski/Circuit/BaseSound.lean`.
-/

namespace Circuit

open B

theorem env_main0 {T : Table} {r i : Nat} (hr : r < T.h) : T.env r (.main 0 i) = T.main r i := by
  simp [Table.env, Nat.mod_eq_of_lt hr]

theorem Sat.cons {A : AirD} {T : Table} (h : Sat A T) {c : E} (hc : c ∈ A.cons) {r : Nat} (hr : r < T.h) :
    c.eval (T.env r) = 0 := h.2 c hc r hr

/-- The sum of a list, folded as `B.sum` folds it. -/
theorem eval_sum (ρ : Atom → F) : ∀ (xs : List E) (acc : E),
    (xs.foldl .add acc).eval ρ = acc.eval ρ + (xs.map fun e => e.eval ρ).foldr (· + ·) 0
  | [], acc => by simp [add_zero']
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons, List.foldr_cons]
    rw [eval_sum ρ xs (.add acc x)]
    show acc.eval ρ + x.eval ρ + _ = _
    rw [add_assoc']

theorem env_main1 {T : Table} {r i : Nat} : T.env r (.main 1 i) = T.main ((r + 1) % T.h) i := rfl
theorem env_first {T : Table} {r : Nat} : T.env r .first = if r = 0 then 1 else 0 := rfl
theorem env_last {T : Table} {r : Nat} : T.env r .last = if r + 1 = T.h then 1 else 0 := rfl
theorem env_trans {T : Table} {r : Nat} : T.env r .trans = if r + 1 = T.h then 0 else 1 := rfl

/-- **Row `r` satisfies the CPU's constraints**: what the lemmas below use
    of `Sat`, one row at a time, so a CPU with more kinds can reuse them on
    its corpus rows. -/
def RowSat (hd0 stk0 ctr0 : Nat) (T : Table) (r : Nat) : Prop :=
  ∀ c ∈ cpuCons hd0 stk0 ctr0, c.eval (T.env r) = 0

theorem Sat.row {hd0 stk0 ctr0 : Nat} {T : Table} (hs : Sat (cpuAir hd0 stk0 ctr0) T) {r : Nat} (hr : r < T.h) :
    RowSat hd0 stk0 ctr0 T r := fun _ hc => hs.2 _ hc r hr

section Row

variable {hd0 stk0 ctr0 : Nat} {T : Table} {r : Nat} (hs : RowSat hd0 stk0 ctr0 T r) (hr : r < T.h)
include hs hr

theorem mem_cpuCons {c : E} (h : c ∈ cpuCons hd0 stk0 ctr0) : c.eval (T.env r) = 0 :=
  hs c h

/-- The kind selectors are bits. -/
theorem sel_bit {i : Nat} (hi : i < NKINDS) :
    T.main r (SEL + i) * (T.main r (SEL + i) - 1) = 0 := by
  have := mem_cpuCons hs hr (c := bool (col (SEL + i)))
    (by unfold cpuCons; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))))))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- The kind selectors sum to one. -/
theorem sel_sum :
    ((List.range NKINDS).map fun i => T.main r (SEL + i)).foldr (· + ·) 0 = 1 := by
  have := mem_cpuCons hs hr (c := B.eq (B.sum ((List.range NKINDS).map fun i => B.col (SEL + i))) B.one)
    (by unfold cpuCons; simp)
  simp only [B.eq, E.eval, B.sum] at this
  rw [eval_sum] at this
  have e := sub_eq_zero this
  simp only [B.zero, B.c, B.one, E.eval, ofN_zero, ofN_one, zero_add', List.map_map] at e
  rw [← e]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [B.col, E.eval, env_main0 hr]

/-- The range checks' bits are bits. -/
theorem range_bit {j i : Nat} (hj : j < 4) (hi : i < RANGE_BITS) :
    T.main r (BITS + j * RANGE_BITS + i) * (T.main r (BITS + j * RANGE_BITS + i) - 1) = 0 := by
  have hm : B.bool (B.col (BITS + j * RANGE_BITS + i)) ∈ readCons j :=
    List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  have := mem_cpuCons hs hr (c := B.bool (B.col (BITS + j * RANGE_BITS + i))) (by
    unfold cpuCons
    simp only [List.mem_append]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact .inl (.inl (.inl (.inl (.inr hm))))
    · exact .inl (.inl (.inl (.inr hm)))
    · exact .inl (.inl (.inr hm))
    · exact .inl (.inr hm))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- A read's range equation. -/
theorem range_eq {j : Nat} (hj : j < 4) :
    (acts.getD j B.zero).eval (T.env r) *
      (T.main r CTR - (addrs.getD j B.zero).eval (T.env r) - 1 - (rangeVal j).eval (T.env r)) = 0 := by
  have hm : E.mul (acts.getD j B.zero) (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one) (rangeVal j))
      ∈ readCons j := List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hmem : E.mul (acts.getD j B.zero) (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one)
      (rangeVal j)) ∈ cpuCons hd0 stk0 ctr0 := by
    unfold cpuCons
    simp only [List.mem_append]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact .inl (.inl (.inl (.inl (.inr hm))))
    · exact .inl (.inl (.inl (.inr hm)))
    · exact .inl (.inl (.inr hm))
    · exact .inl (.inr hm)
  have := mem_cpuCons hs hr hmem
  simpa [E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem inst_zero : T.main r (SEL + 11) = 0 := by
  have := mem_cpuCons hs hr (c := sInst) (by unfold cpuCons; simp)
  simpa [E.eval, sInst, B.col, env_main0 hr] using this

theorem pfirst_zero : T.main r (SEL + 12) = 0 := by
  have := mem_cpuCons hs hr (c := sPFirst) (by unfold cpuCons; simp)
  simpa [E.eval, sPFirst, B.col, env_main0 hr] using this

theorem plater_zero : T.main r (SEL + 13) = 0 := by
  have := mem_cpuCons hs hr (c := sPLater) (by unfold cpuCons; simp)
  simpa [E.eval, sPLater, B.col, env_main0 hr] using this

/-- The transitions: the next row's registers. -/
theorem next_regs (hn : r + 1 < T.h) :
    T.main (r + 1) HD = nextHd.eval (T.env r) ∧ T.main (r + 1) STK = nextStk.eval (T.env r) ∧
      T.main (r + 1) CTR = nextCtr.eval (T.env r) := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h1 := mem_cpuCons hs hr (c := B.whenTrans (B.eq (B.nxt HD) nextHd)) (by unfold cpuCons; simp)
  have h2 := mem_cpuCons hs hr (c := B.whenTrans (B.eq (B.nxt STK) nextStk)) (by unfold cpuCons; simp)
  have h3 := mem_cpuCons hs hr (c := B.whenTrans (B.eq (B.nxt CTR) nextCtr)) (by unfold cpuCons; simp)
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

/-- The first row: the loaded term's registers. -/
theorem first_regs (h0 : r = 0) :
    T.main r HD = ofN hd0 ∧ T.main r STK = ofN stk0 ∧ T.main r CTR = ofN ctr0 := by
  have hf : T.env r .first = 1 := by simp [env_first, h0]
  have h1 := mem_cpuCons hs hr (c := B.whenFirst (B.eq (B.col HD) (B.c hd0))) (by unfold cpuCons; simp)
  have h2 := mem_cpuCons hs hr (c := B.whenFirst (B.eq (B.col STK) (B.c stk0))) (by unfold cpuCons; simp)
  have h3 := mem_cpuCons hs hr (c := B.whenFirst (B.eq (B.col CTR) (B.c ctr0))) (by unfold cpuCons; simp)
  simp only [B.whenFirst, B.eq, B.col, B.c, E.eval, hf, one_mul', env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

/-- The last row has halted. -/
theorem last_halt (hl : r + 1 = T.h) : halt.eval (T.env r) = 1 := by
  have hla : T.env r .last = 1 := by simp [env_last, hl]
  have h1 := mem_cpuCons hs hr (c := B.whenLast (B.eq halt B.one)) (by unfold cpuCons; simp)
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one] at h1
  exact sub_eq_zero h1

end Row

end Circuit
