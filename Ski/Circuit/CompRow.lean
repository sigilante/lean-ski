import Ski.Circuit.CompAir
import Ski.Circuit.Bus

/-!
# One composed CPU row's constraints, as equations

The composed CPU's constraints (`cpuConsC`) at a row, unfolded: the kind
selectors and the restart selector are bits summing to one; the reads'
range equations; no instantiation or probe; the segment counter; the next
registers, with a restart's jump; the first and last rows.
-/

namespace Circuit

open B

section Row

variable {hd0 stk0 ctr0 n nilA : Nat} {T : Table} (hs : Sat (cpuAirC hd0 stk0 ctr0 n nilA) T)
  {r : Nat} (hr : r < T.h)
include hs hr

theorem memC {c : E} (h : c ∈ cpuConsC hd0 stk0 ctr0 n nilA) : c.eval (T.env r) = 0 := hs.cons h hr

theorem memC_tail {c : E} (h : c ∈ [sInst, sPFirst, sPLater,
    whenFirst (col CNT), whenTrans (eq (nxt CNT) (.add (col CNT) sRS)), whenLast (eq (col CNT) (B.c (n - 1))),
    whenTrans (eq (nxt HD) (.add nextHd (.mul sRS (col ROOT)))),
    whenTrans (eq (nxt STK) (.add nextStk (.mul sRS (B.c nilA)))),
    whenTrans (eq (nxt CTR) nextCtr),
    whenFirst (eq (col HD) (B.c hd0)), whenFirst (eq (col STK) (B.c stk0)), whenFirst (eq (col CTR) (B.c ctr0)),
    whenLast (eq halt one),
    B.bool (col (BLA + 4)), B.bool (col (BLB + 4)),
    whenLast (eq sHK1 one)]) : c.eval (T.env r) = 0 :=
  memC hs hr (List.mem_append_right _ h)

theorem memC_read {j : Nat} (hj : j < 4) {c : E} (h : c ∈ readCons j) : c.eval (T.env r) = 0 := by
  apply memC hs hr
  unfold cpuConsC
  simp only [List.mem_append]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)

theorem sel_bitC {i : Nat} (hi : i < NKINDS) :
    T.main r (SEL + i) * (T.main r (SEL + i) - 1) = 0 := by
  have := memC hs hr (c := B.bool (col (SEL + i)))
    (by unfold cpuConsC; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inl
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem rs_bit : T.main r RS * (T.main r RS - 1) = 0 := by
  have := memC hs hr (c := B.bool sRS)
    (by unfold cpuConsC; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_singleton.2 rfl))))))))
  simpa [E.eval, B.bool, sRS, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- The kind selectors and the restart selector sum to one. -/
theorem sel_sumC :
    ((List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RS]).foldr (· + ·) 0 = 1 := by
  have := memC hs hr (c := B.eq (B.sum ((List.range NKINDS).map (fun i => B.col (SEL + i)) ++ [sRS])) B.one)
    (by unfold cpuConsC; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_singleton.2 rfl)))))))
  simp only [B.eq, E.eval, B.sum] at this
  rw [eval_sum] at this
  have e := sub_eq_zero this
  simp only [B.zero, B.c, B.one, E.eval, ofN_zero, ofN_one, zero_add', List.map_append, List.map_map,
    List.map_cons, List.map_nil] at e
  rw [← e]
  congr 1
  simp [B.col, sRS, E.eval, env_main0 hr]

theorem range_bitC {j i : Nat} (hj : j < 4) (hi : i < RANGE_BITS) :
    T.main r (BITS + j * RANGE_BITS + i) * (T.main r (BITS + j * RANGE_BITS + i) - 1) = 0 := by
  have := memC_read hs hr hj (c := B.bool (B.col (BITS + j * RANGE_BITS + i)))
    (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem range_eqC {j : Nat} (hj : j < 4) :
    (acts.getD j B.zero).eval (T.env r) *
      (T.main r CTR - (addrs.getD j B.zero).eval (T.env r) - 1 - (rangeVal j).eval (T.env r)) = 0 := by
  have := memC_read hs hr hj (c := E.mul (acts.getD j B.zero)
    (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one) (rangeVal j)))
    (List.mem_append_right _ (List.mem_singleton.2 rfl))
  simpa [E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem inst_zeroC : T.main r (SEL + 11) = 0 := by
  have := memC_tail hs hr (c := sInst) (by simp)
  simpa [E.eval, sInst, B.col, env_main0 hr] using this

theorem pfirst_zeroC : T.main r (SEL + 12) = 0 := by
  have := memC_tail hs hr (c := sPFirst) (by simp)
  simpa [E.eval, sPFirst, B.col, env_main0 hr] using this

theorem plater_zeroC : T.main r (SEL + 13) = 0 := by
  have := memC_tail hs hr (c := sPLater) (by simp)
  simpa [E.eval, sPLater, B.col, env_main0 hr] using this

/-- The segment counter: `0` on the first row, growing by the restart
    selector, `n - 1` on the last. -/
theorem cnt_rows :
    (r = 0 → T.main r CNT = 0) ∧
    (r + 1 < T.h → T.main (r + 1) CNT = T.main r CNT + T.main r RS) ∧
    (r + 1 = T.h → T.main r CNT = ofN (n - 1)) := by
  refine ⟨fun h0 => ?_, fun hn => ?_, fun hl => ?_⟩
  · have hf : T.env r .first = 1 := by simp [env_first, h0]
    have := memC_tail hs hr (c := whenFirst (col CNT)) (by simp)
    simp only [B.whenFirst, B.col, E.eval, hf, one_mul', env_main0 hr] at this
    exact this
  · have ht : T.env r .trans = 1 := by simp [env_trans]; omega
    have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
    have := memC_tail hs hr (c := whenTrans (eq (nxt CNT) (.add (col CNT) sRS))) (by simp)
    simp only [B.whenTrans, B.eq, B.nxt, B.col, sRS, E.eval, ht, one_mul', env_main1, hmod, env_main0 hr] at this
    exact sub_eq_zero this
  · have hla : T.env r .last = 1 := by simp [env_last, hl]
    have := memC_tail hs hr (c := whenLast (eq (col CNT) (B.c (n - 1)))) (by simp)
    simp only [B.whenLast, B.eq, B.col, B.c, E.eval, hla, one_mul', env_main0 hr] at this
    exact sub_eq_zero this

/-- The transitions, with a restart's jump. -/
theorem next_regsC (hn : r + 1 < T.h) :
    T.main (r + 1) HD = nextHd.eval (T.env r) + T.main r RS * T.main r ROOT ∧
    T.main (r + 1) STK = nextStk.eval (T.env r) + T.main r RS * ofN nilA ∧
    T.main (r + 1) CTR = nextCtr.eval (T.env r) := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h1 := memC_tail hs hr (c := whenTrans (eq (nxt HD) (.add nextHd (.mul sRS (col ROOT))))) (by simp)
  have h2 := memC_tail hs hr (c := whenTrans (eq (nxt STK) (.add nextStk (.mul sRS (B.c nilA))))) (by simp)
  have h3 := memC_tail hs hr (c := whenTrans (eq (nxt CTR) nextCtr)) (by simp)
  simp only [B.whenTrans, B.eq, B.nxt, B.col, B.c, sRS, E.eval, ht, one_mul', env_main1, hmod,
    env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

theorem first_regsC (h0 : r = 0) :
    T.main r HD = ofN hd0 ∧ T.main r STK = ofN stk0 ∧ T.main r CTR = ofN ctr0 := by
  have hf : T.env r .first = 1 := by simp [env_first, h0]
  have h1 := memC_tail hs hr (c := whenFirst (eq (col HD) (B.c hd0))) (by simp)
  have h2 := memC_tail hs hr (c := whenFirst (eq (col STK) (B.c stk0))) (by simp)
  have h3 := memC_tail hs hr (c := whenFirst (eq (col CTR) (B.c ctr0))) (by simp)
  simp only [B.whenFirst, B.eq, B.col, B.c, E.eval, hf, one_mul', env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

/-- The last row has halted, as `HK1`. -/
theorem last_rowC (hl : r + 1 = T.h) : halt.eval (T.env r) = 1 ∧ T.main r (SEL + 5) = 1 := by
  have hla : T.env r .last = 1 := by simp [env_last, hl]
  have h1 := memC_tail hs hr (c := whenLast (eq halt one)) (by simp)
  have h2 := memC_tail hs hr (c := whenLast (eq sHK1 one)) (by simp)
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one, sHK1, B.col, env_main0 hr] at h1 h2
  exact ⟨sub_eq_zero h1, sub_eq_zero h2⟩

end Row

end Circuit

#print axioms Circuit.sel_sumC
#print axioms Circuit.cnt_rows
#print axioms Circuit.next_regsC
#print axioms Circuit.last_rowC
#print axioms Circuit.range_eqC
