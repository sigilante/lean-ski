import Ski.Circuit.CompJAir
import Ski.Circuit.CompKind
import Ski.Circuit.JetKind

/-!
# One row of the composed CPU with jets, as equations

The constraints of `cpuAirCJ` at a row, unfolded: the kind selectors and
the restart selector are bits summing to one; the reads' range equations;
the row counter and the root flags; no probe; the segment counter; the
next registers, with an instantiation's and a restart's parts; the first
and last rows.  The composed CPU's (`Ski/Circuit/CompRow.lean`) and the jet
CPU's (`Ski/Circuit/JetKind.lean`), at once.
-/

namespace Circuit

open B

/-- The constraints after the reads. -/
def cjTail (hd0 stk0 ctr0 n nilA : Nat) : List E :=
  [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
   bool (col J_RL), bool (col J_RA), bool (col J_RG),
   eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst,
   sPFirst, sPLater,
   whenFirst (col CNTJ), whenTrans (eq (nxt CNTJ) (.add (col CNTJ) sRSJ)), whenLast (eq (col CNTJ) (c (n - 1))),
   whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sRSJ (col ROOTJ)))),
   whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST))) (.mul sRSJ (c nilA)))),
   whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))),
   whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
   whenLast (eq halt one),
   bool (col (BLAJ + 4)), bool (col (BLBJ + 4)), bool (col (BLCJ + 4)),
   whenLast (eq sHK1 one)]

theorem cpuConsCJ_split (hd0 stk0 ctr0 n nilA : Nat) : cpuConsCJ hd0 stk0 ctr0 n nilA =
    (List.range NKINDS).map (fun i => bool (col (SEL + i))) ++ [bool sRSJ] ++
    [eq (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRSJ])) one] ++
    readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3 ++ cjTail hd0 stk0 ctr0 n nilA := rfl

section Row

variable {hd0 stk0 ctr0 n nilA : Nat} {T : Table} (hs : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) T)
  {r : Nat} (hr : r < T.h)
include hs hr

theorem memCJ {x : E} (h : x ∈ cpuConsCJ hd0 stk0 ctr0 n nilA) : x.eval (T.env r) = 0 := hs.2 x h r hr

theorem memCJ_tail {x : E} (h : x ∈ cjTail hd0 stk0 ctr0 n nilA) : x.eval (T.env r) = 0 :=
  memCJ hs hr (by rw [cpuConsCJ_split]; exact List.mem_append_right _ h)

theorem memCJ_read {j : Nat} (hj : j < 4) {x : E} (h : x ∈ readCons j) : x.eval (T.env r) = 0 := by
  apply memCJ hs hr
  rw [cpuConsCJ_split]
  simp only [List.mem_append]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)

theorem sel_bitCJ {i : Nat} (hi : i < NKINDS) :
    T.main r (SEL + i) * (T.main r (SEL + i) - 1) = 0 := by
  have := memCJ hs hr (x := B.bool (col (SEL + i)))
    (by rw [cpuConsCJ_split]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inl
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem rs_bitCJ : T.main r RSJ * (T.main r RSJ - 1) = 0 := by
  have := memCJ hs hr (x := B.bool sRSJ)
    (by rw [cpuConsCJ_split]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_singleton.2 rfl))))))))
  simpa [E.eval, B.bool, sRSJ, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- The kind selectors and the restart selector sum to one. -/
theorem sel_sumCJ :
    ((List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RSJ]).foldr (· + ·) 0 = 1 := by
  have := memCJ hs hr (x := B.eq (B.sum ((List.range NKINDS).map (fun i => B.col (SEL + i)) ++ [sRSJ])) B.one)
    (by rw [cpuConsCJ_split]; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_singleton.2 rfl)))))))
  simp only [B.eq, E.eval, B.sum] at this
  rw [eval_sum] at this
  have e := sub_eq_zero this
  simp only [B.zero, B.c, B.one, E.eval, ofN_zero, ofN_one, zero_add', List.map_append, List.map_map,
    List.map_cons, List.map_nil] at e
  rw [← e]
  congr 1
  simp [B.col, sRSJ, E.eval, env_main0 hr]

theorem range_bitCJ {j i : Nat} (hj : j < 4) (hi : i < RANGE_BITS) :
    T.main r (BITS + j * RANGE_BITS + i) * (T.main r (BITS + j * RANGE_BITS + i) - 1) = 0 := by
  have := memCJ_read hs hr hj (x := B.bool (B.col (BITS + j * RANGE_BITS + i)))
    (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem range_eqCJ {j : Nat} (hj : j < 4) :
    (acts.getD j B.zero).eval (T.env r) *
      (T.main r CTR - (addrs.getD j B.zero).eval (T.env r) - 1 - (rangeVal j).eval (T.env r)) = 0 := by
  have := memCJ_read hs hr hj (x := E.mul (acts.getD j B.zero)
    (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one) (rangeVal j)))
    (List.mem_append_right _ (List.mem_singleton.2 rfl))
  simpa [E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem pfirst_zeroCJ : T.main r (SEL + 12) = 0 := by
  have := memCJ_tail hs hr (x := sPFirst) (by simp [cjTail])
  simpa [E.eval, sPFirst, B.col, env_main0 hr] using this

theorem plater_zeroCJ : T.main r (SEL + 13) = 0 := by
  have := memCJ_tail hs hr (x := sPLater) (by simp [cjTail])
  simpa [E.eval, sPLater, B.col, env_main0 hr] using this

theorem flag_bitsCJ : T.main r J_RL * (T.main r J_RL - 1) = 0 ∧ T.main r J_RA * (T.main r J_RA - 1) = 0 ∧
    T.main r J_RG * (T.main r J_RG - 1) = 0 := by
  have h1 := memCJ_tail hs hr (x := bool (col J_RL)) (by simp [cjTail])
  have h2 := memCJ_tail hs hr (x := bool (col J_RA)) (by simp [cjTail])
  have h3 := memCJ_tail hs hr (x := bool (col J_RG)) (by simp [cjTail])
  simp only [B.bool, E.eval, B.col, B.one, B.c, ofN_one, env_main0 hr] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem jflags_sumCJ : T.main r J_RL + T.main r J_RA + T.main r J_RG = T.main r (SEL + 11) := by
  have h := memCJ_tail hs hr (x := eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst) (by simp [cjTail])
  simp only [B.eq, E.eval, B.col, sInst, env_main0 hr] at h
  exact sub_eq_zero h

/-- A row other than an instantiation has its root flags zero. -/
theorem flags_zeroCJ (h11 : T.main r (SEL + 11) = 0) :
    T.main r J_RL = 0 ∧ T.main r J_RA = 0 ∧ T.main r J_RG = 0 := by
  obtain ⟨b1, b2, b3⟩ := flag_bitsCJ hs hr
  have hs3 := jflags_sumCJ hs hr
  rw [h11] at hs3
  obtain ⟨hv, _, _, _⟩ := bits3_val b1 b2 b3
  rw [hs3] at hv
  have z : (0 : F).val = 0 := rfl
  rw [z] at hv
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> (show _ = 0; omega)

/-- The segment counter: `0` on the first row, growing by the restart
    selector, `n - 1` on the last. -/
theorem cnt_rowsCJ :
    (r = 0 → T.main r CNTJ = 0) ∧
    (r + 1 < T.h → T.main (r + 1) CNTJ = T.main r CNTJ + T.main r RSJ) ∧
    (r + 1 = T.h → T.main r CNTJ = ofN (n - 1)) := by
  refine ⟨fun h0 => ?_, fun hn => ?_, fun hl => ?_⟩
  · have hf : T.env r .first = 1 := by simp [env_first, h0]
    have := memCJ_tail hs hr (x := whenFirst (col CNTJ)) (by simp [cjTail])
    simp only [B.whenFirst, B.col, E.eval, hf, one_mul', env_main0 hr] at this
    exact this
  · have ht : T.env r .trans = 1 := by simp [env_trans]; omega
    have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
    have := memCJ_tail hs hr (x := whenTrans (eq (nxt CNTJ) (.add (col CNTJ) sRSJ))) (by simp [cjTail])
    simp only [B.whenTrans, B.eq, B.nxt, B.col, sRSJ, E.eval, ht, one_mul', env_main1, hmod, env_main0 hr] at this
    exact sub_eq_zero this
  · have hla : T.env r .last = 1 := by simp [env_last, hl]
    have := memCJ_tail hs hr (x := whenLast (eq (col CNTJ) (B.c (n - 1)))) (by simp [cjTail])
    simp only [B.whenLast, B.eq, B.col, B.c, E.eval, hla, one_mul', env_main0 hr] at this
    exact sub_eq_zero this

/-- The transitions: an instantiation's and a restart's parts added. -/
theorem next_regsCJ (hn : r + 1 < T.h) :
    T.main (r + 1) HD = nextHd.eval (T.env r) + jetHd.eval (T.env r) + T.main r RSJ * T.main r ROOTJ ∧
    T.main (r + 1) STK = nextStk.eval (T.env r) + T.main r (SEL + 11) * T.main r J_REST +
      T.main r RSJ * ofN nilA ∧
    T.main (r + 1) CTR = nextCtr.eval (T.env r) + T.main r (SEL + 11) * T.main r J_N := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h1 := memCJ_tail hs hr (x := whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sRSJ (col ROOTJ)))))
    (by simp [cjTail])
  have h2 := memCJ_tail hs hr
    (x := whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST))) (.mul sRSJ (B.c nilA)))))
    (by simp [cjTail])
  have h3 := memCJ_tail hs hr (x := whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))))
    (by simp [cjTail])
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod] at h1 h2 h3
  simp only [sInst, sRSJ, B.col, B.c, E.eval, env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

theorem first_regsCJ (h0 : r = 0) :
    T.main r HD = ofN hd0 ∧ T.main r STK = ofN stk0 ∧ T.main r CTR = ofN ctr0 := by
  have hf : T.env r .first = 1 := by simp [env_first, h0]
  have h1 := memCJ_tail hs hr (x := whenFirst (eq (col HD) (B.c hd0))) (by simp [cjTail])
  have h2 := memCJ_tail hs hr (x := whenFirst (eq (col STK) (B.c stk0))) (by simp [cjTail])
  have h3 := memCJ_tail hs hr (x := whenFirst (eq (col CTR) (B.c ctr0))) (by simp [cjTail])
  simp only [B.whenFirst, B.eq, B.col, B.c, E.eval, hf, one_mul', env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

/-- The last row has halted, as `HK1`. -/
theorem last_rowCJ (hl : r + 1 = T.h) : halt.eval (T.env r) = 1 ∧ T.main r (SEL + 5) = 1 := by
  have hla : T.env r .last = 1 := by simp [env_last, hl]
  have h1 := memCJ_tail hs hr (x := whenLast (eq halt one)) (by simp [cjTail])
  have h2 := memCJ_tail hs hr (x := whenLast (eq sHK1 one)) (by simp [cjTail])
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one, sHK1, B.col, env_main0 hr] at h1 h2
  exact ⟨sub_eq_zero h1, sub_eq_zero h2⟩

theorem first_clkCJ (h0 : r = 0) : T.main r J_CLK = 0 := by
  have h := memCJ_tail hs hr (x := whenFirst (col J_CLK)) (by simp [cjTail])
  simp only [B.whenFirst, E.eval, B.col, env_first, h0, if_pos, one_mul'] at h
  subst h0; exact h

theorem next_clkCJ (hn : r + 1 < T.h) : T.main (r + 1) J_CLK = T.main r J_CLK + 1 := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h := memCJ_tail hs hr (x := whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one))) (by simp [cjTail])
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod, B.col, env_main0 hr, B.one, B.c,
    ofN_one] at h
  exact sub_eq_zero h

end Row

/-- **The row counter is the row's index.** -/
theorem clk_eqCJ {hd0 stk0 ctr0 n nilA : Nat} {T : Table} (hs : Sat (cpuAirCJ hd0 stk0 ctr0 n nilA) T) :
    ∀ r, r < T.h → T.main r J_CLK = ofN r
  | 0, hr => first_clkCJ hs hr rfl
  | r + 1, hr => by
    rw [next_clkCJ hs (Nat.lt_of_succ_lt hr) hr, clk_eqCJ hs r (Nat.lt_of_succ_lt hr), ofN_add, ofN_one]

end Circuit
