import Ski.Circuit.CompPAir
import Ski.Circuit.CompRow

/-!
# One CPU row of the circuit with the Poseidon2 jet, as equations

The CPU's constraints (`cpuConsP2`) at a row, unfolded, as
`Ski/Circuit/CompRow.lean` unfolds the composed CPU's: the kind, restart
and jet selectors are bits summing to one; the reads' range equations;
no instantiation or probe; the segment counter; the jet row's atom and
root; the next registers, with a restart's jump and the jet's step; the
first and last rows.
-/

namespace Circuit

open B

section Row

variable {hd0 stk0 ctr0 n nilA J root : Nat} {T : Table}
  (hs : Sat (cpuAirP2 hd0 stk0 ctr0 n nilA J root) T) {r : Nat} (hr : r < T.h)
include hs hr

theorem memP2 {c : E} (h : c ∈ cpuConsP2 hd0 stk0 ctr0 n nilA J root) : c.eval (T.env r) = 0 := hs.cons h hr

theorem memP_tail {c : E} (h : c ∈ [sInst, sPFirst, sPLater,
    whenFirst (col CNT), whenTrans (eq (nxt CNT) (.add (col CNT) sRS)), whenLast (eq (col CNT) (B.c (n - 1))),
    .mul sP2 (.sub (fld 0) (B.c J)), .mul sP2 (.sub (fld 4) (B.c root)),
    whenTrans (eq (nxt HD) (.add (.add nextHd (.mul sRS (col ROOT))) (.mul sP2 (fld 2)))),
    whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sRS (B.c nilA))) (.mul sP2 (.add (col CTR) (B.c (P2_BITS - 1)))))),
    whenTrans (eq (nxt CTR) (.add nextCtr (.mul sP2 (B.c P2_BITS)))),
    whenFirst (eq (col HD) (B.c hd0)), whenFirst (eq (col STK) (B.c stk0)), whenFirst (eq (col CTR) (B.c ctr0)),
    whenLast (eq halt one),
    B.bool (col (BLA + 4)), B.bool (col (BLB + 4)),
    whenLast (eq sHK1 one)]) : c.eval (T.env r) = 0 :=
  memP2 hs hr (List.mem_append_right _ h)

theorem memP_read {j : Nat} (hj : j < 4) {c : E} (h : c ∈ readConsP j) : c.eval (T.env r) = 0 := by
  apply memP2 hs hr
  unfold cpuConsP2
  simp only [List.mem_append]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inr h))))
  · exact .inl (.inl (.inl (.inr h)))
  · exact .inl (.inl (.inr h))
  · exact .inl (.inr h)

theorem sel_bitP2 {i : Nat} (hi : i < NKINDS) :
    T.main r (SEL + i) * (T.main r (SEL + i) - 1) = 0 := by
  have := memP2 hs hr (c := B.bool (col (SEL + i)))
    (by unfold cpuConsP2; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inl
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem rs_bitP : T.main r RS * (T.main r RS - 1) = 0 := by
  have := memP2 hs hr (c := B.bool sRS)
    (by unfold cpuConsP2; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_cons_self ..))))))))
  simpa [E.eval, B.bool, sRS, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem p2_bitP : T.main r P2SEL * (T.main r P2SEL - 1) = 0 := by
  have := memP2 hs hr (c := B.bool sP2)
    (by unfold cpuConsP2; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))))))))
  simpa [E.eval, B.bool, sP2, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- The kind selectors, the restart selector and the jet selector sum to one. -/
theorem sel_sumP2 :
    ((List.range NKINDS).map (fun i => T.main r (SEL + i)) ++ [T.main r RS, T.main r P2SEL]).foldr (· + ·) 0 = 1 := by
  have := memP2 hs hr (c := B.eq (B.sum ((List.range NKINDS).map (fun i => B.col (SEL + i)) ++ [sRS, sP2])) B.one)
    (by unfold cpuConsP2; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl (.inr
      (List.mem_singleton.2 rfl)))))))
  simp only [B.eq, E.eval, B.sum] at this
  rw [eval_sum] at this
  have e := sub_eq_zero this
  simp only [B.zero, B.c, B.one, E.eval, ofN_zero, ofN_one, zero_add', List.map_append, List.map_map,
    List.map_cons, List.map_nil] at e
  rw [← e]
  congr 1
  simp [B.col, sRS, sP2, E.eval, env_main0 hr]

theorem range_bitP2 {j i : Nat} (hj : j < 4) (hi : i < RANGE_BITS) :
    T.main r (BITS + j * RANGE_BITS + i) * (T.main r (BITS + j * RANGE_BITS + i) - 1) = 0 := by
  have := memP_read hs hr hj (c := B.bool (B.col (BITS + j * RANGE_BITS + i)))
    (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem range_eqP2 {j : Nat} (hj : j < 4) :
    (actsP.getD j B.zero).eval (T.env r) *
      (T.main r CTR - (addrs.getD j B.zero).eval (T.env r) - 1 - (rangeVal j).eval (T.env r)) = 0 := by
  have := memP_read hs hr hj (c := E.mul (actsP.getD j B.zero)
    (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one) (rangeVal j)))
    (List.mem_append_right _ (List.mem_singleton.2 rfl))
  simpa [E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem inst_zeroP : T.main r (SEL + 11) = 0 := by
  have := memP_tail hs hr (c := sInst) (by simp)
  simpa [E.eval, sInst, B.col, env_main0 hr] using this

theorem pfirst_zeroP : T.main r (SEL + 12) = 0 := by
  have := memP_tail hs hr (c := sPFirst) (by simp)
  simpa [E.eval, sPFirst, B.col, env_main0 hr] using this

theorem plater_zeroP : T.main r (SEL + 13) = 0 := by
  have := memP_tail hs hr (c := sPLater) (by simp)
  simpa [E.eval, sPLater, B.col, env_main0 hr] using this

/-- The segment counter: `0` on the first row, growing by the restart
    selector, `n - 1` on the last. -/
theorem cnt_rowsP :
    (r = 0 → T.main r CNT = 0) ∧
    (r + 1 < T.h → T.main (r + 1) CNT = T.main r CNT + T.main r RS) ∧
    (r + 1 = T.h → T.main r CNT = ofN (n - 1)) := by
  refine ⟨fun h0 => ?_, fun hn => ?_, fun hl => ?_⟩
  · have hf : T.env r .first = 1 := by simp [env_first, h0]
    have := memP_tail hs hr (c := whenFirst (col CNT)) (by simp)
    simp only [B.whenFirst, B.col, E.eval, hf, one_mul', env_main0 hr] at this
    exact this
  · have ht : T.env r .trans = 1 := by simp [env_trans]; omega
    have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
    have := memP_tail hs hr (c := whenTrans (eq (nxt CNT) (.add (col CNT) sRS))) (by simp)
    simp only [B.whenTrans, B.eq, B.nxt, B.col, sRS, E.eval, ht, one_mul', env_main1, hmod, env_main0 hr] at this
    exact sub_eq_zero this
  · have hla : T.env r .last = 1 := by simp [env_last, hl]
    have := memP_tail hs hr (c := whenLast (eq (col CNT) (B.c (n - 1)))) (by simp)
    simp only [B.whenLast, B.eq, B.col, B.c, E.eval, hla, one_mul', env_main0 hr] at this
    exact sub_eq_zero this

/-- The jet row's atom and root. -/
theorem p2_pinsP :
    T.main r P2SEL * (T.main r (FLD + 0) - ofN J) = 0 ∧ T.main r P2SEL * (T.main r (FLD + 4) - ofN root) = 0 := by
  have h1 := memP_tail hs hr (c := .mul sP2 (.sub (fld 0) (B.c J))) (by simp)
  have h2 := memP_tail hs hr (c := .mul sP2 (.sub (fld 4) (B.c root))) (by simp)
  simp only [sP2, fld, B.col, B.c, E.eval, env_main0 hr] at h1 h2
  exact ⟨h1, h2⟩

/-- The transitions, with a restart's jump and the jet's step. -/
theorem next_regsP2 (hn : r + 1 < T.h) :
    T.main (r + 1) HD = nextHd.eval (T.env r) + T.main r RS * T.main r ROOT + T.main r P2SEL * T.main r (FLD + 2) ∧
    T.main (r + 1) STK = nextStk.eval (T.env r) + T.main r RS * ofN nilA +
      T.main r P2SEL * (T.main r CTR + ofN (P2_BITS - 1)) ∧
    T.main (r + 1) CTR = nextCtr.eval (T.env r) + T.main r P2SEL * ofN P2_BITS := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h1 := memP_tail hs hr
    (c := whenTrans (eq (nxt HD) (.add (.add nextHd (.mul sRS (col ROOT))) (.mul sP2 (fld 2))))) (by simp)
  have h2 := memP_tail hs hr (c := whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sRS (B.c nilA)))
    (.mul sP2 (.add (col CTR) (B.c (P2_BITS - 1))))))) (by simp)
  have h3 := memP_tail hs hr (c := whenTrans (eq (nxt CTR) (.add nextCtr (.mul sP2 (B.c P2_BITS))))) (by simp)
  simp only [B.whenTrans, B.eq, B.nxt, B.col, B.c, sRS, sP2, fld, E.eval, ht, one_mul', env_main1, hmod,
    env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

theorem first_regsP2 (h0 : r = 0) :
    T.main r HD = ofN hd0 ∧ T.main r STK = ofN stk0 ∧ T.main r CTR = ofN ctr0 := by
  have hf : T.env r .first = 1 := by simp [env_first, h0]
  have h1 := memP_tail hs hr (c := whenFirst (eq (col HD) (B.c hd0))) (by simp)
  have h2 := memP_tail hs hr (c := whenFirst (eq (col STK) (B.c stk0))) (by simp)
  have h3 := memP_tail hs hr (c := whenFirst (eq (col CTR) (B.c ctr0))) (by simp)
  simp only [B.whenFirst, B.eq, B.col, B.c, E.eval, hf, one_mul', env_main0 hr] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

/-- The last row has halted, as `HK1`. -/
theorem last_rowP (hl : r + 1 = T.h) : halt.eval (T.env r) = 1 ∧ T.main r (SEL + 5) = 1 := by
  have hla : T.env r .last = 1 := by simp [env_last, hl]
  have h1 := memP_tail hs hr (c := whenLast (eq halt one)) (by simp)
  have h2 := memP_tail hs hr (c := whenLast (eq sHK1 one)) (by simp)
  simp only [B.whenLast, B.eq, E.eval, hla, one_mul', B.one, B.c, ofN_one, sHK1, B.col, env_main0 hr] at h1 h2
  exact ⟨sub_eq_zero h1, sub_eq_zero h2⟩

end Row

end Circuit
