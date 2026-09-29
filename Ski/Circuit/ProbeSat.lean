import Ski.Circuit.ProbeCpuSat

/-!
# The honest probe tables satisfy their AIRs

The memory table counts the messages of five senders (`memTable5`): the
CPU, the program, POP, INSTW and PW.  POP's rows are pops below their
counters (`PRun.pop_satP`); PW's rows are active (`PRun.pw_satP`).
-/

namespace Circuit

open B Air JetTable Mach

/-- The memory table: each cell, with the count of messages sent to it by
    the CPU, the program, POP, INSTW and PW. -/
def memTable5 (A : List Cell) (cpu prog pop instw pw : AirD) (C Pg Po Iw Pw : Table) : Table :=
  ⟨A.length, fun m col =>
    if col = 0 then ofN m
    else if col = 1 then ofN (cellTag (A.getD m .nil))
    else if col = 2 then ofN (cellFields (A.getD m .nil)).1
    else if col = 3 then ofN (cellFields (A.getD m .nil)).2
    else if col = 4 then tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
      (tableSends pop Po "mem" (tupleOf A m) + (tableSends instw Iw "mem" (tupleOf A m) +
        tableSends pw Pw "mem" (tupleOf A m))))
    else 0, fun _ _ => 0⟩

theorem mem5_sat (A : List Cell) (cpu prog pop instw pw : AirD) (C Pg Po Iw Pw : Table) (hA : 0 < A.length) :
    Sat memAir (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw) := by
  refine ⟨hA, fun e he m hm' => ?_⟩
  have hm : m < (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw).h := hm'
  simp only [memAir, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simp only [B.whenFirst, B.col, E.eval, env_first, env_main0 hm]
    split
    · next h0 => subst h0; exact mul_zero' _
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, B.nxt, B.col, B.one, B.c, E.eval, env_trans, env_main1, env_main0 hm]
    split
    · exact zero_mul' _
    · next hne =>
      have hne' : ¬ (m + 1 = A.length) := hne
      have hm1 : m + 1 < A.length := by have : m < A.length := hm; omega
      show 1 * ((memTable5 A cpu prog pop instw pw C Pg Po Iw Pw).main ((m + 1) % A.length) 0 - (ofN m + ofN 1)) = 0
      rw [Nat.mod_eq_of_lt hm1, one_mul', ofN_one, ofN_succ]
      exact sub_self' _

def at5 (a b c d f : F) : Atom → F
  | .main 0 0 => a | .main 0 1 => b | .main 0 2 => c | .main 0 3 => d | .main 0 4 => f | _ => 0

/-- `a + (-(a + (b + (c + (d + f)))) + (b + (c + (d + f)))) = 0`, by normal forms. -/
theorem bal5_identity (a b c d f : F) : a + (-(a + (b + (c + (d + f)))) + (b + (c + (d + f)))) = 0 :=
  E.eval_eq_of_norm
    (e := .add (.atom (.main 0 0)) (.add (.neg (.add (.atom (.main 0 0)) (.add (.atom (.main 0 1))
      (.add (.atom (.main 0 2)) (.add (.atom (.main 0 3)) (.atom (.main 0 4))))))) (.add (.atom (.main 0 1))
      (.add (.atom (.main 0 2)) (.add (.atom (.main 0 3)) (.atom (.main 0 4)))))))
    (e' := .const 0) (by decide) (at5 a b c d f)

/-- **`mem` balances with five senders.** -/
theorem bal_mem5 {A : List Cell} {cpu prog pop instw pw : AirD} {C Pg Po Iw Pw : Table} (hML : A.length < P)
    (hc : HonestMem A cpu C) (hp : HonestMem A prog Pg) (ho : HonestMem A pop Po) (hw : HonestMem A instw Iw)
    (hx : HonestMem A pw Pw) (v : List F) :
    tableSends cpu C "mem" v + (tableSends memAir (memTable5 A cpu prog pop instw pw C Pg Po Iw Pw) "mem" v +
      (tableSends prog Pg "mem" v + (tableSends pop Po "mem" v + (tableSends instw Iw "mem" v +
        tableSends pw Pw "mem" v)))) = 0 := by
  let Mm := memTable5 A cpu prog pop instw pw C Pg Po Iw Pw
  have hrow : ∀ m, m < A.length → rowSends memAir Mm "mem" v m =
      if tupleOf A m = v then -(tableSends cpu C "mem" (tupleOf A m) + (tableSends prog Pg "mem" (tupleOf A m) +
        (tableSends pop Po "mem" (tupleOf A m) + (tableSends instw Iw "mem" (tupleOf A m) +
          tableSends pw Pw "mem" (tupleOf A m))))) else 0 := by
    intro m hm
    have hm' : m < Mm.h := hm
    simp only [rowSends, memAir, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, B.col, E.eval,
      env_main0 hm', true_and, add_zero']
    rfl
  cases hany : (List.range A.length).any (fun m => decide (tupleOf A m = v)) with
  | true =>
    obtain ⟨m0, hm0, e0⟩ := List.any_eq_true.1 hany
    have hm0 := List.mem_range.1 hm0
    have e0 := of_decide_eq_true e0
    have hmem : tableSends memAir Mm "mem" v = -(tableSends cpu C "mem" v + (tableSends prog Pg "mem" v +
        (tableSends pop Po "mem" v + (tableSends instw Iw "mem" v + tableSends pw Pw "mem" v)))) := by
      show List.foldr (fun r acc => rowSends memAir Mm "mem" v r + acc) 0 (List.range A.length) = _
      rw [fold_single _ A.length m0 hm0, hrow m0 hm0, if_pos e0, e0]
      intro b hb hne
      rw [hrow b hb, if_neg]
      intro e
      rw [← e0] at e
      have := congrArg List.head? e
      simp only [tupleOf, List.head?_cons, Option.some.injEq] at this
      exact hne (ofN_inj (Nat.lt_trans hb hML) (Nat.lt_trans hm0 hML) this)
    rw [hmem]
    exact bal5_identity _ _ _ _ _
  | false =>
    have hno : ¬ ∃ m, m < A.length ∧ v = tupleOf A m := by
      rintro ⟨m, hm, e⟩
      have := List.any_eq_false.1 hany m (List.mem_range.2 hm)
      exact this (decide_eq_true e.symm)
    have z : ∀ {X : AirD} {T : Table}, HonestMem A X T → tableSends X T "mem" v = 0 := fun hX =>
      sends_zero_of (Q := fun w => ∃ m, m < A.length ∧ w = tupleOf A m)
        (fun r hr I hI hb hc => by obtain ⟨m, hm, e⟩ := hX r hr I hI hb hc; exact ⟨m, hm, e⟩) hno
    have h5 : tableSends memAir Mm "mem" v = 0 := by
      show List.foldr (fun r acc => rowSends memAir Mm "mem" v r + acc) 0 (List.range A.length) = 0
      apply fold_zero
      intro m hm
      rw [hrow m (List.mem_range.1 hm), if_neg (fun e => hno ⟨m, List.mem_range.1 hm, e.symm⟩)]
    rw [z hc, z hp, z ho, z hw, z hx, h5]; decide

namespace PRun

variable {R : PRun}

/-- **A probe POP row is a pop** of a later probe row's ending segment. -/
theorem probePops_mem {i : Nat} {rw : List F} (h : rw ∈ R.probePops i) :
    R.isP i = true ∧ 0 < R.pcnt i ∧ ∃ f s x s',
      (popsOf R.A (R.row i).ctr (R.seg (R.pcnt i - 1)).arity (R.row i).stk)[f]? = some (s, x, s') ∧
      rw = popRow i (R.row i).ctr f s x s' (R.uses (R.pcnt i - 1) f) := by
  unfold probePops at h
  split at h
  · next hc =>
    obtain ⟨⟨⟨s, x, s'⟩, f⟩, hz, e⟩ := List.mem_map.1 h
    obtain ⟨_, hf, hget⟩ := List.mem_zipIdx hz
    simp only [Nat.zero_add, Nat.sub_zero] at hf hget
    exact ⟨hc.1, hc.2, f, s, x, s', by rw [List.getElem?_eq_getElem hf, hget], e.symm⟩
  · cases h

variable {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
  (hroots : RootsOK (load t).heap R.roots R.jets)
include hA hroots

/-- A probe POP row reads a stack cell below its counter. -/
theorem probePop_facts {i f s x s' : Nat} (hp : R.isP i = true) (h0 : 0 < R.pcnt i)
    (hf : (popsOf R.A (R.row i).ctr (R.seg (R.pcnt i - 1)).arity (R.row i).stk)[f]? = some (s, x, s')) :
    s < (R.row i).ctr ∧ R.A[s]? = some (.cons x s') ∧ f < (R.seg (R.pcnt i - 1)).arity := by
  obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
  obtain ⟨_, hpops, _⟩ := later_end hA hjn h0
  rw [hpj] at hpops
  have hp' : popR (fun a => R.A[a]?) (R.row i).ctr (R.seg (R.pcnt i - 1)).arity (R.row i).stk =
      some (R.fld (R.pcnt i - 1), R.restE i) := hpops
  obtain ⟨σ, ξ, _, _, _, hs⟩ := popsOf_spec (A := R.A) _ _ hp'
  have hfk : f < (R.seg (R.pcnt i - 1)).arity := by
    have := (List.getElem?_eq_some_iff.1 hf).1
    rw [popsOf_length hp'] at this; exact this
  obtain ⟨e1, e2⟩ := hs f hfk
  rw [hf] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl⟩ := e1
  unfold rd at e2
  split at e2
  · next hlt => exact ⟨hlt, e2, hfk⟩
  · cases e2

/-- **The honest POP table satisfies POP's AIR.** -/
theorem pop_satP (hlen : R.A.length ≤ 2 ^ 24) {K HP : Nat} (hHP : 0 < HP) : Sat popAir (R.popTableP K HP) :=
  JRun.pop_sat_of (fun rw hmem => by
    obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 hmem
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨i', g, J, j, s, x, s', _, hn, hget, rfl⟩ := R.J.popRows_mem (K := K)
        (List.mem_flatMap.2 ⟨i, hi, hm⟩)
      obtain ⟨hs, _, _⟩ := R.J.pop_facts hn hget
      have hi1 := (JRun.instAt_some hn).1
      have hc : (R.row i').ctr ≤ 2 ^ 24 := by
        have := JRun.ctr_le (jok hA hroots) i'; rw [JRun.rowQ_lt (Nat.lt_of_succ_lt hi1)] at this
        exact Nat.le_trans this hlen
      exact ⟨i', (R.row i').ctr, j, s, x, s', usesOf J j, rfl, hs, hc⟩
    · obtain ⟨hp, h0, f, s, x, s', hget, rfl⟩ := probePops_mem hm
      obtain ⟨hs, _, _⟩ := probePop_facts hA hroots hp h0 hget
      have hil := isP_lt hA hp
      have hc : (R.row i).ctr ≤ 2 ^ 24 :=
        Nat.le_trans (hA.ctrs hroots i (by unfold last at hil; unfold n at hil; omega)).2.1 hlen
      exact ⟨i, (R.row i).ctr, f, s, x, s', R.uses (R.pcnt i - 1) f, rfl, hs, hc⟩) hHP

omit hA hroots in
/-- **The honest PW table satisfies PW's AIR.** -/
theorem pw_satP {K HW : Nat} (hHW : 0 < HW) : Sat pwAir (R.pwTable K HW) := by
  refine ⟨hHW, fun e he q (hq : q < HW) => ?_⟩
  have cv : ∀ c, (col c).eval ((R.pwTable K HW).env q) = ofRows (R.pwRows K) q c := by
    intro c; show ofRows (R.pwRows K) ((q + 0) % HW) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  simp only [pwAir, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
  rcases JRun.ofRows_cases (R.pwRows K) q with ⟨rw, hmem, hrw⟩ | hz
  · obtain ⟨i, _, hm⟩ := List.mem_flatMap.1 hmem
    unfold pwRowsAt at hm
    split at hm
    · obtain ⟨_, _, rfl⟩ := List.mem_map.1 hm
      rw [hrw]; show (1 : F) * (1 - 1) = 0; decide
    · cases hm
  · rw [hz 5]; exact zero_mul' _

end PRun

end Circuit
