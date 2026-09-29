import Ski.Circuit.CompHeap

/-!
# The witness table forces the private cells

An active witness row names its address's memory cell (`CompOK.witCell`):
`S`, `K`, `I`, or an application of two cells below it (`cellOK`); in bit
mode, `K` or `K I` (`A 0 1`).
-/

namespace Circuit

open B Wit

/-- A 24-bit number from bit columns is below `2^24`. -/
theorem bits_lt {T : Table} {r : Nat} (hr : r < T.h) (base : Nat)
    (hb : ∀ i, i < RANGE_BITS → T.main r (base + i) * (T.main r (base + i) - 1) = 0) :
    (((List.range RANGE_BITS).foldl (fun v i => E.add v (E.mul (col (base + i)) (c (2 ^ i)))) zero).eval
      (T.env r)).val < 2 ^ 24 := by
  have step : ∀ n, n ≤ RANGE_BITS →
      (((List.range n).foldl (fun v i => E.add v (E.mul (col (base + i)) (c (2 ^ i)))) zero).eval
        (T.env r)).val < 2 ^ n := by
    intro n
    induction n with
    | zero => intro _; show (0 : Nat) < 1; decide
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := ih (Nat.le_of_succ_le hn)
      generalize (List.foldl (fun v i => E.add v (E.mul (col (base + i)) (c (2 ^ i)))) zero (List.range n)) = X at ih ⊢
      simp only [E.eval, B.col, B.c, env_main0 hr]
      generalize X.eval (T.env r) = x at ih ⊢
      have hpow : 2 ^ (n + 1) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hn
      have hP : 2 ^ 24 < P := by decide
      rcases bit_of (hb n hn) with h | h <;> rw [h]
      · rw [zero_mul', add_zero']
        exact Nat.lt_of_lt_of_le ih (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
      · rw [one_mul', val_add_nat (by rw [Nat.pow_succ] at hpow; omega), Nat.pow_succ]
        omega
  exact step RANGE_BITS (Nat.le_refl _)

/-- `a - b - 1 - x = 0` with `b` and `x` small puts `b` below `a`. -/
theorem below_of {a b x : F} (h : a - b - 1 - x = 0) (hb : b.val < 2 ^ 24) (hx : x.val < 2 ^ 24) :
    b.val < a.val := by
  have e := sub_eq_zero h
  have ha : a = b + 1 + x := by rw [← e, add_sub_cancel3]
  have hPb := P_big
  have h1 : (b + 1).val = b.val + 1 := val_add_of_lt (by show _ + 1 < P; omega)
  have h2 : (b + 1 + x).val = b.val + 1 + x.val := by
    rw [val_add_of_lt (by rw [h1]; omega), h1]
  rw [ha, h2]; omega

theorem wit_env {Wt : Table} {q : Nat} (hq : q < Wt.h) (i : Nat) : (col i).eval (Wt.env q) = Wt.main q i := env_main0 hq

theorem wit_pre {Wt : Table} {q : Nat} (hq : q < Wt.h) (i : Nat) : (prec i).eval (Wt.env q) = Wt.pre q i := by
  show Wt.pre ((q + 0) % Wt.h) i = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]

/-- **An active witness row's cell**, from any tables: in memory at its
    address, well formed, and in bit mode `K` or `A 0 1`. -/
theorem witCellG {Wt Mm : Table}
    (hsat : ∀ c ∈ witCons, ∀ q, q < Wt.h → c.eval (Wt.env q) = 0)
    (hlook : ∀ q, q < Wt.h → (prec 1).eval (Wt.env q) = 1 → ∃ m, m < Mm.h ∧
      [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] =
        (witInters.headD ⟨"", 0, .const 0, []⟩).fields.map (fun e => e.eval (Wt.env q)))
    (haddr : ∀ m, m < Mm.h → Mm.main m 0 = ofN m) (hmh : Mm.h ≤ 2 ^ 27)
    {q : Nat} (hq : q < Wt.h) (hact : Wt.pre q 1 = 1) :
    ∃ cell, (Wt.pre q 0).val < Mm.h ∧ (memOf Mm)[(Wt.pre q 0).val]? = some cell ∧
      cellOK (Wt.pre q 0).val cell = true ∧ (Wt.pre q 2 = 1 → cell = .K ∨ cell = .app 0 1) := by
  have mem := fun {c : E} (hc : c ∈ witCons) => hsat c hc q hq
  have ev := wit_env hq
  have pv := wit_pre hq
  -- the flags are bits, one of them set
  have fb : ∀ i, i < 4 → Wt.main q i = 0 ∨ Wt.main q i = 1 := by
    intro i hi
    have := mem (c := B.bool (col i)) (by
      unfold witCons; simp only [List.mem_append]
      exact .inl (.inl (.inl (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))
    simp only [B.bool, E.eval, ev, B.one, B.c, ofN_one] at this
    exact bit_of this
  have hsum := mem (c := B.eq (.add (.add (.add (col 0) (col 1)) (col 2)) (col 3)) (prec 1)) (by
    unfold witCons; simp only [List.mem_append, List.mem_cons, true_or, or_true])
  simp only [B.eq, E.eval, ev, pv, hact] at hsum
  have hsum := sub_eq_zero hsum
  have ma := mem (c := .mul (.sub one (col 3)) (col WT_A)) (by
    unfold witCons; simp only [List.mem_append, List.mem_cons, true_or, or_true])
  have mb := mem (c := .mul (.sub one (col 3)) (col WT_B)) (by
    unfold witCons; simp only [List.mem_append, List.mem_cons, true_or, or_true])
  simp only [E.eval, ev, B.one, B.c, ofN_one] at ma mb
  have tail : ∀ c ∈ [.mul (col 3) (.sub (col WT_A) (wnum 0)),
      .mul (col 3) (.sub (.sub (.sub (prec 0) (col WT_A)) one) (wnum 1)),
      .mul (col 3) (.sub (col WT_B) (wnum 2)),
      .mul (col 3) (.sub (.sub (.sub (prec 0) (col WT_B)) one) (wnum 3)),
      .mul (prec 2) (.add (col 0) (col 2)), .mul (prec 2) (col WT_A), .mul (prec 2) (.sub (col WT_B) (col 3)),
      B.bool (col (WT_BLIND + 4))], c.eval (Wt.env q) = 0 := fun c hc => mem (by
    unfold witCons; simp only [List.mem_append]; exact .inr hc)
  have t1 := tail (.mul (col 3) (.sub (col WT_A) (wnum 0))) (by simp only [List.mem_cons, true_or, or_true])
  have t2 := tail (.mul (col 3) (.sub (.sub (.sub (prec 0) (col WT_A)) one) (wnum 1)))
    (by simp only [List.mem_cons, true_or, or_true])
  have t3 := tail (.mul (col 3) (.sub (col WT_B) (wnum 2))) (by simp only [List.mem_cons, true_or, or_true])
  have t4 := tail (.mul (col 3) (.sub (.sub (.sub (prec 0) (col WT_B)) one) (wnum 3)))
    (by simp only [List.mem_cons, true_or, or_true])
  have t5 := tail (.mul (prec 2) (.add (col 0) (col 2))) (by simp only [List.mem_cons, true_or, or_true])
  have t6 := tail (.mul (prec 2) (col WT_A)) (by simp only [List.mem_cons, true_or, or_true])
  have t7 := tail (.mul (prec 2) (.sub (col WT_B) (col 3))) (by simp only [List.mem_cons, true_or, or_true])
  simp only [E.eval, ev, pv, B.one, B.c, ofN_one] at t1 t2 t3 t4 t5 t6 t7
  -- the lookup
  have hbits : ∀ k, k < 4 → ∀ i, i < RANGE_BITS →
      Wt.main q (WT_BITS + k * RANGE_BITS + i) * (Wt.main q (WT_BITS + k * RANGE_BITS + i) - 1) = 0 := by
    intro k hk i hi
    have := mem (c := B.bool (col (WT_BITS + (k * RANGE_BITS + i)))) (by
      unfold witCons; simp only [List.mem_append]
      exact .inl (.inr (List.mem_map.2 ⟨k * RANGE_BITS + i, List.mem_range.2 (by unfold RANGE_BITS at *; omega), rfl⟩)))
    simp only [B.bool, E.eval, ev, B.one, B.c, ofN_one] at this
    rwa [← Nat.add_assoc] at this
  have nlt : ∀ k, k < 4 → ((wnum k).eval (Wt.env q)).val < 2 ^ 24 := fun k hk =>
    bits_lt hq (WT_BITS + k * RANGE_BITS) (hbits k hk)
  let tag := Wt.main q 1 + Wt.main q 2 * ofN 2 + Wt.main q 3 * ofN 3
  obtain ⟨m, hm, e⟩ := hlook q hq (by rw [pv, hact])
  have e' : [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] =
      [Wt.pre q 0, tag, Wt.main q WT_A, Wt.main q WT_B] := by
    rw [e]; simp only [witInters, List.headD_cons, List.map_cons, List.map_nil, E.eval, ev, pv, B.c]; rfl
  simp only [List.cons.injEq, and_true] at e'
  obtain ⟨e0, e1, e2, e3⟩ := e'
  have hmP : m < P := Nat.lt_of_lt_of_le hm (Nat.le_trans hmh (by decide))
  rw [haddr m hm] at e0
  have hlt : (Wt.pre q 0).val < Mm.h := by rw [← e0, val_ofN hmP]; exact hm
  have hget : (memOf Mm)[(Wt.pre q 0).val]? = some (cellOf tag (Wt.main q WT_A) (Wt.main q WT_B)) := by
    rw [← e0, val_ofN hmP, memOf_get hm, e1, e2, e3]
  refine ⟨_, hlt, hget, ?_⟩
  -- the four kinds
  rcases fb 0 (by decide) with f0 | f0 <;> rcases fb 1 (by decide) with f1 | f1 <;>
    rcases fb 2 (by decide) with f2 | f2 <;> rcases fb 3 (by decide) with f3 | f3 <;>
    simp only [tag, f0, f1, f2, f3] at hsum ma mb t1 t2 t3 t4 t5 t6 t7 ⊢ <;>
    first | exact absurd hsum (by decide) | skip
  · -- `A`
    rw [one_mul'] at t1 t2 t3 t4
    have hA : (Wt.main q WT_A).val < 2 ^ 24 := by rw [sub_eq_zero t1]; exact nlt 0 (by decide)
    have hB : (Wt.main q WT_B).val < 2 ^ 24 := by rw [sub_eq_zero t3]; exact nlt 2 (by decide)
    have la := below_of t2 hA (nlt 1 (by decide))
    have lb := below_of t4 hB (nlt 3 (by decide))
    rw [show (0 : F) + 0 * ofN 2 + 1 * ofN 3 = ofN 3 by decide, cellOf_app]
    refine ⟨by simp only [cellOK, decide_eq_true la, decide_eq_true lb, Bool.and_self], fun hb => .inr ?_⟩
    rw [hb, one_mul'] at t6 t7
    rw [t6, sub_eq_zero t7]; rfl
  · -- `I`
    rw [show (0 : F) + 1 * ofN 2 + 0 * ofN 3 = ofN 2 by decide, cellOf_I]
    refine ⟨rfl, fun hb => ?_⟩
    rw [hb] at t5
    exact absurd t5 (by decide)
  · -- `K`
    rw [show (1 : F) + 0 * ofN 2 + 0 * ofN 3 = ofN 1 by decide, cellOf_K]
    exact ⟨rfl, fun _ => .inl rfl⟩
  · -- `S`
    rw [show (0 : F) + 0 * ofN 2 + 0 * ofN 3 = ofN 0 by decide, cellOf_S]
    refine ⟨rfl, fun hb => ?_⟩
    rw [hb] at t5
    exact absurd t5 (by decide)


section

variable {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg : Table} (h : CompOK hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)
include h

theorem CompOK.memW {c : E} (hc : c ∈ witCons) {q : Nat} (hq : q < Wt.h) : c.eval (Wt.env q) = 0 :=
  h.wit.cons hc hq

/-- **An active witness row's cell**: in memory at its address, well
    formed, and in bit mode `K` or `A 0 1`. -/
theorem CompOK.witCell {q : Nat} (hq : q < Wt.h) (hact : Wt.pre q 1 = 1) :
    ∃ cell, (Wt.pre q 0).val < Mm.h ∧ (memOf Mm)[(Wt.pre q 0).val]? = some cell ∧
      cellOK (Wt.pre q 0).val cell = true ∧ (Wt.pre q 2 = 1 → cell = .K ∨ cell = .app 0 1) :=
  witCellG (fun c hc q hq => h.memW hc hq)
    (fun q hq hc => h.memHit ⟨(witAir N W, Wt), by simp [compTables], rfl, q, hq, _, List.mem_cons_self, rfl, rfl, hc⟩)
    (mem_addrC h.mem) h.mem_h hq hact
end

end Circuit
