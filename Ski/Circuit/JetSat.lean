import Ski.Circuit.JetCpuSat

/-!
# The honest POP and INSTW tables satisfy their AIRs

Each row is an instantiation's pop or written cell (`popRows_mem`,
`instwRows_mem`), or zero.  A pop's range check holds because it reads
below the counter; a cell's operands resolve as `Op.res` does.
-/

namespace Circuit

open B Air JetTable Mach

/-- Bits at columns `b0 + i` reassemble their value. -/
theorem bitsVal_eq {T : Table} {r b0 n : Nat} (hr : r < T.h)
    (hb : ∀ i, i < RANGE_BITS → T.main r (b0 + i) = ofN ((n / 2 ^ i) % 2)) (hn : n < 2 ^ 24) :
    ((List.range RANGE_BITS).foldl (fun v i => E.add v (E.mul (col (b0 + i)) (c (2 ^ i)))) zero).eval (T.env r) =
      ofN n := by
  have step : ∀ m, m ≤ RANGE_BITS →
      ((List.range m).foldl (fun v i => E.add v (E.mul (col (b0 + i)) (c (2 ^ i)))) zero).eval
        (T.env r) = ofN (n % 2 ^ m) := by
    intro m
    induction m with
    | zero => intro _; show ofN 0 = ofN (n % 1); rw [Nat.mod_one]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      show E.eval (T.env r) (List.foldl _ zero (List.range m)) + T.env r (.main 0 (b0 + m)) * ofN (2 ^ m) = _
      rw [ih (Nat.le_of_succ_le hm), env_main0 hr, hb m hm, ← ofN_mul, ← ofN_add, mod_two_pow_succ, Nat.mul_comm]
  rw [step RANGE_BITS (Nat.le_refl _), Nat.mod_eq_of_lt (show n < 2 ^ RANGE_BITS from hn)]

theorem bitsOf_get {n i : Nat} (hi : i < RANGE_BITS) : (bitsOf n).getD i 0 = ofN ((n / 2 ^ i) % 2) := by
  unfold bitsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem bitsOf_length (n : Nat) : (bitsOf n).length = RANGE_BITS := by
  unfold bitsOf; rw [List.length_map, List.length_range]

namespace JRun

variable (R : JRun)

/-- **A POP row is a pop** of some instantiation. -/
theorem popRows_mem {K : Nat} {rw : List F} (h : rw ∈ R.popRows K) :
    ∃ i g J j s x s', i < K ∧ R.instAt i = some (g, J) ∧
      (popsOf R.A (R.row i).ctr J.xs.length (R.row i).stk)[j]? = some (s, x, s') ∧
      rw = popRow i (R.row i).ctr j s x s' (usesOf J j) := by
  obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 h
  unfold popRowsAt at hm
  cases hn : R.instAt i with
  | none => rw [hn] at hm; cases hm
  | some p =>
    obtain ⟨g, J⟩ := p
    rw [hn] at hm
    obtain ⟨⟨⟨s, x, s'⟩, j⟩, hz, e⟩ := List.mem_map.1 hm
    obtain ⟨_, hj, hget⟩ := List.mem_zipIdx hz
    simp only [Nat.zero_add, Nat.sub_zero] at hj hget
    exact ⟨i, g, J, j, s, x, s', List.mem_range.1 hi, hn, by rw [List.getElem?_eq_getElem hj, hget], e.symm⟩

/-- **An INSTW row is a written cell** of some instantiation. -/
theorem instwRows_mem {K : Nat} {rw : List F} (h : rw ∈ R.instwRows K) :
    ∃ i g J j cl, i < K ∧ R.instAt i = some (g, J) ∧ (symCells J J.body 0).1[j]? = some cl ∧
      rw = instwRow i (R.row i).ctr g j (R.ps i J) cl := by
  obtain ⟨i, hi, hm⟩ := List.mem_flatMap.1 h
  unfold instwRowsAt at hm
  cases hn : R.instAt i with
  | none => rw [hn] at hm; cases hm
  | some p =>
    obtain ⟨g, J⟩ := p
    rw [hn] at hm
    obtain ⟨⟨cl, j⟩, hz, e⟩ := List.mem_map.1 hm
    obtain ⟨_, hj, hget⟩ := List.mem_zipIdx hz
    simp only [Nat.zero_add, Nat.sub_zero] at hj hget
    exact ⟨i, g, J, j, cl, List.mem_range.1 hi, hn, by rw [List.getElem?_eq_getElem hj, hget], e.symm⟩

/-- A row of a table built from rows: a listed row, or zero. -/
theorem ofRows_cases (rows : List (List F)) (q : Nat) :
    (∃ rw ∈ rows, ∀ c, ofRows rows q c = rw.getD c 0) ∨ ∀ c, ofRows rows q c = 0 := by
  rcases Nat.lt_or_ge q rows.length with h | h
  · refine .inl ⟨rows[q], List.getElem_mem h, fun c => ?_⟩
    unfold ofRows; rw [List.getD_eq_getElem?_getD (l := rows), List.getElem?_eq_getElem h]; rfl
  · refine .inr fun c => ?_
    unfold ofRows; rw [List.getD_eq_getElem?_getD (l := rows), List.getElem?_eq_none h]; rfl

/-- A pop reads a stack cell below the counter. -/
theorem pop_facts {i g : Nat} {J : Air.Jet} (h : R.instAt i = some (g, J)) {j s x s' : Nat}
    (hj : (popsOf R.A (R.row i).ctr J.xs.length (R.row i).stk)[j]? = some (s, x, s')) :
    s < (R.row i).ctr ∧ R.A[s]? = some (.cons x s') ∧ j < J.xs.length := by
  obtain ⟨hp, _, _, _⟩ := inst_spec h
  have hp' : popR (fun a => R.A[a]?) (R.row i).ctr J.xs.length (R.row i).stk = some (R.ps i J, R.rest i J) := hp
  obtain ⟨σ, ξ, _, _, _, hs⟩ := popsOf_spec (A := R.A) J.xs.length (R.row i).stk hp'
  have hjk : j < J.xs.length := by
    have := (List.getElem?_eq_some_iff.1 hj).1
    rw [popsOf_length hp'] at this; exact this
  obtain ⟨e1, e2⟩ := hs j hjk
  rw [hj] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl⟩ := e1
  unfold rd at e2
  split at e2
  · next hlt => exact ⟨hlt, e2, hjk⟩
  · cases e2

theorem popRow_get (i c j s x s' u : Nat) :
    (popRow i c j s x s' u).getD 0 0 = ofN i ∧ (popRow i c j s x s' u).getD 1 0 = ofN c ∧
    (popRow i c j s x s' u).getD 2 0 = ofN j ∧ (popRow i c j s x s' u).getD 3 0 = ofN s ∧
    (popRow i c j s x s' u).getD 4 0 = ofN x ∧ (popRow i c j s x s' u).getD 5 0 = ofN s' ∧
    (popRow i c j s x s' u).getD 6 0 = ofN u ∧ (popRow i c j s x s' u).getD 7 0 = 1 ∧
    ∀ b, b < RANGE_BITS → (popRow i c j s x s' u).getD (8 + b) 0 = ofN (((c - s - 1) / 2 ^ b) % 2) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun b hb => ?_⟩
  unfold popRow
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD.symm]
  simp only [List.length_cons, List.length_nil]
  rw [show 8 + b - 8 = b by omega]
  exact bitsOf_get hb

theorem bit_mod (n : Nat) : ofN (n % 2) * (ofN (n % 2) - 1) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

/-- **The honest POP table satisfies POP's AIR.** -/
theorem pop_sat {m0 : Mach} (hA : AcceptsJ R.A m0 R.roots R.jets R.k R.row) (hroots : RootsOK m0.heap R.roots R.jets)
    (hlen : R.A.length ≤ 2 ^ 24) {K HP : Nat} (hHP : 0 < HP) : Sat popAir (R.popTable K HP) := by
  refine ⟨hHP, fun e he q (hq : q < HP) => ?_⟩
  have cv : ∀ c, (col c).eval ((R.popTable K HP).env q) = ofRows (R.popRows K) q c := by
    intro c; show ofRows (R.popRows K) ((q + 0) % HP) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  simp only [popAir, popCons, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at he
  rcases ofRows_cases (R.popRows K) q with ⟨rw, hmem, hrw⟩ | hz
  · obtain ⟨i, g, J, j, s, x, s', _, hn, hget, rfl⟩ := R.popRows_mem hmem
    obtain ⟨hs, _, _⟩ := R.pop_facts hn hget
    have hi1 := (instAt_some hn).1
    have hc : (R.row i).ctr ≤ 2 ^ 24 := by
      have := ctr_le hA hroots i; rw [rowQ_lt (Nat.lt_of_succ_lt hi1)] at this; omega
    obtain ⟨g0, g1, _, g3, _, _, g6, g7, gb⟩ := popRow_get i (R.row i).ctr j s x s' (usesOf J j)
    rcases he with ((rfl | rfl) | ⟨b, hb, rfl⟩) | rfl
    · simp only [B.bool, E.eval, cv, hrw, g7, B.one, B.c, ofN_one]; decide
    · simp only [E.eval, cv, hrw, g7, g6, B.one, B.c, ofN_one]
      rw [sub_self', mul_zero']
    · simp only [B.bool, E.eval, cv, hrw, gb b hb, B.one, B.c, ofN_one]
      exact bit_mod _
    · have hv := bitsVal_eq (T := R.popTable K HP) (r := q) (b0 := 8) (n := (R.row i).ctr - s - 1) hq
        (fun b hb => by show ofRows _ q (8 + b) = _; rw [hrw, gb b hb]) (by omega)
      simp only [E.eval, cv, hrw, g7, g1, g3, B.one, B.c, ofN_one, one_mul']
      rw [show popVal.eval ((R.popTable K HP).env q) = ofN ((R.row i).ctr - s - 1) from hv]
      have e : (R.row i).ctr = ((R.row i).ctr - s - 1) + s + 1 := by omega
      rw [show ofN (R.row i).ctr = ofN ((R.row i).ctr - s - 1) + ofN s + 1 by
        rw [← ofN_one, ← ofN_add, ← ofN_add]; exact congrArg ofN e]
      exact range_identity _ _
  · rcases he with ((rfl | rfl) | ⟨b, hb, rfl⟩) | rfl
    · simp only [B.bool, E.eval, cv, hz, zero_mul']
    · simp only [E.eval, cv, hz, zero_mul']
    · simp only [B.bool, E.eval, cv, hz, zero_mul']
    · simp only [E.eval, cv, hz, zero_mul']

theorem instwRow_some (i c g j t : Nat) (ps : List Nat) (oa ob : Op) :
    instwRow i c g j ps (t, some (oa, ob)) = [ofN i, ofN c, ofN g, ofN j, ofN t] ++ opCols oa ++ opCols ob ++
      [ofN (oa.res c ps), ofN (ob.res c ps), ofN (argVal ps oa), ofN (argVal ps ob), 1] := by
  unfold instwRow tmplRow
  simp only [JetTable.cellOf, cellFields, List.append_assoc, List.cons_append, List.nil_append]

theorem instwRow_none (i c g j t : Nat) (ps : List Nat) (ht : t < 3) :
    instwRow i c g j ps (t, none) = [ofN i, ofN c, ofN g, ofN j, ofN t, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;> rfl

/-- An operand resolved honestly. -/
theorem resolve_honest (o : Op) (c : Nat) (ps : List Nat) :
    ofN (o.res c ps) = (opCols o).getD 0 0 * (ofN c + (opCols o).getD 3 0) + (opCols o).getD 1 0 * ofN (argVal ps o) +
      (opCols o).getD 2 0 * (opCols o).getD 3 0 := by
  cases o with
  | local_ j =>
    show ofN (c + j) = ofN 1 * (ofN c + ofN j) + ofN 0 * ofN 0 + ofN 0 * ofN j
    rw [ofN_add, ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', add_zero', add_zero']
  | arg i =>
    show ofN (ps.getD i 0) = ofN 0 * (ofN c + ofN i) + ofN 1 * ofN (ps.getD i 0) + ofN 0 * ofN i
    rw [ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', zero_add', add_zero']
  | glob a =>
    show ofN a = ofN 0 * (ofN c + ofN a) + ofN 0 * ofN 0 + ofN 1 * ofN a
    rw [ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', zero_add', zero_add']

theorem instwRow_some_get (i c g j t : Nat) (ps : List Nat) (oa ob : Op) :
    (∀ q, q < 4 → (instwRow i c g j ps (t, some (oa, ob))).getD (5 + q) 0 = (opCols oa).getD q 0 ∧
      (instwRow i c g j ps (t, some (oa, ob))).getD (9 + q) 0 = (opCols ob).getD q 0) ∧
    (instwRow i c g j ps (t, some (oa, ob))).getD 1 0 = ofN c ∧
    (instwRow i c g j ps (t, some (oa, ob))).getD 13 0 = ofN (oa.res c ps) ∧
    (instwRow i c g j ps (t, some (oa, ob))).getD 14 0 = ofN (ob.res c ps) ∧
    (instwRow i c g j ps (t, some (oa, ob))).getD 15 0 = ofN (argVal ps oa) ∧
    (instwRow i c g j ps (t, some (oa, ob))).getD 16 0 = ofN (argVal ps ob) ∧
    (instwRow i c g j ps (t, some (oa, ob))).getD 17 0 = 1 := by
  rw [instwRow_some]
  refine ⟨fun q hq => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases (show q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 by omega) with rfl | rfl | rfl | rfl <;>
      cases oa <;> cases ob <;> exact ⟨rfl, rfl⟩
  all_goals (cases oa <;> cases ob <;> rfl)

/-- **The honest INSTW table satisfies INSTW's AIR.** -/
theorem instw_sat {K HW : Nat} (hHW : 0 < HW) : Sat instwAir (R.instwTable K HW) := by
  refine ⟨hHW, fun e he q (hq : q < HW) => ?_⟩
  have cv : ∀ c, (col c).eval ((R.instwTable K HW).env q) = ofRows (R.instwRows K) q c := by
    intro c; show ofRows (R.instwRows K) ((q + 0) % HW) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hq]
  simp only [instwAir, instwCons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases ofRows_cases (R.instwRows K) q with ⟨rw, hmem, hrw⟩ | hz
  · obtain ⟨i, g, J, j, cl, _, _, hcl, rfl⟩ := R.instwRows_mem hmem
    have hm : cl ∈ (symCells J J.body 0).1 := List.mem_of_getElem? hcl
    obtain ⟨t, ops⟩ := cl
    rcases symCells_cells J J.body 0 _ hm with ⟨hno, ht⟩ | ⟨_, oa, ob, hso⟩
    · simp only at hno ht
      subst hno
      have v := instwRow_none i (R.row i).ctr g j t (R.ps i J) ht
      have z : ∀ c, 5 ≤ c → c < 17 → ofRows (R.instwRows K) q c = 0 := by
        intro c h5 h17; rw [hrw, v]
        rcases (show c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨
          c = 15 ∨ c = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      have o17 : ofRows (R.instwRows K) q 17 = 1 := by rw [hrw, v]; rfl
      rcases he with (rfl | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl)) |
        (rfl | rfl)
      · simp only [B.bool, E.eval, cv, o17, B.one, B.c, ofN_one]; decide
      all_goals
        simp only [B.bool, B.eq, resolveE, E.eval, cv, o17, B.one, B.c, ofN_one,
          z 5 (by decide) (by decide), z 6 (by decide) (by decide), z 7 (by decide) (by decide),
          z 8 (by decide) (by decide), z 9 (by decide) (by decide), z 10 (by decide) (by decide),
          z 11 (by decide) (by decide), z 12 (by decide) (by decide), z 13 (by decide) (by decide),
          z 14 (by decide) (by decide), z 15 (by decide) (by decide), z 16 (by decide) (by decide),
          zero_mul', mul_zero', add_zero']
        try decide
    · simp only at hso
      subst hso
      obtain ⟨hops, h1, h13, h14, h15, h16, h17⟩ := instwRow_some_get i (R.row i).ctr g j t (R.ps i J) oa ob
      have o : ∀ c, ofRows (R.instwRows K) q c = (instwRow i (R.row i).ctr g j (R.ps i J) (t, some (oa, ob))).getD c 0 :=
        fun c => by rw [hrw]
      have a0 := (hops 0 (by decide)).1
      have a1 := (hops 1 (by decide)).1
      have a2 := (hops 2 (by decide)).1
      have a3 := (hops 3 (by decide)).1
      have b0 := (hops 0 (by decide)).2
      have b1 := (hops 1 (by decide)).2
      have b2 := (hops 2 (by decide)).2
      have b3 := (hops 3 (by decide)).2
      simp only [Nat.add_zero] at a0 b0
      rcases he with (rfl | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl)) |
        (rfl | rfl)
      · simp only [B.bool, E.eval, cv, o, h17, B.one, B.c, ofN_one]; decide
      · simp only [B.bool, E.eval, cv, o, a0, B.one, B.c, ofN_one]; exact opCols_bit _ 0 (by decide)
      · simp only [E.eval, cv, o, h17, B.one, B.c, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cv, o, a1, B.one, B.c, ofN_one]; exact opCols_bit _ 1 (by decide)
      · simp only [E.eval, cv, o, h17, B.one, B.c, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cv, o, a2, B.one, B.c, ofN_one]; exact opCols_bit _ 2 (by decide)
      · simp only [E.eval, cv, o, h17, B.one, B.c, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cv, o, b0, B.one, B.c, ofN_one]; exact opCols_bit _ 0 (by decide)
      · simp only [E.eval, cv, o, h17, B.one, B.c, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cv, o, b1, B.one, B.c, ofN_one]; exact opCols_bit _ 1 (by decide)
      · simp only [E.eval, cv, o, h17, B.one, B.c, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cv, o, b2, B.one, B.c, ofN_one]; exact opCols_bit _ 2 (by decide)
      · simp only [E.eval, cv, o, h17, B.one, B.c, ofN_one, sub_self', mul_zero']
      · simp only [B.eq, resolveE, E.eval, cv, o, h13, h1, h15, a0, a1, a2, a3]
        rw [resolve_honest oa (R.row i).ctr (R.ps i J), sub_self']
      · simp only [B.eq, resolveE, E.eval, cv, o, h14, h1, h16, b0, b1, b2, b3]
        rw [resolve_honest ob (R.row i).ctr (R.ps i J), sub_self']
  · rcases he with (rfl | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl) | (rfl | rfl)) |
      (rfl | rfl)
    all_goals
      simp only [B.bool, B.eq, resolveE, E.eval, cv, hz, zero_mul', mul_zero', add_zero', B.one, B.c]
      try decide

end JRun

end Circuit
