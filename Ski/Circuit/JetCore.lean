import Ski.Circuit.JetSound

/-!
# An instantiation row, from the buses' facts

What makes an instantiation row `Air.instRow`, gathered as `JetCore`: the
POP and INSTW tables' constraints, the row counter, the memory's
addresses, what the lookups find (`popMem`, `instwMem`, `argHit`,
`tmplHit`, `rootsHit`, `hdrHit`), the flows of `POPCH` and `WCH` at an
instantiation, and an instantiation row's kind and next registers.  The
jet circuit gives it (`JetOK.core`), and so does the probe circuit, whose
CPU has more kinds and more messages; `JetCore.inst` then serves both.
-/

namespace Circuit

open B Air JetTable Mach

/-- **What an instantiation row needs of an accepted proof.** -/
structure JetCore (heap : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet) (C Mm Po Iw : Table) :
    Prop where
  po : Sat popAir Po
  iw : Sat instwAir Iw
  clk : ∀ r, r < C.h → C.main r J_CLK = ofN r
  memH : Mm.h ≤ 2 ^ 27
  popH : Po.h ≤ 2 ^ 27
  instwH : Iw.h ≤ 2 ^ 27
  addr : ∀ m, m < Mm.h → Mm.main m 0 = ofN m
  jetsLe : jets.length ≤ 2 ^ 27
  heapLe : heap.length ≤ 2 ^ 27
  popMem : ∀ q, q < Po.h → Po.main q 7 = 1 → ∃ m, m < Mm.h ∧
    [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = [Po.main q 3, ofN 5, Po.main q 4, Po.main q 5]
  instwMem : ∀ w, w < Iw.h → Iw.main w 17 = 1 → ∃ m, m < Mm.h ∧
    [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] =
      [Iw.main w 1 + Iw.main w 3, Iw.main w 4, Iw.main w 13, Iw.main w 14]
  argHit : ∀ v : List F,
    ((∃ r, r < C.h ∧ C.main r J_RA = 1 ∧ v = [C.main r J_CLK, C.main r J_RV, C.main r J_XROOT]) ∨
     (∃ w, w < Iw.h ∧ Iw.main w 6 = 1 ∧ v = [Iw.main w 0, Iw.main w 8, Iw.main w 15]) ∨
     (∃ w, w < Iw.h ∧ Iw.main w 10 = 1 ∧ v = [Iw.main w 0, Iw.main w 12, Iw.main w 16])) →
    ∃ q, q < Po.h ∧ Po.main q 7 = 1 ∧ [Po.main q 0, Po.main q 2, Po.main q 4] = v
  tmplHit : ∀ w, w < Iw.h → Iw.main w 17 = 1 → ∃ J g j cl, jets[g]? = some J ∧
    (symCells J J.body 0).1[j]? = some cl ∧ (List.range 11).map (fun i => Iw.main w (2 + i)) = tmplRow g j cl
  rootsHit : ∀ r, r < C.h → C.main r (SEL + 11) = 1 →
    ∃ a g, (a, g) ∈ roots ∧ C.main r HD = ofN a ∧ C.main r J_G = ofN g
  hdrHit : ∀ r, r < C.h → C.main r (SEL + 11) = 1 → ∃ J g, jets[g]? = some J ∧
    [C.main r J_G, C.main r J_K, C.main r J_N, C.main r J_RL, C.main r J_RA, C.main r J_RG, C.main r J_RV] =
      hdrRow J g
  popConserve : ∀ r0, r0 < C.h → C.main r0 (SEL + 11) = 1 → ∀ c' : F,
    (popEdges Po (ofN r0) c').Conserve (popStart C r0 c') (popEnd C r0 c')
  wchConserve : ∀ r0, r0 < C.h → C.main r0 (SEL + 11) = 1 →
    (wchEdges Iw (ofN r0) (C.main r0 CTR) (C.main r0 J_G)).Conserve (some ((0 : F), [])) (some (C.main r0 J_N, []))
  instNext : ∀ r, r + 1 < C.h → C.main r (SEL + 11) = 1 →
    C.main (r + 1) HD = jetHd.eval (C.env r) ∧ C.main (r + 1) STK = C.main r J_REST ∧
      C.main (r + 1) CTR = C.main r CTR + C.main r J_N

section

variable {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Po Iw : Table}
  (h : JetCore heap roots jets C Mm Po Iw)
include h

/-- A memory message, decoded: the cell at its address. -/
theorem JetCore.cell {a t x y : F}
    (hm : ∃ m, m < Mm.h ∧ [Mm.main m 0, Mm.main m 1, Mm.main m 2, Mm.main m 3] = [a, t, x, y]) :
    a.val < Mm.h ∧ (memOf Mm)[a.val]? = some (cellOf t x y) := by
  obtain ⟨m, hm, e⟩ := hm
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  have hmP : m < P := Nat.lt_of_lt_of_le hm (Nat.le_trans h.memH (by decide))
  rw [h.addr m hm] at e0
  rw [← e0, val_ofN hmP, memOf_get hm, e1, e2, e3]
  exact ⟨hm, rfl⟩

/-- **An active POP row reads a stack cell below its counter.** -/
theorem JetCore.popRead {q : Nat} (hq : q < Po.h) (ha : Po.main q 7 = 1) :
    (Po.main q 3).val < (Po.main q 1).val ∧
    rd (memOf Mm) (Po.main q 1).val (Po.main q 3).val = some (.cons (Po.main q 4).val (Po.main q 5).val) := by
  have cv := col_eval hq
  obtain ⟨hlt, hget⟩ := h.cell (h.popMem q hq ha)
  rw [cellOf_cons] at hget
  -- the range check: `c = s + 1 + v`, with no wrap
  have hc := h.po.2 (.mul (col 7) (.sub (.sub (.sub (col 1) (col 3)) one) popVal))
    (List.mem_append_right _ List.mem_cons_self) q hq
  simp only [E.eval, cv, ha, one_mul', B.one, B.c, ofN_one] at hc
  have e := sub_eq_zero hc
  have hv := bitsVal_lt hq 8 24 (Nat.le_refl _) (fun i hi => col_bit h.po (i := 8 + i)
    (by simp only [popAir, popCons, List.mem_append]; exact .inl (.inr (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
    hq)
  have hv' : (popVal.eval (Po.env q)).val < 2 ^ 24 := hv
  have hm := h.memH
  have hctr : Po.main q 1 = (Po.main q 3 + 1) + popVal.eval (Po.env q) := by rw [← e, add_sub_cancel3]
  have h1 : (Po.main q 3 + 1).val = (Po.main q 3).val + 1 :=
    val_add_of_lt (by have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big; show _ + 1 < P; omega)
  have hval : (Po.main q 1).val = (Po.main q 3).val + 1 + (popVal.eval (Po.env q)).val := by
    rw [hctr, val_add_of_lt (by rw [h1]; have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big; omega), h1]
  refine ⟨by omega, ?_⟩
  unfold rd
  rw [if_pos (by omega), hget]

/-- **An instantiation's pops are one path of POP rows**, and they are the
    only active POP rows at its counter. -/
theorem JetCore.popPath {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) {k : Nat} (hk : k < 2 ^ 24)
    (hK : C.main r J_K = ofN k) :
    ∃ (e : Nat → Nat) (sF : Nat → F), sF 0 = C.main r STK ∧ sF k = C.main r J_REST ∧
      (∀ i, i < k → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = ofN r ∧
        Po.main (e i) 1 = C.main r CTR ∧ Po.main (e i) 2 = ofN i ∧ Po.main (e i) 3 = sF i ∧
        Po.main (e i) 5 = sF (i + 1)) ∧
      ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q := by
  have hH : Po.h < P := Nat.lt_of_le_of_lt h.popH (by decide)
  have hkP : k < P := Nat.lt_trans hk (by decide)
  have hc : (popEdges Po (ofN r) (C.main r CTR)).Conserve (some ((0 : F), [C.main r STK]))
      (some (ofN k, [C.main r J_REST])) := by
    have := h.popConserve r hr hi (C.main r CTR)
    unfold popStart popEnd at this
    rw [if_pos rfl, if_pos rfl, hK] at this
    exact this
  obtain ⟨e, st, h0, hkst, hp, hu⟩ := Edges.path _ hH hkP hc
  refine ⟨e, fun i => (st i).headD 0, by show (st 0).headD 0 = _; rw [h0]; rfl,
    by show (st k).headD 0 = _; rw [hkst]; rfl, fun i hi => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hp i hi
    have ha : (decide (Po.main (e i) 7 = 1) && decide (Po.main (e i) 0 = ofN r) &&
        decide (Po.main (e i) 1 = C.main r CTR)) = true := h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    refine ⟨h1, ha.1.1, ha.1.2, ha.2, h3, ?_, ?_⟩
    · show Po.main (e i) 3 = (st i).headD 0
      have : [Po.main (e i) 3] = st i := h4
      rw [← this]; rfl
    · show Po.main (e i) 5 = (st (i + 1)).headD 0
      have : [Po.main (e i) 5] = st (i + 1) := h5
      rw [← this]; rfl
  · intro q hq ha hclk
    have hact : ∀ c' : F, Po.main q 1 = c' → (popEdges Po (ofN r) c').act q = true := by
      intro c' hc'
      show (decide (Po.main q 7 = 1) && decide (Po.main q 0 = ofN r) && decide (Po.main q 1 = c')) = true
      rw [decide_eq_true ha, decide_eq_true hclk, decide_eq_true hc']; rfl
    rcases (inferInstance : Decidable (Po.main q 1 = C.main r CTR)) with hc0 | hc0
    · exfalso
      have hcn := h.popConserve r hr hi (Po.main q 1)
      unfold popStart popEnd at hcn
      rw [if_neg hc0, if_neg hc0] at hcn
      have hz := Edges.noFlow _ hH hcn q hq
      rw [hact (Po.main q 1) rfl] at hz
      cases hz
    · exact hu q hq (hact _ hc0)

/-- **The pops, read**: along the path, `popR` pops the POP rows' arguments. -/
theorem JetCore.popR_path {r k : Nat} {e : Nat → Nat} {sF : Nat → F}
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 7 = 1 ∧ Po.main (e i) 0 = ofN r ∧
        Po.main (e i) 1 = C.main r CTR ∧ Po.main (e i) 2 = ofN i ∧ Po.main (e i) 3 = sF i ∧
        Po.main (e i) 5 = sF (i + 1)) :
    ∀ m, m ≤ k → popR (fun a => (memOf Mm)[a]?) (C.main r CTR).val m (sF (k - m)).val =
      some ((List.range m).map (fun i => (Po.main (e (k - m + i)) 4).val), (sF k).val)
  | 0, _ => by show some ([], (sF (k - 0)).val) = _; rw [Nat.sub_zero]; rfl
  | m + 1, hm => by
    have hj : k - (m + 1) < k := by omega
    obtain ⟨h1, h2, _, h4, _, h6, h7⟩ := hp _ hj
    obtain ⟨_, hrd⟩ := h.popRead h1 h2
    rw [h4, h6, h7, show k - (m + 1) + 1 = k - m by omega] at hrd
    show (match rdG (fun a => (memOf Mm)[a]?) (C.main r CTR).val (sF (k - (m + 1))).val with
      | some (.cons x r') => (popR (fun a => (memOf Mm)[a]?) (C.main r CTR).val m r').map fun (p : List Nat × Nat) => (x :: p.1, p.2)
      | _ => none) = _
    rw [← rd_G, hrd]
    dsimp only
    rw [JetCore.popR_path hp m (Nat.le_of_succ_le hm)]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    show (Po.main (e (k - m + i)) 4).val = (Po.main (e (k - (m + 1) + (i + 1))) 4).val
    rw [show k - (m + 1) + (i + 1) = k - m + i by omega]

/-- **An argument lookup at an instantiation's counter finds its pops.** -/
theorem JetCore.argPath {r k : Nat} {e : Nat → Nat}
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) {v x : F}
    (hit : ∃ q, q < Po.h ∧ Po.main q 7 = 1 ∧ [Po.main q 0, Po.main q 2, Po.main q 4] = [ofN r, v, x]) :
    ∃ i, i < k ∧ v = ofN i ∧ x = Po.main (e i) 4 := by
  obtain ⟨q, hq, ha, hf⟩ := hit
  simp only [List.cons.injEq, and_true] at hf
  obtain ⟨i, hi, hiq⟩ := hu q hq ha hf.1
  subst hiq
  exact ⟨i, hi, by rw [← hf.2.1, (hp i hi).2], hf.2.2.symm⟩

/-- **An instantiation's writes are one path of INSTW rows.** -/
theorem JetCore.wchPath {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) {n : Nat} (hn : n < 2 ^ 24)
    (hN : C.main r J_N = ofN n) :
    ∃ w : Nat → Nat, ∀ j, j < n → w j < Iw.h ∧ Iw.main (w j) 17 = 1 ∧ Iw.main (w j) 0 = ofN r ∧
      Iw.main (w j) 1 = C.main r CTR ∧ Iw.main (w j) 2 = C.main r J_G ∧ Iw.main (w j) 3 = ofN j := by
  have hH : Iw.h < P := Nat.lt_of_le_of_lt h.instwH (by decide)
  have hnP : n < P := Nat.lt_trans hn (by decide)
  have hc := h.wchConserve r hr hi
  rw [hN] at hc
  obtain ⟨w, _, _, _, hp, _⟩ := Edges.path _ hH hnP hc
  refine ⟨w, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3, _, _⟩ := hp j hj
  have ha : (decide (Iw.main (w j) 17 = 1) && decide (Iw.main (w j) 0 = ofN r) &&
      decide (Iw.main (w j) 1 = C.main r CTR) && decide (Iw.main (w j) 2 = C.main r J_G)) = true := h2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ⟨h1, ha.1.1.1, ha.1.1.2, ha.1.2, ha.2, h3⟩

/-- **An INSTW operand resolves** as `Op.res` does: a written cell at the
    counter plus its offset, a popped argument, or a public address. -/
theorem JetCore.resolve {r k : Nat} {e : Nat → Nat}
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) (hk : k < 2 ^ 24)
    {q : Nat} (hq : q < Iw.h) (hclk : Iw.main q 0 = ofN r)
    {fl fa fg v xc out : Nat} (hcons : eq (col out) (resolveE fl fa fg v xc) ∈ instwCons)
    (hI : Iw.main q fa = 1 → ∃ q', q' < Po.h ∧ Po.main q' 7 = 1 ∧
      [Po.main q' 0, Po.main q' 2, Po.main q' 4] = [Iw.main q 0, Iw.main q v, Iw.main q xc])
    {o : Op} (hops : [Iw.main q fl, Iw.main q fa, Iw.main q fg, Iw.main q v] = opCols o) (hs : opSmall o = true)
    (hc : (Iw.main q 1).val < 2 ^ 27) :
    (Iw.main q out).val = o.res (Iw.main q 1).val ((List.range k).map (fun i => (Po.main (e i) 4).val)) := by
  have cv := col_eval hq
  have hr := h.iw.2 _ hcons q hq
  simp only [B.eq, resolveE, E.eval, cv] at hr
  have e0 := sub_eq_zero hr
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  cases o with
  | local_ j =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', add_zero', add_zero'] at e0
    have hj : j < 2 ^ 24 := of_decide_eq_true hs
    rw [e0, val_add_nat (by omega)]; rfl
  | arg i =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, ofN_one, ofN_zero, zero_mul', one_mul', zero_mul', zero_add', add_zero'] at e0
    have hi : i < 2 ^ 24 := of_decide_eq_true hs
    obtain ⟨i', hi', hv, hx⟩ := h.argPath (fun i hi => hp i hi) hu (v := Iw.main q v) (x := Iw.main q xc)
      (by rw [← hclk]; exact hI (by rw [h2]; rfl))
    rw [h4] at hv
    have := ofN_inj (Nat.lt_trans hi (by decide)) (Nat.lt_trans (Nat.lt_trans hi' hk) (by decide)) hv
    subst this
    rw [e0, hx]
    show _ = ((List.range k).map (fun i => (Po.main (e i) 4).val)).getD i 0
    rw [getD_range_map _ hi']
  | glob a =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, zero_mul', zero_mul', one_mul', zero_add', zero_add'] at e0
    have ha : a < 2 ^ 24 := of_decide_eq_true hs
    rw [e0, val_ofN (Nat.lt_trans ha (by decide))]; rfl

/-- **The instantiation's root resolves** as `Op.res` does. -/
theorem JetCore.rootRes {r k : Nat} {e : Nat → Nat} (hr : r < C.h)
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) (hk : k < 2 ^ 24)
    {o : Op} (hops : [C.main r J_RL, C.main r J_RA, C.main r J_RG, C.main r J_RV] = opCols o)
    (hs : opSmall o = true) (hc : ∀ j, o = .local_ j → (C.main r CTR).val < 2 ^ 27) :
    (jetHd.eval (C.env r)).val = o.res (C.main r CTR).val ((List.range k).map (fun i => (Po.main (e i) 4).val)) := by
  have cv := col_eval hr
  simp only [jetHd, E.eval, cv]
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  cases o with
  | local_ j =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', add_zero', add_zero']
    have hj : j < 2 ^ 24 := of_decide_eq_true hs
    have hc' := hc j rfl
    rw [val_add_nat (by omega)]; rfl
  | arg i =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, ofN_one, ofN_zero, zero_mul', zero_mul', one_mul', zero_add', zero_add']
    have hi : i < 2 ^ 24 := of_decide_eq_true hs
    obtain ⟨i', hi', hv, hx⟩ := h.argPath (fun i hi => hp i hi) hu (v := C.main r J_RV) (x := C.main r J_XROOT)
      (by rw [← h.clk r hr]; exact h.argHit _ (.inl ⟨r, hr, by rw [h2]; rfl, rfl⟩))
    rw [h4] at hv
    have := ofN_inj (Nat.lt_trans hi (by decide)) (Nat.lt_trans (Nat.lt_trans hi' hk) (by decide)) hv
    subst this
    rw [hx]
    show _ = ((List.range k).map (fun i => (Po.main (e i) 4).val)).getD i 0
    rw [getD_range_map _ hi']
  | glob a =>
    simp only [opCols, List.cons.injEq, and_true] at hops
    obtain ⟨h1, h2, h3, h4⟩ := hops
    rw [h1, h2, h3, h4, ofN_one, ofN_zero, zero_mul', zero_mul', one_mul', zero_add', add_zero']
    have ha : a < 2 ^ 24 := of_decide_eq_true hs
    rw [val_ofN (Nat.lt_trans ha (by decide))]; rfl

/-- **The instantiation's cells are in memory**: at the counter plus `j`,
    the template's `j`-th cell, resolved. -/
theorem JetCore.cellAt {r k g : Nat} {J : Air.Jet} {e w : Nat → Nat} (hjl : jets.length ≤ 2 ^ 27)
    (hJ : jets[g]? = some J) (hG : C.main r J_G = ofN g)
    (hn : (symCells J J.body 0).1.length < 2 ^ 24)
    (hops : ((symCells J J.body 0).1.all fun cl => match cl.2 with
      | some (a, b) => opSmall a && opSmall b
      | none => true) = true)
    (hp : ∀ i, i < k → e i < Po.h ∧ Po.main (e i) 2 = ofN i)
    (hu : ∀ q, q < Po.h → Po.main q 7 = 1 → Po.main q 0 = ofN r → ∃ i, i < k ∧ e i = q) (hk : k < 2 ^ 24)
    (hw : ∀ j, j < (symCells J J.body 0).1.length → w j < Iw.h ∧ Iw.main (w j) 17 = 1 ∧
      Iw.main (w j) 0 = ofN r ∧ Iw.main (w j) 1 = C.main r CTR ∧ Iw.main (w j) 2 = C.main r J_G ∧
      Iw.main (w j) 3 = ofN j)
    (hc : (C.main r CTR).val < 2 ^ 27) {j : Nat} (hj : j < (symCells J J.body 0).1.length) :
    (memOf Mm)[(C.main r CTR).val + j]? =
      some (JetTable.cellOf (C.main r CTR).val ((List.range k).map (fun i => (Po.main (e i) 4).val))
        (symCells J J.body 0).1[j]) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hw j hj
  have cv := col_eval h1
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  -- the template row
  obtain ⟨J', g', j', cl, hJ', hcl, hrow⟩ := h.tmplHit (w j) h1 h2
  have hx : ∀ i, i < 11 → Iw.main (w j) (2 + i) = (tmplRow g' j' cl).getD i 0 := fun i hi => by
    rw [← hrow, getD_range_mapF _ hi]
  have hg' : g' < jets.length := (List.getElem?_eq_some_iff.1 hJ').1
  have hg : g < jets.length := (List.getElem?_eq_some_iff.1 hJ).1
  obtain ⟨tag, ops⟩ := cl
  have t0 : (tmplRow g' j' (tag, ops)).getD 0 0 = ofN g' := by cases ops <;> rfl
  have t1 : (tmplRow g' j' (tag, ops)).getD 1 0 = ofN j' := by cases ops <;> rfl
  have t2 : (tmplRow g' j' (tag, ops)).getD 2 0 = ofN tag := by cases ops <;> rfl
  have e0 := hx 0 (by decide); rw [t0, h5, hG] at e0
  have egg := ofN_inj (Nat.lt_of_lt_of_le hg (Nat.le_trans hjl (by decide))) (Nat.lt_of_lt_of_le hg' (Nat.le_trans hjl (by decide))) e0
  subst egg
  rw [hJ] at hJ'
  cases hJ'
  have hj' : j' < (symCells J J.body 0).1.length := (List.getElem?_eq_some_iff.1 hcl).1
  have e1 := hx 1 (by decide); rw [t1, h6] at e1
  have ejj := ofN_inj (Nat.lt_trans (Nat.lt_trans hj hn) (by decide)) (Nat.lt_trans (Nat.lt_trans hj' hn) (by decide)) e1
  subst ejj
  have hclj : (symCells J J.body 0).1[j] = (tag, ops) := (List.getElem?_eq_some_iff.1 hcl).2
  rw [hclj]
  have e2 := hx 2 (by decide); rw [t2] at e2
  -- the write
  obtain ⟨_, hget⟩ := h.cell (h.instwMem (w j) h1 h2)
  rw [h4, h6, val_add_nat (by omega), e2] at hget
  rw [hget]
  congr 1
  have hmem : ((tag, ops) : Nat × Option (Op × Op)) ∈ (symCells J J.body 0).1 := by
    rw [← hclj]; exact List.getElem_mem hj
  rcases symCells_cells J J.body 0 _ hmem with ⟨hno, htag⟩ | ⟨htag, oa, ob, hso⟩
  · -- a leaf: its operand columns are zero
    simp only at hno htag
    subst hno
    have z : ∀ i, 3 ≤ i → i < 11 → Iw.main (w j) (2 + i) = 0 := by
      intro i h3 h11
      rw [hx i h11]
      show ([ofN g, ofN j, ofN tag] ++ List.replicate 8 (ofN 0)).getD i 0 = 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
      simp only [List.length_cons, List.length_nil]
      rw [if_pos (by omega)]; rfl
    have ra := h.iw.2 _ (show eq (col 13) (resolveE 5 6 7 8 15) ∈ instwCons by simp [instwCons]) (w j) h1
    have rb := h.iw.2 _ (show eq (col 14) (resolveE 9 10 11 12 16) ∈ instwCons by simp [instwCons]) (w j) h1
    simp only [B.eq, resolveE, E.eval, cv, z 3 (by decide) (by decide), z 4 (by decide) (by decide),
      z 5 (by decide) (by decide), z 7 (by decide) (by decide), z 8 (by decide) (by decide),
      z 9 (by decide) (by decide), zero_mul', add_zero'] at ra rb
    rw [sub_eq_zero ra, sub_eq_zero rb]
    rcases (show tag = 0 ∨ tag = 1 ∨ tag = 2 by omega) with rfl | rfl | rfl <;> rfl
  · -- an application: its operands resolve
    simp only at htag hso
    subst htag hso
    have hs := List.all_eq_true.1 hops _ hmem
    simp only [Bool.and_eq_true] at hs
    have hA : [Iw.main (w j) 5, Iw.main (w j) 6, Iw.main (w j) 7, Iw.main (w j) 8] = opCols oa := by
      rw [hx 3 (by decide), hx 4 (by decide), hx 5 (by decide), hx 6 (by decide)]
      show [([ofN g, ofN j, ofN 3] ++ opCols oa ++ opCols ob).getD 3 0, _, _, _] = _
      cases oa <;> cases ob <;> rfl
    have hB : [Iw.main (w j) 9, Iw.main (w j) 10, Iw.main (w j) 11, Iw.main (w j) 12] = opCols ob := by
      rw [hx 7 (by decide), hx 8 (by decide), hx 9 (by decide), hx 10 (by decide)]
      show [([ofN g, ofN j, ofN 3] ++ opCols oa ++ opCols ob).getD 7 0, _, _, _] = _
      cases oa <;> cases ob <;> rfl
    have ea := h.resolve hp hu hk h1 h3 (show eq (col 13) (resolveE 5 6 7 8 15) ∈ instwCons by simp [instwCons])
      (fun hf => h.argHit _ (.inr (.inl ⟨w j, h1, hf, rfl⟩))) hA hs.1 (by rw [h4]; exact hc)
    have eb := h.resolve hp hu hk h1 h3 (show eq (col 14) (resolveE 9 10 11 12 16) ∈ instwCons by simp [instwCons])
      (fun hf => h.argHit _ (.inr (.inr ⟨w j, h1, hf, rfl⟩))) hB hs.2 (by rw [h4]; exact hc)
    rw [h4] at ea eb
    show Circuit.cellOf (ofN 3) _ _ = _
    rw [cellOf_app, ea, eb]
    rfl

/-- **An instantiation row is `Air.instRow`** for the jet at a listed root,
    given licensed roots and a jet table whose numbers fit. -/
theorem JetCore.inst {r : Nat} (hr1 : r + 1 < C.h) (hi : C.main r (SEL + 11) = 1)
    (hroots : RootsOK heap roots jets) (hfit : jets.all jetFitB = true) :
    ∃ g J, ((rowOf C r).hd, g) ∈ roots ∧ jets[g]? = some J ∧
      instRow (memOf Mm) J (rowOf C r) = some (rowOf C (r + 1)) := by
  have hr : r < C.h := Nat.lt_of_succ_lt hr1
  have hP : 2 ^ 27 + 2 ^ 24 < P := by decide
  -- the kind
  obtain ⟨m1, m2, m3⟩ := h.instNext r hr1 hi
  -- the root and the header
  obtain ⟨a, g1, hmem, hHD, hG1⟩ := h.rootsHit r hr hi
  obtain ⟨J, g, hJ, hhdr⟩ := h.hdrHit r hr hi
  obtain ⟨J1, hJ1, _, htm, _⟩ := hroots a g1 hmem
  have hjl := h.jetsLe
  have hg1 : g1 < jets.length := (List.getElem?_eq_some_iff.1 hJ1).1
  have hg : g < jets.length := (List.getElem?_eq_some_iff.1 hJ).1
  simp only [hdrRow, List.cons_append, List.nil_append, List.cons.injEq] at hhdr
  obtain ⟨hG, hK, hN, hops⟩ := hhdr
  have e1 : g1 = g := ofN_inj (Nat.lt_of_lt_of_le hg1 (Nat.le_trans hjl (by decide)))
    (Nat.lt_of_lt_of_le hg (Nat.le_trans hjl (by decide))) (hG1.symm.trans hG)
  subst e1
  rw [hJ] at hJ1
  cases hJ1
  -- the jet's numbers fit
  have hfJ := List.all_eq_true.1 hfit J (List.mem_of_getElem? hJ)
  unfold jetFitB at hfJ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hfJ
  obtain ⟨⟨⟨hkf, hnf⟩, hrf⟩, hcf⟩ := hfJ
  -- the head is the root's address
  have hhp := h.heapLe
  have ha : a < heap.length := termAt_lt htm
  have hhd : (rowOf C r).hd = a := by
    show (C.main r HD).val = a; rw [hHD, val_ofN (by omega)]
  refine ⟨g1, J, by rw [hhd]; exact hmem, hJ, ?_⟩
  -- the pops
  obtain ⟨e, sF, hs0, hsk, hp, hu⟩ := h.popPath hr hi hkf hK
  have hp' : ∀ i, i < J.xs.length → e i < Po.h ∧ Po.main (e i) 2 = ofN i :=
    fun i hi => ⟨(hp i hi).1, (hp i hi).2.2.2.2.1⟩
  have hpop := h.popR_path hp J.xs.length (Nat.le_refl _)
  rw [Nat.sub_self, hs0, hsk] at hpop
  simp only [Nat.zero_add] at hpop
  -- the writes
  obtain ⟨w, hw⟩ := h.wchPath hr hi hnf hN
  -- with a cell to write, the counter is an address
  have hc : 0 < (symCells J J.body 0).1.length → (C.main r CTR).val < 2 ^ 27 := by
    intro hn0
    obtain ⟨h1, h2, _, h4, _, h6⟩ := hw 0 hn0
    have cv := col_eval h1
    obtain ⟨hlt, _⟩ := h.cell (h.instwMem (w 0) h1 h2)
    rw [h4, h6, ofN_zero, add_zero'] at hlt
    exact Nat.lt_of_lt_of_le hlt h.memH
  -- the instantiation
  unfold instRow instRowG
  show (match popR (fun a => (memOf Mm)[a]?) (C.main r CTR).val J.xs.length (C.main r STK).val with
    | some (ps, rest) =>
      let (cs, root) := icells (Mach.overrideN J.genv J.xs ps) (C.main r CTR).val J.body
      if wrsG (fun a => (memOf Mm)[a]?) (C.main r CTR).val cs then
        some (⟨root, rest, (C.main r CTR).val + cs.length⟩ : Air.Row) else none
    | none => none) = _
  rw [hpop]
  dsimp only
  have hic := symCells_icells J (C.main r CTR).val ((List.range J.xs.length).map (fun i => (Po.main (e i) 4).val))
    (by rw [List.length_map, List.length_range]) J.body 0
  rw [Nat.add_zero] at hic
  rw [← hic]
  dsimp only
  rw [if_pos (wrsG_of _ _ (fun j hj => by
    rw [List.length_map] at hj
    rw [List.getElem_map]
    exact h.cellAt hjl hJ hG hnf hcf hp' hu hkf hw (hc (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)) hj))]
  -- the next row
  show some _ = some (⟨(C.main (r + 1) HD).val, (C.main (r + 1) STK).val, (C.main (r + 1) CTR).val⟩ : Air.Row)
  rw [m1, m2, m3, hN]
  congr 2
  · rw [h.rootRes hr hp' hu hkf hops hrf (fun j hj => hc (by
      have := symCells_root_local J J.body 0 j hj
      omega))]
  · rw [List.length_map]
    rcases Nat.eq_zero_or_pos (symCells J J.body 0).1.length with hz | hz
    · rw [hz, ofN_zero, add_zero', Nat.add_zero]
    · rw [val_add_nat (by have := hc hz; omega)]

end

section

variable {hd0 stk0 ctr0 : Nat} {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {C Mm Pg Rt Hd Tm Po Iw : Table} (h : JetOK hd0 stk0 ctr0 heap roots jets C Mm Pg Rt Hd Tm Po Iw)
include h

/-- **The jet circuit's accepted proofs give the facts an instantiation row
    needs.** -/
theorem JetOK.core : JetCore heap roots jets C Mm Po Iw := by
  refine ⟨h.po, h.iw, clk_eq h.cpu, h.mem_h, h.pop_h, h.instw_h, mem_addr h.mem, h.jets_le, h.heap_le,
    fun q hq ha => ?_, fun w hw ha => ?_, fun v hv => ?_, fun w hw ha => h.tmplHit hw ha,
    fun r hr hi => h.rootsHit hr hi, fun r hr hi => h.hdrHit hr hi, fun r0 hr0 hi c' => h.popConserve hr0 hi c',
    fun r0 hr0 hi => h.wchConserve hr0 hi, fun r hr1 hi => ?_⟩
  · have cv := col_eval hq
    exact h.memHit ⟨(popAir, Po), by simp [jetTables], rfl, q, hq, ⟨"mem", 1, col 7, [col 3, c 5, col 4, col 5]⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl,
      by simp only [List.map_cons, List.map_nil, cv, B.c]; rfl, by rw [cv, ha]⟩
  · have cv := col_eval hw
    exact h.memHit ⟨(instwAir, Iw), by simp [jetTables], rfl, w, hw,
      ⟨"mem", 1, col 17, [.add (col 1) (col 3), col 4, col 13, col 14]⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))), rfl,
      by simp only [List.map_cons, List.map_nil, E.eval, cv], by rw [cv, ha]⟩
  · rcases hv with ⟨r, hr, ha, rfl⟩ | ⟨w, hw, ha, rfl⟩ | ⟨w, hw, ha, rfl⟩
    · have cv := col_eval hr
      exact h.argHit ⟨(cpuAirJ hd0 stk0 ctr0, C), by simp [jetTables], rfl, r, hr,
        ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩,
        List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))), rfl,
        by simp only [List.map_cons, List.map_nil, cv], by rw [cv, ha]⟩
    · have cv := col_eval hw
      exact h.argHit ⟨(instwAir, Iw), by simp [jetTables], rfl, w, hw, ⟨"arg", 1, col 6, [col 0, col 8, col 15]⟩,
        List.mem_cons_self, rfl, by simp only [List.map_cons, List.map_nil, cv], by rw [cv, ha]⟩
    · have cv := col_eval hw
      exact h.argHit ⟨(instwAir, Iw), by simp [jetTables], rfl, w, hw, ⟨"arg", 1, col 10, [col 0, col 12, col 16]⟩,
        List.mem_cons_of_mem _ List.mem_cons_self, rfl, by simp only [List.map_cons, List.map_nil, cv],
        by rw [cv, ha]⟩
  · have hr : r < C.h := Nat.lt_of_succ_lt hr1
    have hsel : SelsAre C r 11 := by
      obtain ⟨k, _, hs⟩ := kind_ofJ h.cpu hr
      have e := hs 11 (by decide); rw [hi] at e
      rcases Nat.decEq 11 k with hk | hk
      · rw [if_neg hk] at e; exact absurd e (by decide)
      · rw [← hk] at hs; exact hs
    obtain ⟨_, _, _, _, hnHd, hnStk, hnCtr⟩ := inst_facts hr hsel
    obtain ⟨m1, m2, m3⟩ := next_regsJ h.cpu hr hr1
    rw [m1, m2, m3, hnHd, hnStk, hnCtr, hi, zero_add', zero_add', one_mul', one_mul']
    exact ⟨rfl, rfl, rfl⟩

end

end Circuit
