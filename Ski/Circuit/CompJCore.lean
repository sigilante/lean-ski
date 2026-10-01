import Ski.Circuit.CompJStep

/-!
# The composed circuit with jets: its instantiation rows

The jet circuit's argument that an instantiation row is `Air.instRow`
(`JetCore.inst`) reads the tables only through `JetCore`: the POP and
INSTW constraints, the row counter, the memory, the jet lookups, the two
chains as flows, and an instantiation's next registers.  `CJOK.core` gives
it from the composed circuit with jets, whose CPU keeps the jet columns at
the jet CPU's indices; the blinding blocks and the restart are on other
buses and columns.
-/

namespace Circuit

open B Air JetTable

/-- The CPU's messages on a bus other than `mem`, `segs` and the blinding
    buses are its jet messages. -/
theorem cpuCJ_rowSends_jet {hd0 stk0 ctr0 n nilA : Nat} {C : Table} {bus : String}
    (hb : bus ≠ "mem" ∧ bus ≠ "segs" ∧ bus ≠ "blind_a" ∧ bus ≠ "blind_b" ∧ bus ≠ "blind_c") (v : List F)
    (r : Nat) : rowSends (cpuAirCJ hd0 stk0 ctr0 n nilA) C bus v r =
      jetInters.foldr (fun I acc => (if I.bus = bus ∧ I.fields.map (fun e => e.eval (C.env r)) = v then
        I.count.eval (C.env r) else 0) + acc) 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  unfold rowSends
  show ([readInterCJ 0, readInterCJ 1, readInterCJ 2, readInterCJ 3] ++ writeInters ++ jetInters ++
    [⟨"segs", 1, sRSJ, [.add (col CNTJ) one, col ROOTJ]⟩,
     blindMsg "blind_a" BLAJ false, blindMsg "blind_b" BLBJ true, blindMsg "blind_c" BLCJ true]).foldr _ 0 = _
  rw [List.foldr_append, List.foldr_append]
  rw [foldr_zero_init _ _ ([readInterCJ 0, readInterCJ 1, readInterCJ 2, readInterCJ 3] ++ writeInters)
    (fun I hI => by
      have hm : I.bus = "mem" := by
        have : ([readInterCJ 0, readInterCJ 1, readInterCJ 2, readInterCJ 3] ++ writeInters).all
          (fun I => I.bus == "mem") = true := by decide
        exact beq_iff_eq.1 (List.all_eq_true.1 this I hI)
      exact if_neg (fun h' => h1 (h'.1.symm.trans hm)))]
  rw [foldr_zero_init _ 0 [⟨"segs", 1, sRSJ, [.add (col CNTJ) one, col ROOTJ]⟩,
     blindMsg "blind_a" BLAJ false, blindMsg "blind_b" BLBJ true, blindMsg "blind_c" BLCJ true] (fun I hI => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl
    · exact if_neg (fun h' => h2 h'.1.symm)
    · exact if_neg (fun h' => h3 h'.1.symm)
    · exact if_neg (fun h' => h4 h'.1.symm)
    · exact if_neg (fun h' => h5 h'.1.symm))]

section

variable {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {segRoots : List Nat}
  {roots : List (Nat × Nat)} {jets : List Air.Jet} {C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table}
  (h : CJOK hd0 stk0 ctr0 n nilA heap N W segRoots roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)
include h

omit h in
/-- The CPU's chain-start and chain-end messages on `POPCH`. -/
theorem cpuCJ_popch (r : Nat) (v : List F) : rowSends (cpuAirCJ hd0 stk0 ctr0 n nilA) C "popch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), 0, C.env r (.main 0 STK)] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_K), C.env r (.main 0 J_REST)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpuCJ_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("wch" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "popch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

omit h in
/-- The CPU's chain-start and chain-end messages on `WCH`. -/
theorem cpuCJ_wch (r : Nat) (v : List F) : rowSends (cpuAirCJ hd0 stk0 ctr0 n nilA) C "wch" v r =
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), 0] = v then
      C.env r (.main 0 (SEL + 11)) else 0) +
    (if [C.env r (.main 0 J_CLK), C.env r (.main 0 CTR), C.env r (.main 0 J_G), C.env r (.main 0 J_N)] = v then
      -C.env r (.main 0 (SEL + 11)) else 0) := by
  rw [cpuCJ_rowSends_jet (by decide)]
  simp only [jetInters, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, E.eval, B.col, B.c, sInst,
    true_and, ofN_zero]
  rw [if_neg (show ¬ ("roots" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("hdr" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("popch" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide)),
    if_neg (show ¬ ("arg" = "wch" ∧ _) from fun h' => absurd h'.1 (by decide))]
  simp only [zero_add', add_zero']

/-- **`POPCH` is a flow** at an instantiation row's key. -/
theorem CJOK.popConserve {r0 : Nat} (hr0 : r0 < C.h) (hi : C.main r0 (SEL + 11) = 1) (c' : F) :
    (popEdges Po (ofN r0) c').Conserve (popStart C r0 c') (popEnd C r0 c') := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  have zero_case : (∀ x : F, st ≠ [x]) →
      (popEdges Po (ofN r0) c').cntOut (l, st) + Edges.oneIf (popStart C r0 c') (l, st) =
        (popEdges Po (ofN r0) c').cntIn (l, st) + Edges.oneIf (popEnd C r0 c') (l, st) := by
    intro hst
    have z1 : (popEdges Po (ofN r0) c').cntOut (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((popEdges Po (ofN r0) c').outN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have z2 : (popEdges Po (ofN r0) c').cntIn (l, st) = 0 := sumTo_zero (fun q => by
      rw [show decide ((popEdges Po (ofN r0) c').inN q = (l, st)) = false from
        decide_eq_false (fun e => hst _ (congrArg Prod.snd e).symm), Bool.and_false]; rfl) _
    have o1 : Edges.oneIf (popStart C r0 c') (l, st) = 0 := by
      unfold Edges.oneIf popStart; split
      · exact if_neg (fun e => hst _ (congrArg Prod.snd (Option.some.inj e)).symm)
      · exact if_neg (fun e => by cases e)
    have o2 : Edges.oneIf (popEnd C r0 c') (l, st) = 0 := by
      unfold Edges.oneIf popEnd; split
      · exact if_neg (fun e => hst _ (congrArg Prod.snd (Option.some.inj e)).symm)
      · exact if_neg (fun e => by cases e)
    rw [z1, z2, o1, o2]
  match st with
  | [] => exact zero_case (fun _ e => by cases e)
  | _ :: _ :: _ => exact zero_case (fun _ e => by cases e)
  | [s] =>
    have hb := h.bal "popch" [ofN r0, c', l, s]
    simp only [compJTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAirC) rfl, sends_nobus' (A := progAirC heap N W) rfl, sends_nobus' (A := witAir N W) rfl,
      sends_nobus' (A := segsAir segRoots) rfl, sends_nobus' (A := rootsAirCJ roots) rfl,
      sends_nobus' (A := hdrAirCJ jets) rfl, sends_nobus' (A := tmplAirCJ jets) rfl,
      sends_nobus' (A := instwAirCJ) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', add_zero', add_zero'] at hb
    have hpop : tableSends popAirCJ Po "popch" [ofN r0, c', l, s] =
        ofN ((popEdges Po (ofN r0) c').cntOut (l, [s])) - ofN ((popEdges Po (ofN r0) c').cntIn (l, [s])) := by
      unfold tableSends
      rw [foldr_range_congr (f := fun q => rowSends popAirCJ Po "popch" [ofN r0, c', l, s] q) Po.h (fun q hq =>
        show rowSends popAirCJ Po "popch" [ofN r0, c', l, s] q = _ from (rowSends_withBlocks (A := popAir) (blocks := [("blind_c", false), ("blind_d", true)]) (by decide) _ q).trans
          (pop_rowSendsG hq (h.pop_act hq) _ _ _ _)), fold_sub, fold_ofN, fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirCJ hd0 stk0 ctr0 n nilA) C "popch" [ofN r0, c', l, s] =
        ofN (Edges.oneIf (popStart C r0 c') (l, [s])) - ofN (Edges.oneIf (popEnd C r0 c') (l, [s])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [cpuCJ_popch, env_main0 hr, env_main0 hr, clk_eqCJ h.cpu r hr]
        have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
        rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
          if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [cpuCJ_popch]
      simp only [env_main0 hr0, clk_eqCJ h.cpu r0 hr0, hi]
      rw [msg_ite, msg_ite]
      unfold Edges.oneIf popStart popEnd
      have ep : ∀ (o : Option Node), (if o = some (l, [s]) then (1 : F) else 0) =
          ofN (if o = some (l, [s]) then 1 else 0) := by
        intro o; split <;> rfl
      have en : ∀ (o : Option Node), (if o = some (l, [s]) then -(1 : F) else 0) =
          -ofN (if o = some (l, [s]) then 1 else 0) := by
        intro o; split
        · rfl
        · decide
      rw [ep, en, ← sub_eq_add_neg']
    rw [hcpu, hpop] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 := sumTo_le_one (f := fun q => if (popEdges Po (ofN r0) c').act q &&
      decide ((popEdges Po (ofN r0) c').outN q = (l, [s])) then 1 else 0) (fun q => by split <;> decide) Po.h
    have b2 := sumTo_le_one (f := fun q => if (popEdges Po (ofN r0) c').act q &&
      decide ((popEdges Po (ofN r0) c').inN q = (l, [s])) then 1 else 0) (fun q => by split <;> decide) Po.h
    have o1 : Edges.oneIf (popStart C r0 c') (l, [s]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (popEnd C r0 c') (l, [s]) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Po.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.pop_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show sumTo Po.h _ + _ = sumTo Po.h _ + _
    omega

/-- **`WCH` is a flow** at an instantiation row's key, from `0` to its
    cell count. -/
theorem CJOK.wchConserve {r0 : Nat} (hr0 : r0 < C.h) (hi : C.main r0 (SEL + 11) = 1) :
    (wchEdges Iw (ofN r0) (C.main r0 CTR) (C.main r0 J_G)).Conserve (some ((0 : F), []))
      (some (C.main r0 J_N, [])) := by
  intro v
  obtain ⟨l, st⟩ := v
  have hCP : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  let E' := wchEdges Iw (ofN r0) (C.main r0 CTR) (C.main r0 J_G)
  match st with
  | x :: xs =>
    have z1 : E'.cntOut (l, x :: xs) = 0 := sumTo_zero (fun q => by
      rw [show decide (E'.outN q = (l, x :: xs)) = false from decide_eq_false (fun e => by
        have := congrArg Prod.snd e; cases this), Bool.and_false]; rfl) _
    have z2 : E'.cntIn (l, x :: xs) = 0 := sumTo_zero (fun q => by
      rw [show decide (E'.inN q = (l, x :: xs)) = false from decide_eq_false (fun e => by
        have := congrArg Prod.snd e; cases this), Bool.and_false]; rfl) _
    have o1 : Edges.oneIf (some ((0 : F), [])) (l, x :: xs) = 0 :=
      if_neg (fun e => by have := congrArg Prod.snd (Option.some.inj e); cases this)
    have o2 : Edges.oneIf (some (C.main r0 J_N, [])) (l, x :: xs) = 0 :=
      if_neg (fun e => by have := congrArg Prod.snd (Option.some.inj e); cases this)
    show E'.cntOut _ + _ = E'.cntIn _ + _
    rw [z1, z2, o1, o2]
  | [] =>
    have hb := h.bal "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l]
    simp only [compJTables, List.foldr_cons, List.foldr_nil] at hb
    rw [sends_nobus' (A := memAirC) rfl, sends_nobus' (A := progAirC heap N W) rfl, sends_nobus' (A := witAir N W) rfl,
      sends_nobus' (A := segsAir segRoots) rfl, sends_nobus' (A := rootsAirCJ roots) rfl,
      sends_nobus' (A := hdrAirCJ jets) rfl, sends_nobus' (A := tmplAirCJ jets) rfl,
      sends_nobus' (A := popAirCJ) rfl,
      zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', zero_add', add_zero'] at hb
    have hiw : tableSends instwAirCJ Iw "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] =
        ofN (E'.cntOut (l, [])) - ofN (E'.cntIn (l, [])) := by
      unfold tableSends
      rw [foldr_range_congr (f := fun q => rowSends instwAirCJ Iw "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] q)
        Iw.h (fun q hq =>
        show rowSends instwAirCJ Iw "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] q = _ from (rowSends_withBlocks (A := instwAir) (blocks := [("blind_d", false), ("blind_e", true)]) (by decide) _ q).trans
          (instw_rowSendsG hq (h.instw_act hq) _ _ _ _)), fold_sub, fold_ofN, fold_ofN]
      rfl
    have hcpu : tableSends (cpuAirCJ hd0 stk0 ctr0 n nilA) C "wch" [ofN r0, C.main r0 CTR, C.main r0 J_G, l] =
        ofN (Edges.oneIf (some ((0 : F), [])) (l, [])) - ofN (Edges.oneIf (some (C.main r0 J_N, [])) (l, [])) := by
      unfold tableSends
      rw [fold_single _ C.h r0 hr0 (fun r hr hne => by
        rw [cpuCJ_wch, env_main0 hr, env_main0 hr, clk_eqCJ h.cpu r hr]
        have hne' : ofN r ≠ ofN r0 := fun e => hne (ofN_inj (Nat.lt_trans hr hCP) (Nat.lt_trans hr0 hCP) e)
        rw [if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)),
          if_neg (fun e => hne' (by simp only [List.cons.injEq] at e; exact e.1)), add_zero'])]
      rw [cpuCJ_wch]
      simp only [env_main0 hr0, clk_eqCJ h.cpu r0 hr0, hi]
      rw [msg_iteW, msg_iteW]
      unfold Edges.oneIf
      have ep : ∀ (o : Option Node), (if o = some (l, []) then (1 : F) else 0) =
          ofN (if o = some (l, []) then 1 else 0) := by
        intro o; split <;> rfl
      have en : ∀ (o : Option Node), (if o = some (l, []) then -(1 : F) else 0) =
          -ofN (if o = some (l, []) then 1 else 0) := by
        intro o; split
        · rfl
        · decide
      rw [ep, en, ← sub_eq_add_neg']
    rw [hcpu, hiw] at hb
    have e := bal_sub hb
    rw [← ofN_add, ← ofN_add] at e
    have b1 : E'.cntOut (l, []) ≤ Iw.h := sumTo_le_one (fun q => by split <;> decide) Iw.h
    have b2 : E'.cntIn (l, []) ≤ Iw.h := sumTo_le_one (fun q => by split <;> decide) Iw.h
    have o1 : Edges.oneIf (some ((0 : F), [])) (l, []) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have o2 : Edges.oneIf (some (C.main r0 J_N, [])) (l, []) ≤ 1 := by unfold Edges.oneIf; split <;> decide
    have hP : Iw.h + 1 < P := Nat.lt_of_le_of_lt (Nat.add_le_add_right h.instw_h 1) (by decide)
    have e' := ofN_inj (Nat.lt_of_le_of_lt (Nat.add_le_add o1 b1) (by rw [Nat.add_comm]; exact hP))
      (Nat.lt_of_le_of_lt (Nat.add_le_add o2 b2) (by rw [Nat.add_comm]; exact hP)) e
    show E'.cntOut (l, []) + _ = E'.cntIn (l, []) + _
    omega

omit h in
theorem padCopies8_length_ge : ∀ rows : List (List F), rows.length ≤ (padCopies8 rows).length
  | [] => Nat.le_refl 0
  | r :: rs => by show _ ≤ ((r :: rs) ++ _).length; rw [List.length_append]; exact Nat.le_add_right _ _

theorem CJOK.jets_le : jets.length ≤ 2 ^ 27 := by
  have e : Hd.h = (hdrRowsCJ jets).length := h.hdpre.1
  have hl : jets.length ≤ (hdrRowsCJ jets).length := by
    have := padCopies8_length_ge (jets.zipIdx.map fun (J, g) => hdrRow J g)
    rw [List.length_map, List.length_zipIdx] at this
    exact this
  have : Hd.h ≤ 2 ^ 27 := h.two (hdrAirCJ jets, Hd) (by simp [compJTables])
  omega

/-- **A row with the instantiation selector is an instantiation.** -/
theorem CJOK.instKind {r : Nat} (hr : r < C.h) (hi : C.main r (SEL + 11) = 1) : IsKindCJ C r 11 := by
  obtain ⟨k, hk⟩ := kind_ofCJ h.cpu hr
  have e := hk.2.1 11 (by decide)
  rw [hi] at e
  by_cases hk11 : 11 = k ∧ k < 12
  · rw [← hk11.1] at hk; exact hk
  · rw [if_neg hk11] at e; exact absurd e (by decide)

/-- **The instantiation rows' facts, as the jet circuit's argument reads
    them**, for a heap the roots are licensed over that fits. -/
theorem CJOK.core {heap' : List Cell} (hheap : heap'.length ≤ 2 ^ 27) : JetCore heap' roots jets C Mm Po Iw := by
  refine ⟨sat_of_withBlocks h.po, sat_of_withBlocks h.iw, clk_eqCJ h.cpu, h.mem_h, h.pop_h, h.instw_h,
    mem_addrC h.mem, h.jets_le, hheap,
    fun q hq ha => ?_, fun w hw ha => ?_, fun v hv => ?_, fun w hw ha => h.tmplHit hw ha,
    fun r hr hi => h.rootsHit hr hi, fun r hr hi => h.hdrHit hr hi, fun r0 hr0 hi c' => h.popConserve hr0 hi c',
    fun r0 hr0 hi => h.wchConserve hr0 hi, fun r hr1 hi => ?_⟩
  · have cv := col_eval hq
    exact h.memHit ⟨(popAirCJ, Po), by simp [compJTables], rfl, q, hq, ⟨"mem", 1, col 7, [col 3, c 5, col 4, col 5]⟩,
      List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), rfl,
      by simp only [List.map_cons, List.map_nil, cv, B.c]; rfl, by rw [cv, ha]⟩
  · have cv := col_eval hw
    exact h.memHit ⟨(instwAirCJ, Iw), by simp [compJTables], rfl, w, hw,
      ⟨"mem", 1, col 17, [.add (col 1) (col 3), col 4, col 13, col 14]⟩,
      List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))), rfl,
      by simp only [List.map_cons, List.map_nil, E.eval, cv], by rw [cv, ha]⟩
  · rcases hv with ⟨r, hr, ha, rfl⟩ | ⟨w, hw, ha, rfl⟩ | ⟨w, hw, ha, rfl⟩
    · have cv := col_eval hr
      exact h.argHit ⟨(cpuAirCJ hd0 stk0 ctr0 n nilA, C), by simp [compJTables], rfl, r, hr,
        ⟨"arg", 1, col J_RA, [col J_CLK, col J_RV, col J_XROOT]⟩,
        by rw [show (cpuAirCJ hd0 stk0 ctr0 n nilA).inters = cpuIntersCJ from rfl, cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true], rfl,
        by simp only [List.map_cons, List.map_nil, cv], by rw [cv, ha]⟩
    · have cv := col_eval hw
      exact h.argHit ⟨(instwAirCJ, Iw), by simp [compJTables], rfl, w, hw, ⟨"arg", 1, col 6, [col 0, col 8, col 15]⟩,
        List.mem_append_left _ List.mem_cons_self, rfl, by simp only [List.map_cons, List.map_nil, cv],
        by rw [cv, ha]⟩
    · have cv := col_eval hw
      exact h.argHit ⟨(instwAirCJ, Iw), by simp [compJTables], rfl, w, hw,
        ⟨"arg", 1, col 10, [col 0, col 12, col 16]⟩,
        List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl,
        by simp only [List.map_cons, List.map_nil, cv], by rw [cv, ha]⟩
  · have hr : r < C.h := Nat.lt_of_succ_lt hr1
    have hk := h.instKind hr hi
    obtain ⟨_, _, _, _, hnHd, hnStk, hnCtr⟩ := inst_facts hr (hk.sels (by decide))
    have hrs : C.main r RSJ = 0 := by rw [hk.2.2, if_neg (by decide)]
    obtain ⟨m1, m2, m3⟩ := next_regsCJ h.cpu hr hr1
    rw [m1, m2, m3, hnHd, hnStk, hnCtr, hi, hrs, zero_add', zero_add', one_mul', one_mul', zero_mul', zero_mul',
      add_zero', add_zero']
    exact ⟨rfl, rfl, rfl⟩

end

end Circuit
