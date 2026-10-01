import Ski.Circuit.CompJHonest

/-!
# The honest CPU table of the composed circuit with jets satisfies its AIR

A row other than a restart is the jet table's row (`R.J.cpuCol`), its
restart selector clear: the jet CPU's constraints hold on it
(`JRun.cpu_row`, through `cpuTableCJ`'s agreement with the jet table on
every atom the jet CPU reads), and the restart's terms vanish.  A restart
row reads `K` at the head over the nil as the base `HK1` row does
(`cpu_read`), carries no jet, and jumps to the next segment's root
(`AcceptsCJ.restart`).
-/

namespace Circuit

open B Air JetTable Compose CompM Mach

namespace CRun

variable (R : CRun)

theorem colCJ_low {i c : Nat} (hc : c < CPU_WIDTH + JET_WIDTH)
    (hs : ¬ (SEL ≤ c ∧ c < SEL + NKINDS) ∨ isRestart R.e R.n i = false) :
    R.cpuColCJ i c = R.J.cpuCol i c := by
  unfold cpuColCJ
  rw [if_pos hc, if_neg (fun h => by rcases hs with hs | hs; exact hs ⟨h.1, h.2.1⟩; rw [hs] at h; exact absurd h.2.2 (by decide))]

theorem colCJ_sel {i c : Nat} (hr : isRestart R.e R.n i = true) (h1 : SEL ≤ c) (h2 : c < SEL + NKINDS) :
    R.cpuColCJ i c = 0 := by
  unfold cpuColCJ
  rw [if_pos (by unfold SEL NKINDS CPU_WIDTH JET_WIDTH BITS FLD RANGE_BITS at *; omega), if_pos ⟨h1, h2, hr⟩]

theorem colCJ_rs (i : Nat) : R.cpuColCJ i RSJ = if isRestart R.e R.n i then 1 else 0 := by
  unfold cpuColCJ; rw [if_neg (by decide), if_pos rfl]

theorem colCJ_cnt (i : Nat) : R.cpuColCJ i CNTJ = ofN (cntS (rsI R.e R.n) i) := by
  unfold cpuColCJ; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem colCJ_root (i : Nat) : R.cpuColCJ i ROOTJ = ofN (R.segRoots.getD (cntS (rsI R.e R.n) i + 1) 0) := by
  unfold cpuColCJ; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem colCJ_blind {i c : Nat} (h1 : CPU_WIDTH + JET_WIDTH ≤ c) (h2 : c < RSJ) : R.cpuColCJ i c = 0 := by
  unfold cpuColCJ
  rw [if_neg (by omega), if_neg (by omega), if_neg (by unfold CNTJ; omega), if_neg (by unfold ROOTJ; omega)]

/-- A restart row is skipped: no instantiation. -/
theorem J_restart {i : Nat} (hr : isRestart R.e R.n i = true) : R.J.instAt i = none := by
  unfold JRun.instAt; rw [if_pos (show R.J.skip i = true from hr)]

/-- A restart row's jet columns: the counter, and zero. -/
theorem J_jet_restart {i c : Nat} (hr : isRestart R.e R.n i = true) (h1 : CPU_WIDTH ≤ c) (h3 : c ≠ J_CLK) :
    R.J.cpuCol i c = 0 := by
  unfold JRun.cpuCol; rw [R.J_restart hr]; simp only; rw [if_neg (by omega), if_neg h3]

/-- The registers, on every row. -/
theorem colCJ_reg (j : Nat) {c : Nat} (hc : c < 3) :
    R.cpuColCJ j c = Circuit.cpuCol R.A (R.J.rowQ j) c := by
  rw [R.colCJ_low (by unfold CPU_WIDTH JET_WIDTH BITS FLD RANGE_BITS SEL NKINDS at *; omega)
    (.inl (by unfold SEL at *; omega))]
  exact R.J.col_reg j hc R.J.rowQ_inst

theorem colCJ_clk (j : Nat) : R.cpuColCJ j J_CLK = ofN j := by
  rw [R.colCJ_low (by decide) (.inl (by decide))]; exact R.J.col_clk j

/-- **Off a restart, the table agrees with the jet table** on every atom
    the jet CPU reads. -/
theorem env_agreeCJ {K i : Nat} (hi : i < K) (hr : isRestart R.e R.n i = false) :
    ∀ a, PRun.atomJJ a = true → (R.cpuTableCJ K).env i a = (R.J.cpuTable K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    rcases o with _ | _ | o
    · simp only [PRun.atomJJ, decide_eq_true_eq] at ha
      show R.cpuColCJ ((i + 0) % K) c = R.J.cpuCol ((i + 0) % K) c
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
      exact R.colCJ_low (by unfold P_CNT at ha; exact ha) (.inr hr)
    · simp only [PRun.atomJJ, Bool.or_eq_true, decide_eq_true_eq] at ha
      show R.cpuColCJ ((i + 1) % K) c = R.J.cpuCol ((i + 1) % K) c
      rcases ha with ha | ha
      · rw [R.colCJ_reg _ ha, R.J.col_reg _ ha R.J.rowQ_inst]; rfl
      · subst ha; rw [R.colCJ_clk, R.J.col_clk]
    · simp [PRun.atomJJ] at ha
  | pre _ _ => simp [PRun.atomJJ] at ha
  | first => rfl
  | last => rfl
  | trans => rfl

/-- **A restart row is of the restart kind.** -/
theorem kind_restart {K i : Nat} (hr : isRestart R.e R.n i = true) :
    IsKindCJ (R.cpuTableCJ K) i 12 := by
  refine ⟨by decide, fun j hj => ?_, ?_⟩
  · show R.cpuColCJ i (SEL + j) = _
    rw [R.colCJ_sel hr (Nat.le_add_right _ _) (by omega), if_neg (fun h => absurd h.2 (by decide))]
  · show R.cpuColCJ i RSJ = _
    rw [R.colCJ_rs, hr]; rfl

-- ---------------------------------------------------------------------------
-- The constraints, row by row
-- ---------------------------------------------------------------------------

section

variable {R} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCJ R.A m0 R.jroots R.jets R.segRoots nilA R.n R.e R.row) (hroots : RootsOK m0.heap R.jroots R.jets)
  {K : Nat} (hK : R.e (R.n - 1) < K)
include hA hK

omit hA hK in
theorem cvCJ {i : Nat} (hi : i < K) (c : Nat) : (col c).eval ((R.cpuTableCJ K).env i) = R.cpuColCJ i c := by
  show R.cpuColCJ ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]

omit hA hK in
theorem rowQ_J {i : Nat} (hi : i ≤ R.e (R.n - 1)) : R.J.rowQ i = R.row i :=
  JRun.rowQ_lt (R := R.J) (by show i < R.e (R.n - 1) + 1; omega)

/-- **The segment counter's constraints hold on every row.** -/
theorem cnt_cons {i : Nat} (hi : i < K) :
    (whenFirst (col CNTJ)).eval ((R.cpuTableCJ K).env i) = 0 ∧
    (whenTrans (eq (nxt CNTJ) (.add (col CNTJ) sRSJ))).eval ((R.cpuTableCJ K).env i) = 0 ∧
    (whenLast (eq (col CNTJ) (B.c (R.n - 1)))).eval ((R.cpuTableCJ K).env i) = 0 := by
  have cv := cvCJ (R := R) (K := K) hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [B.whenFirst, E.eval, env_first, cv, R.colCJ_cnt]
    split
    · next h0 => subst h0; show (1 : F) * ofN 0 = 0; decide
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, E.eval, env_trans]
    split
    · exact zero_mul' _
    · next hl =>
      have hmod : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by show i + 1 < K; simp [cpuTableCJ] at hl; omega)
      show (1 : F) * (R.cpuColCJ ((i + 1) % K) CNTJ - (_ + _)) = 0
      rw [hmod, R.colCJ_cnt, cv CNTJ, show sRSJ = col RSJ from rfl, cv RSJ, R.colCJ_cnt, R.colCJ_rs, one_mul']
      show ofN (cntS (rsI R.e R.n) i + rsI R.e R.n i) - _ = 0
      rw [ofN_add]
      have : ofN (rsI R.e R.n i) = (if isRestart R.e R.n i then 1 else 0 : F) := by unfold rsI; split <;> rfl
      rw [this, sub_self']
  · simp only [B.whenLast, B.eq, E.eval, env_last, cv, R.colCJ_cnt, B.c]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      rw [cntS_after hA.emono hA.npos (show R.e (R.n - 1) ≤ i by omega), sub_self', mul_zero']
    · exact zero_mul' _

omit hA hK in
/-- **The first row's registers.** -/
theorem first_cons {i : Nat} (hi : i < K) :
    (whenFirst (eq (col HD) (B.c (R.row 0).hd))).eval ((R.cpuTableCJ K).env i) = 0 ∧
    (whenFirst (eq (col STK) (B.c (R.row 0).stk))).eval ((R.cpuTableCJ K).env i) = 0 ∧
    (whenFirst (eq (col CTR) (B.c (R.row 0).ctr))).eval ((R.cpuTableCJ K).env i) = 0 := by
  have cv := cvCJ (R := R) (K := K) hi
  have hq : R.J.rowQ 0 = R.row 0 := rowQ_J (R := R) (Nat.zero_le _)
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [B.whenFirst, B.eq, E.eval, env_first, cv, B.c]
    split
    · next h0 =>
      subst h0
      rw [R.colCJ_reg 0 (by decide), hq]
      simp only [Circuit.cpuCol_hd, Circuit.cpuCol_stk, Circuit.cpuCol_ctr, sub_self', mul_zero']
    · exact zero_mul' _

omit hA hK in
/-- **The blinding flags are clear.** -/
theorem blind_cons {i : Nat} (hi : i < K) :
    (B.bool (col (BLAJ + 4))).eval ((R.cpuTableCJ K).env i) = 0 ∧
    (B.bool (col (BLBJ + 4))).eval ((R.cpuTableCJ K).env i) = 0 ∧
    (B.bool (col (BLCJ + 4))).eval ((R.cpuTableCJ K).env i) = 0 := by
  have cv := cvCJ (R := R) (K := K) hi
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [B.bool, E.eval, cv]
    rw [R.colCJ_blind (by decide) (by decide), zero_mul']

omit hA hK in
theorem kindSumCJ :
    kindEqCJ 12 (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRSJ])) one = true := by decide

include hroots in
/-- **A restart row satisfies the CPU's constraints.** -/
theorem restart_row (hlen : R.A.length ≤ 2 ^ 24) {i : Nat} (hi : i < K) (hr : isRestart R.e R.n i = true) :
    ∀ c ∈ cpuConsCJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n nilA, c.eval ((R.cpuTableCJ K).env i) = 0 := by
  intro c hc
  obtain ⟨j, hj, hij⟩ := isRestart_iff.1 hr
  have hlt : i < R.e (R.n - 1) := hA.restart_lt hr
  have hi1 : i + 1 < K := by omega
  have hiT : i < (R.cpuTableCJ K).h := hi
  have cv := cvCJ (R := R) (K := K) hi
  have hq : R.J.rowQ i = R.row i := rowQ_J (R := R) (by omega)
  have hq1 : R.J.rowQ (i + 1) = R.row (i + 1) := rowQ_J (R := R) (by omega)
  have hmod : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt hi1
  obtain ⟨hend1, hend2⟩ := hA.ends j (by omega)
  rw [hij] at hend1 hend2
  have hk := R.kind_restart (K := K) hr
  obtain ⟨hf, _, _, _, _, _, hIn, nh, ns, nc⟩ := kind_factsCJ hiT hk
  have hsel : ∀ q, q < NKINDS → (col (SEL + q)).eval ((R.cpuTableCJ K).env i) = 0 := fun q hq' => by
    rw [cv, R.colCJ_sel hr (Nat.le_add_right _ _) (by omega)]
  have hjet : ∀ c, CPU_WIDTH ≤ c → c < CPU_WIDTH + JET_WIDTH → c ≠ J_CLK →
      (col c).eval ((R.cpuTableCJ K).env i) = 0 := fun c h1 h2 h3 => by
    rw [cv, R.colCJ_low h2 (.inl (by unfold SEL NKINDS CPU_WIDTH BITS FLD RANGE_BITS at *; omega)),
      R.J_jet_restart hr h1 h3]
  have hRL := hjet J_RL (by decide) (by decide) (by decide)
  have hRA := hjet J_RA (by decide) (by decide) (by decide)
  have hRG := hjet J_RG (by decide) (by decide) (by decide)
  have hrs : (col RSJ).eval ((R.cpuTableCJ K).env i) = 1 := by rw [cv, R.colCJ_rs, hr]; rfl
  have fL : (R.cpuTableCJ K).env i .last = 0 := by
    show (if i + 1 = K then 1 else 0) = 0; rw [if_neg (by omega)]
  have fT : (R.cpuTableCJ K).env i .trans = 1 := by
    show (if i + 1 = K then 0 else 1) = 1; rw [if_neg (by omega)]
  have nx : ∀ c, (nxt c).eval ((R.cpuTableCJ K).env i) = R.cpuColCJ (i + 1) c := fun c => by
    show R.cpuColCJ ((i + 1) % K) c = _; rw [hmod]
  have hjh : jetHd.eval ((R.cpuTableCJ K).env i) = 0 := by
    simp only [jetHd, E.eval]
    rw [hRL, hRG, hRA, zero_mul', zero_mul', zero_mul', add_zero', add_zero']
  have h11 : sInst.eval ((R.cpuTableCJ K).env i) = 0 := hsel 11 (by decide)
  have hst := hA.restart j hj
  rw [hij] at hst
  -- the reads: as the base `HK1` row's
  have hval : Valid R.A (R.J.rowQ i) := .inr (by rw [hq]; exact halt_K hend1 hend2)
  have hb : (R.J.rowQ i).ctr ≤ 2 ^ 24 := by
    rw [hq]; exact Nat.le_trans (hA.ctr_le hroots i (by omega)) hlen
  have agree : ∀ a, baseAtom a = true →
      (R.cpuTableCJ K).env i a = (Circuit.cpuTable R.A R.J.rowQ K).env i a := by
    intro a ha
    cases a with
    | main o c =>
      cases o with
      | zero =>
        simp only [baseAtom, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not] at ha
        show R.cpuColCJ ((i + 0) % K) c = Circuit.cpuCol R.A (R.J.rowQ ((i + 0) % K)) c
        rw [Nat.add_zero, Nat.mod_eq_of_lt hi,
          R.colCJ_low (by unfold CPU_WIDTH JET_WIDTH at *; omega) (.inl (fun h => by rcases ha.2 with h' | h' <;> omega))]
        unfold JRun.cpuCol; rw [R.J_restart hr]; simp only; rw [if_pos ha.1]; rfl
      | succ o => simp [baseAtom] at ha
    | _ => simp [baseAtom] at ha
  have hkind : kindOf R.A (R.J.rowQ i) = 5 := by rw [hq]; simp only [kindOf, hend1, hend2]
  have hread : ∀ j', j' < 4 → ∀ c ∈ readCons j', c.eval ((R.cpuTableCJ K).env i) = 0 := by
    intro j' hj' c hc
    have hbase := cpu_read (M := R.A) (row := R.J.rowQ) (k := K) hval hb hi hj'
    have cong := E.eval_congr agree
    obtain ⟨hrest, hbits⟩ := readRest_base j' hj'
    have hc' := hc
    unfold readCons at hc'
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hc'
    rcases hc' with ⟨b, hb', rfl⟩ | rfl
    · rw [cong _ (hbits b hb')]; exact hbase _ hc
    · show (acts.getD j' zero).eval _ * _ = 0
      rw [cong _ hrest]
      have hk0 := cpu_kind (M := R.A) (row := R.J.rowQ) (k := K) hi (shape hval)
      have e1 := ((kind_facts hi hk0).1 j' hj').1
      rw [hkind] at e1
      rw [(hf j' hj').1, show actOfCJ 12 j' = actOf 5 j' by
        unfold actOfCJ actOf
        rcases (show j' = 0 ∨ j' = 1 ∨ j' = 2 ∨ j' = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl, ← e1]
      exact hbase _ hc
  rw [cpuConsCJ_split] at hc
  simp only [List.mem_append] at hc
  rcases hc with ((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc
  · -- the selectors are bits
    obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hc
    simp only [B.bool, E.eval]; rw [hsel q (List.mem_range.1 hq'), zero_mul']
  · rw [List.mem_singleton.1 hc]; simp only [B.bool, E.eval]
    rw [show sRSJ = col RSJ from rfl, hrs]; show (1 : F) * (1 - ofN 1) = 0; decide
  · rw [List.mem_singleton.1 hc]; simp only [B.eq, E.eval]
    rw [kind_evalCJ hiT hk kindSumCJ]; show (1 : F) * (ofN 1 - ofN 1) = 0; decide
  · exact hread 0 (by decide) _ hc
  · exact hread 1 (by decide) _ hc
  · exact hread 2 (by decide) _ hc
  · exact hread 3 (by decide) _ hc
  · obtain ⟨c1, c2, c3⟩ := cnt_cons hA hK hi
    obtain ⟨f1, f2, f3⟩ := first_cons (R := R) (K := K) hi
    obtain ⟨b1, b2, b3⟩ := blind_cons (R := R) (K := K) hi
    have hclk := R.colCJ_clk i
    simp only [cjTail, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [B.whenFirst, E.eval, env_first, cv, hclk]
      split
      · next h0 => rw [h0]; show (1 : F) * ofN 0 = 0; decide
      · exact zero_mul' _
    · simp only [B.whenTrans, B.eq, E.eval, fT, one_mul', nx, cv, R.colCJ_clk, B.one, B.c, ofN_one]
      rw [ofN_add, ofN_one, sub_self']
    · simp only [B.bool, E.eval]; rw [hRL, zero_mul']
    · simp only [B.bool, E.eval]; rw [hRA, zero_mul']
    · simp only [B.bool, E.eval]; rw [hRG, zero_mul']
    · simp only [B.eq, E.eval]; rw [hRL, hRA, hRG, h11, add_zero', add_zero', sub_self']
    · exact hsel 12 (by decide)
    · exact hsel 13 (by decide)
    · exact c1
    · exact c2
    · exact c3
    · simp only [B.whenTrans, B.eq, E.eval, fT, one_mul', nx, nh, hjh]
      rw [show sRSJ = col RSJ from rfl, hrs, one_mul', cv, R.colCJ_root]
      rw [R.colCJ_reg _ (by decide), hq1, hst, Circuit.cpuCol_hd]
      have e0 : (nextHdOfCJ 12).eval ((R.cpuTableCJ K).env i) = 0 := rfl
      rw [e0, zero_add', zero_add', ← hij, cntS_end hA.emono j (by omega), sub_self']
    · simp only [B.whenTrans, B.eq, E.eval, fT, one_mul', nx, ns, h11]
      rw [show sRSJ = col RSJ from rfl, hrs, one_mul', zero_mul', R.colCJ_reg _ (by decide), hq1, hst,
        Circuit.cpuCol_stk]
      have e0 : (nextStkOfCJ 12).eval ((R.cpuTableCJ K).env i) = 0 := rfl
      rw [e0, zero_add', zero_add', B.c, E.eval, sub_self']
    · simp only [B.whenTrans, B.eq, E.eval, fT, one_mul', nx, nc, h11]
      rw [zero_mul', add_zero', R.colCJ_reg _ (by decide), hq1, hst, Circuit.cpuCol_ctr]
      show ofN (R.row i).ctr - (col CTR).eval _ = 0
      rw [cv, R.colCJ_reg _ (by decide), hq, Circuit.cpuCol_ctr, sub_self']
    · exact f1
    · exact f2
    · exact f3
    · simp only [B.whenLast, E.eval, fL, zero_mul']
    · exact b1
    · exact b2
    · exact b3
    · simp only [B.whenLast, E.eval, fL, zero_mul']

include hroots in
/-- **A row other than a restart satisfies the CPU's constraints**: the jet
    CPU's, by `JRun.cpu_row`, its restart terms vanishing. -/
theorem normal_row (hlen : R.A.length ≤ 2 ^ 24) {i : Nat} (hi : i < K) (hr : isRestart R.e R.n i = false) :
    ∀ c ∈ cpuConsCJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n nilA, c.eval ((R.cpuTableCJ K).env i) = 0 := by
  intro c hc
  have hJ : JOK R.J := hA.jok hroots
  have cv := cvCJ (R := R) (K := K) hi
  have tr : ∀ e ∈ cpuConsJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr, e.eval ((R.cpuTableCJ K).env i) = 0 := by
    intro e he
    rw [E.eval_congr (R.env_agreeCJ hi hr) e (List.all_eq_true.1 (PRun.cpuConsJ_atoms _ _ _) e he)]
    exact R.J.cpu_row hJ (show R.e (R.n - 1) + 1 ≤ K by omega) hlen hi hr e he
  have trT : ∀ e ∈ [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
      bool (col J_RL), bool (col J_RA), bool (col J_RG),
      eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst,
      sPFirst, sPLater,
      whenTrans (eq (nxt HD) (.add nextHd jetHd)),
      whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST)))),
      whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))),
      whenFirst (eq (col HD) (B.c (R.row 0).hd)), whenFirst (eq (col STK) (B.c (R.row 0).stk)),
      whenFirst (eq (col CTR) (B.c (R.row 0).ctr)),
      whenLast (eq halt one)], e.eval ((R.cpuTableCJ K).env i) = 0 :=
    fun e he => tr e (by rw [cpuConsJ_split]; exact List.mem_append_right _ he)
  have trP : ∀ e ∈ cpuPre, e.eval ((R.cpuTableCJ K).env i) = 0 :=
    fun e he => tr e (by rw [cpuConsJ_split]; exact List.mem_append_left _ he)
  have hrs : (col RSJ).eval ((R.cpuTableCJ K).env i) = 0 := by rw [cv, R.colCJ_rs, hr]; rfl
  obtain ⟨c1, c2, c3⟩ := cnt_cons hA hK hi
  obtain ⟨b1, b2, b3⟩ := blind_cons (R := R) (K := K) hi
  rw [cpuConsCJ_split] at hc
  simp only [List.mem_append] at hc
  rcases hc with ((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc
  · exact trP c (by unfold cpuPre; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl hc)))))
  · rw [List.mem_singleton.1 hc]; simp only [B.bool, E.eval]
    rw [show sRSJ = col RSJ from rfl, hrs, zero_mul']
  · rw [List.mem_singleton.1 hc]
    have h1 := trP (eq (sum ((List.range NKINDS).map fun i => col (SEL + i))) one) (by unfold cpuPre; simp)
    simp only [B.eq, E.eval, B.sum] at h1 ⊢
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, E.eval, show sRSJ = col RSJ from rfl, hrs, add_zero']
    exact h1
  · exact trP c (by unfold cpuPre; simp only [List.mem_append]; exact .inl (.inl (.inl (.inr hc))))
  · exact trP c (by unfold cpuPre; simp only [List.mem_append]; exact .inl (.inl (.inr hc)))
  · exact trP c (by unfold cpuPre; simp only [List.mem_append]; exact .inl (.inr hc))
  · exact trP c (by unfold cpuPre; simp only [List.mem_append]; exact .inr hc)
  · simp only [cjTail, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact c1
    · exact c2
    · exact c3
    · have h := trT (whenTrans (eq (nxt HD) (.add nextHd jetHd))) (by simp)
      simp only [B.whenTrans, B.eq, E.eval] at h ⊢
      rw [show sRSJ = col RSJ from rfl, hrs, zero_mul', add_zero']; exact h
    · have h := trT (whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST))))) (by simp)
      simp only [B.whenTrans, B.eq, E.eval] at h ⊢
      rw [show sRSJ = col RSJ from rfl, hrs, zero_mul', add_zero']; exact h
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact trT _ (by simp)
    · exact b1
    · exact b2
    · exact b3
    · -- the last row is `HK1`
      simp only [B.whenLast, B.eq, E.eval, env_last]
      split
      · next hl =>
        have hl' : i + 1 = K := hl
        have hn := hA.npos
        have hk0 : R.J.instAt i = none := JRun.instAt_none_of (R := R.J) (by show R.e (R.n - 1) + 1 ≤ i + 1; omega)
        have hq : R.J.rowQ i = R.row (R.e (R.n - 1)) := by
          show Circuit.rowQ R.row (R.e (R.n - 1) + 1) i = _
          unfold Circuit.rowQ; split
          · rw [show i = R.e (R.n - 1) by omega]
          · rfl
        obtain ⟨hend1, hend2⟩ := hA.ends (R.n - 1) (by omega)
        rw [show sHK1 = col (SEL + 5) from rfl, cv, R.colCJ_low (by decide) (.inr hr)]
        unfold JRun.cpuCol; rw [hk0]; simp only
        rw [if_pos (by decide), Circuit.cpuCol_sel _ _ (by decide), hq]
        simp only [show R.J.A = R.A from rfl, kindOf, hend1, hend2]
        show (1 : F) * ((1 : F) - ofN 1) = 0; decide
      · exact zero_mul' _

include hroots in
/-- **The honest CPU table satisfies the CPU's constraints.** -/
theorem cpuCJ_sat (hlen : R.A.length ≤ 2 ^ 24) :
    Sat (cpuAirCJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n nilA) (R.cpuTableCJ K) := by
  refine ⟨by show 0 < K; omega, fun c hc i hi => ?_⟩
  cases hr : isRestart R.e R.n i with
  | false => exact normal_row hA hroots hK hlen hi hr c hc
  | true => exact restart_row hA hroots hK hlen hi hr c hc

end

end CRun

end Circuit
