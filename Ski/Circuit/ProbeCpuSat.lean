import Ski.Circuit.ProbeHonest

/-!
# The honest probe CPU satisfies its AIR

A probe row is checked constraint by constraint (`PRun.probe_rowSat`); a
row within a segment satisfies the jet CPU's constraints (`JRun.cpu_row`,
on the run that skips the probe rows) and the probe constraints, which
there read only the count and, on the last row, the nil at the stack
(`PRun.cpu_satP`).
-/

namespace Circuit

open B Air JetTable Mach

namespace PRun

variable (R : PRun)

-- ---------------------------------------------------------------------------
-- The columns
-- ---------------------------------------------------------------------------

theorem cvP {K i : Nat} (hi : i < K) (c : Nat) : (col c).eval ((R.cpuTableP K).env i) = R.cpuColP K i c := by
  show R.cpuColP K ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]

theorem nxP {K i : Nat} (c : Nat) : (nxt c).eval ((R.cpuTableP K).env i) = R.cpuColP K ((i + 1) % K) c := rfl

theorem colP_sel {K i : Nat} (hp : R.isP i = true) {m : Nat} (hm : m < NKINDS) :
    R.cpuColP K i (SEL + m) = if m = (if i = 0 then 12 else 13) then 1 else 0 := by
  unfold cpuColP
  rw [if_pos hp, if_pos (by unfold SEL CPU_WIDTH BITS FLD RANGE_BITS NKINDS at *; omega),
    if_pos ⟨Nat.le_add_right _ _, by unfold FLD; omega⟩]
  rcases Nat.decEq m (if i = 0 then 12 else 13) with h | h
  · rw [if_neg (fun e => h (Nat.add_left_cancel e)), if_neg h]
  · rw [if_pos (by rw [h]), if_pos h]

theorem colP_base {K i c : Nat} (hp : R.isP i = true) (hc : c < CPU_WIDTH) (hn : ¬ (SEL ≤ c ∧ c < FLD)) :
    R.cpuColP K i c = Circuit.cpuCol R.A (R.row i) c := by
  unfold cpuColP; rw [if_pos hp, if_pos hc, if_neg hn]

theorem colP_clk {K i : Nat} (hp : R.isP i = true) : R.cpuColP K i J_CLK = ofN i := by
  unfold cpuColP; rw [if_pos hp, if_neg (by decide), if_pos rfl]

theorem colP_jet {K i c : Nat} (hp : R.isP i = true) (h1 : CPU_WIDTH ≤ c) (h2 : c < P_CNT) (h3 : c ≠ J_CLK) :
    R.cpuColP K i c = 0 := by
  unfold cpuColP; rw [if_pos hp, if_neg (by omega), if_neg h3, if_pos h2]

theorem colP_x {K i c : Nat} (hp : R.isP i = true) (h : P_CNT ≤ c) : R.cpuColP K i c = R.probeX i c := by
  unfold cpuColP
  rw [if_pos hp, if_neg (by unfold P_CNT J_CLK JET_WIDTH at h; omega),
    if_neg (by unfold P_CNT J_CLK JET_WIDTH CPU_WIDTH at *; omega), if_neg (by omega)]

theorem colP_low {K i c : Nat} (hp : R.isP i = false) (h : c < P_CNT) : R.cpuColP K i c = R.J.cpuCol i c := by
  unfold cpuColP; rw [hp, if_neg Bool.false_ne_true, if_pos h]

theorem colP_high {K i c : Nat} (hp : R.isP i = false) (h : P_CNT ≤ c) : R.cpuColP K i c = R.normX K i c := by
  unfold cpuColP; rw [hp, if_neg Bool.false_ne_true, if_neg (by omega)]

theorem probeX_cnt (i : Nat) : R.probeX i P_CNT = ofN (R.pcnt i) := rfl
theorem probeX_f (i : Nat) : R.probeX i P_F = ofN (R.row (i + 1)).hd := rfl
theorem probeX_s (i : Nat) {m : Nat} (hm : m < 6) :
    R.probeX i (S_BASE + m) = (segCols (R.seg (R.pcnt i))).getD m 0 := by
  unfold probeX
  simp only
  rw [if_neg (by unfold S_BASE P_CNT; omega), if_neg (by unfold S_BASE P_F P_CNT; omega),
    if_pos ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left]

theorem probeX_first {i c : Nat} (h0 : R.pcnt i = 0) (h1 : c ≠ P_CNT) (h2 : c ≠ P_F)
    (h3 : ¬ (S_BASE ≤ c ∧ c < S_BASE + 6)) : R.probeX i c = 0 := by
  unfold probeX
  simp only
  rw [if_neg h1, if_neg h2, if_neg h3, if_pos h0]

theorem probeX_later {i c : Nat} (h0 : 0 < R.pcnt i) (h1 : c ≠ P_CNT) (h2 : c ≠ P_F)
    (h3 : ¬ (S_BASE ≤ c ∧ c < S_BASE + 6)) :
    R.probeX i c =
      if E_BASE ≤ c ∧ c < E_BASE + 6 then (segCols (R.seg (R.pcnt i - 1))).getD (c - E_BASE) 0
      else if c = E_REST then ofN (R.restE i)
      else if c = P_NILACT then 1
      else if c = P_NILADDR then ofN (R.restE i)
      else if c = P_CLKP then ofN (R.p ((R.seg (R.pcnt i)).parent + 1))
      else if c = P_NKIDS then ofN (R.nkids (R.pcnt i - 1))
      else if P_NILBITS ≤ c then ofN ((((R.row i).ctr - R.restE i - 1) / 2 ^ (c - P_NILBITS)) % 2)
      else 0 := by
  unfold probeX
  simp only
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg (by omega)]

theorem probeX_E (i : Nat) (h0 : 0 < R.pcnt i) {m : Nat} (hm : m < 6) :
    R.probeX i (E_BASE + m) = (segCols (R.seg (R.pcnt i - 1))).getD m 0 := by
  rw [R.probeX_later h0 (by unfold E_BASE P_CNT; omega) (by unfold E_BASE P_F P_CNT; omega)
    (by unfold E_BASE S_BASE P_CNT; omega), if_pos ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left]

theorem probeX_rest (i : Nat) (h0 : 0 < R.pcnt i) : R.probeX i E_REST = ofN (R.restE i) := by
  rw [R.probeX_later h0 (by decide) (by decide) (by decide), if_neg (by decide), if_pos rfl]

theorem probeX_nilact (i : Nat) (h0 : 0 < R.pcnt i) : R.probeX i P_NILACT = 1 := by
  rw [R.probeX_later h0 (by decide) (by decide) (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem probeX_niladdr (i : Nat) (h0 : 0 < R.pcnt i) : R.probeX i P_NILADDR = ofN (R.restE i) := by
  rw [R.probeX_later h0 (by decide) (by decide) (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]

theorem probeX_clkp (i : Nat) (h0 : 0 < R.pcnt i) :
    R.probeX i P_CLKP = ofN (R.p ((R.seg (R.pcnt i)).parent + 1)) := by
  rw [R.probeX_later h0 (by decide) (by decide) (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem probeX_nkids (i : Nat) (h0 : 0 < R.pcnt i) : R.probeX i P_NKIDS = ofN (R.nkids (R.pcnt i - 1)) := by
  rw [R.probeX_later h0 (by decide) (by decide) (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem probeX_bits (i : Nat) (h0 : 0 < R.pcnt i) {b : Nat} (hb : b < RANGE_BITS) :
    R.probeX i (P_NILBITS + b) = ofN ((((R.row i).ctr - R.restE i - 1) / 2 ^ b) % 2) := by
  rw [R.probeX_later h0 (by unfold P_NILBITS P_CNT; omega) (by unfold P_NILBITS P_F P_CNT; omega)
    (by unfold P_NILBITS S_BASE P_CNT; omega), if_neg (by unfold P_NILBITS E_BASE P_CNT; omega),
    if_neg (by unfold P_NILBITS E_REST P_CNT; omega), if_neg (by unfold P_NILBITS P_NILACT P_CNT; omega),
    if_neg (by unfold P_NILBITS P_NILADDR P_CNT; omega), if_neg (by unfold P_NILBITS P_CLKP P_CNT; omega),
    if_neg (by unfold P_NILBITS P_NKIDS P_CNT; omega), if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Every row's count. -/
theorem colP_cnt (K i : Nat) : R.cpuColP K i P_CNT = ofN (R.pcnt i) := by
  cases hp : R.isP i with
  | true => rw [R.colP_x hp (Nat.le_refl _)]; rfl
  | false => rw [R.colP_high hp (Nat.le_refl _)]; rfl

/-- Every row's clock. -/
theorem colP_clk' (K i : Nat) : R.cpuColP K i J_CLK = ofN i := by
  cases hp : R.isP i with
  | true => exact R.colP_clk hp
  | false => rw [R.colP_low hp (by decide)]; exact R.J.col_clk i

theorem ab_sub (a b : F) : a + b - a - b = 0 :=
  E.eval_eq_of_norm
    (e := .sub (.sub (.add (.atom (.main 0 0)) (.atom (.main 0 1))) (.atom (.main 0 0))) (.atom (.main 0 1)))
    (e' := .const 0) (by decide) (at4 a b 0 0)

theorem ite_bit (P : Prop) [Decidable P] : (if P then (1 : F) else 0) * ((if P then 1 else 0) - 1) = 0 := by
  split <;> decide

-- ---------------------------------------------------------------------------
-- A probe row
-- ---------------------------------------------------------------------------

variable {R} {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
  (hroots : RootsOK (load t).heap R.roots R.jets)
include hA

theorem pcnt_zero : R.pcnt 0 = 0 := by
  have := pcnt_p hA (j := 0) (Nat.zero_le _)
  rw [hA.p0] at this; exact this

/-- Every row's registers are its run row's. -/
theorem regP {K i c : Nat} (hc : c < 3) : R.cpuColP K i c = Circuit.cpuCol R.A (R.J.rowQ i) c := by
  cases hp : R.isP i with
  | true =>
    rw [R.colP_base hp (Nat.lt_trans hc (by decide)) (by unfold SEL; omega),
      JRun.rowQ_lt (by show i < R.last + 1; have := isP_lt hA hp; omega)]
    rfl
  | false =>
    rw [R.colP_low hp (Nat.lt_trans hc (by decide))]
    exact R.J.col_reg i hc R.J.rowQ_inst

omit hA in
theorem jetHd_probe {K i : Nat} (hi : i < K) (hp : R.isP i = true) : jetHd.eval ((R.cpuTableP K).env i) = 0 := by
  simp only [jetHd, E.eval, R.cvP hi, R.colP_jet hp (c := J_RL) (by decide) (by decide) (by decide),
    R.colP_jet hp (c := J_RA) (by decide) (by decide) (by decide),
    R.colP_jet hp (c := J_RG) (by decide) (by decide) (by decide), zero_mul', add_zero']

theorem pr_zero {i : Nat} (hp : R.isP i = true) : i = 0 ↔ R.pcnt i = 0 := by
  obtain ⟨_, hpj⟩ := isP_pcnt hA hp
  constructor
  · intro h0; rw [h0]; exact pcnt_zero hA
  · intro h0; rw [← hpj, h0, hA.p0]

omit hA in
theorem pr_sels {K i : Nat} (hi : i < K) (hp : R.isP i = true) :
    SelsAre (R.cpuTableP K) i (if i = 0 then 12 else 13) ∧
    sPFirst.eval ((R.cpuTableP K).env i) = (if i = 0 then 1 else 0) ∧
    sPLater.eval ((R.cpuTableP K).env i) = (if i = 0 then 0 else 1) := by
  have cv := R.cvP hi
  refine ⟨fun m hm => R.colP_sel hp hm, ?_, ?_⟩
  · show (col (SEL + 12)).eval _ = _
    rw [cv, R.colP_sel hp (by decide)]
    split
    · rw [if_pos rfl]
    · rw [if_neg (by decide)]
  · show (col (SEL + 13)).eval _ = _
    rw [cv, R.colP_sel hp (by decide)]
    split
    · rw [if_neg (by decide)]
    · rw [if_pos rfl]

/-- A probe row's registers, and the next row's. -/
theorem pr_regs {K i : Nat} (hK : R.last < K) (hp : R.isP i = true) :
    R.cpuColP K i HD = ofN (R.row i).hd ∧ R.cpuColP K i CTR = ofN (R.row i).ctr ∧
    R.cpuColP K (i + 1) HD = ofN (R.row (i + 1)).hd ∧ R.cpuColP K (i + 1) STK = ofN (R.row (i + 1)).stk ∧
    R.cpuColP K (i + 1) CTR = ofN (R.row (i + 1)).ctr := by
  have hil := isP_lt hA hp
  have hq1 : R.J.rowQ (i + 1) = R.row (i + 1) := JRun.rowQ_lt (by show i + 1 < R.last + 1; omega)
  have hq0 : R.J.rowQ i = R.row i := JRun.rowQ_lt (by show i < R.last + 1; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [regP hA (by decide), hq0]; rfl
  · rw [regP hA (by decide), hq0]; rfl
  · rw [regP hA (by decide), hq1]; rfl
  · rw [regP hA (by decide), hq1]; rfl
  · rw [regP hA (by decide), hq1]; rfl

include hroots in
/-- A probe row's corpus constraints. -/
theorem probe_pre {K : Nat} (hK : R.last < K) (hlen : R.A.length ≤ 2 ^ 24) {i : Nat} (hi : i < K)
    (hp : R.isP i = true) : ∀ e ∈ cpuPre, e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
  have hil := isP_lt hA hp
  have cv := R.cvP hi
  have hk0 := pr_zero hA hp
  obtain ⟨hsel, _, _⟩ := R.pr_sels hi hp
  have hk2 : (if i = 0 then 12 else 13) = 12 ∨ (if i = 0 then 12 else 13) = 13 := by
    split
    · exact .inl rfl
    · exact .inr rfl
  obtain ⟨ha0, ha, _⟩ := probe_facts hi hsel hk2
  have hctr : (R.row i).ctr ≤ R.A.length := (hA.ctrs hroots i (by unfold last at hil; unfold n at hil; omega)).2.1
  obtain ⟨rHD, rCTR, _⟩ := pr_regs hA hK hp
  have bits : ∀ jj b, jj < 4 → b < RANGE_BITS →
      (B.bool (B.col (BITS + jj * RANGE_BITS + b))).eval ((R.cpuTableP K).env i) = 0 := by
    intro jj b hjj hb
    simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
    rw [R.colP_base hp (by show 25 + jj * 24 + b < 121; unfold RANGE_BITS at hb; omega)
      (by show ¬ (3 ≤ 25 + jj * 24 + b ∧ 25 + jj * 24 + b < 17); omega), cpuCol_bit _ _ hjj hb]
    exact JRun.bit_mod _
  unfold cpuPre at he
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
  rcases he with (((((⟨m, hm, rfl⟩ | rfl) | he) | he) | he) | he)
  · simp only [B.bool, E.eval, cv, R.colP_sel hp hm, B.one, B.c, ofN_one]
    exact ite_bit _
  · have hk := kind_evalS hi hsel (e := B.eq (B.sum ((List.range NKINDS).map fun i => B.col (SEL + i))) B.one)
      (e' := zero) (by rcases hk2 with h | h <;> rw [h] <;> decide)
    rw [hk]; rfl
  · unfold readCons at he
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
    rcases he with ⟨b, hb, rfl⟩ | rfl
    · exact bits 0 b (by decide) hb
    · simp only [E.eval]
      rw [ha0]
      rcases Nat.decEq i 0 with h0 | h0
      · rw [if_neg h0, if_pos rfl, ofN_one, one_mul']
        have hj0 : 0 < R.pcnt i := Nat.pos_of_ne_zero (fun e => h0 (hk0.2 e))
        have hend := (later_end hA hjn hj0).1
        rw [hpj] at hend
        have hlt : (R.row i).hd < (R.row i).ctr := by
          unfold rd at hend; split at hend
          · assumption
          · cases hend
        have hadr : (addrs.getD 0 zero).eval ((R.cpuTableP K).env i) = ofN (R.row i).hd := by
          show (col HD).eval _ = _; rw [cv, rHD]
        have hv := bitsVal_eq (T := R.cpuTableP K) (r := i) (b0 := BITS + 0 * RANGE_BITS)
          (n := (R.row i).ctr - (R.row i).hd - 1) hi (fun b hb => by
            show R.cpuColP K i _ = _
            rw [R.colP_base hp (by show 25 + 0 * 24 + b < 121; unfold RANGE_BITS at hb; omega)
              (by show ¬ (3 ≤ 25 + 0 * 24 + b ∧ 25 + 0 * 24 + b < 17); omega), cpuCol_bit _ _ (by decide) hb]
            rfl) (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.sub_pos_of_lt hlt) Nat.one_pos)
              (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans hctr hlen)))
        rw [show (rangeVal 0).eval ((R.cpuTableP K).env i) = ofN ((R.row i).ctr - (R.row i).hd - 1) from hv,
          hadr, cv, rCTR]
        have e : (R.row i).ctr = ((R.row i).ctr - (R.row i).hd - 1) + (R.row i).hd + 1 := by omega
        rw [show ofN (R.row i).ctr = ofN ((R.row i).ctr - (R.row i).hd - 1) + ofN (R.row i).hd + 1 by
          rw [← ofN_one, ← ofN_add, ← ofN_add]; exact congrArg ofN e]
        exact range_identity _ _
      · rw [if_pos h0, if_neg (by decide), ofN_zero, zero_mul']
  all_goals
    (unfold readCons at he
     simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
     rcases he with ⟨b, hb, rfl⟩ | rfl
     · first
         | exact bits 1 b (by decide) hb
         | exact bits 2 b (by decide) hb
         | exact bits 3 b (by decide) hb
     · simp only [E.eval]
       first
         | rw [ha 1 (by decide) (by decide), zero_mul']
         | rw [ha 2 (by decide) (by decide), zero_mul']
         | rw [ha 3 (by decide) (by decide), zero_mul'])

/-- A probe row's jet constraints. -/
theorem probe_jet {K : Nat} (hK : R.last < K) {i : Nat} (hi : i < K) (hp : R.isP i = true) :
    ∀ e ∈ [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
      bool (col J_RL), bool (col J_RA), bool (col J_RG),
      eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst], e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  have hil := isP_lt hA hp
  have hK1 : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by omega)
  have cv := R.cvP hi
  have htr : (R.cpuTableP K).env i .trans = 1 := by
    show (if i + 1 = K then 0 else 1) = 1; rw [if_neg (by omega)]
  have hfst : (R.cpuTableP K).env i .first = if i = 0 then 1 else 0 := rfl
  obtain ⟨hsel, _, _⟩ := R.pr_sels hi hp
  have hk2 : (if i = 0 then 12 else 13) = 12 ∨ (if i = 0 then 12 else 13) = 13 := by
    split
    · exact .inl rfl
    · exact .inr rfl
  obtain ⟨_, _, _, _, _, _, hsI, _⟩ := probe_facts hi hsel hk2
  have z : ∀ c, CPU_WIDTH ≤ c → c < P_CNT → c ≠ J_CLK → (col c).eval ((R.cpuTableP K).env i) = 0 :=
    fun c h1 h2 h3 => by rw [cv, R.colP_jet hp h1 h2 h3]
  have zl := z J_RL (by decide) (by decide) (by decide)
  have za := z J_RA (by decide) (by decide) (by decide)
  have zg := z J_RG (by decide) (by decide) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [B.whenFirst, E.eval, cv, R.colP_clk' K i, hfst]
    split
    · next h0 => rw [h0, ofN_zero, mul_zero']
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, E.eval, htr, R.nxP, R.colP_clk' K, cv, B.one, B.c, ofN_one, hK1]
    rw [ofN_add, ofN_one, sub_self', mul_zero']
  · simp only [B.bool, E.eval, zl, zero_mul']
  · simp only [B.bool, E.eval, za, zero_mul']
  · simp only [B.bool, E.eval, zg, zero_mul']
  · simp only [B.eq, E.eval, zl, za, zg, hsI, add_zero']; decide

/-- The count's step at a probe row. -/
theorem probe_cntStep {K : Nat} (hK : R.last < K) {i : Nat} (hi : i < K) (hp : R.isP i = true) :
    (whenTrans (eq (nxt P_CNT) (.add (col P_CNT) sProbe))).eval ((R.cpuTableP K).env i) = 0 := by
  have hil := isP_lt hA hp
  have hK1 : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨hsel, _, _⟩ := R.pr_sels hi hp
  have hk2 : (if i = 0 then 12 else 13) = 12 ∨ (if i = 0 then 12 else 13) = 13 := by
    split
    · exact .inl rfl
    · exact .inr rfl
  obtain ⟨_, _, _, _, _, _, _, hsP, _⟩ := probe_facts hi hsel hk2
  simp only [B.whenTrans, B.eq, E.eval, R.nxP, R.cvP hi, R.colP_cnt K, hK1, hsP]
  rw [pcnt_succ hA, hp, if_pos rfl, ofN_add, ofN_one, sub_self', mul_zero']

include hroots in
/-- A later probe row's probe constraints. -/
theorem probe_later {K : Nat} (hK : R.last < K) (hlen : R.A.length ≤ 2 ^ 24) (la : Nat) {i : Nat} (hi : i < K)
    (hp : R.isP i = true) (h0 : i ≠ 0) : ∀ e ∈ probeCons R.n la, e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
  have hil := isP_lt hA hp
  have cv := R.cvP hi
  have hj0 : 0 < R.pcnt i := Nat.pos_of_ne_zero (fun e => h0 ((pr_zero hA hp).2 e))
  obtain ⟨hhead, hpops, hnil⟩ := later_end hA hjn hj0
  rw [hpj] at hhead hpops hnil
  have hctr : (R.row i).ctr ≤ R.A.length := (hA.ctrs hroots i (by unfold last at hil; unfold n at hil; omega)).2.1
  have hrl : R.restE i < (R.row i).ctr := by
    unfold rd at hnil; split at hnil
    · assumption
    · cases hnil
  obtain ⟨_, hsF, hsL⟩ := R.pr_sels hi hp
  have fF : sPFirst.eval ((R.cpuTableP K).env i) = 0 := by rw [hsF, if_neg h0]
  have fL : sPLater.eval ((R.cpuTableP K).env i) = 1 := by rw [hsL, if_neg h0]
  have f0 : (R.cpuTableP K).env i .first = 0 := by show (if i = 0 then 1 else 0) = 0; rw [if_neg h0]
  have hlst : (R.cpuTableP K).env i .last = 0 := by
    show (if i + 1 = K then 1 else 0) = 0; rw [if_neg (by omega)]
  obtain ⟨_, rCTR, _⟩ := pr_regs hA hK hp
  have hcx : ∀ c, P_CNT ≤ c → (col c).eval ((R.cpuTableP K).env i) = R.probeX i c :=
    fun c h => by rw [cv, R.colP_x hp h]
  have xNA : (col P_NILACT).eval ((R.cpuTableP K).env i) = 1 := by
    rw [hcx _ (by decide), R.probeX_nilact i hj0]
  have xNAD : (col P_NILADDR).eval ((R.cpuTableP K).env i) = ofN (R.restE i) := by
    rw [hcx _ (by decide), R.probeX_niladdr i hj0]
  have xER : (col E_REST).eval ((R.cpuTableP K).env i) = ofN (R.restE i) := by
    rw [hcx _ (by decide), R.probeX_rest i hj0]
  have xE2 : (col (E_BASE + 2)).eval ((R.cpuTableP K).env i) = ofN (R.seg (R.pcnt i - 1)).ctor := by
    rw [hcx _ (by decide), R.probeX_E i hj0 (m := 2) (by decide)]; rfl
  have xE0 : (col E_BASE).eval ((R.cpuTableP K).env i) = ofN (R.seg (R.pcnt i - 1)).base := by
    rw [hcx _ (by decide), show E_BASE = E_BASE + 0 from rfl, R.probeX_E i hj0 (m := 0) (by decide)]; rfl
  have hF : (Circuit.fld 0).eval ((R.cpuTableP K).env i) =
      ofN ((R.seg (R.pcnt i - 1)).ctor + (R.seg (R.pcnt i - 1)).base) := by
    show (col (FLD + 0)).eval _ = _
    rw [cv, R.colP_base hp (by decide) (by decide), cpuCol_fld _ _ (by decide), if_pos rfl]
    show ofN (cellFields ((rd R.A (R.row i).ctr (R.row i).hd).getD .nil)).1 = _
    rw [hhead]; rfl
  unfold probeCons at he
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at he
  rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨b, hb, rfl⟩) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · simp only [B.whenFirst, B.eq, E.eval, f0, zero_mul']
  · simp only [B.whenFirst, E.eval, f0, zero_mul']
  · simp only [E.eval, fF, zero_mul']
  · exact probe_cntStep hA hK hi hp
  · simp only [E.eval, fL, one_mul']
    rw [hF, xE2, xE0, ofN_add]; exact ab_sub _ _
  · simp only [B.bool, E.eval, xNA, B.one, B.c, ofN_one]; decide
  · simp only [E.eval, fL, xNA, B.one, B.c, ofN_one, one_mul']; decide
  · simp only [E.eval, fL, xNAD, xER, one_mul', sub_self']
  · simp only [B.bool, E.eval, B.one, B.c, ofN_one]
    rw [hcx _ (show P_CNT ≤ P_NILBITS + b by unfold P_NILBITS; omega), R.probeX_bits i hj0 hb]
    exact JRun.bit_mod _
  · have hv := bitsVal_eq (T := R.cpuTableP K) (r := i) (b0 := P_NILBITS)
      (n := (R.row i).ctr - R.restE i - 1) hi (fun b hb => by
        show R.cpuColP K i _ = _
        rw [R.colP_x hp (by unfold P_NILBITS; omega), R.probeX_bits i hj0 hb])
      (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.sub_pos_of_lt hrl) Nat.one_pos)
        (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans hctr hlen)))
    simp only [E.eval, xNA, xNAD, one_mul', cv, rCTR, B.one, B.c, ofN_one]
    rw [show nilVal.eval ((R.cpuTableP K).env i) = ofN ((R.row i).ctr - R.restE i - 1) from hv]
    have e : (R.row i).ctr = ((R.row i).ctr - R.restE i - 1) + R.restE i + 1 := by omega
    rw [show ofN (R.row i).ctr = ofN ((R.row i).ctr - R.restE i - 1) + ofN (R.restE i) + 1 by
      rw [← ofN_one, ← ofN_add, ← ofN_add]; exact congrArg ofN e]
    exact range_identity _ _
  · simp only [E.eval, fL, B.one, B.c, ofN_one, sub_self', mul_zero']
  · simp only [E.eval, fF, zero_mul']
  all_goals simp only [B.whenLast, B.eq, E.eval, hlst, zero_mul']

/-- The first probe row's probe constraints. -/
theorem probe_first {K : Nat} (hK : R.last < K) (la : Nat) {i : Nat} (hi : i < K)
    (hp : R.isP i = true) (h0 : i = 0) : ∀ e ∈ probeCons R.n la, e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  have hil := isP_lt hA hp
  have cv := R.cvP hi
  have hj0 : R.pcnt i = 0 := (pr_zero hA hp).1 h0
  obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
  obtain ⟨_, hnext⟩ := probe_spec hA hjn
  rw [hpj, hj0] at hnext
  obtain ⟨_, hsF, hsL⟩ := R.pr_sels hi hp
  have fF : sPFirst.eval ((R.cpuTableP K).env i) = 1 := by rw [hsF, if_pos h0]
  have fL : sPLater.eval ((R.cpuTableP K).env i) = 0 := by rw [hsL, if_pos h0]
  have f1 : (R.cpuTableP K).env i .first = 1 := by show (if i = 0 then 1 else 0) = 1; rw [if_pos h0]
  have hlst : (R.cpuTableP K).env i .last = 0 := by
    show (if i + 1 = K then 1 else 0) = 0; rw [if_neg (by omega)]
  obtain ⟨rHD, _⟩ := pr_regs hA hK hp
  have xz : ∀ c, P_CNT ≤ c → c ≠ P_CNT → c ≠ P_F → ¬ (S_BASE ≤ c ∧ c < S_BASE + 6) →
      (col c).eval ((R.cpuTableP K).env i) = 0 := fun c h1 h2 h3 h4 => by
    rw [cv, R.colP_x hp h1, R.probeX_first hj0 h2 h3 h4]
  have xNA := xz P_NILACT (by decide) (by decide) (by decide) (by decide)
  have xNK := xz P_NKIDS (by decide) (by decide) (by decide) (by decide)
  have xCNT : (col P_CNT).eval ((R.cpuTableP K).env i) = 0 := by
    rw [cv, R.colP_cnt, hj0, ofN_zero]
  unfold probeCons at he
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at he
  rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨b, hb, rfl⟩) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · simp only [B.whenFirst, B.eq, E.eval, f1, fF, B.one, B.c, ofN_one, one_mul', sub_self']
  · simp only [B.whenFirst, E.eval, f1, xCNT, one_mul']
  · simp only [E.eval, xCNT, mul_zero']
  · exact probe_cntStep hA hK hi hp
  · simp only [E.eval, fL, zero_mul']
  · simp only [B.bool, E.eval, xNA, zero_mul']
  · simp only [E.eval, fL, zero_mul']
  · simp only [E.eval, fL, zero_mul']
  · simp only [B.bool, E.eval]
    rw [xz (P_NILBITS + b) (by unfold P_NILBITS; omega) (by unfold P_NILBITS P_CNT; omega)
      (by unfold P_NILBITS P_F P_CNT; omega) (by unfold P_NILBITS S_BASE P_CNT; omega), zero_mul']
  · simp only [E.eval, xNA, zero_mul']
  · simp only [E.eval, xNK, zero_mul']
  · simp only [E.eval, fF, one_mul', cv, rHD]
    rw [R.colP_x hp (by decide), R.probeX_f, hnext]
    show ofN (fptr R.plan R.fld (R.row 0).hd 0) - ofN (R.row i).hd = 0
    unfold fptr; rw [if_pos rfl, h0, sub_self']
  all_goals simp only [B.whenLast, B.eq, E.eval, hlst, zero_mul']

/-- A probe row's next registers, first registers and last-row halt. -/
theorem probe_regs {K : Nat} (hK : R.last < K) {i : Nat} (hi : i < K) (hp : R.isP i = true) :
    ∀ e ∈ [whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F)))),
     whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
       (.mul sProbe (.add (col CTR) (col (S_BASE + 1)))))),
     whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
       (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one)))),
     whenFirst (eq (col HD) (c (R.row 0).hd)), whenFirst (eq (col STK) (c (R.row 0).stk)),
     whenFirst (eq (col CTR) (c (R.row 0).ctr)),
     whenLast (eq halt one)], e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  obtain ⟨hjn, hpj⟩ := isP_pcnt hA hp
  have hil := isP_lt hA hp
  have hK1 : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by omega)
  have cv := R.cvP hi
  obtain ⟨_, hnext⟩ := probe_spec hA hjn
  rw [hpj] at hnext
  obtain ⟨hsel, _, _⟩ := R.pr_sels hi hp
  have hk2 : (if i = 0 then 12 else 13) = 12 ∨ (if i = 0 then 12 else 13) = 13 := by
    split
    · exact .inl rfl
    · exact .inr rfl
  obtain ⟨_, _, _, _, _, _, hsI, hsP, _, _, hnHd, hnStk, hnCtr⟩ := probe_facts hi hsel hk2
  obtain ⟨rHD, rCTR, nHD, nSTK, nCTR⟩ := pr_regs hA hK hp
  have htr : (R.cpuTableP K).env i .trans = 1 := by
    show (if i + 1 = K then 0 else 1) = 1; rw [if_neg (by omega)]
  have hlst : (R.cpuTableP K).env i .last = 0 := by
    show (if i + 1 = K then 1 else 0) = 0; rw [if_neg (by omega)]
  have hS1 : (col (S_BASE + 1)).eval ((R.cpuTableP K).env i) = ofN (R.seg (R.pcnt i)).k := by
    rw [cv, R.colP_x hp (by decide), R.probeX_s i (by decide)]; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', R.nxP, hK1, nHD, hnHd, jetHd_probe hi hp, hsP, zero_add',
      cv, R.colP_x hp (show P_CNT ≤ P_F by decide), R.probeX_f, sub_self']
  · simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', R.nxP, hK1, nSTK, hnStk, hsI, hsP, zero_mul', zero_add',
      hS1, cv, rCTR]
    rw [hnext, ← ofN_add, sub_self']
  · simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', R.nxP, hK1, nCTR, hnCtr, hsI, hsP, zero_mul', add_zero',
      hS1, cv, rCTR, B.c, B.one, ofN_one]
    rw [hnext]
    show ofN ((R.row i).ctr + ((R.seg (R.pcnt i)).k + (R.seg (R.pcnt i)).k + 1)) -
      (R.cpuColP K i CTR + (ofN (R.seg (R.pcnt i)).k * ofN 2 + 1)) = 0
    rw [rCTR, ← ofN_mul, ← ofN_one, ← ofN_add, ← ofN_add, Nat.mul_two, sub_self']
  all_goals first
    | (simp only [B.whenLast, B.eq, E.eval, hlst, zero_mul']; done)
    | (simp only [B.whenFirst, B.eq, B.c, E.eval, cv]
       show (if i = 0 then (1 : F) else 0) * _ = 0
       split
       · next h0 =>
         subst h0
         rw [regP hA (by decide), JRun.rowQ_lt (by show 0 < R.last + 1; omega), one_mul']
         exact sub_self' _
       · exact zero_mul' _)

include hroots in
/-- **A probe row satisfies the probe CPU's constraints.** -/
theorem probe_rowSat {K : Nat} (hK : R.last < K) (hlen : R.A.length ≤ 2 ^ 24) (la : Nat) {i : Nat} (hi : i < K)
    (hp : R.isP i = true) :
    ∀ e ∈ cpuConsP (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la, e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  rw [cpuConsP_split] at he
  rcases List.mem_append.1 he with he | he
  · exact probe_pre hA hroots hK hlen hi hp e he
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact probe_jet hA hK hi hp e he
      · rcases Nat.decEq i 0 with h0 | h0
        · exact probe_later hA hroots hK hlen la hi hp h0 e he
        · exact probe_first hA hK la hi hp h0 e he
    · exact probe_regs hA hK hi hp e he

-- ---------------------------------------------------------------------------
-- A row within a segment
-- ---------------------------------------------------------------------------

omit hA in
/-- The jet CPU's atoms: its columns now, and the registers and clock next. -/
def atomJJ : Atom → Bool
  | .main 0 c => decide (c < P_CNT)
  | .main 1 c => decide (c < 3) || decide (c = J_CLK)
  | .first | .last | .trans => true
  | _ => false

set_option maxRecDepth 100000 in
omit hA in
theorem cpuConsJ_atoms (hd0 stk0 ctr0 : Nat) : (cpuConsJ hd0 stk0 ctr0).all (·.onlyAtoms atomJJ) = true := rfl

/-- **The probe table agrees with the jet table** on a row within a
    segment, on every atom the jet CPU reads. -/
theorem env_agreeP {K i : Nat} (hi : i < K) (hp : R.isP i = false) :
    ∀ a, atomJJ a = true → (R.cpuTableP K).env i a = (R.J.cpuTable K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    rcases o with _ | _ | o
    · simp only [atomJJ, decide_eq_true_eq] at ha
      show R.cpuColP K ((i + 0) % K) c = R.J.cpuCol ((i + 0) % K) c
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi, R.colP_low hp ha]
    · simp only [atomJJ, Bool.or_eq_true, decide_eq_true_eq] at ha
      show R.cpuColP K ((i + 1) % K) c = R.J.cpuCol ((i + 1) % K) c
      rcases ha with ha | ha
      · rw [regP hA ha, R.J.col_reg _ ha R.J.rowQ_inst]; rfl
      · subst ha; rw [R.colP_clk', R.J.col_clk]
    · simp [atomJJ] at ha
  | pre _ _ => simp [atomJJ] at ha
  | first => rfl
  | last => rfl
  | trans => rfl

omit hA in
/-- The jet table's probe selectors are zero. -/
theorem J_sel_probe (i : Nat) {m : Nat} (hm : m = 12 ∨ m = 13) : R.J.cpuCol i (SEL + m) = 0 := by
  have hk := kindOf_lt R.J.A (R.J.rowQ i)
  unfold JRun.cpuCol
  rcases hm with rfl | rfl
  all_goals
    cases hn : R.J.instAt i with
    | none =>
      simp only
      rw [if_pos (by decide), cpuCol_sel _ _ (by decide), if_neg (by omega)]
    | some q =>
      obtain ⟨g, J⟩ := q
      simp only
      exact R.J.instCol_low i g J (by decide) (by decide) (by decide)

omit hA in
theorem normX_zero {K i c : Nat} (h1 : c ≠ P_CNT)
    (h2 : i + 1 ≠ K ∨ (c ≠ P_NILACT ∧ c ≠ P_NILADDR ∧ c < P_NILBITS)) : R.normX K i c = 0 := by
  unfold normX
  rw [if_neg h1]
  rcases h2 with h2 | ⟨a, b, d⟩
  · rw [if_neg h2]
  · split
    · first
        | rw [if_neg a, if_neg b, if_neg (by omega)]
        | rw [if_neg (by omega)]
    · rfl

omit hA in
theorem normX_last {K i : Nat} (hl : i + 1 = K) :
    R.normX K i P_NILACT = 1 ∧ R.normX K i P_NILADDR = ofN (R.J.rowQ i).stk ∧
    ∀ b, R.normX K i (P_NILBITS + b) = ofN ((((R.J.rowQ i).ctr - (R.J.rowQ i).stk - 1) / 2 ^ b) % 2) := by
  refine ⟨?_, ?_, fun b => ?_⟩
  · unfold normX; rw [if_neg (by decide), if_pos hl, if_pos rfl]
  · unfold normX; rw [if_neg (by decide), if_pos hl, if_neg (by decide), if_pos rfl]
  · unfold normX
    rw [if_neg (by unfold P_NILBITS P_CNT; omega), if_pos hl, if_neg (by unfold P_NILBITS P_NILACT; omega),
      if_neg (by unfold P_NILBITS P_NILADDR; omega), if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

include hroots in
/-- The table's last row: a copy of the run's last, which counts every
    segment, reads the last marker at its head and a nil at its stack. -/
theorem last_facts {K i : Nat} (hK : R.last < K) (hl : i + 1 = K) (hlast : (R.seg (R.n - 1)).arity = 0) :
    R.J.rowQ i = R.row R.last ∧ R.pcnt i = R.n ∧ (R.row R.last).stk < (R.row R.last).ctr ∧
    (R.row R.last).ctr ≤ R.A.length ∧
    rd R.A (R.row R.last).ctr (R.row R.last).hd =
      some (.atom ((R.seg (R.n - 1)).ctor + (R.seg (R.n - 1)).base)) := by
  have hq : R.J.rowQ i = R.row R.last := by
    rcases Nat.lt_or_ge i (R.last + 1) with h | h
    · rw [JRun.rowQ_lt h]
      show R.row i = R.row R.last
      rw [show i = R.last by omega]
    · rw [JRun.rowQ_ge h]; rfl
  obtain ⟨rest, hhead, hpop, hnil⟩ := last_end hA
  rw [hlast] at hpop
  have hr : rest = (R.row R.last).stk := by
    have e : (some ([], (R.row R.last).stk) : Option (List Nat × Nat)) = some (R.fld (R.n - 1), rest) := hpop
    exact (congrArg Prod.snd (Option.some.inj e)).symm
  rw [hr] at hnil
  refine ⟨hq, ?_, ?_, (hA.ctrs hroots R.last (Nat.le_refl _)).2.1, hhead⟩
  · rcases Nat.lt_or_ge R.last i with h | h
    · exact pcnt_ge hA h
    · have : i = R.last := by omega
      rw [this]; exact pcnt_p hA (Nat.le_refl _)
  · unfold rd at hnil; split at hnil
    · assumption
    · cases hnil

include hroots in
/-- **A row within a segment satisfies the probe CPU's constraints**, the
    last segment having no fields and `la` its marker. -/
theorem norm_rowSat {K : Nat} (hK : R.last < K) (hlen : R.A.length ≤ 2 ^ 24)
    (hlast : (R.seg (R.n - 1)).arity = 0) {la : Nat} (hla : la = (R.seg (R.n - 1)).ctor + (R.seg (R.n - 1)).base)
    {i : Nat} (hi : i < K) (hp : R.isP i = false) :
    ∀ e ∈ cpuConsP (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la, e.eval ((R.cpuTableP K).env i) = 0 := by
  intro e he
  have hJ := jok hA hroots
  have cv := R.cvP hi
  have tr : ∀ e ∈ cpuConsJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr, e.eval ((R.cpuTableP K).env i) = 0 := by
    intro e he'
    rw [E.eval_congr (env_agreeP hA hi hp) e (List.all_eq_true.1 (cpuConsJ_atoms _ _ _) e he')]
    exact R.J.cpu_row hJ (show R.last + 1 ≤ K by omega) hlen hi hp e he'
  have hs12 : (col (SEL + 12)).eval ((R.cpuTableP K).env i) = 0 := by
    rw [cv, R.colP_low hp (by decide), R.J_sel_probe i (.inl rfl)]
  have hs13 : (col (SEL + 13)).eval ((R.cpuTableP K).env i) = 0 := by
    rw [cv, R.colP_low hp (by decide), R.J_sel_probe i (.inr rfl)]
  have fF : sPFirst.eval ((R.cpuTableP K).env i) = 0 := hs12
  have fL : sPLater.eval ((R.cpuTableP K).env i) = 0 := hs13
  have fP : sProbe.eval ((R.cpuTableP K).env i) = 0 := by
    show sPFirst.eval _ + sPLater.eval _ = 0; rw [fF, fL, add_zero']
  have hn0 : 0 < R.n := hA.nonempty
  have hi0 : i ≠ 0 := fun h0 => by
    have := isP_p hA hn0
    rw [hA.p0, ← h0, hp] at this; cases this
  have f0 : (R.cpuTableP K).env i .first = 0 := by show (if i = 0 then 1 else 0) = 0; rw [if_neg hi0]
  have hcx : ∀ c, P_CNT ≤ c → (col c).eval ((R.cpuTableP K).env i) = R.normX K i c :=
    fun c h => by rw [cv, R.colP_high hp h]
  rw [cpuConsP_split] at he
  rcases List.mem_append.1 he with he | he
  · exact tr e (by rw [cpuConsJ_split]; exact List.mem_append_left _ he)
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact tr e (by
          rw [cpuConsJ_split]; refine List.mem_append_right _ ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
          rcases he with h | h | h | h | h | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr (.inl h)))
          · exact .inr (.inr (.inr (.inr (.inl h))))
          · exact .inr (.inr (.inr (.inr (.inr (.inl h))))))
      · -- the probe constraints
        unfold probeCons at he
        simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at he
        rcases Nat.decEq (i + 1) K with hl | hl
        · -- an inner row
          have hlst : (R.cpuTableP K).env i .last = 0 := by
            show (if i + 1 = K then 1 else 0) = 0; rw [if_neg hl]
          have htr : (R.cpuTableP K).env i .trans = 1 := by
            show (if i + 1 = K then 0 else 1) = 1; rw [if_neg hl]
          have hK1 : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by omega)
          have xz : ∀ c, P_CNT ≤ c → c ≠ P_CNT → (col c).eval ((R.cpuTableP K).env i) = 0 :=
            fun c h1 h2 => by rw [hcx c h1, R.normX_zero h2 (.inl hl)]
          rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨b, hb, rfl⟩) |
            (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · simp only [B.whenFirst, B.eq, E.eval, f0, zero_mul']
          · simp only [B.whenFirst, E.eval, f0, zero_mul']
          · simp only [E.eval, fF, zero_mul']
          · simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', R.nxP, hK1, cv, R.colP_cnt K, fP]
            rw [pcnt_succ hA, hp, if_neg Bool.false_ne_true, Nat.add_zero, add_zero', sub_self']
          · simp only [E.eval, fL, zero_mul']
          · simp only [B.bool, E.eval, xz P_NILACT (by decide) (by decide), zero_mul']
          · simp only [E.eval, fL, zero_mul']
          · simp only [E.eval, fL, zero_mul']
          · simp only [B.bool, E.eval]
            rw [xz (P_NILBITS + b) (by unfold P_NILBITS; omega) (by unfold P_NILBITS P_CNT; omega), zero_mul']
          · simp only [E.eval, xz P_NILACT (by decide) (by decide), zero_mul']
          · simp only [E.eval, xz P_NKIDS (by decide) (by decide), zero_mul']
          · simp only [E.eval, fF, zero_mul']
          all_goals simp only [B.whenLast, B.eq, E.eval, hlst, zero_mul']
        · -- the table's last row
          obtain ⟨hq, hpc, hsc, hctr, hhead⟩ := last_facts hA hroots hK hl hlast
          obtain ⟨xNA, xNAD, xB⟩ := R.normX_last hl
          rw [hq] at xNAD xB
          have hlst : (R.cpuTableP K).env i .last = 1 := by
            show (if i + 1 = K then 1 else 0) = 1; rw [if_pos hl]
          have htr : (R.cpuTableP K).env i .trans = 0 := by
            show (if i + 1 = K then 0 else 1) = 0; rw [if_pos hl]
          have hn : R.J.instAt i = none := JRun.instAt_none_of (by show R.last + 1 ≤ i + 1; omega)
          have cq : ∀ c, c < CPU_WIDTH → (col c).eval ((R.cpuTableP K).env i) = Circuit.cpuCol R.A (R.row R.last) c := by
            intro c hc
            rw [cv, R.colP_low hp (by unfold P_CNT J_CLK JET_WIDTH; omega)]
            unfold JRun.cpuCol; rw [hn]; simp only; rw [if_pos hc, hq]; rfl
          have hkind : kindOf R.A (R.row R.last) = 10 := kindOf_atom hhead
          rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨b, hb, rfl⟩) |
            (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · simp only [B.whenFirst, B.eq, E.eval, f0, zero_mul']
          · simp only [B.whenFirst, E.eval, f0, zero_mul']
          · simp only [E.eval, fF, zero_mul']
          · simp only [B.whenTrans, E.eval, htr, zero_mul']
          · simp only [E.eval, fL, zero_mul']
          · simp only [B.bool, E.eval, hcx _ (show P_CNT ≤ P_NILACT by decide), xNA, B.one, B.c, ofN_one]; decide
          · simp only [E.eval, fL, zero_mul']
          · simp only [E.eval, fL, zero_mul']
          · simp only [B.bool, E.eval, B.one, B.c, ofN_one]
            rw [hcx _ (show P_CNT ≤ P_NILBITS + b by unfold P_NILBITS; omega), xB b]
            exact JRun.bit_mod _
          · have hv := bitsVal_eq (T := R.cpuTableP K) (r := i) (b0 := P_NILBITS)
              (n := (R.row R.last).ctr - (R.row R.last).stk - 1) hi (fun b hb => by
                show R.cpuColP K i _ = _
                rw [R.colP_high hp (by unfold P_NILBITS; omega), xB b])
              (Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.sub_pos_of_lt hsc) Nat.one_pos)
                (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans hctr hlen)))
            simp only [E.eval, hcx _ (show P_CNT ≤ P_NILACT by decide), hcx _ (show P_CNT ≤ P_NILADDR by decide),
              xNA, xNAD, one_mul', cq CTR (by decide), B.one, B.c, ofN_one]
            rw [show nilVal.eval ((R.cpuTableP K).env i) = ofN ((R.row R.last).ctr - (R.row R.last).stk - 1) from hv]
            have e : (R.row R.last).ctr = ((R.row R.last).ctr - (R.row R.last).stk - 1) + (R.row R.last).stk + 1 := by
              omega
            rw [show Circuit.cpuCol R.A (R.row R.last) CTR = ofN ((R.row R.last).ctr - (R.row R.last).stk - 1) +
                ofN (R.row R.last).stk + 1 by
              show ofN (R.row R.last).ctr = _
              rw [← ofN_one, ← ofN_add, ← ofN_add]; exact congrArg ofN e]
            exact range_identity _ _
          · simp only [E.eval, hcx _ (show P_CNT ≤ P_NKIDS by decide),
              R.normX_zero (c := P_NKIDS) (by decide) (.inr ⟨by decide, by decide, by decide⟩), zero_mul']
          · simp only [E.eval, fF, zero_mul']
          · simp only [B.whenLast, B.eq, B.c, E.eval, hlst, one_mul', hcx _ (show P_CNT ≤ P_CNT by decide)]
            rw [show R.normX K i P_CNT = ofN (R.pcnt i) from rfl, hpc, sub_self']
          · simp only [B.whenLast, B.eq, B.one, B.c, ofN_one, sHA, E.eval, hlst, one_mul', cq _ (show SEL + 10 < CPU_WIDTH by decide)]
            rw [cpuCol_sel _ _ (by decide), hkind, if_pos rfl, sub_self']
          · simp only [B.whenLast, B.eq, B.c, Circuit.fld, E.eval, hlst, one_mul', cq _ (show FLD + 0 < CPU_WIDTH by decide)]
            rw [cpuCol_fld _ _ (by decide), if_pos rfl]
            show ofN (cellFields ((rd R.A (R.row R.last).ctr (R.row R.last).hd).getD .nil)).1 - ofN la = 0
            rw [hhead, hla]; exact sub_self' _
          · simp only [B.whenLast, B.eq, B.one, B.c, ofN_one, E.eval, hlst, one_mul', hcx _ (show P_CNT ≤ P_NILACT by decide), xNA]
            exact sub_self' _
          · simp only [B.whenLast, B.eq, E.eval, hlst, one_mul', hcx _ (show P_CNT ≤ P_NILADDR by decide), xNAD,
              cq STK (by decide)]
            exact sub_self' _
    · -- the registers, first and last
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have := tr (whenTrans (eq (nxt HD) (.add nextHd jetHd))) (by simp [cpuConsJ])
        simp only [B.whenTrans, B.eq, E.eval] at this ⊢
        rw [fP, zero_mul', add_zero']; exact this
      · have := tr (whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST))))) (by simp [cpuConsJ])
        simp only [B.whenTrans, B.eq, E.eval] at this ⊢
        rw [fP, zero_mul', add_zero']; exact this
      · have := tr (whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N))))) (by simp [cpuConsJ])
        simp only [B.whenTrans, B.eq, E.eval] at this ⊢
        rw [fP, zero_mul', add_zero']; exact this
      · exact tr _ (by simp [cpuConsJ])
      · exact tr _ (by simp [cpuConsJ])
      · exact tr _ (by simp [cpuConsJ])
      · exact tr _ (by simp [cpuConsJ])

include hroots in
/-- **The honest probe CPU satisfies the probe CPU's AIR**, for a run whose
    last segment has no fields and `la` its marker. -/
theorem cpu_satP {K : Nat} (hK : R.last < K) (hlen : R.A.length ≤ 2 ^ 24)
    (hlast : (R.seg (R.n - 1)).arity = 0) {la : Nat} (hla : la = (R.seg (R.n - 1)).ctor + (R.seg (R.n - 1)).base) :
    Sat (cpuAirP (R.row 0).hd (R.row 0).stk (R.row 0).ctr R.n la) (R.cpuTableP K) := by
  refine ⟨by show 0 < K; omega, fun e he i (hi : i < K) => ?_⟩
  cases hp : R.isP i with
  | true => exact probe_rowSat hA hroots hK hlen la hi hp e he
  | false => exact norm_rowSat hA hroots hK hlen hlast hla hi hp e he

end PRun

end Circuit
