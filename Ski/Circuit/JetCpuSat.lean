import Ski.Circuit.JetHonest

/-!
# The honest jet CPU satisfies its AIR

A corpus row satisfies the corpus constraints (`cpu_rowSat`), and the jet
table agrees with the corpus table on every column those constraints
read: the corpus columns now and the registers next (`cpuAtomJ`).  Its jet
columns are zero but the counter, so the jet constraints hold.  An
instantiation row is checked constraint by constraint (`JRun.cpu_sat`).
-/

namespace Circuit

open B Air JetTable Mach

/-- The corpus CPU's atoms: its columns now, its registers next, and the
    selectors. -/
def cpuAtomJ : Atom → Bool
  | .main 0 c => decide (c < CPU_WIDTH)
  | .main 1 c => decide (c < 3)
  | .first | .last | .trans => true
  | _ => false

set_option maxRecDepth 100000 in
theorem cpuCons_atomsJ (hd0 stk0 ctr0 : Nat) : (cpuCons hd0 stk0 ctr0).all (·.onlyAtoms cpuAtomJ) = true := rfl

namespace JRun

variable (R : JRun)

theorem col_reg (j : Nat) {c : Nat} (hc : c < 3) (hj : R.instAt j ≠ none → R.rowQ j = R.row j) :
    R.cpuCol j c = Circuit.cpuCol R.A (R.rowQ j) c := by
  unfold cpuCol
  cases h : R.instAt j with
  | none => simp only; rw [if_pos (Nat.lt_trans hc (by decide))]
  | some p =>
    obtain ⟨g, J⟩ := p
    simp only
    rw [hj (by rw [h]; exact fun e => by cases e)]
    unfold instCol
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl

theorem col_clk (j : Nat) : R.cpuCol j J_CLK = ofN j := by
  unfold cpuCol
  cases R.instAt j with
  | none => simp only; rw [if_neg (by decide), if_pos trivial]
  | some p => obtain ⟨g, J⟩ := p; rfl

theorem rowQ_inst {j : Nat} (hj : R.instAt j ≠ none) : R.rowQ j = R.row j := by
  cases h : R.instAt j with
  | none => exact absurd h hj
  | some p => obtain ⟨g, J⟩ := p; exact rowQ_lt (Nat.lt_of_succ_lt (instAt_some h).1)

theorem opCols_bit (o : Op) (q : Nat) (hq : q < 3) :
    (opCols o).getD q 0 * ((opCols o).getD q 0 - 1) = 0 := by
  have z : (ofN 0 : F) * (ofN 0 - 1) = 0 := by decide
  have u : (ofN 1 : F) * (ofN 1 - 1) = 0 := by decide
  cases o <;> rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl <;> first | exact z | exact u

theorem opCols_sum (o : Op) : (opCols o).getD 0 0 + (opCols o).getD 1 0 + (opCols o).getD 2 0 - 1 = 0 := by
  cases o
  · show (ofN 1 : F) + ofN 0 + ofN 0 - 1 = 0; decide
  · show (ofN 0 : F) + ofN 1 + ofN 0 - 1 = 0; decide
  · show (ofN 0 : F) + ofN 0 + ofN 1 - 1 = 0; decide

theorem instCol_other (i g : Nat) (J : Air.Jet) {c : Nat}
    (h : c ≠ HD ∧ c ≠ STK ∧ c ≠ CTR ∧ c ≠ SEL + 11 ∧ c ≠ J_CLK ∧ c ≠ J_G ∧ c ≠ J_K ∧ c ≠ J_N ∧ c ≠ J_RL ∧
      c ≠ J_RA ∧ c ≠ J_RG ∧ c ≠ J_RV ∧ c ≠ J_XROOT ∧ c ≠ J_REST) : R.instCol i g J c = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  unfold instCol
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8, if_neg h9,
    if_neg h10, if_neg h11, if_neg h12, if_neg h13, if_neg h14]

/-- Columns below the jet columns and above the selectors' first eleven. -/
theorem instCol_low (i g : Nat) (J : Air.Jet) {c : Nat} (h3 : 3 ≤ c) (h14 : c ≠ 14) (h121 : c < 121) :
    R.instCol i g J c = 0 := by
  have c1 : HD = 0 := rfl
  have c2 : STK = 1 := rfl
  have c3 : CTR = 2 := rfl
  have c4 : SEL = 3 := rfl
  have c5 : J_CLK = 121 := rfl
  have c6 : J_G = 122 := rfl
  have c7 : J_K = 123 := rfl
  have c8 : J_N = 124 := rfl
  have c9 : J_RL = 125 := rfl
  have c10 : J_RA = 126 := rfl
  have c11 : J_RG = 127 := rfl
  have c12 : J_RV = 128 := rfl
  have c13 : J_XROOT = 129 := rfl
  have c14 : J_REST = 130 := rfl
  exact R.instCol_other i g J ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem instCol_sel (i g : Nat) (J : Air.Jet) {j : Nat} (hj : j < NKINDS) :
    R.instCol i g J (SEL + j) = if j = 11 then 1 else 0 := by
  rcases Nat.decEq j 11 with h | h
  · rw [if_neg h]
    exact R.instCol_low i g J (by unfold SEL; omega) (by unfold SEL; omega) (by unfold SEL NKINDS at *; omega)
  · subst h; rfl

theorem env_agree {K i : Nat} (hi : i < K) (hn : R.instAt i = none) :
    ∀ a, cpuAtomJ a = true → (R.cpuTable K).env i a = (Circuit.cpuTable R.A R.rowQ K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    rcases o with _ | _ | o
    · simp only [cpuAtomJ, decide_eq_true_eq] at ha
      show R.cpuCol ((i + 0) % K) c = Circuit.cpuCol R.A (R.rowQ ((i + 0) % K)) c
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
      unfold cpuCol; rw [hn]; simp only; rw [if_pos ha]
    · simp only [cpuAtomJ, decide_eq_true_eq] at ha
      show R.cpuCol ((i + 1) % K) c = Circuit.cpuCol R.A (R.rowQ ((i + 1) % K)) c
      exact R.col_reg _ ha (R.rowQ_inst)
    · simp [cpuAtomJ] at ha
  | pre _ _ => simp [cpuAtomJ] at ha
  | first => rfl
  | last => rfl
  | trans => rfl

/-- The corpus parts of a jet-CPU constraint agree with the corpus CPU's. -/
theorem mem_cpuCons_of_pre {hd0 stk0 ctr0 : Nat} {e : E} (he : e ∈ cpuPre) : e ∈ cpuCons hd0 stk0 ctr0 := by
  rw [cpuCons_split]; exact List.mem_append_left _ he

/-- **The honest jet CPU satisfies the jet CPU's AIR.** -/
theorem cpu_sat {m0 : Mach} (hA : AcceptsJ R.A m0 R.roots R.jets R.k R.row) (hroots : RootsOK m0.heap R.roots R.jets)
    {K : Nat} (hkK : R.k ≤ K) (hlen : R.A.length ≤ 2 ^ 24) :
    Sat (cpuAirJ (R.row 0).hd (R.row 0).stk (R.row 0).ctr) (R.cpuTable K) := by
  have hk := hA.pos
  have hK0 : 0 < K := Nat.lt_of_lt_of_le hk hkK
  refine ⟨hK0, fun e he i (hi : i < K) => ?_⟩
  have cvJ : ∀ c, (col c).eval ((R.cpuTable K).env i) = R.cpuCol i c := by
    intro c; show R.cpuCol ((i + 0) % K) c = _; rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  have nxJ : ∀ c, (nxt c).eval ((R.cpuTable K).env i) = R.cpuCol ((i + 1) % K) c := fun c => rfl
  have e0 : R.rowQ 0 = R.row 0 := rowQ_lt hk
  change e ∈ cpuConsJ _ _ _ at he
  rw [cpuConsJ_split] at he
  cases hn : R.instAt i with
  | none =>
    have hvi := base_valid hA hn
    have hrs := cpu_rowSat (M := R.A) (row := R.rowQ) (k := K) hi hvi (fun _ => base_trans hA hn)
      (fun h1 => by rw [Nat.eq_sub_of_add_eq h1]; exact last_halt hA hkK)
      (Nat.le_trans (ctr_le hA hroots i) hlen)
    rw [e0] at hrs
    have tr : ∀ e ∈ cpuCons (R.row 0).hd (R.row 0).stk (R.row 0).ctr, e.eval ((R.cpuTable K).env i) = 0 := by
      intro e he'
      rw [E.eval_congr (R.env_agree hi hn) e (List.all_eq_true.1 (cpuCons_atomsJ _ _ _) e he')]
      exact hrs e he'
    rcases List.mem_append.1 he with he | he
    · exact tr e (mem_cpuCons_of_pre he)
    · have z : ∀ c, CPU_WIDTH ≤ c → c ≠ J_CLK → R.cpuCol i c = 0 := by
        intro c h1 h2; unfold cpuCol; rw [hn]; simp only; rw [if_neg (by omega), if_neg h2]
      have zl := z J_RL (by decide) (by decide)
      have za := z J_RA (by decide) (by decide)
      have zg := z J_RG (by decide) (by decide)
      have hsel : R.cpuCol i (SEL + 11) = 0 := by
        unfold cpuCol; rw [hn]; simp only; rw [if_pos (by decide), cpuCol_sel _ _ (by decide),
          if_neg (Nat.ne_of_gt (shape hvi).lt)]
      have hjet : jetHd.eval ((R.cpuTable K).env i) = 0 := by
        simp only [jetHd, E.eval, cvJ, zl, za, zg, zero_mul', add_zero']
      have hI : sInst.eval ((R.cpuTable K).env i) = 0 := by simp only [sInst, cvJ, hsel]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [B.whenFirst, E.eval, cvJ, col_clk, env_first]
        split
        · next h0 => rw [h0, ofN_zero, mul_zero']
        · exact zero_mul' _
      · simp only [B.whenTrans, B.eq, E.eval, env_trans, nxJ, col_clk, cvJ, B.one, B.c, ofN_one]
        split
        · exact zero_mul' _
        · next hl =>
          have e : (R.cpuTable K).h = K := rfl
          rw [e] at hl
          rw [Nat.mod_eq_of_lt (by omega), ofN_add, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cvJ, zl, zero_mul']
      · simp only [B.bool, E.eval, cvJ, za, zero_mul']
      · simp only [B.bool, E.eval, cvJ, zg, zero_mul']
      · simp only [B.eq, E.eval, cvJ, zl, za, zg, hI, add_zero']; decide
      · exact tr _ (by simp [cpuCons])
      · exact tr _ (by simp [cpuCons])
      · have := tr (whenTrans (eq (nxt HD) nextHd)) (by simp [cpuCons])
        simp only [B.whenTrans, B.eq, E.eval] at this ⊢
        rw [hjet, add_zero']; exact this
      · have := tr (whenTrans (eq (nxt STK) nextStk)) (by simp [cpuCons])
        simp only [B.whenTrans, B.eq, E.eval] at this ⊢
        rw [show (sInst.eval ((R.cpuTable K).env i)) = 0 from hI, zero_mul', add_zero']; exact this
      · have := tr (whenTrans (eq (nxt CTR) nextCtr)) (by simp [cpuCons])
        simp only [B.whenTrans, B.eq, E.eval] at this ⊢
        rw [show (sInst.eval ((R.cpuTable K).env i)) = 0 from hI, zero_mul', add_zero']; exact this
      · exact tr _ (by simp [cpuCons])
      · exact tr _ (by simp [cpuCons])
      · exact tr _ (by simp [cpuCons])
      · exact tr _ (by simp [cpuCons])
  | some p =>
    obtain ⟨g, J⟩ := p
    obtain ⟨hi1, _, _, _⟩ := instAt_some hn
    obtain ⟨_, _, _, hnext⟩ := inst_spec hn
    have cI : ∀ c, R.cpuCol i c = R.instCol i g J c := by intro c; unfold cpuCol; rw [hn]
    have hsel : SelsAre (R.cpuTable K) i 11 := fun j hj => by
      show R.cpuCol i (SEL + j) = _
      rw [cI, R.instCol_sel i g J hj]
    obtain ⟨hacts, hhalt, _, _, hnHd, hnStk, hnCtr⟩ := inst_facts hi hsel
    have cvI : ∀ c, (col c).eval ((R.cpuTable K).env i) = R.instCol i g J c := fun c => by rw [cvJ, cI]
    -- the next row's registers
    have hK1 : (i + 1) % K = i + 1 := Nat.mod_eq_of_lt (by omega)
    have nreg : ∀ c, c < 3 → (nxt c).eval ((R.cpuTable K).env i) = Circuit.cpuCol R.A (R.row (i + 1)) c := by
      intro c hc
      rw [nxJ, hK1, R.col_reg _ hc R.rowQ_inst, rowQ_lt hi1]
    have hroot := (symCells J J.body 0).2
    rcases List.mem_append.1 he with he | he
    · unfold cpuPre at he
      simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
      rcases he with (((((⟨j, hj, rfl⟩ | rfl) | he) | he) | he) | he)
      · simp only [B.bool, E.eval, cvI, R.instCol_sel i g J hj, B.one, B.c, ofN_one]
        split <;> decide
      · have hk := kind_evalS hi hsel (e := B.eq (B.sum ((List.range NKINDS).map fun i => B.col (SEL + i))) B.one)
          (e' := zero) (by decide)
        rw [hk]; rfl
      all_goals
        (unfold readCons at he
         simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at he
         rcases he with ⟨b, hb, rfl⟩ | rfl
         · simp only [B.bool, E.eval, cvI, B.one, B.c, ofN_one]
           rw [R.instCol_low i g J (by unfold BITS FLD SEL NKINDS; omega) (by unfold BITS FLD SEL NKINDS; omega)
             (by unfold BITS FLD SEL NKINDS RANGE_BITS at *; omega), zero_mul']
         · simp only [E.eval]
           first
             | rw [hacts 0 (by decide), zero_mul']
             | rw [hacts 1 (by decide), zero_mul']
             | rw [hacts 2 (by decide), zero_mul']
             | rw [hacts 3 (by decide), zero_mul'])
    · have vRL : R.instCol i g J J_RL = (opCols (symCells J J.body 0).2).getD 0 0 := rfl
      have vRA : R.instCol i g J J_RA = (opCols (symCells J J.body 0).2).getD 1 0 := rfl
      have vRG : R.instCol i g J J_RG = (opCols (symCells J J.body 0).2).getD 2 0 := rfl
      have vRV : R.instCol i g J J_RV = (opCols (symCells J J.body 0).2).getD 3 0 := rfl
      have vX : R.instCol i g J J_XROOT = ofN (argVal (R.ps i J) (symCells J J.body 0).2) := rfl
      have vR : R.instCol i g J J_REST = ofN (R.rest i J) := rfl
      have vN : R.instCol i g J J_N = ofN (symCells J J.body 0).1.length := rfl
      have vI : R.instCol i g J (SEL + 11) = 1 := rfl
      have vC : R.instCol i g J CTR = ofN (R.row i).ctr := rfl
      have v12 : R.instCol i g J (SEL + 12) = 0 := R.instCol_low i g J (by decide) (by decide) (by decide)
      have v13 : R.instCol i g J (SEL + 13) = 0 := R.instCol_low i g J (by decide) (by decide) (by decide)
      have hla : (R.cpuTable K).env i .last = 0 := by
        show (if i + 1 = K then 1 else 0) = 0; rw [if_neg (by omega)]
      have htr : (R.cpuTable K).env i .trans = 1 := by
        show (if i + 1 = K then 0 else 1) = 1; rw [if_neg (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [B.whenFirst, E.eval, cvJ, col_clk, env_first]
        split
        · next h0 => rw [h0, ofN_zero, mul_zero']
        · exact zero_mul' _
      · simp only [B.whenTrans, B.eq, E.eval, htr, nxJ, col_clk, cvJ, B.one, B.c, ofN_one, hK1]
        rw [ofN_add, ofN_one, sub_self', mul_zero']
      · simp only [B.bool, E.eval, cvI, vRL, B.one, B.c, ofN_one]
        exact opCols_bit _ 0 (by decide)
      · simp only [B.bool, E.eval, cvI, vRA, B.one, B.c, ofN_one]
        exact opCols_bit _ 1 (by decide)
      · simp only [B.bool, E.eval, cvI, vRG, B.one, B.c, ofN_one]
        exact opCols_bit _ 2 (by decide)
      · simp only [B.eq, E.eval, cvI, vRL, vRA, vRG, sInst, vI]
        exact opCols_sum _
      · show (col (SEL + 12)).eval _ = 0; rw [cvI, v12]
      · show (col (SEL + 13)).eval _ = 0; rw [cvI, v13]
      · simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', hnHd, zero_add']
        rw [nreg HD (by decide), cpuCol_hd, hnext]
        simp only [jetHd, E.eval, cvI, vRL, vRA, vRG, vRV, vX, vC]
        show ofN ((symCells J J.body 0).2.res (R.row i).ctr (R.ps i J)) - _ = 0
        cases (symCells J J.body 0).2 with
        | local_ j =>
          show ofN ((R.row i).ctr + j) - (ofN 1 * (ofN (R.row i).ctr + ofN j) + ofN 0 * ofN j + ofN 0 * _) = 0
          rw [ofN_add, ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', add_zero', add_zero', sub_self']
        | arg a =>
          show ofN ((R.ps i J).getD a 0) - (ofN 0 * (ofN (R.row i).ctr + ofN a) + ofN 0 * ofN a +
            ofN 1 * ofN ((R.ps i J).getD a 0)) = 0
          rw [ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', zero_add', zero_add', sub_self']
        | glob a =>
          show ofN a - (ofN 0 * (ofN (R.row i).ctr + ofN a) + ofN 1 * ofN a + ofN 0 * _) = 0
          rw [ofN_one, ofN_zero, one_mul', zero_mul', zero_mul', zero_add', add_zero', sub_self']
      · simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', hnStk, zero_add', sInst, cvI, vI, vR]
        rw [nreg STK (by decide), cpuCol_stk, hnext, sub_self']
      · have vCt : (R.cpuTable K).main i CTR = ofN (R.row i).ctr := by show R.cpuCol i CTR = _; rw [cI]; rfl
        simp only [B.whenTrans, B.eq, E.eval, htr, one_mul', hnCtr, sInst, cvI, vI, vN, vC, vCt]
        rw [nreg CTR (by decide), cpuCol_ctr, hnext]
        show ofN ((R.row i).ctr + _) - _ = 0
        rw [ofN_add, sub_self']
      · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first, cvI]
        split
        · next h0 => subst h0; show 1 * (ofN (R.row 0).hd - ofN (R.row 0).hd) = 0; rw [sub_self', mul_zero']
        · exact zero_mul' _
      · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first, cvI]
        split
        · next h0 => subst h0; show 1 * (ofN (R.row 0).stk - ofN (R.row 0).stk) = 0; rw [sub_self', mul_zero']
        · exact zero_mul' _
      · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first, cvI]
        split
        · next h0 => subst h0; show 1 * (ofN (R.row 0).ctr - ofN (R.row 0).ctr) = 0; rw [sub_self', mul_zero']
        · exact zero_mul' _
      · simp only [B.whenLast, E.eval, hla, zero_mul']

end JRun

end Circuit
