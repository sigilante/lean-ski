import Ski.Circuit.ProbeAir
import Ski.Circuit.JetKind

/-!
# One probe-CPU row: its kind

A row of the probe CPU is one of the machine's eleven kinds, an
instantiation (selector 11), or a probe row (12, the first; 13, a later
one).  A row of the eleven satisfies the corpus CPU's constraints
(`rowSat_ofP`); an instantiation's corpus parts vanish as in the jet CPU
(`inst_facts`); a probe row reads, at most, the atom at the head, and
moves to the probed pointer (`probe_facts`, `next_regsP`).
-/

namespace Circuit

open B

theorem cpuConsP_split (hd0 stk0 ctr0 n la : Nat) : cpuConsP hd0 stk0 ctr0 n la = cpuPre ++
    ([whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
      bool (col J_RL), bool (col J_RA), bool (col J_RG),
      eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst] ++
    probeCons n la ++
    [whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F)))),
     whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
       (.mul sProbe (.add (col CTR) (col (S_BASE + 1)))))),
     whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
       (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one)))),
     whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
     whenLast (eq halt one)]) := by
  unfold cpuConsP cpuPre
  simp only [List.append_assoc]

/-- **The probe kinds' table**: what a probe row reads, halts, and computes
    of the next registers, from the corpus expressions. -/
def probeKindOK (k : Nat) : Bool :=
  kindEq k (acts.getD 0 zero) (c (if k = 13 then 1 else 0)) && kindEq k (acts.getD 1 zero) zero &&
  kindEq k (acts.getD 2 zero) zero && kindEq k (acts.getD 3 zero) zero &&
  kindEq k (tags.getD 0 zero) (c (if k = 13 then 6 else 0)) && kindEq k halt zero && kindEq k sApp zero && kindEq k sS zero &&
  kindEq k sInst zero && kindEq k sProbe one && kindEq k sPFirst (c (if k = 12 then 1 else 0)) &&
  kindEq k sPLater (c (if k = 13 then 1 else 0)) &&
  kindEq k nextHd zero && kindEq k nextStk zero && kindEq k nextCtr (col CTR)

theorem probeKindOK_12 : probeKindOK 12 = true := by decide
theorem probeKindOK_13 : probeKindOK 13 = true := by decide

theorem probe_facts {T : Table} {r k : Nat} (hr : r < T.h) (hk : SelsAre T r k) (hk2 : k = 12 ∨ k = 13) :
    (acts.getD 0 zero).eval (T.env r) = ofN (if k = 13 then 1 else 0) ∧
    (∀ j, 1 ≤ j → j < 4 → (acts.getD j zero).eval (T.env r) = 0) ∧
    (tags.getD 0 zero).eval (T.env r) = ofN (if k = 13 then 6 else 0) ∧ halt.eval (T.env r) = 0 ∧
    sApp.eval (T.env r) = 0 ∧ sS.eval (T.env r) = 0 ∧ sInst.eval (T.env r) = 0 ∧ sProbe.eval (T.env r) = 1 ∧
    sPFirst.eval (T.env r) = ofN (if k = 12 then 1 else 0) ∧ sPLater.eval (T.env r) = ofN (if k = 13 then 1 else 0) ∧
    nextHd.eval (T.env r) = 0 ∧ nextStk.eval (T.env r) = 0 ∧ nextCtr.eval (T.env r) = T.main r CTR := by
  have h : probeKindOK k = true := by rcases hk2 with rfl | rfl; exact probeKindOK_12; exact probeKindOK_13
  simp only [probeKindOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := h
  refine ⟨kind_evalS hr hk h0, fun j hj1 hj4 => ?_, kind_evalS hr hk h4, kind_evalS hr hk h5, kind_evalS hr hk h6,
    kind_evalS hr hk h7, kind_evalS hr hk h8, kind_evalS hr hk h9, kind_evalS hr hk h10, kind_evalS hr hk h11,
    kind_evalS hr hk h12, kind_evalS hr hk h13, ?_⟩
  · rcases (show j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl
    · exact kind_evalS hr hk h1
    · exact kind_evalS hr hk h2
    · exact kind_evalS hr hk h3
  · rw [kind_evalS hr hk h14, col_eval hr]

section Row

variable {hd0 stk0 ctr0 n la : Nat} {T : Table} (hs : Sat (cpuAirP hd0 stk0 ctr0 n la) T) {r : Nat} (hr : r < T.h)
include hs hr

theorem memP {x : E} (h : x ∈ cpuConsP hd0 stk0 ctr0 n la) : x.eval (T.env r) = 0 := hs.2 x h r hr

theorem memP_pre {x : E} (h : x ∈ cpuPre) : x.eval (T.env r) = 0 :=
  memP hs hr (by rw [cpuConsP_split]; exact List.mem_append_left _ h)

theorem memP_jet {x : E} (h : x ∈ [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
      bool (col J_RL), bool (col J_RA), bool (col J_RG),
      eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst]) : x.eval (T.env r) = 0 :=
  memP hs hr (by rw [cpuConsP_split]; exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ h)))

theorem memP_probe {x : E} (h : x ∈ probeCons n la) : x.eval (T.env r) = 0 :=
  memP hs hr (by rw [cpuConsP_split]; exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ h)))

theorem memP_last {x : E} (h : x ∈ [whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F)))),
     whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
       (.mul sProbe (.add (col CTR) (col (S_BASE + 1)))))),
     whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
       (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one)))),
     whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
     whenLast (eq halt one)]) : x.eval (T.env r) = 0 :=
  memP hs hr (by rw [cpuConsP_split]; exact List.mem_append_right _ (List.mem_append_right _ h))

theorem sel_bitP {i : Nat} (hi : i < NKINDS) : T.main r (SEL + i) * (T.main r (SEL + i) - 1) = 0 := by
  have := memP_pre hs hr (x := bool (col (SEL + i)))
    (by unfold cpuPre; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem sel_sumP : ((List.range NKINDS).map fun i => T.main r (SEL + i)).foldr (· + ·) 0 = 1 := by
  have := memP_pre hs hr (x := B.eq (B.sum ((List.range NKINDS).map fun i => B.col (SEL + i))) B.one)
    (by unfold cpuPre; simp)
  simp only [B.eq, E.eval, B.sum] at this
  rw [eval_sum] at this
  have e := sub_eq_zero this
  simp only [B.zero, B.c, B.one, E.eval, ofN_zero, ofN_one, zero_add', List.map_map] at e
  rw [← e]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [B.col, E.eval, env_main0 hr]

/-- **The row's kind**: one of the fourteen. -/
theorem kind_ofP : ∃ k, k < NKINDS ∧ SelsAre T r k := by
  let xs := (List.range NKINDS).map fun i => T.main r (SEL + i)
  have hb : ∀ x ∈ xs, x.val ≤ 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rcases val_of_bit (sel_bitP hs hr (List.mem_range.1 hi)) with h | h <;> omega
  obtain ⟨hv, _⟩ := sum_bits_val xs hb (by simp [xs, NKINDS, P])
  have hsum := sel_sumP hs hr
  rw [show ((List.range NKINDS).map fun i => T.main r (SEL + i)) = xs from rfl, Fin.ext_iff] at hsum
  rw [hv] at hsum
  obtain ⟨k, hk, h1, h0⟩ := onehot (xs.map Fin.val) (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hb x hx) hsum
  have hlen : (xs.map Fin.val).length = NKINDS := by simp [xs]
  have get : ∀ i, i < NKINDS → (xs.map Fin.val).getD i 0 = (T.main r (SEL + i)).val := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hi)]
    simp [xs]
  refine ⟨k, by rw [hlen] at hk; exact hk, fun i hi => ?_⟩
  apply Fin.ext
  rcases Nat.decEq i k with hik | hik
  · rw [if_neg hik, ← get i hi, h0 i (by rw [hlen]; exact hi) hik]; rfl
  · rw [if_pos hik]; subst hik; rw [← get i hi, h1]; rfl

theorem flag_bitsP : T.main r J_RL * (T.main r J_RL - 1) = 0 ∧ T.main r J_RA * (T.main r J_RA - 1) = 0 ∧
    T.main r J_RG * (T.main r J_RG - 1) = 0 := by
  have h1 := memP_jet hs hr (x := bool (col J_RL)) (by simp)
  have h2 := memP_jet hs hr (x := bool (col J_RA)) (by simp)
  have h3 := memP_jet hs hr (x := bool (col J_RG)) (by simp)
  simp only [B.bool, E.eval, B.col, B.one, B.c, ofN_one, env_main0 hr] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem jflags_sumP : T.main r J_RL + T.main r J_RA + T.main r J_RG = T.main r (SEL + 11) := by
  have h := memP_jet hs hr (x := eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst) (by simp)
  simp only [B.eq, E.eval, B.col, sInst, env_main0 hr] at h
  exact sub_eq_zero h

theorem flags_zeroP (h11 : T.main r (SEL + 11) = 0) :
    T.main r J_RL = 0 ∧ T.main r J_RA = 0 ∧ T.main r J_RG = 0 := by
  obtain ⟨b1, b2, b3⟩ := flag_bitsP hs hr
  have hs3 := jflags_sumP hs hr
  rw [h11] at hs3
  obtain ⟨hv, _, _, _⟩ := bits3_val b1 b2 b3
  rw [hs3] at hv
  have z : (0 : F).val = 0 := rfl
  rw [z] at hv
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> (show _ = 0; omega)

/-- **A row of the eleven kinds satisfies the corpus CPU's constraints.** -/
theorem rowSat_ofP (h11 : T.main r (SEL + 11) = 0) (h12 : T.main r (SEL + 12) = 0) (h13 : T.main r (SEL + 13) = 0) :
    RowSat hd0 stk0 ctr0 T r := by
  obtain ⟨z1, z2, z3⟩ := flags_zeroP hs hr h11
  have hjet : jetHd.eval (T.env r) = 0 := by
    simp only [jetHd, E.eval, B.col, env_main0 hr, z1, z2, z3, zero_mul', add_zero']
  have hi : sInst.eval (T.env r) = 0 := by simp only [sInst, E.eval, B.col, env_main0 hr, h11]
  have hpf : sPFirst.eval (T.env r) = 0 := by simp only [sPFirst, E.eval, B.col, env_main0 hr, h12]
  have hpl : sPLater.eval (T.env r) = 0 := by simp only [sPLater, E.eval, B.col, env_main0 hr, h13]
  have hp : sProbe.eval (T.env r) = 0 := by simp only [sProbe, E.eval, hpf, hpl, add_zero']
  intro x hx
  rw [cpuCons_split] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact memP_pre hs hr hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hi
    · exact hpf
    · exact hpl
    · have := memP_last hs hr (x := whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F)))))
        (by simp)
      have e : (whenTrans (eq (nxt HD) nextHd)).eval (T.env r) =
          (whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F))))).eval (T.env r) := by
        simp only [B.whenTrans, B.eq, E.eval, hjet, hp, zero_mul', add_zero']
      rw [e]; exact this
    · have := memP_last hs hr (x := whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
        (.mul sProbe (.add (col CTR) (col (S_BASE + 1))))))) (by simp)
      have e : (whenTrans (eq (nxt STK) nextStk)).eval (T.env r) =
          (whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
            (.mul sProbe (.add (col CTR) (col (S_BASE + 1))))))).eval (T.env r) := by
        simp only [B.whenTrans, B.eq, E.eval, hi, hp, zero_mul', add_zero']
      rw [e]; exact this
    · have := memP_last hs hr (x := whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
        (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one))))) (by simp)
      have e : (whenTrans (eq (nxt CTR) nextCtr)).eval (T.env r) =
          (whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
            (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one))))).eval (T.env r) := by
        simp only [B.whenTrans, B.eq, E.eval, hi, hp, zero_mul', add_zero']
      rw [e]; exact this
    · exact memP_last hs hr (by simp)
    · exact memP_last hs hr (by simp)
    · exact memP_last hs hr (by simp)
    · exact memP_last hs hr (by simp)

/-- The transitions: the next row's registers. -/
theorem next_regsP (hn : r + 1 < T.h) :
    T.main (r + 1) HD = nextHd.eval (T.env r) + jetHd.eval (T.env r) + sProbe.eval (T.env r) * T.main r P_F ∧
    T.main (r + 1) STK = nextStk.eval (T.env r) + T.main r (SEL + 11) * T.main r J_REST +
      sProbe.eval (T.env r) * (T.main r CTR + T.main r (S_BASE + 1)) ∧
    T.main (r + 1) CTR = nextCtr.eval (T.env r) + T.main r (SEL + 11) * T.main r J_N +
      sProbe.eval (T.env r) * (T.main r (S_BASE + 1) * ofN 2 + 1) := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h1 := memP_last hs hr (x := whenTrans (eq (nxt HD) (.add (.add nextHd jetHd) (.mul sProbe (col P_F))))) (by simp)
  have h2 := memP_last hs hr (x := whenTrans (eq (nxt STK) (.add (.add nextStk (.mul sInst (col J_REST)))
        (.mul sProbe (.add (col CTR) (col (S_BASE + 1))))))) (by simp)
  have h3 := memP_last hs hr (x := whenTrans (eq (nxt CTR) (.add (.add nextCtr (.mul sInst (col J_N)))
        (.mul sProbe (.add (.mul (col (S_BASE + 1)) (c 2)) one))))) (by simp)
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod] at h1 h2 h3
  simp only [sInst, B.col, B.c, B.one, E.eval, env_main0 hr, ofN_one] at h1 h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

theorem first_clkP (h0 : r = 0) : T.main r J_CLK = 0 := by
  have h := memP_jet hs hr (x := whenFirst (col J_CLK)) (by simp)
  simp only [B.whenFirst, E.eval, B.col, env_first, h0, if_pos, env_main0 hr, one_mul'] at h
  subst h0; exact h

theorem next_clkP (hn : r + 1 < T.h) : T.main (r + 1) J_CLK = T.main r J_CLK + 1 := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h := memP_jet hs hr (x := whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one))) (by simp)
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod, B.col, env_main0 hr, B.one, B.c,
    ofN_one] at h
  exact sub_eq_zero h

end Row

theorem clk_eqP {hd0 stk0 ctr0 n la : Nat} {T : Table} (hs : Sat (cpuAirP hd0 stk0 ctr0 n la) T) :
    ∀ r, r < T.h → T.main r J_CLK = ofN r
  | 0, hr => first_clkP hs hr rfl
  | r + 1, hr => by
    rw [next_clkP hs (Nat.lt_of_succ_lt hr) hr, clk_eqP hs r (Nat.lt_of_succ_lt hr), ofN_add, ofN_one]

end Circuit
