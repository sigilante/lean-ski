import Ski.Circuit.JetAir
import Ski.Circuit.BaseStep
import Ski.Circuit.BaseTable

/-!
# One jet-CPU row: its kind

A row of the jet CPU is one of the machine's eleven kinds or an
instantiation (selector 11).  A row of one of the eleven satisfies the
corpus CPU's constraints (`rowSat_ofJ`): its root flags are zero, so the
jet parts of its transitions vanish, and the corpus lemmas of
`Ski/Circuit/BaseStep.lean` and `Ski/Circuit/RowSound.lean` apply to it.
An instantiation row reads nothing and writes nothing through the corpus
messages, and moves to the root, the rest of the stack, and the counter
past the jet's cells (`inst_facts`, `next_regsJ`).  The row counter is the
row's index (`clk_eq`).
-/

namespace Circuit

open B

/-- Row `r`'s selectors are kind `k`'s. -/
def SelsAre (T : Table) (r k : Nat) : Prop :=
  ∀ i, i < NKINDS → T.main r (SEL + i) = if i = k then 1 else 0

theorem selSub_evalS {T : Table} {r k : Nat} (hr : r < T.h) (hk : SelsAre T r k) (a : Atom) :
    (selSub k a).eval (T.env r) = T.env r a := by
  cases a with
  | main o i =>
    cases o with
    | zero =>
      simp only [selSub]
      split
      · next h =>
        rw [env_main0 hr]
        have e := hk (i - SEL) (Nat.sub_lt_left_of_lt_add h.1 h.2)
        rw [Nat.add_sub_cancel' h.1] at e
        rw [e]; rfl
      · rfl
    | succ o => rfl
  | pre _ _ => rfl
  | first => rfl
  | last => rfl
  | trans => rfl

theorem kind_evalS {T : Table} {r k : Nat} (hr : r < T.h) (hk : SelsAre T r k) {e e' : E}
    (h : kindEq k e e' = true) : e.eval (T.env r) = e'.eval (T.env r) := by
  rw [← E.eval_subst (selSub k) (T.env r) (selSub_evalS hr hk) e]
  exact E.eval_eq_of_norm (beq_iff_eq.1 h) _

/-- **The instantiation kind's table**: no corpus read, no corpus write, no
    halt, and the corpus parts of the next registers are `0`, `0`, `ctr`. -/
def instOK : Bool :=
  (List.range 4).all (fun j => kindEq 11 (acts.getD j zero) zero) && kindEq 11 halt zero &&
  kindEq 11 sApp zero && kindEq 11 sS zero &&
  kindEq 11 nextHd zero && kindEq 11 nextStk zero && kindEq 11 nextCtr (col CTR)

theorem instOK_true : instOK = true := by decide

theorem inst_facts {T : Table} {r : Nat} (hr : r < T.h) (hk : SelsAre T r 11) :
    (∀ j, j < 4 → (acts.getD j zero).eval (T.env r) = 0) ∧ halt.eval (T.env r) = 0 ∧
    sApp.eval (T.env r) = 0 ∧ sS.eval (T.env r) = 0 ∧
    nextHd.eval (T.env r) = 0 ∧ nextStk.eval (T.env r) = 0 ∧ nextCtr.eval (T.env r) = T.main r CTR := by
  have h := instOK_true
  simp only [instOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hj, hh⟩, ha⟩, hs⟩, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun j hj' => kind_evalS hr hk (hj j hj'), kind_evalS hr hk hh, kind_evalS hr hk ha,
    kind_evalS hr hk hs, kind_evalS hr hk h1, kind_evalS hr hk h2, ?_⟩
  rw [kind_evalS hr hk h3, col_eval hr]

/-- The corpus CPU's constraints before its `inst = 0`: the jet CPU's too. -/
def cpuPre : List E :=
  (List.range NKINDS).map (fun i => bool (col (SEL + i))) ++
  [eq (sum ((List.range NKINDS).map fun i => col (SEL + i))) one] ++
  readCons 0 ++ readCons 1 ++ readCons 2 ++ readCons 3

theorem cpuCons_split (hd0 stk0 ctr0 : Nat) : cpuCons hd0 stk0 ctr0 = cpuPre ++
    [sInst, sPFirst, sPLater,
     whenTrans (eq (nxt HD) nextHd), whenTrans (eq (nxt STK) nextStk), whenTrans (eq (nxt CTR) nextCtr),
     whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
     whenLast (eq halt one)] := rfl

theorem cpuConsJ_split (hd0 stk0 ctr0 : Nat) : cpuConsJ hd0 stk0 ctr0 = cpuPre ++
    [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
     bool (col J_RL), bool (col J_RA), bool (col J_RG),
     eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst,
     sPFirst, sPLater,
     whenTrans (eq (nxt HD) (.add nextHd jetHd)),
     whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST)))),
     whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))),
     whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
     whenLast (eq halt one)] := rfl

/-- Three bits summing to `s`, as numbers. -/
theorem bits3_val {x y z : F} (hx : x * (x - 1) = 0) (hy : y * (y - 1) = 0) (hz : z * (z - 1) = 0) :
    (x + y + z).val = x.val + y.val + z.val ∧ x.val ≤ 1 ∧ y.val ≤ 1 ∧ z.val ≤ 1 := by
  have bx := val_of_bit hx
  have bY := val_of_bit hy
  have bz := val_of_bit hz
  have lx : x.val ≤ 1 := by rcases bx with h | h <;> omega
  have ly : y.val ≤ 1 := by rcases bY with h | h <;> omega
  have lz : z.val ≤ 1 := by rcases bz with h | h <;> omega
  have hP : 3 < P := by decide
  rw [val_add_of_lt (by rw [val_add_of_lt (by omega)]; omega), val_add_of_lt (by omega)]
  exact ⟨rfl, lx, ly, lz⟩

section Row

variable {hd0 stk0 ctr0 : Nat} {T : Table} (hs : Sat (cpuAirJ hd0 stk0 ctr0) T) {r : Nat} (hr : r < T.h)
include hs hr

theorem memJ {x : E} (h : x ∈ cpuConsJ hd0 stk0 ctr0) : x.eval (T.env r) = 0 := hs.2 x h r hr

theorem memJ_tail {x : E} (h : x ∈ [whenFirst (col J_CLK), whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one)),
     bool (col J_RL), bool (col J_RA), bool (col J_RG),
     eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst,
     sPFirst, sPLater,
     whenTrans (eq (nxt HD) (.add nextHd jetHd)),
     whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST)))),
     whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N)))),
     whenFirst (eq (col HD) (c hd0)), whenFirst (eq (col STK) (c stk0)), whenFirst (eq (col CTR) (c ctr0)),
     whenLast (eq halt one)]) : x.eval (T.env r) = 0 :=
  memJ hs hr (by rw [cpuConsJ_split]; exact List.mem_append_right _ h)

theorem memJ_pre {x : E} (h : x ∈ cpuPre) : x.eval (T.env r) = 0 :=
  memJ hs hr (by rw [cpuConsJ_split]; exact List.mem_append_left _ h)

theorem sel_bitJ {i : Nat} (hi : i < NKINDS) : T.main r (SEL + i) * (T.main r (SEL + i) - 1) = 0 := by
  have := memJ_pre hs hr (x := bool (col (SEL + i)))
    (by unfold cpuPre; simp only [List.mem_append]; exact .inl (.inl (.inl (.inl (.inl
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))))))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem sel_sumJ : ((List.range NKINDS).map fun i => T.main r (SEL + i)).foldr (· + ·) 0 = 1 := by
  have := memJ_pre hs hr (x := B.eq (B.sum ((List.range NKINDS).map fun i => B.col (SEL + i))) B.one)
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

theorem pfirst_zeroJ : T.main r (SEL + 12) = 0 := by
  have := memJ_tail hs hr (x := sPFirst) (by simp)
  simpa [E.eval, sPFirst, B.col, env_main0 hr] using this

theorem plater_zeroJ : T.main r (SEL + 13) = 0 := by
  have := memJ_tail hs hr (x := sPLater) (by simp)
  simpa [E.eval, sPLater, B.col, env_main0 hr] using this

/-- **The row's kind**: one of the machine's eleven, or an instantiation. -/
theorem kind_ofJ : ∃ k, k < 12 ∧ SelsAre T r k := by
  let xs := (List.range NKINDS).map fun i => T.main r (SEL + i)
  have hb : ∀ x ∈ xs, x.val ≤ 1 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    rcases val_of_bit (sel_bitJ hs hr (List.mem_range.1 hi)) with h | h <;> omega
  obtain ⟨hv, _⟩ := sum_bits_val xs hb (by simp [xs, NKINDS, P])
  have hsum := sel_sumJ hs hr
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
  have hval : ∀ i, i < NKINDS → T.main r (SEL + i) = if i = k then 1 else 0 := by
    intro i hi
    apply Fin.ext
    rcases Nat.decEq i k with hik | hik
    · rw [if_neg hik, ← get i hi, h0 i (by rw [hlen]; exact hi) hik]; rfl
    · rw [if_pos hik]; subst hik; rw [← get i hi, h1]; rfl
  have hk12 : k < 12 := by
    rw [hlen] at hk
    have e12 := hval 12 (by decide)
    have e13 := hval 13 (by decide)
    rw [pfirst_zeroJ hs hr] at e12
    rw [plater_zeroJ hs hr] at e13
    rcases Nat.decEq 12 k with h12 | h12
    · rcases Nat.decEq 13 k with h13 | h13
      · unfold NKINDS at hk; omega
      · rw [if_pos h13] at e13; exact absurd e13 (by decide)
    · rw [if_pos h12] at e12; exact absurd e12 (by decide)
  exact ⟨k, hk12, hval⟩

theorem flag_bits : T.main r J_RL * (T.main r J_RL - 1) = 0 ∧ T.main r J_RA * (T.main r J_RA - 1) = 0 ∧
    T.main r J_RG * (T.main r J_RG - 1) = 0 := by
  have h1 := memJ_tail hs hr (x := bool (col J_RL)) (by simp)
  have h2 := memJ_tail hs hr (x := bool (col J_RA)) (by simp)
  have h3 := memJ_tail hs hr (x := bool (col J_RG)) (by simp)
  simp only [B.bool, E.eval, B.col, B.one, B.c, ofN_one, env_main0 hr] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem jflags_sum : T.main r J_RL + T.main r J_RA + T.main r J_RG = T.main r (SEL + 11) := by
  have h := memJ_tail hs hr (x := eq (.add (.add (col J_RL) (col J_RA)) (col J_RG)) sInst) (by simp)
  simp only [B.eq, E.eval, B.col, sInst, env_main0 hr] at h
  exact sub_eq_zero h

/-- A row of the eleven kinds has its root flags zero. -/
theorem flags_zero (h11 : T.main r (SEL + 11) = 0) :
    T.main r J_RL = 0 ∧ T.main r J_RA = 0 ∧ T.main r J_RG = 0 := by
  obtain ⟨b1, b2, b3⟩ := flag_bits hs hr
  have hs3 := jflags_sum hs hr
  rw [h11] at hs3
  obtain ⟨hv, _, _, _⟩ := bits3_val b1 b2 b3
  rw [hs3] at hv
  have z : (0 : F).val = 0 := rfl
  rw [z] at hv
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> (show _ = 0; omega)

/-- **A row of the eleven kinds satisfies the corpus CPU's constraints.** -/
theorem rowSat_ofJ (h11 : T.main r (SEL + 11) = 0) : RowSat hd0 stk0 ctr0 T r := by
  obtain ⟨z1, z2, z3⟩ := flags_zero hs hr h11
  have hjet : jetHd.eval (T.env r) = 0 := by
    simp only [jetHd, E.eval, B.col, env_main0 hr, z1, z2, z3, zero_mul', add_zero']
  have hi : sInst.eval (T.env r) = 0 := by simp only [sInst, E.eval, B.col, env_main0 hr, h11]
  intro c hc
  rw [cpuCons_split] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact memJ_pre hs hr hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hi
    · exact memJ_tail hs hr (by simp)
    · exact memJ_tail hs hr (by simp)
    · have := memJ_tail hs hr (x := whenTrans (eq (nxt HD) (.add nextHd jetHd))) (by simp)
      have e : (whenTrans (eq (nxt HD) nextHd)).eval (T.env r) =
          (whenTrans (eq (nxt HD) (.add nextHd jetHd))).eval (T.env r) := by
        simp only [B.whenTrans, B.eq, E.eval, hjet, add_zero']
      rw [e]; exact this
    · have := memJ_tail hs hr (x := whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST))))) (by simp)
      have e : (whenTrans (eq (nxt STK) nextStk)).eval (T.env r) =
          (whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST))))).eval (T.env r) := by
        simp only [B.whenTrans, B.eq, E.eval, hi, zero_mul', add_zero']
      rw [e]; exact this
    · have := memJ_tail hs hr (x := whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N))))) (by simp)
      have e : (whenTrans (eq (nxt CTR) nextCtr)).eval (T.env r) =
          (whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N))))).eval (T.env r) := by
        simp only [B.whenTrans, B.eq, E.eval, hi, zero_mul', add_zero']
      rw [e]; exact this
    · exact memJ_tail hs hr (by simp)
    · exact memJ_tail hs hr (by simp)
    · exact memJ_tail hs hr (by simp)
    · exact memJ_tail hs hr (by simp)

/-- The transitions: the next row's registers. -/
theorem next_regsJ (hn : r + 1 < T.h) :
    T.main (r + 1) HD = nextHd.eval (T.env r) + jetHd.eval (T.env r) ∧
    T.main (r + 1) STK = nextStk.eval (T.env r) + T.main r (SEL + 11) * T.main r J_REST ∧
    T.main (r + 1) CTR = nextCtr.eval (T.env r) + T.main r (SEL + 11) * T.main r J_N := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h1 := memJ_tail hs hr (x := whenTrans (eq (nxt HD) (.add nextHd jetHd))) (by simp)
  have h2 := memJ_tail hs hr (x := whenTrans (eq (nxt STK) (.add nextStk (.mul sInst (col J_REST))))) (by simp)
  have h3 := memJ_tail hs hr (x := whenTrans (eq (nxt CTR) (.add nextCtr (.mul sInst (col J_N))))) (by simp)
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod] at h1 h2 h3
  simp only [sInst, B.col, E.eval, env_main0 hr] at h2 h3
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3⟩

theorem first_clk (h0 : r = 0) : T.main r J_CLK = 0 := by
  have h := memJ_tail hs hr (x := whenFirst (col J_CLK)) (by simp)
  simp only [B.whenFirst, E.eval, B.col, env_first, h0, if_pos, env_main0 hr, one_mul'] at h
  subst h0; exact h

theorem next_clk (hn : r + 1 < T.h) : T.main (r + 1) J_CLK = T.main r J_CLK + 1 := by
  have ht : T.env r .trans = 1 := by simp [env_trans]; omega
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h := memJ_tail hs hr (x := whenTrans (eq (nxt J_CLK) (.add (col J_CLK) one))) (by simp)
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod, B.col, env_main0 hr, B.one, B.c,
    ofN_one] at h
  exact sub_eq_zero h

end Row

/-- **The row counter is the row's index.** -/
theorem clk_eq {hd0 stk0 ctr0 : Nat} {T : Table} (hs : Sat (cpuAirJ hd0 stk0 ctr0) T) :
    ∀ r, r < T.h → T.main r J_CLK = ofN r
  | 0, hr => first_clk hs hr rfl
  | r + 1, hr => by
    rw [next_clk hs (Nat.lt_of_succ_lt hr) hr, clk_eq hs r (Nat.lt_of_succ_lt hr), ofN_add, ofN_one]

end Circuit
