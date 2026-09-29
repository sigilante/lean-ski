import Ski.Circuit.ProbeSound

/-!
# Probe soundness: the probe rows

The probe constraints, one row at a time, and what they give: the probe
counter counts the probe rows before a row, so the probe rows are the
plan's segments in order; the first row is the first probe row and the
last row ends the last segment.
-/

namespace Circuit

open B Air JetTable Mach

section Row

variable {hd0 stk0 ctr0 n la : Nat} {T : Table} (hs : Sat (cpuAirP hd0 stk0 ctr0 n la) T) {r : Nat} (hr : r < T.h)
include hs hr

/-- **A probe row's constraints**, on any row. -/
theorem probe_row :
    T.main r (SEL + 12) * T.main r P_CNT = 0 ∧
    T.main r (SEL + 13) * (T.main r FLD - T.main r (E_BASE + 2) - T.main r E_BASE) = 0 ∧
    T.main r P_NILACT * (T.main r P_NILACT - 1) = 0 ∧
    T.main r (SEL + 13) * (1 - T.main r P_NILACT) = 0 ∧
    T.main r (SEL + 13) * (T.main r P_NILADDR - T.main r E_REST) = 0 ∧
    T.main r P_NILACT * (T.main r CTR - T.main r P_NILADDR - 1 - nilVal.eval (T.env r)) = 0 ∧
    T.main r P_NKIDS * (1 - T.main r (SEL + 13)) = 0 ∧
    T.main r (SEL + 12) * (T.main r P_F - T.main r HD) = 0 := by
  have h1 := memP_probe hs hr (x := .mul sPFirst (col P_CNT)) (by simp [probeCons])
  have h2 := memP_probe hs hr (x := .mul sPLater (.sub (.sub (fld 0) (col (E_BASE + 2))) (col E_BASE)))
    (by simp [probeCons])
  have h3 := memP_probe hs hr (x := bool (col P_NILACT)) (by simp [probeCons])
  have h4 := memP_probe hs hr (x := .mul sPLater (.sub one (col P_NILACT))) (by simp [probeCons])
  have h5 := memP_probe hs hr (x := .mul sPLater (.sub (col P_NILADDR) (col E_REST))) (by simp [probeCons])
  have h6 := memP_probe hs hr (x := .mul (col P_NILACT) (.sub (.sub (.sub (col CTR) (col P_NILADDR)) one) nilVal))
    (by simp [probeCons])
  have h7 := memP_probe hs hr (x := .mul (col P_NKIDS) (.sub one sPLater)) (by simp [probeCons])
  have h8 := memP_probe hs hr (x := .mul sPFirst (.sub (col P_F) (col HD))) (by simp [probeCons])
  simp only [E.eval, B.bool, B.col, B.one, B.c, ofN_one, sPFirst, sPLater, fld, env_main0 hr, Nat.add_zero]
    at h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The nil read's range bits are bits. -/
theorem nil_bitP {i : Nat} (hi : i < RANGE_BITS) :
    T.main r (P_NILBITS + i) * (T.main r (P_NILBITS + i) - 1) = 0 := by
  have := memP_probe hs hr (x := bool (col (P_NILBITS + i)))
    (by unfold probeCons; simp only [List.mem_append]; exact .inl (.inr (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

/-- The first row: the first probe row, count `0`. -/
theorem probe_first (h0 : r = 0) : T.main r (SEL + 12) = 1 ∧ T.main r P_CNT = 0 := by
  have h1 := memP_probe hs hr (x := whenFirst (eq sPFirst one)) (by simp [probeCons])
  have h2 := memP_probe hs hr (x := whenFirst (col P_CNT)) (by simp [probeCons])
  subst h0
  simp only [B.whenFirst, B.eq, E.eval, env_first, if_pos, B.col, B.one, B.c, ofN_one, sPFirst, env_main0 hr,
    one_mul'] at h1 h2
  exact ⟨sub_eq_zero h1, h2⟩

/-- The count's step: it counts this row if it is a probe row. -/
theorem probe_next (hn : r + 1 < T.h) :
    T.main (r + 1) P_CNT = T.main r P_CNT + (T.main r (SEL + 12) + T.main r (SEL + 13)) := by
  have ht : T.env r .trans = 1 := by
    rw [env_trans, if_neg (Nat.ne_of_lt hn)]
  have hmod : (r + 1) % T.h = r + 1 := Nat.mod_eq_of_lt hn
  have h := memP_probe hs hr (x := whenTrans (eq (nxt P_CNT) (.add (col P_CNT) sProbe))) (by simp [probeCons])
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, ht, one_mul', env_main1, hmod, B.col, env_main0 hr, sProbe, sPFirst,
    sPLater] at h
  exact sub_eq_zero h

/-- The last row: count `n`, a halting atom, the last marker, and a nil
    at the stack. -/
theorem probe_last (hl : r + 1 = T.h) :
    T.main r P_CNT = ofN n ∧ T.main r (SEL + 10) = 1 ∧ T.main r FLD = ofN la ∧ T.main r P_NILACT = 1 ∧
      T.main r P_NILADDR = T.main r STK := by
  have ht : T.env r .last = 1 := by rw [env_last, if_pos hl]
  have h1 := memP_probe hs hr (x := whenLast (eq (col P_CNT) (c n))) (by simp [probeCons])
  have h2 := memP_probe hs hr (x := whenLast (eq sHA one)) (by simp [probeCons])
  have h3 := memP_probe hs hr (x := whenLast (eq (fld 0) (c la))) (by simp [probeCons])
  have h4 := memP_probe hs hr (x := whenLast (eq (col P_NILACT) one)) (by simp [probeCons])
  have h5 := memP_probe hs hr (x := whenLast (eq (col P_NILADDR) (col STK))) (by simp [probeCons])
  simp only [B.whenLast, B.eq, E.eval, ht, one_mul', B.col, B.c, B.one, ofN_one, sHA, fld, env_main0 hr,
    Nat.add_zero] at h1 h2 h3 h4 h5
  exact ⟨sub_eq_zero h1, sub_eq_zero h2, sub_eq_zero h3, sub_eq_zero h4, sub_eq_zero h5⟩

theorem range_bitP {j i : Nat} (hj : j < 4) (hi : i < RANGE_BITS) :
    T.main r (BITS + j * RANGE_BITS + i) * (T.main r (BITS + j * RANGE_BITS + i) - 1) = 0 := by
  have hm : B.bool (B.col (BITS + j * RANGE_BITS + i)) ∈ readCons j :=
    List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  have := memP_pre hs hr (x := B.bool (B.col (BITS + j * RANGE_BITS + i))) (by
    unfold cpuPre
    simp only [List.mem_append]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact .inl (.inl (.inl (.inr hm)))
    · exact .inl (.inl (.inr hm))
    · exact .inl (.inr hm)
    · exact .inr hm)
  simpa [E.eval, B.bool, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

theorem range_eqP {j : Nat} (hj : j < 4) :
    (acts.getD j B.zero).eval (T.env r) *
      (T.main r CTR - (addrs.getD j B.zero).eval (T.env r) - 1 - (rangeVal j).eval (T.env r)) = 0 := by
  have hm : E.mul (acts.getD j B.zero) (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one) (rangeVal j))
      ∈ readCons j := List.mem_append_right _ (List.mem_singleton.2 rfl)
  have := memP_pre hs hr (x := E.mul (acts.getD j B.zero) (.sub (.sub (.sub (B.col CTR) (addrs.getD j B.zero)) B.one)
      (rangeVal j))) (by
    unfold cpuPre
    simp only [List.mem_append]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact .inl (.inl (.inl (.inr hm)))
    · exact .inl (.inl (.inr hm))
    · exact .inl (.inr hm)
    · exact .inr hm)
  simpa [E.eval, B.col, B.one, B.c, env_main0 hr, ofN_one] using this

end Row

/-- **A range check bounds an address**: `c = a + 1 + v`, with no wrap. -/
theorem below_of_range {c a v : F} (hv : v.val < 2 ^ 24) (ha : a.val ≤ 2 ^ 27) (he : c - a - 1 - v = 0) :
    a.val < c.val := by
  have e := sub_eq_zero he
  have hctr : c = (a + 1) + v := by rw [← e, add_sub_cancel3]
  have hb : a.val + 1 + v.val < P := by
    have : 2 ^ 27 + 2 ^ 24 + 8 < P := P_big
    omega
  have h1 : (a + 1).val = a.val + 1 := val_add_of_lt (by show _ + 1 < P; omega)
  have hval : c.val = a.val + 1 + v.val := by
    rw [hctr, val_add_of_lt (by rw [h1]; exact hb), h1]
  omega

-- ---------------------------------------------------------------------------
-- The count: the probe rows before a row
-- ---------------------------------------------------------------------------

/-- Row `r` is a probe row. -/
def isPr (T : Table) (r : Nat) : Bool := decide (T.main r (SEL + 12) + T.main r (SEL + 13) = 1)

/-- The probe rows before row `r`. -/
def pc (T : Table) (r : Nat) : Nat := sumTo r fun i => if isPr T i then 1 else 0

theorem pc_succ (T : Table) (r : Nat) : pc T (r + 1) = pc T r + (if isPr T r then 1 else 0) := rfl

theorem pc_le (T : Table) : ∀ r, pc T r ≤ r
  | 0 => Nat.le_refl 0
  | r + 1 => by
    rw [pc_succ]
    have := pc_le T r
    split <;> omega

theorem pc_mono (T : Table) {a : Nat} : ∀ b, a ≤ b → pc T a ≤ pc T b
  | 0, h => by rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | b + 1, h => by
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · rw [pc_succ]; have := pc_mono T b (Nat.le_of_lt_succ h'); omega
    · rw [Nat.le_antisymm h h']; exact Nat.le_refl _

/-- A probe row is counted by every later row. -/
theorem pc_lt {T : Table} {a b : Nat} (ha : isPr T a = true) (hab : a < b) : pc T a < pc T b := by
  have := pc_mono T b hab
  rw [pc_succ, ha, if_pos rfl] at this
  omega

/-- Each count below `pc R` is some probe row's. -/
theorem pc_hit (T : Table) {j : Nat} : ∀ R, j < pc T R → ∃ r, r < R ∧ isPr T r = true ∧ pc T r = j
  | 0, h => absurd h (Nat.not_lt_zero _)
  | R + 1, h => by
    rw [pc_succ] at h
    rcases Nat.lt_or_ge j (pc T R) with h' | h'
    · obtain ⟨r, hr, h1, h2⟩ := pc_hit T R h'
      exact ⟨r, Nat.lt_succ_of_lt hr, h1, h2⟩
    · cases hp : isPr T R with
      | false => rw [hp] at h; exact absurd h (by simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
      | true => rw [hp, if_pos rfl] at h; exact ⟨R, Nat.lt_succ_self R, hp, by omega⟩

/-- The first `r < k` with `f r`. -/
def firstR (f : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | k + 1 => match firstR f k with
    | some r => some r
    | none => if f k then some k else none

theorem firstR_spec (f : Nat → Bool) : ∀ k r, firstR f k = some r → r < k ∧ f r = true
  | 0, _, h => nomatch h
  | k + 1, r, h => by
    unfold firstR at h
    split at h
    · cases h
      obtain ⟨h1, h2⟩ := firstR_spec f k _ (by assumption)
      exact ⟨Nat.lt_succ_of_lt h1, h2⟩
    · cases hk : f k with
      | false => rw [hk] at h; cases h
      | true => rw [hk, if_pos rfl] at h; cases h; exact ⟨Nat.lt_succ_self k, hk⟩

theorem firstR_some (f : Nat → Bool) : ∀ k r, r < k → f r = true → ∃ r', firstR f k = some r'
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, r, h, hf => by
    unfold firstR
    split
    · exact ⟨_, rfl⟩
    · rename_i hn
      rcases Nat.lt_or_ge r k with h' | h'
      · obtain ⟨r', e⟩ := firstR_some f k r h' hf
        rw [e] at hn; cases hn
      · have : r = k := Nat.le_antisymm (Nat.le_of_lt_succ h) h'
        subst this
        rw [hf, if_pos rfl]; exact ⟨_, rfl⟩

/-- **Where segment `j` starts**: the probe row with count `j`, and the
    last row for `j = n`. -/
def pRow (T : Table) (n j : Nat) : Nat :=
  if j < n then ((firstR (fun r => isPr T r && pc T r == j) T.h).getD 0) else T.h - 1

theorem pRow_last (T : Table) (n : Nat) : pRow T n n = T.h - 1 := by
  unfold pRow; rw [if_neg (Nat.lt_irrefl n)]

section Count

variable {hd0 stk0 ctr0 n la : Nat} {T : Table} (hs : Sat (cpuAirP hd0 stk0 ctr0 n la) T) (hH : T.h < P)
include hs hH

omit hH in
theorem sprobe_ind {r : Nat} (hr : r < T.h) :
    T.main r (SEL + 12) + T.main r (SEL + 13) = ofN (if isPr T r then 1 else 0) := by
  obtain ⟨k, _, hk⟩ := kind_ofP hs hr
  unfold isPr
  rw [hk 12 (by decide), hk 13 (by decide)]
  rcases Nat.decEq k 12 with h12 | h12
  · rcases Nat.decEq k 13 with h13 | h13
    · rw [if_neg (Ne.symm h12), if_neg (Ne.symm h13)]; rfl
    · subst h13; rfl
  · subst h12; rfl

/-- **The count is the probe rows before.** -/
theorem cnt_eq : ∀ r, r < T.h → T.main r P_CNT = ofN (pc T r)
  | 0, hr => (probe_first hs hr rfl).2
  | r + 1, hr => by
    rw [probe_next hs (Nat.lt_of_succ_lt hr) hr, cnt_eq r (Nat.lt_of_succ_lt hr), sprobe_ind hs (Nat.lt_of_succ_lt hr),
      pc_succ, ofN_add]

theorem pr_first (h0 : 0 < T.h) : isPr T 0 = true := by
  have e := sprobe_ind hs h0
  rw [(probe_first hs h0 rfl).1] at e
  cases hp : isPr T 0 with
  | true => rfl
  | false =>
    rw [hp] at e
    have : T.main 0 (SEL + 13) = 0 := by
      obtain ⟨k, _, hk⟩ := kind_ofP hs h0
      have e12 := hk 12 (by decide)
      rw [(probe_first hs h0 rfl).1] at e12
      rcases Nat.decEq 12 k with h | h
      · rw [if_neg h] at e12; exact absurd e12 (by decide)
      · rw [hk 13 (by decide), if_neg (by rw [← h]; decide)]
    rw [this] at e
    exact absurd e (by decide)

/-- **A probe row after the first is a later one.** -/
theorem pr_later {r : Nat} (hr : r < T.h) (h0 : 0 < r) (hp : isPr T r = true) :
    T.main r (SEL + 12) = 0 ∧ T.main r (SEL + 13) = 1 := by
  have hpos : 0 < pc T r := Nat.lt_of_le_of_lt (Nat.zero_le _) (pc_lt (pr_first hs hH (Nat.lt_trans h0 hr)) h0)
  have hc := cnt_eq hs hH r hr
  have h1 := (probe_row hs hr).1
  rw [hc] at h1
  have hne : ofN (pc T r) ≠ 0 := fun e => by
    have := ofN_inj (Nat.lt_of_le_of_lt (pc_le T r) (Nat.lt_trans hr hH)) (by decide) (e.trans ofN_zero.symm)
    omega
  have h12 : T.main r (SEL + 12) = 0 := by
    rcases val_of_bit (sel_bitP hs hr (i := 12) (by decide)) with e | e
    · exact Fin.ext e
    · exfalso; apply hne
      have e1 : T.main r (SEL + 12) = 1 := Fin.ext e
      rw [e1, one_mul'] at h1; exact h1
  refine ⟨h12, ?_⟩
  have e := sprobe_ind hs hr
  rw [hp, if_pos rfl, h12, zero_add'] at e
  exact e

/-- The last row is no probe row. -/
theorem last_notPr (h0 : 0 < T.h) : isPr T (T.h - 1) = false := by
  have hl : T.h - 1 < T.h := Nat.sub_lt h0 (by decide)
  have e10 := (probe_last hs hl (Nat.sub_add_cancel h0)).2.1
  obtain ⟨k, _, hk⟩ := kind_ofP hs hl
  have hk10 := hk 10 (by decide)
  rw [e10] at hk10
  rcases Nat.decEq 10 k with h | h
  · rw [if_neg h] at hk10; exact absurd hk10 (by decide)
  · subst h
    unfold isPr
    rw [hk 12 (by decide), hk 13 (by decide), if_neg (by decide), if_neg (by decide)]
    rfl

variable (hn : n < P)
include hn

/-- The last row counts all `n` probe rows. -/
theorem pc_last (h0 : 0 < T.h) : pc T (T.h - 1) = n := by
  have hl : T.h - 1 < T.h := Nat.sub_lt h0 (by decide)
  have e := (probe_last hs hl (Nat.sub_add_cancel h0)).1
  rw [cnt_eq hs hH _ hl] at e
  exact ofN_inj (Nat.lt_of_le_of_lt (pc_le T _) (Nat.lt_trans hl hH)) hn e

/-- **Segment `j` starts at a probe row**, before the last, with count `j`. -/
theorem pRow_spec (h0 : 0 < T.h) {j : Nat} (hj : j < n) :
    pRow T n j < T.h - 1 ∧ isPr T (pRow T n j) = true ∧ pc T (pRow T n j) = j := by
  obtain ⟨r, hr, hp, hc⟩ := pc_hit T (T.h - 1) (by rw [pc_last hs hH hn h0]; exact hj)
  obtain ⟨r', e⟩ := firstR_some (fun r => isPr T r && pc T r == j) T.h r (Nat.lt_of_lt_of_le hr (Nat.sub_le _ _))
    (by rw [hp, hc]; exact beq_self_eq_true' j)
  obtain ⟨hr', hf⟩ := firstR_spec _ _ _ e
  rw [Bool.and_eq_true, beq_iff_eq] at hf
  have hpr : pRow T n j = r' := by unfold pRow; rw [if_pos hj, e]; rfl
  rw [hpr]
  refine ⟨?_, hf.1, hf.2⟩
  rcases Nat.lt_or_ge r' (T.h - 1) with h | h
  · exact h
  · have : r' = T.h - 1 := by omega
    rw [this, last_notPr hs hH h0] at hf
    exact absurd hf.1 (by decide)

/-- **Every probe row starts a segment.** -/
theorem pr_eq (h0 : 0 < T.h) {r : Nat} (hr : r < T.h) (hp : isPr T r = true) :
    pc T r < n ∧ pRow T n (pc T r) = r := by
  have hl : r < T.h - 1 := by
    rcases Nat.lt_or_ge r (T.h - 1) with h | h
    · exact h
    · have : r = T.h - 1 := by omega
      rw [this, last_notPr hs hH h0] at hp; cases hp
  have hlt : pc T r < n := by rw [← pc_last hs hH hn h0]; exact pc_lt hp hl
  refine ⟨hlt, ?_⟩
  obtain ⟨_, hp', hc'⟩ := pRow_spec hs hH hn h0 hlt
  rcases Nat.lt_trichotomy (pRow T n (pc T r)) r with h | h | h
  · have := pc_lt hp' h; omega
  · exact h
  · have := pc_lt hp h; omega

/-- **The segments start in order.** -/
theorem pRow_mono (h0 : 0 < T.h) {j : Nat} (hj : j < n) : pRow T n j < pRow T n (j + 1) := by
  obtain ⟨hl, hp, hc⟩ := pRow_spec hs hH hn h0 hj
  rcases Nat.lt_or_ge (j + 1) n with h | h
  · obtain ⟨_, _, hc'⟩ := pRow_spec hs hH hn h0 h
    rcases Nat.lt_or_ge (pRow T n j) (pRow T n (j + 1)) with h' | h'
    · exact h'
    · have := pc_mono T _ h'; omega
  · have : j + 1 = n := by omega
    rw [this, pRow_last]; exact hl

end Count

/-- The segment a plan row gives, fields read at `b`. -/
def SegAt (C : Table) (r b : Nat) (s : Air.Seg) : Prop :=
  C.main r b = ofN s.base ∧ C.main r (b + 1) = ofN s.k ∧ C.main r (b + 2) = ofN s.ctor ∧
    C.main r (b + 3) = ofN s.arity ∧ C.main r (b + 4) = ofN s.parent ∧ C.main r (b + 5) = ofN s.field

theorem range6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl

section

variable {hd0 stk0 ctr0 n la : Nat} {heap : List Cell} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {plan : List Air.Seg} {C Mm Pg Rt Hd Tm Po Iw Pl Pw : Table}
  (h : ProbeOK hd0 stk0 ctr0 n la heap roots jets plan C Mm Pg Rt Hd Tm Po Iw Pl Pw)
include h

/-- **The probe CPU's corpus rows are machine transitions.** -/
theorem ProbeOK.row : RowOK hd0 stk0 ctr0 C Mm :=
  ⟨h.cpu.1, fun _ _ hr hk => rowSat_ofP h.cpu hr (by rw [hk.2 11 (by decide), if_neg (Nat.ne_of_gt hk.1)])
      (by rw [hk.2 12 (by decide), if_neg (by have := hk.1; omega)])
      (by rw [hk.2 13 (by decide), if_neg (by have := hk.1; omega)]),
    mem_addr h.mem, h.mem_h, fun r hr I hI hbus hc =>
    h.memHit ⟨(cpuAirP hd0 stk0 ctr0 n la, C), List.mem_cons_self, rfl, r, hr, I,
      List.mem_append_left _ (List.mem_append_left _ hI), hbus, rfl, hc⟩⟩

/-- **A read of the head**, on any row that reads it. -/
theorem ProbeOK.readHead {r : Nat} (hr : r < C.h) (ha : (acts.getD 0 zero).eval (C.env r) = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r HD).val =
      some (cellOf ((tags.getD 0 zero).eval (C.env r)) (C.main r FLD) (C.main r (FLD + 1))) := by
  have hadr : (addrs.getD 0 zero).eval (C.env r) = C.main r HD := by
    simp only [addrs, List.getD_cons_zero, B.col, E.eval, env_main0 hr]
  obtain ⟨hlt, hget⟩ := h.row.send hr (I := readInter 0) List.mem_cons_self rfl
    (a := C.main r HD) (t := (tags.getD 0 zero).eval (C.env r)) (x := C.main r FLD) (y := C.main r (FLD + 1))
    (by simp only [readInter, List.map_cons, List.map_nil, hadr, fld, B.col, E.eval, env_main0 hr, Nat.mul_zero,
      Nat.add_zero, Nat.zero_add]) ha
  have hre := range_eqP h.cpu hr (j := 0) (by decide)
  rw [ha, one_mul', hadr] at hre
  have hv := bitsVal_lt hr (BITS + 0 * RANGE_BITS) 24 (Nat.le_refl _)
    (fun i hi => range_bitP h.cpu hr (j := 0) (by decide) hi)
  have hb := below_of_range hv (Nat.le_of_lt (Nat.lt_of_lt_of_le hlt h.mem_h)) hre
  unfold rd
  rw [if_pos hb, hget]

/-- **The nil read**: below the counter, a nil. -/
theorem ProbeOK.nilRead {r : Nat} (hr : r < C.h) (ha : C.main r P_NILACT = 1) :
    rd (memOf Mm) (C.main r CTR).val (C.main r P_NILADDR).val = some .nil := by
  have cv := col_eval hr
  have hI : (⟨"mem", 1, col P_NILACT, [col P_NILADDR, c 4, c 0, c 0]⟩ : Inter) ∈ cpuInters ++ jetInters ++ probeInters :=
    List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hm := h.memHit ⟨(cpuAirP hd0 stk0 ctr0 n la, C), List.mem_cons_self, rfl, r, hr, _, hI, rfl, rfl,
    by show (col P_NILACT).eval (C.env r) = 1; rw [cv, ha]⟩
  simp only [List.map_cons, List.map_nil, E.eval, B.c, cv] at hm
  obtain ⟨hlt, hget⟩ := h.row.cell hm
  have e := (probe_row h.cpu hr).2.2.2.2.2.1
  rw [ha, one_mul'] at e
  have hv := bitsVal_lt hr P_NILBITS 24 (Nat.le_refl _) (fun i hi => nil_bitP h.cpu hr hi)
  have hb := below_of_range hv (Nat.le_of_lt (Nat.lt_of_lt_of_le hlt h.mem_h)) e
  unfold rd
  rw [if_pos hb, hget]; rfl

theorem ProbeOK.plan_le : plan.length ≤ 2 ^ 27 := by
  have e : Pl.h = (planRows plan).length := h.plpre.1
  have hl : plan.length ≤ (planRows plan).length := by
    have := padCopies_length_ge (plan.zipIdx.map fun (s, j) =>
      [ofN j, ofN s.base, ofN s.k, ofN s.ctor, ofN s.arity, ofN s.parent, ofN s.field])
    rw [List.length_map, List.length_zipIdx] at this
    exact this
  have := h.plan_h
  omega

/-- **A probe row starts the segment of its count.** -/
theorem ProbeOK.sSeg {r : Nat} (hr : r < C.h) (hp : isPr C r = true) :
    ∃ s, plan[pc C r]? = some s ∧ SegAt C r S_BASE s := by
  have cv := col_eval hr
  have hH : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  have hc : sProbe.eval (C.env r) = 1 := by
    have e := sprobe_ind h.cpu hr
    rw [hp, if_pos rfl, ofN_one] at e
    simp only [sProbe, sPFirst, sPLater, E.eval, cv]; exact e
  obtain ⟨j, s, hs, hf⟩ := h.planHit hr (I := ⟨"plan", 1, sProbe, col P_CNT :: (List.range 6).map fun i => col (S_BASE + i)⟩)
    List.mem_cons_self rfl hc
  rw [range6] at hf
  simp only [List.map_cons, List.map_nil, cv, List.cons.injEq, Nat.add_zero] at hf
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := hf
  rw [cnt_eq h.cpu hH r hr] at h0
  have hj : j < plan.length := (List.getElem?_eq_some_iff.1 hs).1
  have e := ofN_inj (Nat.lt_of_le_of_lt (pc_le C r) (Nat.lt_trans hr hH))
    (Nat.lt_of_lt_of_le hj (Nat.le_trans h.plan_le (by decide))) h0
  rw [e]
  exact ⟨s, hs, h1, h2, h3, h4, h5, h6⟩

/-- **A later probe row ends the segment before its count.** -/
theorem ProbeOK.eSeg {r : Nat} (hr : r < C.h) (hl : C.main r (SEL + 13) = 1) :
    0 < pc C r ∧ ∃ s, plan[pc C r - 1]? = some s ∧ SegAt C r E_BASE s := by
  have cv := col_eval hr
  have hH : C.h < P := Nat.lt_of_le_of_lt h.cpu_h (by decide)
  obtain ⟨j, s, hs, hf⟩ := h.planHit hr
    (I := ⟨"plan", 1, sPLater, .sub (col P_CNT) one :: (List.range 6).map fun i => col (E_BASE + i)⟩)
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl (by simp only [sPLater, E.eval, cv]; exact hl)
  rw [range6] at hf
  simp only [List.map_cons, List.map_nil, E.eval, B.one, B.c, ofN_one, cv, List.cons.injEq, Nat.add_zero] at hf
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -⟩ := hf
  rw [cnt_eq h.cpu hH r hr] at h0
  have hj : j < plan.length := (List.getElem?_eq_some_iff.1 hs).1
  have hjP : j + 1 < P := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hj h.plan_le)) (by decide)
  have e1 : ofN (pc C r) = ofN (j + 1) := by
    rw [ofN_add, ofN_one, ← h0, sub_add_cancel']
  have e := ofN_inj (Nat.lt_of_le_of_lt (pc_le C r) (Nat.lt_trans hr hH)) hjP e1
  rw [e, Nat.add_sub_cancel]
  exact ⟨Nat.succ_pos _, s, hs, h1, h2, h3, h4, h5, h6⟩

end

end Circuit
