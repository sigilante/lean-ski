import Ski.Circuit.CompPComplete

/-!
# The honest CPU of the circuit with the Poseidon2 jet satisfies its AIR

The honest CPU row (`P2Run.cpuColP`) is the composed CPU's, but on a jet
row, whose kind selectors are clear, whose selector `P2SEL` is set, and
whose reads' range checks are the jet row's.  Each row has a kind
(`IsKindP`, `Ski/Circuit/CompPKind.lean`): its composed kind
(`kindCf`), or `12` on a jet row (`kindP_isKind`).  The kind table
(`kind_factsP`) evaluates the selectors, the reads' activities and the
next registers on every row alike; what remains is row by row:

- a plain row's reads and next registers are the composed CPU's
  (`cpuC_read`, `cpu_next`), its step a plain one (`rowP_stepP`);
- a jet row reads the atom `J` at the head and the stack cells
  `cons k s₁` and `s₁ ↦ cons root rest`, each below the counter, and its
  next row is `⟨k, ctr + 495, ctr + 496⟩` (`P2Run.p2Row_inv`).

**`P2Run.cpuP_sat`**: the honest CPU table satisfies `cpuAirP2`.
-/

namespace Circuit

open B Air Compose CompM Mach

namespace P2Run

variable (R : P2Run)

-- ---------------------------------------------------------------------------
-- The columns
-- ---------------------------------------------------------------------------

theorem c_vals : SEL = 3 ∧ NKINDS = 14 ∧ FLD = 17 ∧ BITS = 25 ∧ RANGE_BITS = 24 ∧ CPU_WIDTH = 121 ∧
    BLA = 121 ∧ BLB = 126 ∧ RS = 131 ∧ CNT = 132 ∧ ROOT = 133 ∧ P2SEL = 134 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The columns the jet leaves alone are the composed CPU's. -/
theorem colP_eq (i : Nat) {c : Nat} (h1 : c ≠ P2SEL) (h2 : ¬ (SEL ≤ c ∧ c < SEL + NKINDS))
    (h3 : ¬ (BITS ≤ c ∧ c < CPU_WIDTH)) : R.cpuColP i c = cpuColC R.A R.row R.e R.n R.segRoots i c := by
  unfold cpuColP
  rw [if_neg h1, if_neg (fun h => h2 h.2), if_neg (fun h => h3 h.2)]

theorem colP_reg (i : Nat) {c : Nat} (hc : c = HD ∨ c = STK ∨ c = CTR) :
    R.cpuColP i c = cpuCol R.A (R.rowQ i) c := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, -, -, e12⟩ := c_vals
  have hc3 : c < 3 := by rcases hc with rfl | rfl | rfl <;> decide
  rw [R.colP_eq i (by rw [e12]; omega) (by rw [e1, e2]; omega) (by rw [e4, e6]; omega)]
  exact cpuColC_reg i hc

theorem colP_hd (i : Nat) : R.cpuColP i HD = ofN (R.rowQ i).hd := R.colP_reg i (.inl rfl)
theorem colP_stk (i : Nat) : R.cpuColP i STK = ofN (R.rowQ i).stk := R.colP_reg i (.inr (.inl rfl))
theorem colP_ctr (i : Nat) : R.cpuColP i CTR = ofN (R.rowQ i).ctr := R.colP_reg i (.inr (.inr rfl))

theorem colP_cnt (i : Nat) : R.cpuColP i CNT = ofN (cntS (rsI R.e R.n) i) := by
  rw [R.colP_eq i (by decide) (by decide) (by decide)]; exact cpuColC_cnt i

theorem colP_rs (i : Nat) : R.cpuColP i RS = ofN (rsI R.e R.n i) := by
  rw [R.colP_eq i (by decide) (by decide) (by decide)]; exact cpuColC_rs i

theorem colP_root (i : Nat) : R.cpuColP i ROOT = ofN (R.segRoots.getD (cntS (rsI R.e R.n) i + 1) 0) := by
  rw [R.colP_eq i (by decide) (by decide) (by decide)]; exact cpuColC_root i

theorem colP_blind (i : Nat) {c : Nat} (hc : c = BLA + 4 ∨ c = BLB + 4) : R.cpuColP i c = 0 := by
  have : c ≠ P2SEL ∧ ¬ (SEL ≤ c ∧ c < SEL + NKINDS) ∧ ¬ (BITS ≤ c ∧ c < CPU_WIDTH) := by
    rcases hc with rfl | rfl <;> decide
  rw [R.colP_eq i this.1 this.2.1 this.2.2]; exact cpuColC_blind i hc

/-- The last blinding block's flag, past the composed CPU's columns. -/
theorem colP_p2flag (i : Nat) : R.cpuColP i (P2SEL + 5) = 0 := by
  rw [R.colP_eq i (by decide) (by decide) (by decide)]
  unfold cpuColC
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem colP_fld (i : Nat) {m : Nat} (hm : m < 8) :
    R.cpuColP i (FLD + m) =
      if m % 2 = 0 then ofN (fieldsAt R.A (R.rowQ i) (m / 2)).1 else ofN (fieldsAt R.A (R.rowQ i) (m / 2)).2 := by
  obtain ⟨e1, e2, e3, e4, -, e6, -, -, -, -, -, e12⟩ := c_vals
  rw [R.colP_eq i (by rw [e3, e12]; omega) (by rw [e1, e2, e3]; omega) (by rw [e3, e4, e6]; omega)]
  unfold cpuColC
  rw [if_pos (by rw [e3, e6]; omega), if_neg (fun h => by rw [e1, e2, e3] at h; omega)]
  exact cpuCol_fld R.A _ hm

/-- **The honest row's kind**: the jet's on a jet row, else the composed
    kind. -/
def kindP (i : Nat) : Nat := if R.jetAt i then 12 else kindCf R.A R.row R.e R.n i

-- ---------------------------------------------------------------------------
-- The run's rows
-- ---------------------------------------------------------------------------

section

variable {R} {m0 : Mach} {nilA : Nat}
  (hA : AcceptsCP R.A m0 [] [] R.J R.root R.segRoots nilA R.n R.e R.row) {K : Nat} (hK : R.e (R.n - 1) < K)
include hA hK

/-- **Every row has its kind.** -/
theorem kindP_isKind {i : Nat} (hi : i < K) : IsKindP (R.cpuTableP K) i (R.kindP i) := by
  have hR := runC hA hK
  have hk := cpuC_kind hR (roots := R.segRoots) hi
  cases hj : R.jetAt i with
  | false =>
    have ek : R.kindP i = kindCf R.A R.row R.e R.n i := by unfold kindP; rw [hj]; rfl
    rw [ek]
    refine ⟨by have := hk.1; omega, fun s hs => ?_, ?_, ?_⟩
    · show R.cpuColP i (SEL + s) = _
      rw [R.cpuColP_plain hj]; exact hk.2.1 s hs
    · show R.cpuColP i RS = _
      rw [R.cpuColP_plain hj]; exact hk.2.2
    · show R.cpuColP i P2SEL = _
      have := hk.1
      unfold cpuColP; rw [if_pos rfl, hj, if_neg (by omega)]; rfl
  | true =>
    have ek : R.kindP i = 12 := by unfold kindP; rw [hj]; rfl
    obtain ⟨hr, _, _⟩ := jetAt_spec hj
    rw [ek]
    refine ⟨by decide, fun s hs => ?_, ?_, ?_⟩
    · show R.cpuColP i (SEL + s) = _
      unfold cpuColP
      rw [if_neg (by unfold P2SEL ROOT RS CPU_WIDTH BITS FLD SEL NKINDS at *; omega),
        if_pos ⟨hj, Nat.le_add_right _ _, by omega⟩, if_neg (fun h => absurd h.2 (by decide))]
    · show R.cpuColP i RS = _
      rw [R.colP_rs, show rsI R.e R.n i = 0 by unfold rsI; rw [hr]; rfl]; rfl
    · show R.cpuColP i P2SEL = _
      unfold cpuColP; rw [if_pos rfl, hj]; rfl

omit hK in
/-- **A plain row that is no restart steps, or has halted**, padded. -/
theorem rowP_stepP {i : Nat} (hr : isRestart R.e R.n i = false) (hj : R.jetAt i = false) :
    stepRow R.A (rowP R.row R.e R.n i) = some (rowP R.row R.e R.n (i + 1)) ∨
      (haltRow R.A (rowP R.row R.e R.n i) = true ∧ rowP R.row R.e R.n (i + 1) = rowP R.row R.e R.n i) := by
  have hn := hA.npos
  rcases Nat.lt_or_ge i (R.e (R.n - 1)) with hlt | hge
  · unfold rowP
    rw [if_pos (by omega), if_pos (by omega)]
    rcases plain_row hA hlt hr hj with h | ⟨_, _, hm, _, _⟩ | h
    · exact .inl h
    · exact absurd hm List.not_mem_nil
    · exact .inr h
  · have e1 : rowP R.row R.e R.n i = R.row (R.e (R.n - 1)) := by
      unfold rowP; split
      · next h => rw [show i = R.e (R.n - 1) by omega]
      · rfl
    have e2 : rowP R.row R.e R.n (i + 1) = R.row (R.e (R.n - 1)) := by
      unfold rowP; rw [if_neg (by omega)]
    obtain ⟨h1, h2⟩ := hA.ends (R.n - 1) (by omega)
    refine .inr ⟨?_, by rw [e1, e2]⟩
    rw [e1]; simp only [haltRow, h1, short, h2]

omit hA hK in
/-- The composed table's columns, at a row. -/
theorem cvC {i : Nat} (hi : i < K) (c : Nat) :
    (col c).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) = cpuColC R.A R.row R.e R.n R.segRoots i c := by
  show cpuColC R.A R.row R.e R.n R.segRoots ((i + 0) % K) c = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]

/-- **The next registers of a plain row**, with a restart's jump, on the
    composed table (`cpuC_next`, its step a plain one). -/
theorem cpuC_nextP {i : Nat} (hi1 : i + 1 < K) (hjet : R.jetAt i = false) :
    ofN (rowP R.row R.e R.n (i + 1)).hd = nextHd.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) +
      cpuColC R.A R.row R.e R.n R.segRoots i RS * cpuColC R.A R.row R.e R.n R.segRoots i ROOT ∧
    ofN (rowP R.row R.e R.n (i + 1)).stk = nextStk.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) +
      cpuColC R.A R.row R.e R.n R.segRoots i RS * ofN nilA ∧
    ofN (rowP R.row R.e R.n (i + 1)).ctr = nextCtr.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) := by
  have hi : i < K := Nat.lt_of_succ_lt hi1
  have hn := hA.npos
  have hR := runC hA hK
  have hk := cpuC_kind hR (roots := R.segRoots) hi
  obtain ⟨_, _, _, _, _, _, nh, ns, nc⟩ := kind_factsC hi hk
  rw [nh, ns, nc, cpuColC_rs]
  unfold kindCf
  cases hr : isRestart R.e R.n i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, rsI, hr, ofN_zero, zero_mul', add_zero']
    have hS := shape (hR.valid _ hi)
    have hk11 : kindOf R.A (rowP R.row R.e R.n i) < 11 := hS.lt
    simp only [nextHdOfC, nextStkOfC, nextCtrOfC, if_neg (show kindOf R.A (rowP R.row R.e R.n i) ≠ 11 by omega)]
    have hbase := List.all_eq_true.1 nextOf_base _ (List.mem_range.2 hk11)
    simp only [Bool.and_eq_true] at hbase
    have cong := E.eval_congr (cpuC_env_base hR (roots := R.segRoots) hi)
    rw [cong _ hbase.1.1, cong _ hbase.1.2, cong _ hbase.2]
    exact cpu_next (hR.valid _ (Nat.lt_of_succ_lt hi1)) hi1 (rowP_stepP hA hr hjet)
  | true =>
    obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
    have hlt := restart_lt hR hr
    simp only [↓reduceIte, rsI, hr, ofN_one, one_mul']
    have z1 : (nextHdOfC 11).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env (R.e j)) = 0 := rfl
    have z2 : (nextStkOfC 11).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env (R.e j)) = 0 := rfl
    have z3 : (nextCtrOfC 11).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env (R.e j)) =
        cpuColC R.A R.row R.e R.n R.segRoots (R.e j) CTR := cvC hi CTR
    rw [z1, z2, z3, zero_add', zero_add', cpuColC_root, cntS_end hA.emono j (by omega),
      cpuColC_reg _ (.inr (.inr rfl))]
    have e1 : rowP R.row R.e R.n (R.e j + 1) = R.row (R.e j + 1) := by unfold rowP; rw [if_pos (by omega)]
    have e0 : rowP R.row R.e R.n (R.e j) = R.row (R.e j) := by unfold rowP; rw [if_pos (by omega)]
    rw [e1, hA.restart j hj, e0]
    exact ⟨rfl, rfl, rfl⟩

omit hA hK in
theorem rd_lt {M : List Cell} {c a : Nat} {x : Cell} (h : rd M c a = some x) : a < c := by
  unfold rd at h
  split at h
  · assumption
  · cases h

omit hA hK in
/-- **A jet row's reads and next row**: the atom `J` at the head, the stack
    cells `cons k s₁` and `s₁ ↦ cons root rest`, and `⟨k, ctr + 495, ctr + 496⟩`. -/
theorem jet_row {i : Nat} (hj : R.jetAt i = true) :
    ∃ k s1 rest, rd R.A (R.rowQ i).ctr (R.rowQ i).hd = some (.atom R.J) ∧
      rd R.A (R.rowQ i).ctr (R.rowQ i).stk = some (.cons k s1) ∧
      rd R.A (R.rowQ i).ctr s1 = some (.cons R.root rest) ∧
      R.rowQ (i + 1) = ⟨k, (R.rowQ i).ctr + 495, (R.rowQ i).ctr + 496⟩ := by
  obtain ⟨_, _, hp2⟩ := jetAt_spec hj
  obtain ⟨hhd, k, s1, rest, _, hstk, hs1, _, _, _, _, hnext⟩ := p2Row_inv hp2
  exact ⟨k, s1, rest, hhd, hstk, hs1, hnext⟩

omit hA hK in
/-- A range check's bits, on every row: a residue mod 2. -/
theorem colP_bit (i : Nat) {j b : Nat} (hj : j < 4) (hb : b < RANGE_BITS) :
    ∃ x, R.cpuColP i (BITS + j * RANGE_BITS + b) = ofN (x % 2) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, -, -, e12⟩ := c_vals
  have h1 : BITS + j * RANGE_BITS + b ≠ P2SEL := by rw [e4, e5, e12]; omega
  have h2 : ¬ (SEL ≤ BITS + j * RANGE_BITS + b ∧ BITS + j * RANGE_BITS + b < SEL + NKINDS) := by
    rw [e1, e2, e4]; omega
  unfold cpuColP
  rw [if_neg h1]
  cases hjet : R.jetAt i with
  | true =>
    rw [if_neg (fun h => h2 h.2), if_pos ⟨rfl, by rw [e4]; omega, by rw [e4, e5, e6]; omega⟩]
    exact ⟨_, rfl⟩
  | false =>
    rw [if_neg (fun h => nomatch h.1), if_neg (fun h => nomatch h.1)]
    unfold cpuColC
    rw [if_pos (by rw [e4, e5, e6]; omega), if_neg (fun h => h2 ⟨h.1, h.2.1⟩)]
    exact ⟨_, cpuCol_bit R.A _ hj hb⟩

omit hA hK in
/-- A jet row's range check `j`: the bits of `ctr - addr - 1`. -/
theorem colP_jetBit {i : Nat} (hjet : R.jetAt i = true) {j b : Nat} (hj : j < 4) (hb : b < RANGE_BITS) :
    R.cpuColP i (BITS + j * RANGE_BITS + b) = ofN ((R.jetRange (R.rowQ i) j / 2 ^ b) % 2) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, -, -, e12⟩ := c_vals
  unfold cpuColP
  rw [if_neg (by rw [e4, e5, e12]; omega), if_neg (fun h => by have := h.2.2; rw [e1, e2, e4] at this; omega),
    if_pos ⟨hjet, by rw [e4]; omega, by rw [e4, e5, e6]; omega⟩]
  have q1 : (BITS + j * RANGE_BITS + b - BITS) / RANGE_BITS = j := by rw [e5]; omega
  have q2 : (BITS + j * RANGE_BITS + b - BITS) % RANGE_BITS = b := by rw [e5]; omega
  rw [q1, q2]

omit hA hK in
theorem bool_mod2 (x : Nat) : ofN (x % 2) * (ofN (x % 2) - ofN 1) = 0 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

omit hA hK in
theorem range_zero {c a : Nat} (h : a < c) : ofN c - ofN a - ofN 1 - ofN (c - a - 1) = 0 := by
  have e : ofN c = ofN (c - a - 1) + ofN a + 1 := by
    rw [← ofN_one, ← ofN_add, ← ofN_add]; congr 1; omega
  rw [e]; exact range_identity _ _

/-- A read's address check, its activity aside. -/
def readX (j : Nat) : E := .sub (.sub (.sub (col CTR) (addrs.getD j zero)) one) (rangeVal j)

omit hA hK in
theorem readX_now : (List.range 4).all (fun j => (readX j).onlyAtoms nowAtom) = true := by decide

/-- **The reads' constraints hold on every row.** -/
theorem cpuP_read (hb : ∀ i, i < K → (rowP R.row R.e R.n i).ctr ≤ 2 ^ 24) {i : Nat} (hi : i < K)
    {j : Nat} (hj : j < 4) : ∀ c ∈ readConsP j, c.eval ((R.cpuTableP K).env i) = 0 := by
  have hR := runC hA hK
  have cv : ∀ c, (col c).eval ((R.cpuTableP K).env i) = R.cpuColP i c := fun c => R.cpuP_col hi c
  have hk := kindP_isKind hA hK hi
  have hacts := (kind_factsP hi hk).1 j hj
  intro c hc
  unfold readConsP at hc
  rcases List.mem_append.1 hc with hc | hc
  · -- a range check's bit
    obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hc
    obtain ⟨x, hx⟩ := R.colP_bit i hj (List.mem_range.1 hb')
    show (col _).eval _ * ((col _).eval _ - ofN 1) = 0
    rw [cv, hx]; exact bool_mod2 x
  · rw [List.mem_singleton.1 hc]
    show (actsP.getD j zero).eval _ * (readX j).eval _ = 0
    rw [hacts.1]
    cases hjet : R.jetAt i with
    | false =>
      -- the composed CPU's read
      have ek : R.kindP i = kindCf R.A R.row R.e R.n i := by unfold kindP; rw [hjet]; rfl
      have hkC := cpuC_kind hR (roots := R.segRoots) hi
      have hlt12 : kindCf R.A R.row R.e R.n i ≠ 12 := by have := hkC.1; omega
      have hC := cpuC_read hR hb (roots := R.segRoots) hi hj
        (.mul (acts.getD j zero) (readX j)) (List.mem_append_right _ (List.mem_singleton_self _))
      rw [show (E.mul (acts.getD j zero) (readX j)).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) =
          (acts.getD j zero).eval _ * (readX j).eval _ from rfl, ((kind_factsC hi hkC).1 j hj).1] at hC
      have ag := E.eval_congr (R.cpuP_env_plain hi hjet) (readX j) (List.all_eq_true.1 readX_now j (List.mem_range.2 hj))
      rw [ek, ag]
      unfold actOfP; rw [if_neg hlt12]; exact hC
    | true =>
      have ek : R.kindP i = 12 := by unfold kindP; rw [hjet]; rfl
      rw [ek]
      unfold actOfP
      rw [if_pos rfl]
      rcases (show j < 3 ∨ j = 3 by omega) with h3 | rfl
      · rw [if_pos h3]
        obtain ⟨k, s1, rest, hhd, hstk, hs1, _⟩ := R.jet_row hjet
        have hctr := hb i hi
        -- the address read `j`, below the counter
        have ha : (addrs.getD j zero).eval ((R.cpuTableP K).env i) = ofN (addrAt R.A (R.rowQ i) j) ∧
            addrAt R.A (R.rowQ i) j < (R.rowQ i).ctr := by
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
          · exact ⟨by show (col HD).eval _ = _; rw [cv, R.colP_hd]; rfl, rd_lt hhd⟩
          · exact ⟨by show (col STK).eval _ = _; rw [cv, R.colP_stk]; rfl, rd_lt hstk⟩
          · have e2 : addrAt R.A (R.rowQ i) 2 = s1 := by
              simp only [addrAt, hstk, Option.getD_some, cellFields]
            refine ⟨?_, by rw [e2]; exact rd_lt hs1⟩
            show (col (FLD + 3)).eval _ = _
            rw [cv, R.colP_fld i (by decide), e2]
            simp only [fieldsAt, addrAt, hstk, Option.getD_some, cellFields]
            rfl
        have hrv : (rangeVal j).eval ((R.cpuTableP K).env i) = ofN (R.jetRange (R.rowQ i) j) := by
          refine rangeVal_bits (show i < (R.cpuTableP K).h from hi) (fun b hb' => R.colP_jetBit hjet (by omega) hb') ?_
          unfold jetRange; rw [if_pos h3]
          have : (R.rowQ i).ctr ≤ 2 ^ 24 := hctr
          omega
        show ofN 1 * ((col CTR).eval _ - (addrs.getD j zero).eval _ - ofN 1 - (rangeVal j).eval _) = 0
        rw [cv, R.colP_ctr, ha.1, hrv]
        show (1 : F) * _ = 0
        rw [one_mul']
        unfold jetRange; rw [if_pos h3]
        exact range_zero ha.2
      · rw [if_neg (by decide)]; exact zero_mul' _

/-- The last row: no restart, the base kind `HK1`. -/
theorem last_kindCfP {i : Nat} (hi : i + 1 = K) : kindCf R.A R.row R.e R.n i = 5 := by
  have hn := hA.npos
  have hR := runC hA hK
  unfold kindCf
  cases hr : isRestart R.e R.n i with
  | true => have := restart_lt hR hr; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have e1 : rowP R.row R.e R.n i = R.row (R.e (R.n - 1)) := by
      unfold rowP; split
      · next h => rw [show i = R.e (R.n - 1) by omega]
      · rfl
    rw [e1]; exact end_kind hR (by omega)

omit hA hK in
theorem kindSumP_all : (List.range 13).all (fun k =>
    kindEqP k (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRS, sP2])) one) = true := by
  decide

omit hA hK in
theorem nextHd_now : nextHd.onlyAtoms nowAtom = true := by decide
omit hA hK in
theorem nextStk_now : nextStk.onlyAtoms nowAtom = true := by decide
omit hA hK in
theorem nextCtr_now : nextCtr.onlyAtoms nowAtom = true := by decide

omit hA hK in
/-- The last row is no jet row. -/
theorem last_plain {i : Nat} (hi : i + 1 = K) (hK' : R.e (R.n - 1) < K) : R.jetAt i = false := by
  cases hj : R.jetAt i with
  | false => rfl
  | true => have := (jetAt_spec hj).2.1; omega

/-- **The honest CPU table of the circuit with the Poseidon2 jet satisfies
    its AIR**, for the run's own start registers, segments, jet atom and
    comb root. -/
theorem cpuP_sat (hb : ∀ i, i < K → (rowP R.row R.e R.n i).ctr ≤ 2 ^ 24) :
    Sat (cpuAirP2 (R.segRoots.getD 0 0) nilA m0.heap.length R.n nilA R.J R.root) (R.cpuTableP K) := by
  have hn := hA.npos
  have hR := runC hA hK
  refine ⟨show 0 < K by omega, fun c hc i (hi : i < K) => ?_⟩
  have cv : ∀ c, (col c).eval ((R.cpuTableP K).env i) = R.cpuColP i c := fun c => R.cpuP_col hi c
  have hk := kindP_isKind hA hK hi
  obtain ⟨_, hhalt, _, _, hHK1, hRS, hP2, nh, ns, nc⟩ := kind_factsP hi hk
  have hk13 := hk.1
  -- the kind, by the row's sort
  have hkplain : R.jetAt i = false → R.kindP i = kindCf R.A R.row R.e R.n i ∧ kindCf R.A R.row R.e R.n i < 12 :=
    fun hj => ⟨by unfold kindP; rw [hj]; rfl, (cpuC_kind hR (roots := R.segRoots) hi).1⟩
  have hkjet : R.jetAt i = true → R.kindP i = 12 := fun hj => by unfold kindP; rw [hj]; rfl
  -- the next row's columns
  have nx : ∀ c', i + 1 < K → (R.cpuTableP K).main ((i + 1) % K) c' = R.cpuColP (i + 1) c' := fun c' hi1 => by
    rw [Nat.mod_eq_of_lt hi1]; rfl
  simp only [cpuAirP2, cpuConsP2, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hc
  rcases hc with (((((((⟨j, hj, rfl⟩ | (rfl | rfl)) | rfl) | hc) | hc) | hc) | hc) | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · -- a kind selector is a bit
    simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
    rw [show R.cpuColP i (SEL + j) = _ from hk.2.1 j hj]
    split <;> decide
  · -- the restart selector is a bit
    simp only [B.bool, sRS, E.eval, cv, B.one, B.c, ofN_one]
    rw [show R.cpuColP i RS = _ from hk.2.2.1]
    split <;> decide
  · -- the jet's selector is a bit
    simp only [B.bool, sP2, E.eval, cv, B.one, B.c, ofN_one]
    rw [show R.cpuColP i P2SEL = _ from hk.2.2.2]
    split <;> decide
  · -- they sum to one
    have := kind_evalP hi hk (List.all_eq_true.1 kindSumP_all _ (List.mem_range.2 hk13))
    simp only [B.eq, E.eval]
    rw [this]; exact sub_self' _
  · exact cpuP_read hA hK hb hi (by decide) _ hc
  · exact cpuP_read hA hK hb hi (by decide) _ hc
  · exact cpuP_read hA hK hb hi (by decide) _ hc
  · exact cpuP_read hA hK hb hi (by decide) _ hc
  · show (col (SEL + 11)).eval _ = 0
    rw [cv, show R.cpuColP i (SEL + 11) = _ from hk.2.1 11 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · show (col (SEL + 12)).eval _ = 0
    rw [cv, show R.cpuColP i (SEL + 12) = _ from hk.2.1 12 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · show (col (SEL + 13)).eval _ = 0
    rw [cv, show R.cpuColP i (SEL + 13) = _ from hk.2.1 13 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · -- the counter starts at 0
    simp only [B.whenFirst, E.eval, env_first]
    split
    · next h0 => subst h0; rw [cv, R.colP_cnt]; exact mul_zero' _
    · exact zero_mul' _
  · -- it counts the restarts
    simp only [B.whenTrans, B.eq, B.nxt, sRS, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableP K).main ((i + 1) % K) CNT - (_ + _)) = 0
      rw [nx CNT hi1, one_mul', cv, cv, R.colP_cnt, R.colP_cnt, R.colP_rs, ← ofN_add]
      exact sub_self' _
  · -- and ends at `n - 1`
    simp only [B.whenLast, B.eq, B.c, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      rw [cv, R.colP_cnt, cntS_after hA.emono hn (by omega), sub_self', mul_zero']
    · exact zero_mul' _
  · -- a jet row reads the jet's atom at the head
    show sP2.eval _ * ((fld 0).eval _ - ofN R.J) = 0
    rw [hP2]
    cases hj : R.jetAt i with
    | false => rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul']
    | true =>
      obtain ⟨k, s1, rest, hhd, _, _, _⟩ := R.jet_row hj
      rw [if_pos (hkjet hj), show fld 0 = col (FLD + 0) from rfl, cv, R.colP_fld i (by decide)]
      simp only [fieldsAt, addrAt, hhd, Option.getD_some, cellFields]
      rw [if_pos trivial, sub_self', mul_zero']
  · -- and the comb's root under the stack's second cell
    show sP2.eval _ * ((fld 4).eval _ - ofN R.root) = 0
    rw [hP2]
    cases hj : R.jetAt i with
    | false => rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul']
    | true =>
      obtain ⟨k, s1, rest, _, hstk, hs1, _⟩ := R.jet_row hj
      rw [if_pos (hkjet hj), show fld 4 = col (FLD + 4) from rfl, cv, R.colP_fld i (by decide)]
      simp only [fieldsAt, addrAt, hstk, hs1, Option.getD_some, cellFields]
      rw [if_pos trivial, sub_self', mul_zero']
  · -- the last blinding flag is clear
    show (col (P2SEL + 5)).eval _ * ((col (P2SEL + 5)).eval _ - ofN 1) = 0
    rw [cv, R.colP_p2flag, zero_mul']
  · -- the next head
    simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableP K).main ((i + 1) % K) HD - (nextHd.eval _ + sRS.eval _ * (col ROOT).eval _ +
        sP2.eval _ * (fld 2).eval _)) = 0
      rw [nx HD hi1, one_mul', R.colP_hd, hP2]
      cases hj : R.jetAt i with
      | false =>
        obtain ⟨_, hk12⟩ := hkplain hj
        rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul', add_zero',
          E.eval_congr (R.cpuP_env_plain hi hj) nextHd nextHd_now,
          show sRS.eval ((R.cpuTableP K).env i) = cpuColC R.A R.row R.e R.n R.segRoots i RS by
            rw [show sRS = col RS from rfl, cv, R.cpuColP_plain hj],
          cv, R.cpuColP_plain hj]
        rw [show R.rowQ (i + 1) = rowP R.row R.e R.n (i + 1) from rfl, (cpuC_nextP hA hK hi1 hj).1]
        exact sub_self' _
      | true =>
        obtain ⟨k, s1, rest, _, hstk, _, hnext⟩ := R.jet_row hj
        rw [if_pos (hkjet hj), nh, hRS, hkjet hj, hnext, show fld 2 = col (FLD + 2) from rfl, cv (FLD + 2),
          R.colP_fld i (show 2 < 8 by decide)]
        simp only [fieldsAt, addrAt, hstk, Option.getD_some, cellFields, nextHdOfP, ↓reduceIte]
        show ofN k - ((0 : F) + ofN 0 * _ + ofN 1 * ofN k) = 0
        rw [ofN_zero, zero_mul', zero_add', zero_add', ofN_one, one_mul', sub_self']
  · -- the next stack
    simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableP K).main ((i + 1) % K) STK - (nextStk.eval _ + sRS.eval _ * ofN nilA +
        sP2.eval _ * ((col CTR).eval _ + ofN (P2_BITS - 1)))) = 0
      rw [nx STK hi1, one_mul', R.colP_stk, hP2]
      cases hj : R.jetAt i with
      | false =>
        rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul', add_zero',
          E.eval_congr (R.cpuP_env_plain hi hj) nextStk nextStk_now,
          show sRS.eval ((R.cpuTableP K).env i) = cpuColC R.A R.row R.e R.n R.segRoots i RS by
            rw [show sRS = col RS from rfl, cv, R.cpuColP_plain hj]]
        rw [show R.rowQ (i + 1) = rowP R.row R.e R.n (i + 1) from rfl, (cpuC_nextP hA hK hi1 hj).2.1]
        exact sub_self' _
      | true =>
        obtain ⟨k, s1, rest, _, _, _, hnext⟩ := R.jet_row hj
        rw [if_pos (hkjet hj), ns, hRS, hkjet hj, hnext, cv, R.colP_ctr]
        simp only [nextStkOfP, ↓reduceIte]
        show ofN ((R.rowQ i).ctr + 495) - ((0 : F) + ofN 0 * _ + ofN 1 * (ofN (R.rowQ i).ctr + ofN (P2_BITS - 1))) = 0
        rw [ofN_zero, zero_mul', zero_add', zero_add', ofN_one, one_mul', ofN_add]
        exact sub_self' _
  · -- the next counter
    simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableP K).main ((i + 1) % K) CTR - (nextCtr.eval _ + sP2.eval _ * ofN P2_BITS)) = 0
      rw [nx CTR hi1, one_mul', R.colP_ctr, hP2]
      cases hj : R.jetAt i with
      | false =>
        rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul', add_zero',
          E.eval_congr (R.cpuP_env_plain hi hj) nextCtr nextCtr_now]
        rw [show R.rowQ (i + 1) = rowP R.row R.e R.n (i + 1) from rfl, (cpuC_nextP hA hK hi1 hj).2.2]
        exact sub_self' _
      | true =>
        obtain ⟨k, s1, rest, _, _, _, hnext⟩ := R.jet_row hj
        rw [if_pos (hkjet hj), nc, hkjet hj, hnext]
        simp only [nextCtrOfP, ↓reduceIte]
        rw [cv, R.colP_ctr]
        show ofN ((R.rowQ i).ctr + 496) - (ofN (R.rowQ i).ctr + ofN 1 * ofN P2_BITS) = 0
        rw [ofN_one, one_mul', ← ofN_add]
        exact sub_self' _
  · -- the first row's registers
    simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
    split
    · next h0 =>
      subst h0
      rw [cv, R.colP_hd, show R.rowQ 0 = R.row 0 from rowQ_of_le (Nat.zero_le _), hA.hd0, sub_self', mul_zero']
    · exact zero_mul' _
  · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
    split
    · next h0 =>
      subst h0
      rw [cv, R.colP_stk, show R.rowQ 0 = R.row 0 from rowQ_of_le (Nat.zero_le _), hA.stk0, sub_self', mul_zero']
    · exact zero_mul' _
  · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
    split
    · next h0 =>
      subst h0
      rw [cv, R.colP_ctr, show R.rowQ 0 = R.row 0 from rowQ_of_le (Nat.zero_le _), hA.ctr0, sub_self', mul_zero']
    · exact zero_mul' _
  · -- the last row has halted
    simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      have hj := last_plain hl' hK
      rw [hhalt, (hkplain hj).1, last_kindCfP hA hK hl']
      show 1 * (ofN 1 - ofN 1) = 0; rw [sub_self', mul_zero']
    · exact zero_mul' _
  · -- the blinding flags are clear
    show (col (BLA + 4)).eval _ * ((col (BLA + 4)).eval _ - ofN 1) = 0
    rw [cv, R.colP_blind i (.inl rfl), zero_mul']
  · show (col (BLB + 4)).eval _ * ((col (BLB + 4)).eval _ - ofN 1) = 0
    rw [cv, R.colP_blind i (.inr rfl), zero_mul']
  · -- the last row is `K` over the nil
    simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      have hj := last_plain hl' hK
      rw [hHK1, (hkplain hj).1, last_kindCfP hA hK hl']
      show 1 * (ofN 1 - ofN 1) = 0; rw [sub_self', mul_zero']
    · exact zero_mul' _

end

end P2Run

end Circuit
