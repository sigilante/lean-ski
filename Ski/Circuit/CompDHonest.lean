import Ski.Circuit.CompDComplete
import Ski.Circuit.CompPCpuSat

/-!
# The honest CPU of the circuit with the `dec` jet

From an honest run of the circuit with the `dec` jet (`DRun.Honest`: the
run `CompM.AcceptsCD` accepts, each row within a segment a plain step, a
halted row repeated, or `DecJet.decRowI`'s step (the subject read through `K`-thunks), as `composed check-dec-run`
replays it), padded to `K` rows by repeating its last, the honest CPU
table (`DRun.cpuTableD`): the composed CPU's honest row (`cpuColC`), and
on a jet row the selector `DECSEL`, the kinds cleared, the reads of the
atom `J` at the head and of the stack cell `cons p rest` range-checked,
and the jet's result row in `DROOT`, `DCTR`.

**`DRun.cpuD_sat`**: the honest CPU table satisfies `cpuAirDec`, as
`P2Run.cpuP_sat` (`Ski/Circuit/CompPCpuSat.lean`) for the Poseidon2 jet,
the kinds by `CompDKind.kind_factsD`.
-/

namespace Circuit

open B Air Compose CompM Mach

/-- **A run of the circuit with the `dec` jet**: the memory, the jet's
    atom, the segments' roots, ends and count, and the rows. -/
structure DRun where
  A : List Cell
  J : Nat
  segRoots : List Nat
  e : Nat → Nat
  n : Nat
  row : Nat → Air.Row

namespace DRun

variable (R : DRun)

/-- **An honest run**: one `AcceptsCD` accepts, each row within a segment a
    plain step, a halted row repeated, or the jet's row. -/
structure Honest (m0 : Mach) (nilA : Nat) : Prop where
  acc : AcceptsCD R.A m0 R.J R.segRoots nilA R.n R.e R.row
  step : ∀ i, i < R.e (R.n - 1) → (∀ j, j + 1 < R.n → i ≠ R.e j) →
    NormRow R.A [] [] (R.row i) (R.row (i + 1)) ∨ DecJet.decRowI R.A R.J (R.row i) = some (R.row (i + 1))

/-- The run, padded by repeating its last row. -/
def rowQ (i : Nat) : Air.Row := rowP R.row R.e R.n i

/-- **Row `i` takes the jet's step**: no restart, within the run, the jet's
    row to the next. -/
def jetAt (i : Nat) : Bool :=
  !isRestart R.e R.n i && decide (i < R.e (R.n - 1)) &&
    decide (DecJet.decRowI R.A R.J (R.row i) = some (R.row (i + 1)))

/-- A jet row's range checks: its reads of the atom and the stack cell lie
    below the counter; its other reads are inactive. -/
def jetRange (r : Air.Row) (j : Nat) : Nat := if j < 2 then r.ctr - addrAt R.A r j - 1 else 0

/-- **The honest CPU row**: the composed CPU's, and on a jet row the
    selector, the kinds cleared, its reads range-checked and its result. -/
def cpuColD (i c : Nat) : F :=
  if c = DECSEL then bF (R.jetAt i)
  else if R.jetAt i = true ∧ SEL ≤ c ∧ c < SEL + NKINDS then 0
  else if R.jetAt i = true ∧ BITS ≤ c ∧ c < CPU_WIDTH then
    ofN ((R.jetRange (R.rowQ i) ((c - BITS) / RANGE_BITS) / 2 ^ ((c - BITS) % RANGE_BITS)) % 2)
  else if c = DROOT then (if R.jetAt i then ofN (R.rowQ (i + 1)).hd else 0)
  else if c = DCTR then (if R.jetAt i then ofN (R.rowQ (i + 1)).ctr else 0)
  else cpuColC R.A R.row R.e R.n R.segRoots i c

def cpuTableD (K : Nat) : Table := ⟨K, fun i c => R.cpuColD i c, fun _ _ => 0⟩

end DRun

-- ---------------------------------------------------------------------------
-- The jet's row, inverted
-- ---------------------------------------------------------------------------

/-- **What a jet row reads**: the atom `J` at the head, the stack cell
    `cons p rest`, the slots; the next stack is `rest`. -/
theorem decRow_inv {M : List Cell} {J : Nat} {r r' : Air.Row} (h : DecJet.decRowI M J r = some r') :
    rd M r.ctr r.hd = some (.atom J) ∧ DecJet.slotsOK (M.take r.ctr) = true ∧
      ∃ p rest, rd M r.ctr r.stk = some (.cons p rest) ∧ r'.stk = rest := by
  obtain ⟨p, rest, _, _, _, _, cells, root, hhd, hs, hpop, _, _, _, _, rfl⟩ := DecJet.decRowI_unfold h
  refine ⟨rd_of_take hhd, hs, ?_⟩
  unfold popN at hpop
  cases hc : (M.take r.ctr)[r.stk]? with
  | none => rw [hc] at hpop; cases hpop
  | some c1 =>
    rw [hc] at hpop
    cases c1 with
    | cons x s =>
      simp only [popN, Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hpop
      obtain ⟨rfl, rfl⟩ := hpop
      exact ⟨x, s, rd_of_take hc, rfl⟩
    | _ => cases hpop

/-- A jet row halts, to the base classification: its head is an atom. -/
theorem decRow_halt {M : List Cell} {J : Nat} {r r' : Air.Row} (h : DecJet.decRowI M J r = some r') :
    haltRow M r = true := by
  have h1 := (decRow_inv h).1
  simp only [haltRow, h1]

-- ---------------------------------------------------------------------------
-- The run's rows
-- ---------------------------------------------------------------------------

namespace DRun

section

variable {R : DRun} {m0 : Mach} {nilA : Nat} (hA : R.Honest m0 nilA) {K : Nat} (hK : R.e (R.n - 1) < K)
include hA

/-- A row within the run, no restart, steps plainly or by the jet. -/
theorem step_row {i : Nat} (hi : i < R.e (R.n - 1)) (hr : isRestart R.e R.n i = false) :
    NormRow R.A [] [] (R.row i) (R.row (i + 1)) ∨ DecJet.decRowI R.A R.J (R.row i) = some (R.row (i + 1)) := by
  refine hA.step i hi (fun j hj h' => ?_)
  rw [isRestart_iff.2 ⟨j, hj, h'.symm⟩] at hr; cases hr

include hK in
/-- **The run gives what the composed CPU's lemmas use.** -/
theorem runC : RunC R.A R.n R.e R.row K := by
  have hn := hA.acc.npos
  refine ⟨hn, hA.acc.emono, hA.acc.ends, hK, fun i _ => ?_⟩
  unfold rowP
  split
  · next hle =>
    rcases Nat.lt_or_ge i (R.e (R.n - 1)) with hlt | hge
    · cases hr : isRestart R.e R.n i with
      | false =>
        rcases step_row hA hlt hr with (h | ⟨_, _, hm, _, _⟩ | h) | h
        · exact .inl (by rw [h]; rfl)
        · exact absurd hm List.not_mem_nil
        · exact .inr h.1
        · exact .inr (decRow_halt h)
      | true =>
        obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
        obtain ⟨h1, h2⟩ := hA.acc.ends j (by omega)
        exact .inr (by simp only [haltRow, h1, short, h2])
    · rw [show i = R.e (R.n - 1) by omega]
      obtain ⟨h1, h2⟩ := hA.acc.ends (R.n - 1) (by omega)
      exact .inr (by simp only [haltRow, h1, short, h2])
  · obtain ⟨h1, h2⟩ := hA.acc.ends (R.n - 1) (by omega)
    exact .inr (by simp only [haltRow, h1, short, h2])

omit hA in
theorem rowQ_of_le {i : Nat} (hi : i ≤ R.e (R.n - 1)) : R.rowQ i = R.row i := by
  unfold rowQ rowP; rw [if_pos hi]

omit hA in
/-- **A jet row**: no restart, within the run, the jet's row to the next. -/
theorem jetAt_spec {i : Nat} (h : R.jetAt i = true) :
    isRestart R.e R.n i = false ∧ i < R.e (R.n - 1) ∧
      DecJet.decRowI R.A R.J (R.rowQ i) = some (R.rowQ (i + 1)) := by
  unfold jetAt at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨hr, hi⟩, hp⟩ := h
  refine ⟨hr, hi, ?_⟩
  rw [rowQ_of_le (by omega), rowQ_of_le (by omega)]
  exact hp

/-- **A row within the run that is no jet row and no restart steps
    plainly.** -/
theorem plain_row {i : Nat} (hi : i < R.e (R.n - 1)) (hr : isRestart R.e R.n i = false) (hj : R.jetAt i = false) :
    NormRow R.A [] [] (R.row i) (R.row (i + 1)) := by
  rcases step_row hA hi hr with h | h
  · exact h
  · exfalso
    have : R.jetAt i = true := by
      unfold jetAt
      simp only [hr, Bool.not_false, Bool.true_and, decide_eq_true hi, decide_eq_true h]
    rw [hj] at this; cases this

end

-- ---------------------------------------------------------------------------
-- The honest CPU's columns
-- ---------------------------------------------------------------------------

variable (R : DRun)

theorem c_vals : SEL = 3 ∧ NKINDS = 14 ∧ FLD = 17 ∧ BITS = 25 ∧ RANGE_BITS = 24 ∧ CPU_WIDTH = 121 ∧
    BLA = 121 ∧ BLB = 126 ∧ RS = 131 ∧ CNT = 132 ∧ ROOT = 133 ∧ DECSEL = 134 ∧ DROOT = 140 ∧ DCTR = 141 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cpuD_col {K i : Nat} (hi : i < K) (c : Nat) : (col c).eval ((R.cpuTableD K).env i) = R.cpuColD i c := by
  show (R.cpuTableD K).main ((i + 0) % K) c = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]; rfl

theorem cpuColC_hi {i c : Nat} (hc : DECSEL ≤ c) : cpuColC R.A R.row R.e R.n R.segRoots i c = 0 := by
  obtain ⟨-, -, -, -, -, e6, -, -, e9, e10, e11, e12, -, -⟩ := c_vals
  unfold cpuColC
  rw [e12] at hc
  rw [if_neg (by rw [e6]; omega), if_neg (by rw [e9]; omega), if_neg (by rw [e10]; omega),
    if_neg (by rw [e11]; omega)]

/-- Off the jet rows, the honest CPU row is the composed one. -/
theorem cpuColD_plain {i : Nat} (hj : R.jetAt i = false) (c : Nat) :
    R.cpuColD i c = cpuColC R.A R.row R.e R.n R.segRoots i c := by
  unfold cpuColD
  by_cases hc : c = DECSEL
  · subst hc; rw [if_pos rfl, hj, R.cpuColC_hi (Nat.le_refl _)]; rfl
  rw [if_neg hc, hj, if_neg (fun h => nomatch h.1), if_neg (fun h => nomatch h.1)]
  by_cases hr : c = DROOT
  · subst hr; rw [if_pos rfl, R.cpuColC_hi (by decide)]; rfl
  rw [if_neg hr]
  by_cases hcc : c = DCTR
  · subst hcc; rw [if_pos rfl, R.cpuColC_hi (by decide)]; rfl
  rw [if_neg hcc]

/-- Off the jet rows, the two tables read the same at the current row. -/
theorem cpuD_env_plain {K i : Nat} (hi : i < K) (hj : R.jetAt i = false) :
    ∀ a, nowAtom a = true → (R.cpuTableD K).env i a = (cpuTableC R.A R.row R.e R.n R.segRoots K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    cases o with
    | zero =>
      show (R.cpuTableD K).main ((i + 0) % K) c = (cpuTableC R.A R.row R.e R.n R.segRoots K).main ((i + 0) % K) c
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
      exact R.cpuColD_plain hj c
    | succ o => simp [nowAtom] at ha
  | _ => simp [nowAtom] at ha

/-- The columns the jet leaves alone are the composed CPU's. -/
theorem colD_eq (i : Nat) {c : Nat} (h1 : c ≠ DECSEL) (h2 : ¬ (SEL ≤ c ∧ c < SEL + NKINDS))
    (h3 : ¬ (BITS ≤ c ∧ c < CPU_WIDTH)) (h4 : c < DROOT) :
    R.cpuColD i c = cpuColC R.A R.row R.e R.n R.segRoots i c := by
  unfold cpuColD
  rw [if_neg h1, if_neg (fun h => h2 h.2), if_neg (fun h => h3 h.2), if_neg (Nat.ne_of_lt h4),
    if_neg (Nat.ne_of_lt (Nat.lt_trans h4 (by decide)))]

theorem colD_sel (i : Nat) : R.cpuColD i DECSEL = bF (R.jetAt i) := by
  unfold cpuColD; rw [if_pos rfl]

theorem colD_droot (i : Nat) : R.cpuColD i DROOT = if R.jetAt i then ofN (R.rowQ (i + 1)).hd else 0 := by
  unfold cpuColD
  rw [if_neg (by decide), if_neg (fun h => by have := h.2.2; revert this; decide),
    if_neg (fun h => by have := h.2.2; revert this; decide), if_pos rfl]

theorem colD_dctr (i : Nat) : R.cpuColD i DCTR = if R.jetAt i then ofN (R.rowQ (i + 1)).ctr else 0 := by
  unfold cpuColD
  rw [if_neg (by decide), if_neg (fun h => by have := h.2.2; revert this; decide),
    if_neg (fun h => by have := h.2.2; revert this; decide), if_neg (by decide), if_pos rfl]

theorem colD_reg (i : Nat) {c : Nat} (hc : c = HD ∨ c = STK ∨ c = CTR) :
    R.cpuColD i c = cpuCol R.A (R.rowQ i) c := by
  obtain ⟨e1, e2, -, e4, -, e6, -, -, -, -, -, e12, e13, -⟩ := c_vals
  have hc3 : c < 3 := by rcases hc with rfl | rfl | rfl <;> decide
  rw [R.colD_eq i (by rw [e12]; omega) (by rw [e1, e2]; omega) (by rw [e4, e6]; omega) (by rw [e13]; omega)]
  exact cpuColC_reg i hc

theorem colD_hd (i : Nat) : R.cpuColD i HD = ofN (R.rowQ i).hd := R.colD_reg i (.inl rfl)
theorem colD_stk (i : Nat) : R.cpuColD i STK = ofN (R.rowQ i).stk := R.colD_reg i (.inr (.inl rfl))
theorem colD_ctr (i : Nat) : R.cpuColD i CTR = ofN (R.rowQ i).ctr := R.colD_reg i (.inr (.inr rfl))

theorem colD_cnt (i : Nat) : R.cpuColD i CNT = ofN (cntS (rsI R.e R.n) i) := by
  rw [R.colD_eq i (by decide) (by decide) (by decide) (by decide)]; exact cpuColC_cnt i

theorem colD_rs (i : Nat) : R.cpuColD i RS = ofN (rsI R.e R.n i) := by
  rw [R.colD_eq i (by decide) (by decide) (by decide) (by decide)]; exact cpuColC_rs i

theorem colD_root (i : Nat) : R.cpuColD i ROOT = ofN (R.segRoots.getD (cntS (rsI R.e R.n) i + 1) 0) := by
  rw [R.colD_eq i (by decide) (by decide) (by decide) (by decide)]; exact cpuColC_root i

theorem colD_blind (i : Nat) {c : Nat} (hc : c = BLA + 4 ∨ c = BLB + 4) : R.cpuColD i c = 0 := by
  have : c ≠ DECSEL ∧ ¬ (SEL ≤ c ∧ c < SEL + NKINDS) ∧ ¬ (BITS ≤ c ∧ c < CPU_WIDTH) := by
    rcases hc with rfl | rfl <;> decide
  rw [R.colD_eq i this.1 this.2.1 this.2.2 (by rcases hc with rfl | rfl <;> decide)]; exact cpuColC_blind i hc

/-- The jet's blinding block, past the composed CPU's columns, is clear. -/
theorem colD_block (i : Nat) {c : Nat} (h1 : DECSEL < c) (h2 : c < DROOT) : R.cpuColD i c = 0 := by
  obtain ⟨e1, e2, -, e4, -, e6, -, -, -, -, -, e12, -, -⟩ := c_vals
  rw [e12] at h1
  rw [R.colD_eq i (by rw [e12]; omega) (by rw [e1, e2]; omega) (by rw [e4, e6]; omega) h2]
  exact R.cpuColC_hi (by rw [e12]; omega)

theorem colD_fld (i : Nat) {m : Nat} (hm : m < 8) :
    R.cpuColD i (FLD + m) =
      if m % 2 = 0 then ofN (fieldsAt R.A (R.rowQ i) (m / 2)).1 else ofN (fieldsAt R.A (R.rowQ i) (m / 2)).2 := by
  obtain ⟨e1, e2, e3, e4, -, e6, -, -, -, -, -, e12, e13, -⟩ := c_vals
  rw [R.colD_eq i (by rw [e3, e12]; omega) (by rw [e1, e2, e3]; omega) (by rw [e3, e4, e6]; omega)
    (by rw [e3, e13]; omega)]
  unfold cpuColC
  rw [if_pos (by rw [e3, e6]; omega), if_neg (fun h => by rw [e1, e2, e3] at h; omega)]
  exact cpuCol_fld R.A _ hm

/-- A range check's bits, on every row: a residue mod 2. -/
theorem colD_bit (i : Nat) {j b : Nat} (hj : j < 4) (hb : b < RANGE_BITS) :
    ∃ x, R.cpuColD i (BITS + j * RANGE_BITS + b) = ofN (x % 2) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, -, -, e12, e13, -⟩ := c_vals
  have h1 : BITS + j * RANGE_BITS + b ≠ DECSEL := by rw [e4, e5, e12]; omega
  have h2 : ¬ (SEL ≤ BITS + j * RANGE_BITS + b ∧ BITS + j * RANGE_BITS + b < SEL + NKINDS) := by
    rw [e1, e2, e4]; omega
  cases hjet : R.jetAt i with
  | true =>
    unfold cpuColD
    rw [if_neg h1, if_neg (fun h => h2 h.2), if_pos ⟨hjet, by rw [e4]; omega, by rw [e4, e5, e6]; omega⟩]
    exact ⟨_, rfl⟩
  | false =>
    rw [R.cpuColD_plain hjet]
    unfold cpuColC
    rw [if_pos (by rw [e4, e5, e6]; omega), if_neg (fun h => h2 ⟨h.1, h.2.1⟩)]
    exact ⟨_, cpuCol_bit R.A _ hj hb⟩

/-- A jet row's range check `j`: the bits of `ctr - addr - 1`. -/
theorem colD_jetBit {i : Nat} (hjet : R.jetAt i = true) {j b : Nat} (hj : j < 4) (hb : b < RANGE_BITS) :
    R.cpuColD i (BITS + j * RANGE_BITS + b) = ofN ((R.jetRange (R.rowQ i) j / 2 ^ b) % 2) := by
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, -, -, e12, -, -⟩ := c_vals
  unfold cpuColD
  rw [if_neg (by rw [e4, e5, e12]; omega), if_neg (fun h => by have := h.2.2; rw [e1, e2, e4] at this; omega),
    if_pos ⟨hjet, by rw [e4]; omega, by rw [e4, e5, e6]; omega⟩]
  have q1 : (BITS + j * RANGE_BITS + b - BITS) / RANGE_BITS = j := by rw [e5]; omega
  have q2 : (BITS + j * RANGE_BITS + b - BITS) % RANGE_BITS = b := by rw [e5]; omega
  rw [q1, q2]

/-- **The honest row's kind**: the jet's on a jet row, else the composed
    kind. -/
def kindD (i : Nat) : Nat := if R.jetAt i then 12 else kindCf R.A R.row R.e R.n i

/-- **A jet row's reads and next row**: the atom `J` at the head, the stack
    cell `cons p rest`, and the next stack `rest`. -/
theorem jet_rowD {i : Nat} (hj : R.jetAt i = true) :
    ∃ p rest, rd R.A (R.rowQ i).ctr (R.rowQ i).hd = some (.atom R.J) ∧
      rd R.A (R.rowQ i).ctr (R.rowQ i).stk = some (.cons p rest) ∧ (R.rowQ (i + 1)).stk = rest ∧
      DecJet.slotsOK (R.A.take (R.rowQ i).ctr) = true := by
  obtain ⟨_, _, hd⟩ := jetAt_spec hj
  obtain ⟨hhd, hs, p, rest, hstk, hr⟩ := decRow_inv hd
  exact ⟨p, rest, hhd, hstk, hr, hs⟩

theorem kindSumD_all : (List.range 13).all (fun k =>
    kindEqD k (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRS, sDec])) one) = true := by
  decide

/-- The last row is no jet row. -/
theorem last_plainD {K i : Nat} (hi : i + 1 = K) (hK' : R.e (R.n - 1) < K) : R.jetAt i = false := by
  cases hj : R.jetAt i with
  | false => rfl
  | true => have := (jetAt_spec hj).2.1; omega

section

variable {R} {m0 : Mach} {nilA : Nat} (hA : R.Honest m0 nilA) {K : Nat} (hK : R.e (R.n - 1) < K)
include hA hK

/-- **Every row has its kind.** -/
theorem kindD_isKind {i : Nat} (hi : i < K) : IsKindD (R.cpuTableD K) i (R.kindD i) := by
  have hR := runC hA hK
  have hk := cpuC_kind hR (roots := R.segRoots) hi
  cases hj : R.jetAt i with
  | false =>
    have ek : R.kindD i = kindCf R.A R.row R.e R.n i := by unfold kindD; rw [hj]; rfl
    rw [ek]
    refine ⟨by have := hk.1; omega, fun s hs => ?_, ?_, ?_⟩
    · show R.cpuColD i (SEL + s) = _
      rw [R.cpuColD_plain hj]; exact hk.2.1 s hs
    · show R.cpuColD i RS = _
      rw [R.cpuColD_plain hj]; exact hk.2.2
    · show R.cpuColD i DECSEL = _
      have := hk.1
      rw [R.colD_sel, hj, if_neg (by omega)]; rfl
  | true =>
    have ek : R.kindD i = 12 := by unfold kindD; rw [hj]; rfl
    obtain ⟨hr, _, _⟩ := jetAt_spec hj
    rw [ek]
    refine ⟨by decide, fun s hs => ?_, ?_, ?_⟩
    · show R.cpuColD i (SEL + s) = _
      unfold cpuColD
      have e1 : SEL = 3 := rfl
      have e2 : NKINDS = 14 := rfl
      have e3 : DECSEL = 134 := rfl
      rw [e2] at hs
      rw [if_neg (by rw [e1, e3]; omega),
        if_pos ⟨hj, Nat.le_add_right _ _, by rw [e2]; omega⟩, if_neg (fun h => absurd h.2 (by decide))]
    · show R.cpuColD i RS = _
      rw [R.colD_rs, show rsI R.e R.n i = 0 by unfold rsI; rw [hr]; rfl]; rfl
    · show R.cpuColD i DECSEL = _
      rw [R.colD_sel, hj]; rfl

omit hK in
/-- **A plain row that is no restart steps, or has halted**, padded. -/
theorem rowP_stepD {i : Nat} (hr : isRestart R.e R.n i = false) (hj : R.jetAt i = false) :
    stepRow R.A (rowP R.row R.e R.n i) = some (rowP R.row R.e R.n (i + 1)) ∨
      (haltRow R.A (rowP R.row R.e R.n i) = true ∧ rowP R.row R.e R.n (i + 1) = rowP R.row R.e R.n i) := by
  have hn := hA.acc.npos
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
    obtain ⟨h1, h2⟩ := hA.acc.ends (R.n - 1) (by omega)
    refine .inr ⟨?_, by rw [e1, e2]⟩
    rw [e1]; simp only [haltRow, h1, short, h2]

/-- **The next registers of a plain row**, with a restart's jump, on the
    composed table. -/
theorem cpuC_nextD {i : Nat} (hi1 : i + 1 < K) (hjet : R.jetAt i = false) :
    ofN (rowP R.row R.e R.n (i + 1)).hd = nextHd.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) +
      cpuColC R.A R.row R.e R.n R.segRoots i RS * cpuColC R.A R.row R.e R.n R.segRoots i ROOT ∧
    ofN (rowP R.row R.e R.n (i + 1)).stk = nextStk.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) +
      cpuColC R.A R.row R.e R.n R.segRoots i RS * ofN nilA ∧
    ofN (rowP R.row R.e R.n (i + 1)).ctr = nextCtr.eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) := by
  have hi : i < K := Nat.lt_of_succ_lt hi1
  have hn := hA.acc.npos
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
    exact cpu_next (hR.valid _ (Nat.lt_of_succ_lt hi1)) hi1 (rowP_stepD hA hr hjet)
  | true =>
    obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
    have hlt := restart_lt hR hr
    simp only [↓reduceIte, rsI, hr, ofN_one, one_mul']
    have z1 : (nextHdOfC 11).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env (R.e j)) = 0 := rfl
    have z2 : (nextStkOfC 11).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env (R.e j)) = 0 := rfl
    have z3 : (nextCtrOfC 11).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env (R.e j)) =
        cpuColC R.A R.row R.e R.n R.segRoots (R.e j) CTR := P2Run.cvC (R := ⟨R.A, 0, 0, R.segRoots, R.e, R.n, R.row⟩) hi CTR
    rw [z1, z2, z3, zero_add', zero_add', cpuColC_root, cntS_end hA.acc.emono j (by omega),
      cpuColC_reg _ (.inr (.inr rfl))]
    have e1 : rowP R.row R.e R.n (R.e j + 1) = R.row (R.e j + 1) := by unfold rowP; rw [if_pos (by omega)]
    have e0 : rowP R.row R.e R.n (R.e j) = R.row (R.e j) := by unfold rowP; rw [if_pos (by omega)]
    rw [e1, hA.acc.restart j hj, e0]
    exact ⟨rfl, rfl, rfl⟩

/-- **The reads' constraints hold on every row.** -/
theorem cpuD_read (hb : ∀ i, i < K → (rowP R.row R.e R.n i).ctr ≤ 2 ^ 24) {i : Nat} (hi : i < K)
    {j : Nat} (hj : j < 4) : ∀ c ∈ readCons j, c.eval ((R.cpuTableD K).env i) = 0 := by
  have hR := runC hA hK
  have cv : ∀ c, (col c).eval ((R.cpuTableD K).env i) = R.cpuColD i c := fun c => R.cpuD_col hi c
  have hk := kindD_isKind hA hK hi
  have hacts := (kind_factsD hi hk).1 j hj
  intro c hc
  unfold readCons at hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨b, hb', rfl⟩ := List.mem_map.1 hc
    obtain ⟨x, hx⟩ := R.colD_bit i hj (List.mem_range.1 hb')
    show (col _).eval _ * ((col _).eval _ - ofN 1) = 0
    rw [cv, hx]; exact P2Run.bool_mod2 x
  · rw [List.mem_singleton.1 hc]
    show (acts.getD j zero).eval _ * (P2Run.readX j).eval _ = 0
    rw [hacts.1]
    cases hjet : R.jetAt i with
    | false =>
      have ek : R.kindD i = kindCf R.A R.row R.e R.n i := by unfold kindD; rw [hjet]; rfl
      have hkC := cpuC_kind hR (roots := R.segRoots) hi
      have hlt12 : kindCf R.A R.row R.e R.n i ≠ 12 := by have := hkC.1; omega
      have hC := cpuC_read hR hb (roots := R.segRoots) hi hj
        (.mul (acts.getD j zero) (P2Run.readX j)) (List.mem_append_right _ (List.mem_singleton_self _))
      rw [show (E.mul (acts.getD j zero) (P2Run.readX j)).eval ((cpuTableC R.A R.row R.e R.n R.segRoots K).env i) =
          (acts.getD j zero).eval _ * (P2Run.readX j).eval _ from rfl, ((kind_factsC hi hkC).1 j hj).1] at hC
      have ag := E.eval_congr (R.cpuD_env_plain hi hjet) (P2Run.readX j)
        (List.all_eq_true.1 P2Run.readX_now j (List.mem_range.2 hj))
      rw [ek, ag]
      unfold actOfD; rw [if_neg hlt12]; exact hC
    | true =>
      have ek : R.kindD i = 12 := by unfold kindD; rw [hjet]; rfl
      rw [ek]
      unfold actOfD
      rw [if_pos rfl]
      rcases (show j < 2 ∨ 2 ≤ j by omega) with h2 | h2
      · rw [if_pos h2]
        obtain ⟨p, rest, hhd, hstk, _, _⟩ := R.jet_rowD hjet
        have hctr := hb i hi
        have ha : (addrs.getD j zero).eval ((R.cpuTableD K).env i) = ofN (addrAt R.A (R.rowQ i) j) ∧
            addrAt R.A (R.rowQ i) j < (R.rowQ i).ctr := by
          rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
          · exact ⟨by show (col HD).eval _ = _; rw [cv, R.colD_hd]; rfl, P2Run.rd_lt hhd⟩
          · exact ⟨by show (col STK).eval _ = _; rw [cv, R.colD_stk]; rfl, P2Run.rd_lt hstk⟩
        have hrv : (rangeVal j).eval ((R.cpuTableD K).env i) = ofN (R.jetRange (R.rowQ i) j) := by
          refine rangeVal_bits (show i < (R.cpuTableD K).h from hi) (fun b hb' => R.colD_jetBit hjet (by omega) hb') ?_
          unfold jetRange; rw [if_pos h2]
          have : (R.rowQ i).ctr ≤ 2 ^ 24 := hctr
          omega
        show ofN 1 * ((col CTR).eval _ - (addrs.getD j zero).eval _ - ofN 1 - (rangeVal j).eval _) = 0
        rw [cv, R.colD_ctr, ha.1, hrv]
        show (1 : F) * _ = 0
        rw [one_mul']
        unfold jetRange; rw [if_pos h2]
        exact P2Run.range_zero ha.2
      · rw [if_neg (by omega)]; exact zero_mul' _

/-- The last row: no restart, the base kind `HK1`. -/
theorem last_kindCfD {i : Nat} (hi : i + 1 = K) : kindCf R.A R.row R.e R.n i = 5 := by
  have hn := hA.acc.npos
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

/-- **The honest CPU table of the circuit with the `dec` jet satisfies its
    AIR**, for the run's own start registers, segments and jet atom. -/
theorem cpuD_sat (hb : ∀ i, i < K → (rowP R.row R.e R.n i).ctr ≤ 2 ^ 24) :
    Sat (cpuAirDec (R.segRoots.getD 0 0) nilA m0.heap.length R.n nilA R.J) (R.cpuTableD K) := by
  have hn := hA.acc.npos
  refine ⟨show 0 < K by omega, fun c hc i (hi : i < K) => ?_⟩
  have cv : ∀ c, (col c).eval ((R.cpuTableD K).env i) = R.cpuColD i c := fun c => R.cpuD_col hi c
  have hk := kindD_isKind hA hK hi
  obtain ⟨_, hhalt, _, _, hHK1, hRS, hDS, nh, ns, nc⟩ := kind_factsD hi hk
  have hk13 := hk.1
  have hkplain : R.jetAt i = false → R.kindD i = kindCf R.A R.row R.e R.n i ∧ kindCf R.A R.row R.e R.n i < 12 :=
    fun hj => ⟨by unfold kindD; rw [hj]; rfl, (cpuC_kind (runC hA hK) (roots := R.segRoots) hi).1⟩
  have hkjet : R.jetAt i = true → R.kindD i = 12 := fun hj => by unfold kindD; rw [hj]; rfl
  have nx : ∀ c', i + 1 < K → (R.cpuTableD K).main ((i + 1) % K) c' = R.cpuColD (i + 1) c' := fun c' hi1 => by
    rw [Nat.mod_eq_of_lt hi1]; rfl
  simp only [cpuAirDec, cpuConsD, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hc
  rcases hc with (((((((⟨j, hj, rfl⟩ | (rfl | rfl)) | rfl) | hc) | hc) | hc) | hc) | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
    rw [show R.cpuColD i (SEL + j) = _ from hk.2.1 j hj]
    split <;> decide
  · simp only [B.bool, sRS, E.eval, cv, B.one, B.c, ofN_one]
    rw [show R.cpuColD i RS = _ from hk.2.2.1]
    split <;> decide
  · simp only [B.bool, sDec, E.eval, cv, B.one, B.c, ofN_one]
    rw [show R.cpuColD i DECSEL = _ from hk.2.2.2]
    split <;> decide
  · have := kind_evalD hi hk (List.all_eq_true.1 kindSumD_all _ (List.mem_range.2 hk13))
    simp only [B.eq, E.eval]
    rw [this]; exact sub_self' _
  · exact cpuD_read hA hK hb hi (by decide) _ hc
  · exact cpuD_read hA hK hb hi (by decide) _ hc
  · exact cpuD_read hA hK hb hi (by decide) _ hc
  · exact cpuD_read hA hK hb hi (by decide) _ hc
  · show (col (SEL + 11)).eval _ = 0
    rw [cv, show R.cpuColD i (SEL + 11) = _ from hk.2.1 11 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · show (col (SEL + 12)).eval _ = 0
    rw [cv, show R.cpuColD i (SEL + 12) = _ from hk.2.1 12 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · show (col (SEL + 13)).eval _ = 0
    rw [cv, show R.cpuColD i (SEL + 13) = _ from hk.2.1 13 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · simp only [B.whenFirst, E.eval, env_first]
    split
    · next h0 => subst h0; rw [cv, R.colD_cnt]; exact mul_zero' _
    · exact zero_mul' _
  · simp only [B.whenTrans, B.eq, B.nxt, sRS, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableD K).main ((i + 1) % K) CNT - (_ + _)) = 0
      rw [nx CNT hi1, one_mul', cv, cv, R.colD_cnt, R.colD_cnt, R.colD_rs, ← ofN_add]
      exact sub_self' _
  · simp only [B.whenLast, B.eq, B.c, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      rw [cv, R.colD_cnt, cntS_after hA.acc.emono hn (by omega), sub_self', mul_zero']
    · exact zero_mul' _
  · -- a jet row reads the atom `J` at the head
    show sDec.eval _ * ((fld 0).eval _ - ofN R.J) = 0
    rw [hDS]
    cases hj : R.jetAt i with
    | false => rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul']
    | true =>
      obtain ⟨p, rest, hhd, _, _, _⟩ := R.jet_rowD hj
      have h0 : (fld 0).eval ((R.cpuTableD K).env i) = ofN R.J := by
        rw [show fld 0 = col (FLD + 0) from rfl, cv, R.colD_fld i (by decide)]
        simp only [fieldsAt, addrAt, hhd, Option.getD_some, cellFields]
        rfl
      rw [h0, sub_self', mul_zero']
  · -- the jet's blinding flag is clear
    show (col (DECSEL + 5)).eval _ * ((col (DECSEL + 5)).eval _ - ofN 1) = 0
    rw [cv, R.colD_block i (by decide) (by decide), zero_mul']
  · -- the next head
    simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableD K).main ((i + 1) % K) HD - (nextHd.eval _ + sRS.eval _ * (col ROOT).eval _ +
        sDec.eval _ * (col DROOT).eval _)) = 0
      rw [nx HD hi1, one_mul', R.colD_hd, hDS]
      cases hj : R.jetAt i with
      | false =>
        rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul', add_zero',
          E.eval_congr (R.cpuD_env_plain hi hj) nextHd P2Run.nextHd_now,
          show sRS.eval ((R.cpuTableD K).env i) = cpuColC R.A R.row R.e R.n R.segRoots i RS by
            rw [show sRS = col RS from rfl, cv, R.cpuColD_plain hj],
          cv, R.cpuColD_plain hj]
        rw [show R.rowQ (i + 1) = rowP R.row R.e R.n (i + 1) from rfl, (cpuC_nextD hA hK hi1 hj).1]
        exact sub_self' _
      | true =>
        rw [if_pos (hkjet hj), nh, hRS, hkjet hj, cv DROOT, R.colD_droot, if_pos hj]
        simp only [nextHdOfD, ↓reduceIte]
        show ofN (R.rowQ (i + 1)).hd - ((0 : F) + ofN 0 * _ + ofN 1 * ofN (R.rowQ (i + 1)).hd) = 0
        rw [ofN_zero, zero_mul', zero_add', zero_add', ofN_one, one_mul', sub_self']
  · -- the next stack
    simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableD K).main ((i + 1) % K) STK - (nextStk.eval _ + sRS.eval _ * ofN nilA +
        sDec.eval _ * (fld 3).eval _)) = 0
      rw [nx STK hi1, one_mul', R.colD_stk, hDS]
      cases hj : R.jetAt i with
      | false =>
        rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul', add_zero',
          E.eval_congr (R.cpuD_env_plain hi hj) nextStk P2Run.nextStk_now,
          show sRS.eval ((R.cpuTableD K).env i) = cpuColC R.A R.row R.e R.n R.segRoots i RS by
            rw [show sRS = col RS from rfl, cv, R.cpuColD_plain hj]]
        rw [show R.rowQ (i + 1) = rowP R.row R.e R.n (i + 1) from rfl, (cpuC_nextD hA hK hi1 hj).2.1]
        exact sub_self' _
      | true =>
        obtain ⟨p, rest, _, hstk, hnext, _⟩ := R.jet_rowD hj
        rw [if_pos (hkjet hj), ns, hRS, hkjet hj, show fld 3 = col (FLD + 3) from rfl, cv (FLD + 3),
          R.colD_fld i (show 3 < 8 by decide), hnext]
        simp only [fieldsAt, addrAt, hstk, Option.getD_some, cellFields, nextStkOfD, ↓reduceIte]
        show ofN rest - ((0 : F) + ofN 0 * _ + ofN 1 * ofN rest) = 0
        rw [ofN_zero, zero_mul', zero_add', zero_add', ofN_one, one_mul', sub_self']
  · -- the next counter
    simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((R.cpuTableD K).main ((i + 1) % K) CTR - (nextCtr.eval _ +
        sDec.eval _ * ((col DCTR).eval _ - (col CTR).eval _))) = 0
      rw [nx CTR hi1, one_mul', R.colD_ctr, hDS]
      cases hj : R.jetAt i with
      | false =>
        rw [if_neg (by have := hkplain hj; omega), ofN_zero, zero_mul', add_zero',
          E.eval_congr (R.cpuD_env_plain hi hj) nextCtr P2Run.nextCtr_now]
        rw [show R.rowQ (i + 1) = rowP R.row R.e R.n (i + 1) from rfl, (cpuC_nextD hA hK hi1 hj).2.2]
        exact sub_self' _
      | true =>
        rw [if_pos (hkjet hj), nc, hkjet hj]
        simp only [nextCtrOfD, ↓reduceIte]
        rw [cv, cv, R.colD_ctr, R.colD_dctr, if_pos hj, ofN_one, one_mul', add_sub_cancel'', sub_self']
  · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
    split
    · next h0 =>
      subst h0
      rw [cv, R.colD_hd, show R.rowQ 0 = R.row 0 from rowQ_of_le (Nat.zero_le _), hA.acc.hd0, sub_self', mul_zero']
    · exact zero_mul' _
  · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
    split
    · next h0 =>
      subst h0
      rw [cv, R.colD_stk, show R.rowQ 0 = R.row 0 from rowQ_of_le (Nat.zero_le _), hA.acc.stk0, sub_self', mul_zero']
    · exact zero_mul' _
  · simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
    split
    · next h0 =>
      subst h0
      rw [cv, R.colD_ctr, show R.rowQ 0 = R.row 0 from rowQ_of_le (Nat.zero_le _), hA.acc.ctr0, sub_self', mul_zero']
    · exact zero_mul' _
  · simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      have hj := R.last_plainD hl' hK
      rw [hhalt, (hkplain hj).1, last_kindCfD hA hK hl']
      show 1 * (ofN 1 - ofN 1) = 0; rw [sub_self', mul_zero']
    · exact zero_mul' _
  · show (col (BLA + 4)).eval _ * ((col (BLA + 4)).eval _ - ofN 1) = 0
    rw [cv, R.colD_blind i (.inl rfl), zero_mul']
  · show (col (BLB + 4)).eval _ * ((col (BLB + 4)).eval _ - ofN 1) = 0
    rw [cv, R.colD_blind i (.inr rfl), zero_mul']
  · simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      have hj := R.last_plainD hl' hK
      rw [hHK1, (hkplain hj).1, last_kindCfD hA hK hl']
      show 1 * (ofN 1 - ofN 1) = 0; rw [sub_self', mul_zero']
    · exact zero_mul' _

end

end DRun

end Circuit
