import Ski.Circuit.ProbeRows
import Ski.Circuit.JetComplete

/-!
# The honest probe tables

The tables a prover builds from a run of `Air.AcceptsP`, segment by segment:

- **CPU**: a row within a segment is the jet CPU's row (`JRun.cpuCol`, the
  run skipping the probe rows); a probe row is the corpus row of its
  registers with selector 12 (the first) or 13 (a later one), the clock,
  and the probe columns: the count, the probed pointer, the starting
  segment's plan row, and for a later row the ending segment's plan row,
  the rest of the stack below its fields and the nil there, the parent's
  end row and the number of children.  Every row carries the count; the
  last reads the nil at its stack.
- **POP**: the jet pops, and a later probe row's fields, each with the
  number of children that read it.
- **PW**: one row per marker a probe row writes.
- **PLAN**: each plan row's lookups on its first row.
-/

namespace Circuit

open B Air JetTable Mach

/-- A run with probe segments: memory, public roots, jets and plan, the
    segments' starts, their fields and the rows. -/
structure PRun where
  A : List Cell
  roots : List (Nat × Nat)
  jets : List Air.Jet
  plan : List Air.Seg
  p : Nat → Nat
  fld : Nat → List Nat
  row : Nat → Air.Row

/-- A segment's plan fields, as the CPU carries them. -/
def segCols (s : Air.Seg) : List F :=
  [ofN s.base, ofN s.k, ofN s.ctor, ofN s.arity, ofN s.parent, ofN s.field]

namespace PRun

variable (R : PRun)

def n : Nat := R.plan.length

/-- The last row: where the last segment ends. -/
def last : Nat := R.p R.n

/-- Segment `j`. -/
def seg (j : Nat) : Air.Seg := R.plan.getD j ⟨0, 0, 0, 0, 0, 0⟩

/-- Row `i` starts a segment. -/
def isP (i : Nat) : Bool := (List.range R.n).any fun j => R.p j == i

/-- The segments that start before row `i`. -/
def pcnt (i : Nat) : Nat := sumTo R.n fun j => if R.p j < i then 1 else 0

/-- The run within segments, skipping the probe rows. -/
def J : JRun := ⟨R.A, R.roots, R.jets, R.last + 1, R.row, R.isP⟩

/-- The segments that read segment `j`'s fields. -/
def nkids (j : Nat) : Nat := sumTo R.n fun c => if 0 < c ∧ (R.seg c).parent = j then 1 else 0

/-- The segments that read field `f` of segment `j`. -/
def uses (j f : Nat) : Nat :=
  sumTo R.n fun c => if 0 < c ∧ (R.seg c).parent = j ∧ (R.seg c).field = f then 1 else 0

/-- What a later probe row pops: the ending segment's fields and the rest. -/
def popsE (i : Nat) : Option (List Nat × Nat) :=
  popR (fun a => R.A[a]?) (R.row i).ctr (R.seg (R.pcnt i - 1)).arity (R.row i).stk

def restE (i : Nat) : Nat := ((R.popsE i).map Prod.snd).getD 0

/-- The probe columns of a probe row. -/
def probeX (i c : Nat) : F :=
  let j := R.pcnt i
  if c = P_CNT then ofN j
  else if c = P_F then ofN (R.row (i + 1)).hd
  else if S_BASE ≤ c ∧ c < S_BASE + 6 then (segCols (R.seg j)).getD (c - S_BASE) 0
  else if j = 0 then 0
  else if E_BASE ≤ c ∧ c < E_BASE + 6 then (segCols (R.seg (j - 1))).getD (c - E_BASE) 0
  else if c = E_REST then ofN (R.restE i)
  else if c = P_NILACT then 1
  else if c = P_NILADDR then ofN (R.restE i)
  else if c = P_CLKP then ofN (R.p ((R.seg j).parent + 1))
  else if c = P_NKIDS then ofN (R.nkids (j - 1))
  else if P_NILBITS ≤ c then ofN ((((R.row i).ctr - R.restE i - 1) / 2 ^ (c - P_NILBITS)) % 2)
  else 0

/-- The probe columns of a row within a segment: the count, and on the
    table's last row the nil at the stack. -/
def normX (K i c : Nat) : F :=
  if c = P_CNT then ofN (R.pcnt i)
  else if i + 1 = K then
    if c = P_NILACT then 1
    else if c = P_NILADDR then ofN (R.J.rowQ i).stk
    else if P_NILBITS ≤ c then ofN ((((R.J.rowQ i).ctr - (R.J.rowQ i).stk - 1) / 2 ^ (c - P_NILBITS)) % 2)
    else 0
  else 0

/-- **The honest probe-CPU row.** -/
def cpuColP (K i c : Nat) : F :=
  if R.isP i then
    if c < CPU_WIDTH then
      (if SEL ≤ c ∧ c < FLD then (if c = SEL + (if i = 0 then 12 else 13) then 1 else 0)
       else Circuit.cpuCol R.A (R.row i) c)
    else if c = J_CLK then ofN i
    else if c < P_CNT then 0
    else R.probeX i c
  else if c < P_CNT then R.J.cpuCol i c else R.normX K i c

def cpuTableP (K : Nat) : Table := ⟨K, fun i c => R.cpuColP K i c, fun _ _ => 0⟩

/-- The POP rows of a later probe row: its fields, each with its readers. -/
def probePops (i : Nat) : List (List F) :=
  if R.isP i ∧ 0 < R.pcnt i then
    (popsOf R.A (R.row i).ctr (R.seg (R.pcnt i - 1)).arity (R.row i).stk).zipIdx.map fun (q, f) =>
      popRow i (R.row i).ctr f q.1 q.2.1 q.2.2 (R.uses (R.pcnt i - 1) f)
  else []

def popRowsAtP (i : Nat) : List (List F) := R.J.popRowsAt i ++ R.probePops i
def popRowsP (K : Nat) : List (List F) := (List.range K).flatMap R.popRowsAtP
def popTableP (K HP : Nat) : Table := ⟨HP, ofRows (R.popRowsP K), fun _ _ => 0⟩

/-- A PW row: `clk c base k i act`. -/
def pwRow (i c b k q : Nat) : List F := [ofN i, ofN c, ofN b, ofN k, ofN q, 1]

def pwRowsAt (i : Nat) : List (List F) :=
  if R.isP i then
    (List.range (R.seg (R.pcnt i)).k).map fun q =>
      pwRow i (R.row i).ctr (R.seg (R.pcnt i)).base (R.seg (R.pcnt i)).k q
  else []

def pwRows (K : Nat) : List (List F) := (List.range K).flatMap R.pwRowsAt
def pwTable (K HW : Nat) : Table := ⟨HW, ofRows (R.pwRows K), fun _ _ => 0⟩

/-- How often the probe rows look up a plan row. -/
def cntPlan (K : Nat) (v : List F) : Nat :=
  sumTo K fun i => if R.isP i then
    (if ofN (R.pcnt i) :: segCols (R.seg (R.pcnt i)) = v then 1 else 0) +
    (if 0 < R.pcnt i ∧ ofN (R.pcnt i - 1) :: segCols (R.seg (R.pcnt i - 1)) = v then 1 else 0)
  else 0

end PRun

-- ---------------------------------------------------------------------------
-- Counting below a bound
-- ---------------------------------------------------------------------------

theorem sumTo_lt (j : Nat) : ∀ n, j ≤ n → sumTo n (fun x => if x < j then 1 else 0) = j
  | 0, h => by rw [Nat.le_zero.1 h]; rfl
  | n + 1, h => by
    show sumTo n (fun x => if x < j then 1 else 0) + (if n < j then 1 else 0) = j
    rcases Nat.lt_or_ge n j with h' | h'
    · have : j = n + 1 := by omega
      subst this
      rw [if_pos h']
      have e : sumTo n (fun x => if x < n + 1 then 1 else 0) = sumTo n (fun x => if x < n then 1 else 0) :=
        sumTo_congr n (fun q hq => by rw [if_pos (by omega), if_pos hq])
      rw [e, sumTo_lt n n (Nat.le_refl n)]
    · rw [if_neg (by omega), sumTo_lt j n h', Nat.add_zero]

theorem sumTo_eq_zero {f : Nat → Nat} : ∀ n, (∀ q, q < n → f q = 0) → sumTo n f = 0
  | 0, _ => rfl
  | n + 1, h => by
    show sumTo n f + f n = 0
    rw [sumTo_eq_zero n (fun q hq => h q (by omega)), h n (by omega)]

theorem sumTo_eq_one {f : Nat → Nat} {x : Nat} : ∀ n, x < n → f x = 1 → (∀ q, q < n → q ≠ x → f q = 0) →
    sumTo n f = 1
  | 0, hx, _, _ => absurd hx (Nat.not_lt_zero _)
  | n + 1, hx, h1, h0 => by
    show sumTo n f + f n = 1
    rcases Nat.lt_or_ge x n with h' | h'
    · rw [sumTo_eq_one n h' h1 (fun q hq hne => h0 q (by omega) hne), h0 n (by omega) (by omega)]
    · have : x = n := by omega
      subst this
      rw [sumTo_eq_zero x (fun q hq => h0 q (by omega) (by omega)), h1]

namespace PRun

variable {R : PRun} {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
include hA

theorem p_mono {a b : Nat} (hab : a < b) (hb : b ≤ R.n) : R.p a < R.p b :=
  Nat.lt_of_lt_of_le (hA.pmono a (by unfold n at hb; omega)) (pmono_le hA.pmono (by omega) hb)

theorem p_inj {a b : Nat} (ha : a ≤ R.n) (hb : b ≤ R.n) (e : R.p a = R.p b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := p_mono hA h hb; omega
  · exact h
  · have := p_mono hA h ha; omega

omit hA in
theorem isP_iff {i : Nat} : R.isP i = true ↔ ∃ j, j < R.n ∧ R.p j = i := by
  unfold isP
  rw [List.any_eq_true]
  constructor
  · rintro ⟨j, hj, e⟩; exact ⟨j, List.mem_range.1 hj, beq_iff_eq.1 e⟩
  · rintro ⟨j, hj, e⟩; exact ⟨j, List.mem_range.2 hj, beq_iff_eq.2 e⟩

theorem isP_p {j : Nat} (hj : j < R.n) : R.isP (R.p j) = true := isP_iff.2 ⟨j, hj, rfl⟩

/-- **The segments before segment `j`'s start are the first `j`.** -/
theorem pcnt_p {j : Nat} (hj : j ≤ R.n) : R.pcnt (R.p j) = j := by
  unfold pcnt
  rw [sumTo_congr R.n (fun q hq => by
    show (if R.p q < R.p j then 1 else 0) = if q < j then 1 else 0
    rcases Nat.lt_or_ge q j with h | h
    · rw [if_pos (p_mono hA h hj), if_pos h]
    · rw [if_neg (Nat.not_lt_of_le (pmono_le hA.pmono h (Nat.le_of_lt hq))), if_neg (by omega)])]
  exact sumTo_lt j R.n hj

theorem pcnt_succ (i : Nat) : R.pcnt (i + 1) = R.pcnt i + (if R.isP i then 1 else 0) := by
  unfold pcnt
  have e : ∀ q, (if R.p q < i + 1 then 1 else 0) = (if R.p q < i then 1 else 0) + (if R.p q = i then 1 else 0) := by
    intro q
    rcases Nat.lt_trichotomy (R.p q) i with h | h | h
    · rw [if_pos (by omega), if_pos h, if_neg (by omega)]
    · rw [if_pos (by omega), if_neg (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [sumTo_congr R.n (fun q _ => e q), sumTo_add]
  congr 1
  cases hp : R.isP i with
  | true =>
    obtain ⟨j, hj, hji⟩ := isP_iff.1 hp
    refine sumTo_eq_one R.n hj (by rw [if_pos hji]) (fun q hq hne => ?_)
    rw [if_neg]
    intro e2
    exact hne (p_inj hA (Nat.le_of_lt hq) (Nat.le_of_lt hj) (e2.trans hji.symm))
  | false =>
    refine sumTo_eq_zero R.n (fun q hq => ?_)
    rw [if_neg]
    intro e2
    have := isP_iff.2 ⟨q, hq, e2⟩
    rw [hp] at this; cases this

/-- A row past the last counts every segment. -/
theorem pcnt_ge {i : Nat} (hi : R.last < i) : R.pcnt i = R.n := by
  unfold pcnt
  rw [sumTo_congr R.n (fun q hq => by
    show (if R.p q < i then 1 else 0) = if q < R.n then 1 else 0
    rw [if_pos (Nat.lt_of_le_of_lt (pmono_le hA.pmono (Nat.le_of_lt hq) (Nat.le_refl _)) hi), if_pos hq])]
  exact sumTo_lt R.n R.n (Nat.le_refl _)

omit hA in
theorem pcnt_le (i : Nat) : R.pcnt i ≤ R.n := by
  unfold pcnt
  have := sumTo_le_one (f := fun q => if R.p q < i then 1 else 0) (fun q => by split <;> decide) R.n
  exact this

/-- A probe row is before the last row. -/
theorem isP_lt {i : Nat} (hp : R.isP i = true) : i < R.last := by
  obtain ⟨j, hj, rfl⟩ := isP_iff.1 hp
  exact p_mono hA hj (Nat.le_refl _)

/-- A probe row starts segment `pcnt i`. -/
theorem isP_pcnt {i : Nat} (hp : R.isP i = true) : R.pcnt i < R.n ∧ R.p (R.pcnt i) = i := by
  obtain ⟨j, hj, rfl⟩ := isP_iff.1 hp
  rw [pcnt_p hA (Nat.le_of_lt hj)]
  exact ⟨hj, rfl⟩

theorem seg_get {j : Nat} (hj : j < R.n) : R.plan[j]? = some (R.seg j) := by
  unfold seg
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

end PRun

/-- An end row, unfolded: the marker at the head, the fields popped, a nil
    below them. -/
theorem endRow_parts {M : List Cell} {s : Air.Seg} {ps : List Nat} {r : Air.Row} (h : Air.endRow M s ps r = true) :
    rd M r.ctr r.hd = some (.atom (s.ctor + s.base)) ∧
      ∃ rest, popR (fun a => M[a]?) r.ctr s.arity r.stk = some (ps, rest) ∧ rd M r.ctr rest = some .nil := by
  unfold Air.endRow endRowG at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨beq_iff_eq.1 h1, ?_⟩
  split at h2
  · next qs rest hp =>
    rw [Bool.and_eq_true] at h2
    obtain ⟨h3, h4⟩ := h2
    rw [beq_iff_eq.1 h3] at hp
    exact ⟨rest, hp, beq_iff_eq.1 h4⟩
  · cases h2

theorem haltRow_atom {M : List Cell} {r : Air.Row} {a : Nat} (h : rd M r.ctr r.hd = some (.atom a)) :
    haltRow M r = true := by
  unfold haltRow; rw [h]

theorem kindOf_atom {M : List Cell} {r : Air.Row} {a : Nat} (h : rd M r.ctr r.hd = some (.atom a)) :
    kindOf M r = 10 := by
  unfold kindOf; rw [h]

namespace PRun

variable {R : PRun} {t : Term} (hA : AcceptsP R.A (load t) R.roots R.jets R.plan R.p R.fld R.row)
  (hroots : RootsOK (load t).heap R.roots R.jets)
include hA

/-- The last row ends the last segment. -/
theorem last_end : ∃ rest, rd R.A (R.row R.last).ctr (R.row R.last).hd =
      some (.atom ((R.seg (R.n - 1)).ctor + (R.seg (R.n - 1)).base)) ∧
    popR (fun a => R.A[a]?) (R.row R.last).ctr (R.seg (R.n - 1)).arity (R.row R.last).stk =
      some (R.fld (R.n - 1), rest) ∧ rd R.A (R.row R.last).ctr rest = some .nil := by
  have hn := hA.nonempty
  have he := hA.ends (R.n - 1) (R.seg (R.n - 1)) (seg_get hA (by unfold n; omega))
  rw [show R.n - 1 + 1 = R.plan.length by unfold n; omega] at he
  obtain ⟨h1, rest, h2, h3⟩ := endRow_parts he
  exact ⟨rest, h1, h2, h3⟩

theorem last_halt : haltRow R.A (R.row R.last) = true := by
  obtain ⟨_, h1, _⟩ := last_end hA
  exact haltRow_atom h1

include hroots in
/-- **The rows within segments are a jetted run**, skipping the probe rows. -/
theorem jok : JOK R.J := by
  refine ⟨Nat.succ_pos _, fun i hi hs => ?_, ?_, fun i hi => ?_⟩
  · have hn : ∀ j, j < R.plan.length → i ≠ R.p j := by
      intro j hj e
      have := isP_iff.2 ⟨j, hj, e.symm⟩
      have hs' : R.isP i = false := hs
      rw [hs'] at this; cases this
    exact hA.norm i (by show i < R.p R.plan.length; have : i + 1 < R.last + 1 := hi; unfold last n at this; omega) hn
  · show haltRow R.A (R.row (R.last + 1 - 1)) = true
    rw [Nat.add_sub_cancel]; exact last_halt hA
  · exact (hA.ctrs hroots i (by have : i < R.last + 1 := hi; unfold last n at this; omega)).2.1

/-- **A probe row, unfolded**: its writes and the next row. -/
theorem probe_spec {j : Nat} (hj : j < R.n) :
    wrs R.A (R.row (R.p j)).ctr (pcells (R.seg j).base (R.seg j).k (R.row (R.p j)).ctr) = true ∧
    R.row (R.p j + 1) = ⟨fptr R.plan R.fld (R.row 0).hd j, (R.row (R.p j)).ctr + (R.seg j).k,
      (R.row (R.p j)).ctr + ((R.seg j).k + (R.seg j).k + 1)⟩ := by
  have h := hA.probe j (R.seg j) (seg_get hA hj)
  unfold probeRow probeRowG at h
  split at h
  · next hw =>
    rw [pcells_length] at h
    exact ⟨by rw [wrs_G]; exact hw, (Option.some.inj h).symm⟩
  · cases h

/-- **A later probe row ends the segment before it**: the marker at the
    head, the fields popped, a nil below them. -/
theorem later_end {j : Nat} (hj : j < R.n) (h0 : 0 < j) :
    rd R.A (R.row (R.p j)).ctr (R.row (R.p j)).hd =
      some (.atom ((R.seg (j - 1)).ctor + (R.seg (j - 1)).base)) ∧
    R.popsE (R.p j) = some (R.fld (j - 1), R.restE (R.p j)) ∧
    rd R.A (R.row (R.p j)).ctr (R.restE (R.p j)) = some .nil := by
  have he := hA.ends (j - 1) (R.seg (j - 1)) (seg_get hA (by omega))
  rw [Nat.sub_add_cancel h0] at he
  obtain ⟨h1, rest, h2, h3⟩ := endRow_parts he
  have hpe : R.popsE (R.p j) = some (R.fld (j - 1), rest) := by
    unfold popsE; rw [pcnt_p hA (Nat.le_of_lt hj)]; exact h2
  have hre : R.restE (R.p j) = rest := by unfold restE; rw [hpe]; rfl
  rw [hre]
  exact ⟨h1, hpe, h3⟩

end PRun

end Circuit
