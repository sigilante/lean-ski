import Ski.Circuit.CompFinal
import Ski.Circuit.Segments

/-!
# The honest composed CPU table

For a run the Lean AIR with segments accepts (`CompM.AcceptsC`), padded
to `K` rows by repeating its last, the CPU table the prover builds
(`cpuTableC`): the base honest columns (`cpuCol`), the kind selectors
cleared on restart rows, the restart selector, the segment counter, the
next root, and the blinding flags clear.
-/

namespace Circuit

open B Air Compose CompM

/-- The run, padded by repeating its last row. -/
def rowP (row : Nat → Row) (e : Nat → Nat) (n i : Nat) : Row :=
  if i ≤ e (n - 1) then row i else row (e (n - 1))

/-- **The honest composed CPU row.** -/
def cpuColC (A : List Cell) (row : Nat → Row) (e : Nat → Nat) (n : Nat) (roots : List Nat) (i col : Nat) : F :=
  if col < CPU_WIDTH then
    (if SEL ≤ col ∧ col < SEL + NKINDS ∧ isRestart e n i = true then 0 else cpuCol A (rowP row e n i) col)
  else if col = RS then (if isRestart e n i then 1 else 0)
  else if col = CNT then ofN (cntS (rsI e n) i)
  else if col = ROOT then ofN (roots.getD (cntS (rsI e n) i + 1) 0)
  else 0

def cpuTableC (A : List Cell) (row : Nat → Row) (e : Nat → Nat) (n : Nat) (roots : List Nat) (K : Nat) : Table :=
  ⟨K, fun i col => cpuColC A row e n roots i col, fun _ _ => 0⟩

/-- The kind of a composed row: a restart, or its base kind. -/
def kindCf (A : List Cell) (row : Nat → Row) (e : Nat → Nat) (n i : Nat) : Nat :=
  if isRestart e n i then 11 else kindOf A (rowP row e n i)

section

variable {A : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Row}
  (hA : AcceptsC A m0 roots nilA n e row) {K : Nat} (hK : e (n - 1) < K)
include hA hK

theorem restart_lt {i : Nat} (hr : isRestart e n i = true) : i < e (n - 1) := by
  obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
  exact emono_lt hA.emono (by omega) (by have := hA.npos; omega)

/-- Every padded row steps or halts. -/
theorem valid_rowP {i : Nat} (hi : i < K) : Valid A (rowP row e n i) := by
  have hn := hA.npos
  unfold rowP
  split
  · next hle =>
    rcases Nat.lt_or_ge i (e (n - 1)) with hlt | hge
    · cases hr : isRestart e n i with
      | false =>
        have hne : ∀ j, j + 1 < n → i ≠ e j := fun j hj h' => by
          rw [show isRestart e n i = true from isRestart_iff.2 ⟨j, hj, h'.symm⟩] at hr; cases hr
        rcases hA.trans i hlt hne with h | h
        · exact .inl (by rw [h]; rfl)
        · exact .inr h.1
      | true =>
        obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
        obtain ⟨h1, h2⟩ := hA.ends j (by omega)
        exact .inr (by simp only [haltRow, h1, short, h2])
    · rw [show i = e (n - 1) by omega]
      obtain ⟨h1, h2⟩ := hA.ends (n - 1) (by omega)
      exact .inr (by simp only [haltRow, h1, short, h2])
  · obtain ⟨h1, h2⟩ := hA.ends (n - 1) (by omega)
    exact .inr (by simp only [haltRow, h1, short, h2])

/-- A segment's end is `HK1` to the base classification. -/
theorem end_kind {j : Nat} (hj : j < n) : kindOf A (row (e j)) = 5 := by
  obtain ⟨h1, h2⟩ := hA.ends j hj
  simp only [kindOf, h1, h2]

theorem restart_kindOf {i : Nat} (hr : isRestart e n i = true) : kindOf A (rowP row e n i) = 5 := by
  obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
  have := restart_lt hA hK hr
  unfold rowP; rw [if_pos (by omega)]
  exact end_kind hA hK (by omega)

theorem kindCf_lt {i : Nat} (hi : i < K) : kindCf A row e n i < 12 := by
  unfold kindCf; split
  · decide
  · have := (shape (valid_rowP hA hK hi)).lt; omega

/-- **The honest composed row has its kind.** -/
theorem cpuC_kind {i : Nat} (hi : i < K) :
    IsKindC (cpuTableC A row e n roots K) i (kindCf A row e n i) := by
  refine ⟨kindCf_lt hA hK hi, fun j hj => ?_, ?_⟩
  · show cpuColC A row e n roots i (SEL + j) = _
    have hw : SEL + j < CPU_WIDTH := by unfold SEL NKINDS CPU_WIDTH BITS FLD RANGE_BITS at *; omega
    unfold cpuColC kindCf
    rw [if_pos hw]
    cases hr : isRestart e n i with
    | true =>
      rw [if_pos ⟨Nat.le_add_right _ _, by omega, rfl⟩, if_pos rfl, if_neg (fun h => absurd h.2 (by decide))]
    | false =>
      rw [if_neg (fun h => absurd h.2.2 (by simp)), cpuCol_sel _ _ hj]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := (shape (valid_rowP hA hK hi)).lt
      by_cases h' : j = kindOf A (rowP row e n i)
      · rw [if_pos h', if_pos ⟨h', this⟩]
      · rw [if_neg h', if_neg (fun h => h' h.1)]
  · show cpuColC A row e n roots i RS = _
    unfold cpuColC kindCf
    rw [if_neg (by unfold RS CPU_WIDTH; omega), if_pos rfl]
    cases hr : isRestart e n i with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have := (shape (valid_rowP hA hK hi)).lt
      rw [if_neg (by omega)]

/-- Rows and columns the two tables share: every base column but the kind
    selectors. -/
theorem cpuC_agree {i : Nat} (hi : i < K) {c : Nat} (hc : c < CPU_WIDTH) (hs : ¬ (SEL ≤ c ∧ c < SEL + NKINDS)) :
    (cpuTableC A row e n roots K).env i (.main 0 c) = (cpuTable A (rowP row e n) K).env i (.main 0 c) := by
  show (cpuTableC A row e n roots K).main ((i + 0) % K) c = (cpuTable A (rowP row e n) K).main ((i + 0) % K) c
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]
  show cpuColC A row e n roots i c = cpuCol A (rowP row e n i) c
  unfold cpuColC
  rw [if_pos hc, if_neg (fun h => hs ⟨h.1, h.2.1⟩)]

/-- The reads' activity is the base kind's: a restart reads as `HK1`. -/
theorem actOfC_kindCf {i : Nat} (hi : i < K) (j : Nat) :
    actOfC (kindCf A row e n i) j = actOf (kindOf A (rowP row e n i)) j := by
  unfold kindCf
  cases hr : isRestart e n i with
  | true =>
    rw [if_pos rfl, restart_kindOf hA hK hr]
    unfold actOfC actOf
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | h3
    · rfl
    · rfl
    · rfl
    · simp only [↓reduceIte, show ¬ j < 2 by omega]
      split <;> first | rfl | omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := (shape (valid_rowP hA hK hi)).lt
    unfold actOfC; rw [if_neg (by omega)]

end

/-- Only base columns other than the kind selectors. -/
def baseAtom : Atom → Bool
  | .main 0 c => decide (c < CPU_WIDTH) && !(decide (SEL ≤ c) && decide (c < SEL + NKINDS))
  | _ => false

def E.onlyAtoms (p : Atom → Bool) : E → Bool
  | .atom a => p a
  | .const _ => true
  | .add a b | .sub a b | .mul a b => a.onlyAtoms p && b.onlyAtoms p
  | .neg a => a.onlyAtoms p

theorem E.eval_congr {p : Atom → Bool} {ρ ρ' : Atom → F} (h : ∀ a, p a = true → ρ a = ρ' a) :
    ∀ e : E, e.onlyAtoms p = true → e.eval ρ = e.eval ρ'
  | .atom a, he => h a he
  | .const _, _ => rfl
  | .add a b, he | .sub a b, he | .mul a b, he => by
    simp only [E.onlyAtoms, Bool.and_eq_true] at he
    simp only [E.eval, E.eval_congr h a he.1, E.eval_congr h b he.2]
  | .neg a, he => by simp only [E.onlyAtoms] at he; simp only [E.eval, E.eval_congr h a he]

theorem readRest_base : ∀ j, j < 4 →
    (E.sub (.sub (.sub (col CTR) (addrs.getD j zero)) one) (rangeVal j)).onlyAtoms baseAtom = true ∧
    ∀ b, b < RANGE_BITS → (B.bool (col (BITS + j * RANGE_BITS + b))).onlyAtoms baseAtom = true := by
  intro j hj
  refine ⟨?_, fun b hb => ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  · have c1 : BITS = 25 := rfl
    have c2 : CPU_WIDTH = 121 := rfl
    have c3 : RANGE_BITS = 24 := rfl
    have c4 : SEL = 3 := rfl
    have c5 : NKINDS = 14 := rfl
    have hjr : j * RANGE_BITS ≤ 72 := by rw [c3]; omega
    have hx : baseAtom (.main 0 (BITS + j * RANGE_BITS + b)) = true := by
      simp only [baseAtom]
      rw [decide_eq_true (show BITS + j * RANGE_BITS + b < CPU_WIDTH by omega),
        decide_eq_false (show ¬ (BITS + j * RANGE_BITS + b < SEL + NKINDS) by omega)]
      cases decide (SEL ≤ BITS + j * RANGE_BITS + b) <;> rfl
    show (baseAtom (.main 0 (BITS + j * RANGE_BITS + b)) &&
      (baseAtom (.main 0 (BITS + j * RANGE_BITS + b)) && true)) = true
    rw [hx]; rfl

section

variable {A : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Row}
  (hA : AcceptsC A m0 roots nilA n e row) {K : Nat} (hK : e (n - 1) < K)
  (hb : ∀ i, i < K → (rowP row e n i).ctr ≤ 2 ^ 24)
include hA hK

theorem cpuC_env_base {i : Nat} (hi : i < K) :
    ∀ a, baseAtom a = true → (cpuTableC A row e n roots K).env i a = (cpuTable A (rowP row e n) K).env i a := by
  intro a ha
  cases a with
  | main o c =>
    cases o with
    | zero =>
      simp only [baseAtom, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at ha
      exact cpuC_agree hA hK hi ha.1 (fun h => by rcases ha.2 with h' | h' <;> omega)
    | succ o => simp [baseAtom] at ha
  | _ => simp [baseAtom] at ha

include hb in
/-- **The reads' constraints hold on the honest composed table.** -/
theorem cpuC_read {i : Nat} (hi : i < K) {j : Nat} (hj : j < 4) :
    ∀ c ∈ readCons j, c.eval ((cpuTableC A row e n roots K).env i) = 0 := by
  have hbase := cpu_read (M := A) (row := rowP row e n) (k := K) (valid_rowP hA hK hi) (hb i hi) hi hj
  have cong := E.eval_congr (cpuC_env_base hA hK hi)
  obtain ⟨hrest, hbits⟩ := readRest_base j hj
  intro c hc
  have hc' := hc
  unfold readCons at hc'
  simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hc'
  rcases hc' with ⟨b, hb', rfl⟩ | rfl
  · rw [cong _ (hbits b hb')]; exact hbase _ hc
  · show (acts.getD j zero).eval _ * _ = 0
    rw [cong _ hrest]
    have hk := cpuC_kind hA hK (roots := roots) hi
    have hk0 := cpu_kind (M := A) (row := rowP row e n) (k := K) hi (shape (valid_rowP hA hK hi))
    rw [((kind_factsC hi hk).1 j hj).1, actOfC_kindCf hA hK hi, ← ((kind_facts hi hk0).1 j hj).1]
    exact hbase _ hc

end

theorem nextOf_base : (List.range 11).all (fun k => (nextHdOf k).onlyAtoms baseAtom &&
    (nextStkOf k).onlyAtoms baseAtom && (nextCtrOf k).onlyAtoms baseAtom) = true := by decide

theorem kindSumC_all :
    (List.range 12).all (fun k => kindEqC k (sum ((List.range NKINDS).map (fun i => col (SEL + i)) ++ [sRS])) one) = true := by
  decide

section

variable {A : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat} {e : Nat → Nat} {row : Nat → Row}
  (hA : AcceptsC A m0 roots nilA n e row) {K : Nat} (hK : e (n - 1) < K)
  (hb : ∀ i, i < K → (rowP row e n i).ctr ≤ 2 ^ 24)
include hA hK

theorem cpuC_col {i : Nat} (hi : i < K) (c : Nat) :
    (col c).eval ((cpuTableC A row e n roots K).env i) = cpuColC A row e n roots i c := by
  show (cpuTableC A row e n roots K).main ((i + 0) % K) c = _
  rw [Nat.add_zero, Nat.mod_eq_of_lt hi]; rfl

omit hA hK in
theorem cpuColC_reg (i : Nat) {c : Nat} (hc : c = HD ∨ c = STK ∨ c = CTR) :
    cpuColC A row e n roots i c = cpuCol A (rowP row e n i) c := by
  unfold cpuColC
  rcases hc with rfl | rfl | rfl <;> rfl

/-- A row that is no restart steps or has halted, padded. -/
theorem rowP_step {i : Nat} (hi1 : i + 1 < K) (hr : isRestart e n i = false) :
    stepRow A (rowP row e n i) = some (rowP row e n (i + 1)) ∨
      (haltRow A (rowP row e n i) = true ∧ rowP row e n (i + 1) = rowP row e n i) := by
  have hn := hA.npos
  rcases Nat.lt_or_ge i (e (n - 1)) with hlt | hge
  · have ne : ∀ j, j + 1 < n → i ≠ e j := fun j hj h' => by
      rw [isRestart_iff.2 ⟨j, hj, h'.symm⟩] at hr; cases hr
    unfold rowP
    rw [if_pos (by omega), if_pos (by omega)]
    exact hA.trans i hlt ne
  · have e1 : rowP row e n i = row (e (n - 1)) := by
      unfold rowP; split
      · next h => rw [show i = e (n - 1) by omega]
      · rfl
    have e2 : rowP row e n (i + 1) = row (e (n - 1)) := by
      unfold rowP; rw [if_neg (by omega)]
    obtain ⟨h1, h2⟩ := hA.ends (n - 1) (by omega)
    refine .inr ⟨?_, by rw [e1, e2]⟩
    rw [e1]; simp only [haltRow, h1, short, h2]

omit hA hK in
theorem cpuColC_cnt (i : Nat) : cpuColC A row e n roots i CNT = ofN (cntS (rsI e n) i) := by
  unfold cpuColC; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

omit hA hK in
theorem cpuColC_rs (i : Nat) : cpuColC A row e n roots i RS = ofN (rsI e n i) := by
  unfold cpuColC rsI; rw [if_neg (by decide), if_pos rfl]; split <;> rfl

omit hA hK in
theorem cpuColC_root (i : Nat) : cpuColC A row e n roots i ROOT = ofN (roots.getD (cntS (rsI e n) i + 1) 0) := by
  unfold cpuColC; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

omit hA hK in
theorem cpuColC_blind (i : Nat) {c : Nat} (hc : c = BLA + 4 ∨ c = BLB + 4) : cpuColC A row e n roots i c = 0 := by
  unfold cpuColC
  rcases hc with rfl | rfl <;> rfl

/-- The last row: no restart, the base kind `HK1`. -/
theorem last_kindCf {i : Nat} (hi : i + 1 = K) : kindCf A row e n i = 5 := by
  have hn := hA.npos
  unfold kindCf
  cases hr : isRestart e n i with
  | true => have := restart_lt hA hK hr; omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have e1 : rowP row e n i = row (e (n - 1)) := by
      unfold rowP; split
      · next h => rw [show i = e (n - 1) by omega]
      · rfl
    rw [e1]; exact end_kind hA hK (by omega)

include hb in
/-- The next registers, with a restart's jump. -/
theorem cpuC_next {i : Nat} (hi1 : i + 1 < K) :
    ofN (rowP row e n (i + 1)).hd = nextHd.eval ((cpuTableC A row e n roots K).env i) +
      cpuColC A row e n roots i RS * cpuColC A row e n roots i ROOT ∧
    ofN (rowP row e n (i + 1)).stk = nextStk.eval ((cpuTableC A row e n roots K).env i) +
      cpuColC A row e n roots i RS * ofN nilA ∧
    ofN (rowP row e n (i + 1)).ctr = nextCtr.eval ((cpuTableC A row e n roots K).env i) := by
  have hi : i < K := Nat.lt_of_succ_lt hi1
  have hn := hA.npos
  have hk := cpuC_kind hA hK (roots := roots) hi
  obtain ⟨_, _, _, _, _, _, nh, ns, nc⟩ := kind_factsC hi hk
  rw [nh, ns, nc, cpuColC_rs]
  unfold kindCf
  cases hr : isRestart e n i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, rsI, hr, ofN_zero, zero_mul', add_zero']
    have hS := shape (valid_rowP hA hK hi)
    have hk11 : kindOf A (rowP row e n i) < 11 := hS.lt
    simp only [nextHdOfC, nextStkOfC, nextCtrOfC, if_neg (show kindOf A (rowP row e n i) ≠ 11 by omega)]
    have hbase := List.all_eq_true.1 nextOf_base _ (List.mem_range.2 hk11)
    simp only [Bool.and_eq_true] at hbase
    have cong := E.eval_congr (cpuC_env_base hA hK (roots := roots) hi)
    rw [cong _ hbase.1.1, cong _ hbase.1.2, cong _ hbase.2]
    exact cpu_next (valid_rowP hA hK (Nat.lt_of_succ_lt hi1)) hi1 (rowP_step hA hK hi1 hr)
  | true =>
    obtain ⟨j, hj, rfl⟩ := isRestart_iff.1 hr
    have hlt := restart_lt hA hK hr
    simp only [↓reduceIte, rsI, hr, ofN_one, one_mul']
    have z1 : (nextHdOfC 11).eval ((cpuTableC A row e n roots K).env (e j)) = 0 := rfl
    have z2 : (nextStkOfC 11).eval ((cpuTableC A row e n roots K).env (e j)) = 0 := rfl
    have z3 : (nextCtrOfC 11).eval ((cpuTableC A row e n roots K).env (e j)) =
        cpuColC A row e n roots (e j) CTR := cpuC_col hA hK hi CTR
    rw [z1, z2, z3, zero_add', zero_add', cpuColC_root, cntS_end hA.emono j (by omega), cpuColC_reg _ (.inr (.inr rfl))]
    have e1 : rowP row e n (e j + 1) = row (e j + 1) := by unfold rowP; rw [if_pos (by omega)]
    have e0 : rowP row e n (e j) = row (e j) := by unfold rowP; rw [if_pos (by omega)]
    rw [e1, hA.restart j hj, e0]
    exact ⟨rfl, rfl, rfl⟩

include hb in
theorem cpuC_transC {i : Nat} (hi : i < K) {reg : Nat} (hreg : reg = HD ∨ reg = STK ∨ reg = CTR) :
    (whenTrans (B.eq (nxt reg) (if reg = HD then E.add nextHd (.mul sRS (col ROOT))
      else if reg = STK then E.add nextStk (.mul sRS (B.c nilA)) else nextCtr))).eval
      ((cpuTableC A row e n roots K).env i) = 0 := by
  simp only [B.whenTrans, B.eq, B.nxt, E.eval, env_trans, env_main1]
  split
  · exact zero_mul' _
  · next hne =>
    have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
    obtain ⟨n1, n2, n3⟩ := cpuC_next hA hK hb (roots := roots) hi1
    show 1 * (cpuColC A row e n roots ((i + 1) % K) reg - _) = 0
    rw [Nat.mod_eq_of_lt hi1, one_mul', cpuColC_reg _ hreg]
    have cv := cpuC_col hA hK (roots := roots) hi
    rcases hreg with rfl | rfl | rfl
    · simp only [↓reduceIte, E.eval, sRS, cv]
      show ofN (rowP row e n (i + 1)).hd - _ = 0
      rw [n1]; exact sub_self' _
    · simp only [show STK ≠ HD by decide, ↓reduceIte, E.eval, sRS, B.c, cv]
      show ofN (rowP row e n (i + 1)).stk - _ = 0
      rw [n2]; exact sub_self' _
    · simp only [show CTR ≠ HD by decide, show CTR ≠ STK by decide, ↓reduceIte]
      show ofN (rowP row e n (i + 1)).ctr - _ = 0
      rw [n3]; exact sub_self' _

theorem cpuC_first {i : Nat} (hi : i < K) {reg : Nat} (hreg : reg = HD ∨ reg = STK ∨ reg = CTR) :
    (whenFirst (B.eq (col reg) (B.c (if reg = HD then roots.getD 0 0 else if reg = STK then nilA
      else m0.heap.length)))).eval ((cpuTableC A row e n roots K).env i) = 0 := by
  simp only [B.whenFirst, B.eq, B.c, E.eval, env_first]
  split
  · next h0 =>
    subst h0
    rw [cpuC_col hA hK hi, cpuColC_reg _ hreg]
    have e0 : rowP row e n 0 = row 0 := by unfold rowP; rw [if_pos (Nat.zero_le _)]
    rcases hreg with rfl | rfl | rfl
    · show 1 * (ofN (rowP row e n 0).hd - _) = _; rw [e0, hA.hd0, if_pos rfl, sub_self', mul_zero']
    · show 1 * (ofN (rowP row e n 0).stk - _) = _
      rw [e0, hA.stk0, if_neg (by decide), if_pos rfl, sub_self', mul_zero']
    · show 1 * (ofN (rowP row e n 0).ctr - _) = _
      rw [e0, hA.ctr0, if_neg (by decide), if_neg (by decide), sub_self', mul_zero']
  · exact zero_mul' _

/-- The reads' tags are the base kind's: a restart reads as `HK1`. -/
theorem tagOfC_kindCf {i : Nat} (hi : i < K) (j : Nat) :
    tagOfC (kindCf A row e n i) j = tagOf (kindOf A (rowP row e n i)) j := by
  unfold kindCf
  cases hr : isRestart e n i with
  | true =>
    rw [if_pos rfl, restart_kindOf hA hK hr]
    unfold tagOfC tagOf
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega) with rfl | rfl | rfl | h3
    · rfl
    · rfl
    · rfl
    · simp only [↓reduceIte, show ¬ j = 0 by omega, show ¬ j = 1 by omega]
      split <;> first | rfl | omega
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := (shape (valid_rowP hA hK hi)).lt
    unfold tagOfC; rw [if_neg (by omega)]

omit hA hK in
theorem writes_base : writeInters.all (fun I => I.count.onlyAtoms (fun a => match a with
    | .main 0 c => decide (SEL ≤ c ∧ c < SEL + NKINDS) | _ => false) &&
    I.fields.all (·.onlyAtoms baseAtom)) = true := by decide

omit hA hK in
theorem reads_base : (List.range 4).all (fun j => (addrs.getD j zero).onlyAtoms baseAtom &&
    (fld (2 * j)).onlyAtoms baseAtom && (fld (2 * j + 1)).onlyAtoms baseAtom) = true := by decide

/-- **A composed CPU `mem` message is a base one**, in count and tuple. -/
theorem cpuC_memSend {i : Nat} (hi : i < K) {I : Inter} (hI : I ∈ cpuIntersC) (hbus : I.bus = "mem") :
    ∃ I0 ∈ cpuInters, I0.count.eval ((cpuTable A (rowP row e n) K).env i) =
        I.count.eval ((cpuTableC A row e n roots K).env i) ∧
      I0.fields.map (fun c => c.eval ((cpuTable A (rowP row e n) K).env i)) =
        I.fields.map (fun c => c.eval ((cpuTableC A row e n roots K).env i)) := by
  have hk := cpuC_kind hA hK (roots := roots) hi
  have hS := shape (valid_rowP hA hK hi)
  have hk0 := cpu_kind (M := A) (row := rowP row e n) (k := K) hi hS
  obtain ⟨hfC, _, hAppC, hSC, _⟩ := kind_factsC hi hk
  obtain ⟨hfB, _, hAppB, hSB, _⟩ := kind_facts hi hk0
  have cong := fun (c : E) (h : c.onlyAtoms baseAtom = true) =>
    (E.eval_congr (cpuC_env_base hA hK (roots := roots) hi) c h).symm
  have hkk : ∀ m, m = 0 ∨ m = 3 → (kindCf A row e n i = m ↔ kindOf A (rowP row e n i) = m) := by
    intro m hm
    unfold kindCf
    cases hr : isRestart e n i with
    | true => rw [if_pos rfl, restart_kindOf hA hK hr]; rcases hm with rfl | rfl <;> decide
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
  have rb := List.all_eq_true.1 reads_base
  have wb := List.all_eq_true.1 writes_base
  change I ∈ [readInterC 0, readInterC 1, readInterC 2, readInterC 3] ++ writeInters ++ _ at hI
  simp only [List.mem_append] at hI
  rcases hI with (hr | hw) | ho
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain ⟨j, hj, hIj⟩ : ∃ j, j < 4 ∧ I = readInterC j := by
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨0, by decide, rfl⟩
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩
    subst hIj
    have hr := rb j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at hr
    refine ⟨readInter j, by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [cpuInters, List.mem_append, List.mem_cons, true_or, or_true], ?_, ?_⟩
    · show (acts.getD j zero).eval _ = (acts.getD j zero).eval _
      rw [(hfB j hj).1, (hfC j hj).1, actOfC_kindCf hA hK hi]
    · simp only [readInter, readInterC, List.map_cons, List.map_nil]
      rw [(hfB j hj).2, (hfC j hj).2, tagOfC_kindCf hA hK hi, cong _ hr.1.1, cong _ hr.1.2, cong _ hr.2]
  · refine ⟨I, List.mem_append_right _ hw, ?_, ?_⟩
    · simp only [writeInters, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · show sApp.eval _ = sApp.eval _
        rw [hAppB, hAppC]
        by_cases h0 : kindOf A (rowP row e n i) = 0
        · rw [if_pos h0, if_pos ((hkk 0 (.inl rfl)).2 h0)]
        · rw [if_neg h0, if_neg (fun h => h0 ((hkk 0 (.inl rfl)).1 h))]
      all_goals
        show sS.eval _ = sS.eval _
        rw [hSB, hSC]
        by_cases h0 : kindOf A (rowP row e n i) = 3
        · rw [if_pos h0, if_pos ((hkk 3 (.inr rfl)).2 h0)]
        · rw [if_neg h0, if_neg (fun h => h0 ((hkk 3 (.inr rfl)).1 h))]
    · have hf := wb I hw
      simp only [Bool.and_eq_true, List.all_eq_true] at hf
      apply List.map_congr_left
      intro c hc
      exact cong c (hf.2 c hc)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> exact absurd hbus (by decide)

include hb in
/-- **The honest composed CPU table satisfies the composed CPU AIR.** -/
theorem cpuC_sat : Sat (cpuAirC (roots.getD 0 0) nilA m0.heap.length n nilA) (cpuTableC A row e n roots K) := by
  have hn := hA.npos
  refine ⟨show 0 < K by omega, fun c hc i (hi : i < K) => ?_⟩
  have hk := cpuC_kind hA hK (roots := roots) hi
  have cv := cpuC_col hA hK (roots := roots) hi
  obtain ⟨_, hhalt, _, _, hHK1, _, nh, ns, nc⟩ := kind_factsC hi hk
  have hk12 := hk.1
  simp only [cpuAirC, cpuConsC, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil,
    or_false] at hc
  rcases hc with (((((((⟨j, hj, rfl⟩ | rfl) | rfl) | hc) | hc) | hc) | hc) | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · -- a kind selector is a bit
    simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
    rw [show cpuColC A row e n roots i (SEL + j) = _ from hk.2.1 j hj]
    split <;> decide
  · -- the restart selector is a bit
    simp only [B.bool, sRS, E.eval, cv, B.one, B.c, ofN_one]
    rw [show cpuColC A row e n roots i RS = _ from hk.2.2]
    split <;> decide
  · -- they sum to one
    have := kind_evalC hi hk (List.all_eq_true.1 kindSumC_all _ (List.mem_range.2 hk12))
    simp only [B.eq, E.eval]
    rw [this]; exact sub_self' _
  · exact cpuC_read hA hK hb hi (by decide) _ hc
  · exact cpuC_read hA hK hb hi (by decide) _ hc
  · exact cpuC_read hA hK hb hi (by decide) _ hc
  · exact cpuC_read hA hK hb hi (by decide) _ hc
  · show (col (SEL + 11)).eval _ = 0
    rw [cv, show cpuColC A row e n roots i (SEL + 11) = _ from hk.2.1 11 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · show (col (SEL + 12)).eval _ = 0
    rw [cv, show cpuColC A row e n roots i (SEL + 12) = _ from hk.2.1 12 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · show (col (SEL + 13)).eval _ = 0
    rw [cv, show cpuColC A row e n roots i (SEL + 13) = _ from hk.2.1 13 (by decide),
      if_neg (fun h => by have := h.1; have := h.2; omega)]
  · -- the counter starts at 0
    simp only [B.whenFirst, E.eval, env_first]
    split
    · next h0 => subst h0; rw [cv, cpuColC_cnt]; exact mul_zero' _
    · exact zero_mul' _
  · -- it counts the restarts
    simp only [B.whenTrans, B.eq, B.nxt, sRS, E.eval, env_trans, env_main1]
    split
    · exact zero_mul' _
    · next hne =>
      have hi1 : i + 1 < K := by have : ¬ (i + 1 = K) := hne; omega
      show 1 * ((cpuTableC A row e n roots K).main ((i + 1) % K) CNT - (_ + _)) = 0
      rw [Nat.mod_eq_of_lt hi1, one_mul', cv, cv]
      show cpuColC A row e n roots (i + 1) CNT - (cpuColC A row e n roots i CNT + cpuColC A row e n roots i RS) = 0
      rw [cpuColC_cnt, cpuColC_cnt, cpuColC_rs, ← ofN_add]
      exact sub_self' _
  · -- and ends at `n - 1`
    simp only [B.whenLast, B.eq, B.c, E.eval, env_last]
    split
    · next hl =>
      have hl' : i + 1 = K := hl
      rw [cv, cpuColC_cnt, cntS_after hA.emono hn (by omega)]
      rw [sub_self', mul_zero']
    · exact zero_mul' _
  · exact cpuC_transC hA hK hb hi (.inl rfl)
  · exact cpuC_transC hA hK hb hi (.inr (.inl rfl))
  · exact cpuC_transC hA hK hb hi (.inr (.inr rfl))
  · exact cpuC_first hA hK hi (.inl rfl)
  · exact cpuC_first hA hK hi (.inr (.inl rfl))
  · exact cpuC_first hA hK hi (.inr (.inr rfl))
  · simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      rw [hhalt, last_kindCf hA hK (i := i) hl]
      show 1 * (ofN 1 - ofN 1) = 0; rw [sub_self', mul_zero']
    · exact zero_mul' _
  · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
    rw [cpuColC_blind _ (.inl rfl), zero_mul']
  · simp only [B.bool, E.eval, cv, B.one, B.c, ofN_one]
    rw [cpuColC_blind _ (.inr rfl), zero_mul']
  · simp only [B.whenLast, B.eq, E.eval, env_last]
    split
    · next hl =>
      rw [hHK1, last_kindCf hA hK (i := i) hl]
      show 1 * (ofN 1 - ofN 1) = 0; rw [sub_self', mul_zero']
    · exact zero_mul' _

end

end Circuit
