import Ski.Witness
import Ski.Statement
import Ski.Compose
import Ski.AirProbe

set_option linter.unusedSectionVars false

open Term

/-!
# The circuit's statement for a composed proof: several evaluations

`Ski/Compose.lean` compiles a composed formula to an evaluation statement,
`Compose.EvalRel`: public terms `P₀ … Pₙ₋₁` and a shape of bits, and the
relation that literal bits `β` of that shape and a hidden term `w` make
every `Pⱼ ⬝ β ⬝ w` evaluate to `K`.  This module is that statement as a
machine the AIR runs, one segment per term.

**The composed machine** (`cMachine ρ shp region Ps`) has four parts:

- the **slots** of `Ski/Statement.lean`: `K`, `I`, `K I` at 0, 1, 2, then
  one cell per bit, `K` or `K I` (`slotHeap`);
- the **witness region**, `W` cells after them, private; each cell is `S`,
  `K`, `I` or an application of two cells below it, so the region reads
  back as a closed term at its last cell (`Wit.wf_termAt`);
- the **bits' encoding**, public: the Scott pairs of the shape, with each
  leaf a pointer to its bit's slot, so they read back as `β.enc`;
- for each term `Pⱼ`, its cells and `Pⱼ ⬝ β ⬝ w`, whose address is the
  segment's **root**; then a nil, the empty stack.

**The AIR** (`AcceptsC`): segment `j` starts at its root with the empty
stack, runs by machine transitions (or has halted and repeats), and ends
at row `e j` with `K` at the head over the empty stack.  The row after an
end is the next segment's start: its root, the nil, the same counter.
The last row ends the last segment.

**The theorems.**
- `cMachine_decode`: each root reads back as `Pⱼ ⬝ β.enc ⬝ w`.
- `composed_sound`: a table the AIR accepts from the composed machine
  proves `Compose.EvalRel` for its bits and witness.
- `cMachine_public`: machines for any bits and any region of the same
  sizes differ only in the bit cells and the region, so the machine with
  those cells blank states it for every witness.
- `checkC_sound` and, for a formula, `checkC_realizes`: a table the
  checker accepts proves the formula's statement, so by
  `Compose.real_of_accepted` its bits and witness read back as a realizer.
-/

namespace CompM

open Mach Stmt Compose Wit BExpr

-- ---------------------------------------------------------------------------
-- The bits' encoding
-- ---------------------------------------------------------------------------

/-- The number of leaves of a shape. -/
def BT.nleaves : BT → Nat
  | .leaf _ => 1
  | .node l r => BT.nleaves l + BT.nleaves r

/-- A Scott pair, as an open term. -/
def pairO (a b : OTerm) : OTerm := .S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ a)) ⬝ₒ (.K ⬝ₒ b)

/-- The encoding of a shape's bits, leaf `i` the slot variable `i + 2`,
    leaves numbered from `off` depth first. -/
def encO : BT → Nat → OTerm
  | .leaf _, off => .var (off + 2)
  | .node l r, off => pairO (encO l off) (encO r (off + BT.nleaves l))

/-- The bits of a shape, leaf `i` set when `ρ i` holds. -/
def fillB : BT → (Nat → Bool) → Nat → BT
  | .leaf _, ρ, off => .leaf (ρ off)
  | .node l r, ρ, off => .node (fillB l ρ off) (fillB r ρ (off + BT.nleaves l))

theorem sbool_boolT (b : Bool) : sbool b = (boolT b).toO := by cases b <;> rfl

/-- **The encoding, filled, is the bits' encoding.** -/
theorem encO_fill (ρ : Nat → Bool) (N : Nat) : ∀ (shp : BT) (off : Nat),
    off + BT.nleaves shp ≤ N →
    (encO shp off).subst (meaning ρ (N + 2)) = (fillB shp ρ off).enc.toO
  | .leaf _, off, h => by
    simp only [BT.nleaves] at h
    show meaning ρ (N + 2) (off + 2) = _
    unfold meaning
    rw [if_pos (by omega)]
    show sbool (ρ off) = _
    rw [sbool_boolT]
    rfl
  | .node l r, off, h => by
    simp only [BT.nleaves] at h
    show (pairO (encO l off) (encO r (off + BT.nleaves l))).subst _ = (pairT _ _).toO
    unfold pairO
    simp only [OTerm.subst]
    rw [encO_fill ρ N l off (by omega), encO_fill ρ N r (off + BT.nleaves l) (by omega)]
    rfl

/-- The bits of a shape have that shape. -/
def SameShape : BT → BT → Prop
  | .leaf _, .leaf _ => True
  | .node l r, .node l' r' => SameShape l l' ∧ SameShape r r'
  | _, _ => False

theorem fillB_shape : ∀ (shp : BT) (ρ : Nat → Bool) (off : Nat), SameShape shp (fillB shp ρ off)
  | .leaf _, _, _ => trivial
  | .node l r, ρ, off => ⟨fillB_shape l ρ off, fillB_shape r ρ _⟩

-- ---------------------------------------------------------------------------
-- The statements' cells
-- ---------------------------------------------------------------------------

/-- For each term `P`, its cells, then `P ⬝ enc` and `(P ⬝ enc) ⬝ w`, with
    `enc` and `w` at `pe` and `wr`.  Returns the heap and the roots. -/
def addStmts (pe wr : Nat) : List Cell → List Term → List Cell × List Nat
  | h, [] => (h, [])
  | h, P :: Ps =>
    let h2 := (build h P).1
    let pp := (build h P).2
    let h3 := h2 ++ [.app pp pe, .app h2.length wr]
    ((addStmts pe wr h3 Ps).1, (h2.length + 1) :: (addStmts pe wr h3 Ps).2)

theorem addStmts_spec (pe wr : Nat) (E Wt : OTerm) : ∀ (Ps : List Term) (h : List Cell),
    otermAt h (h.length + 1) pe = some E → otermAt h (h.length + 1) wr = some Wt →
    ∃ cs, (addStmts pe wr h Ps).1 = h ++ cs ∧ (addStmts pe wr h Ps).2.length = Ps.length ∧
      ∀ j (P : Term), Ps[j]? = some P →
        otermAt (addStmts pe wr h Ps).1 ((addStmts pe wr h Ps).1.length + 1)
          ((addStmts pe wr h Ps).2.getD j 0) = some (P.toO ⬝ₒ E ⬝ₒ Wt)
  | [], h, _, _ => ⟨[], by simp [addStmts], rfl, fun j P hP => by simp at hP⟩
  | P :: Ps, h, hE, hW => by
    obtain ⟨c1, e1, lp, tp⟩ := build_spec P h
    have hl2 : (build h P).1.length = h.length + c1.length := by rw [e1]; simp
    let h3 := (build h P).1 ++ [Cell.app (build h P).2 pe, Cell.app (build h P).1.length wr]
    have hl3 : h3.length = (build h P).1.length + 2 := by simp [h3]
    -- The two new cells read back.
    have hEg : ∀ F, h.length + 1 ≤ F → otermAt h3 F pe = some E := fun F hF => by
      have : h3 = h ++ (c1 ++ [Cell.app (build h P).2 pe, Cell.app (build h P).1.length wr]) := by
        simp [h3, e1]
      rw [this]
      exact otermAt_grow hE hF
    have hWg : ∀ F, h.length + 1 ≤ F → otermAt h3 F wr = some Wt := fun F hF => by
      have : h3 = h ++ (c1 ++ [Cell.app (build h P).2 pe, Cell.app (build h P).1.length wr]) := by
        simp [h3, e1]
      rw [this]
      exact otermAt_grow hW hF
    have hPg : ∀ F, (build h P).2 + 1 ≤ F → otermAt h3 F (build h P).2 = some P.toO := fun F hF =>
      otermAt_grow (otermAt_of_termAt tp) hF
    have h1 : h3[(build h P).1.length]? = some (Cell.app (build h P).2 pe) := by
      simp [h3]
    have h2 : h3[(build h P).1.length + 1]? = some (Cell.app (build h P).1.length wr) := by
      simp [h3]
    have r1 : ∀ F, (build h P).1.length + 1 ≤ F →
        otermAt h3 (F + 1) (build h P).1.length = some (P.toO ⬝ₒ E) := fun F hF => by
      unfold otermAt
      rw [h1]
      dsimp only
      rw [hPg F (by omega), hEg F (by omega)]
    have r2 : ∀ F, (build h P).1.length + 1 ≤ F →
        otermAt h3 (F + 2) ((build h P).1.length + 1) = some (P.toO ⬝ₒ E ⬝ₒ Wt) := fun F hF => by
      unfold otermAt
      rw [h2]
      dsimp only
      rw [r1 F hF, hWg (F + 1) (by omega)]
    obtain ⟨cs, e, hlen, hj⟩ := addStmts_spec pe wr E Wt Ps h3
      (hEg _ (by omega)) (hWg _ (by omega))
    refine ⟨c1 ++ [Cell.app (build h P).2 pe, Cell.app (build h P).1.length wr] ++ cs, ?_, ?_, ?_⟩
    · show (addStmts pe wr h3 Ps).1 = _
      rw [e]; simp [h3, e1]
    · show (((build h P).1.length + 1) :: (addStmts pe wr h3 Ps).2).length = _
      simp [hlen]
    · intro j Q hQ
      cases j with
      | zero =>
        simp at hQ
        subst hQ
        show otermAt (addStmts pe wr h3 Ps).1 _ ((build h P).1.length + 1) = _
        rw [e]
        refine otermAt_grow (cs := cs) (r2 ((build h P).1.length + 1) (Nat.le_refl _)) ?_
        show _ ≤ (addStmts pe wr h3 Ps).1.length + 1
        rw [e, List.length_append, hl3]; omega
      | succ j =>
        simp at hQ
        exact hj j Q hQ

-- ---------------------------------------------------------------------------
-- The composed machine
-- ---------------------------------------------------------------------------

/-- The composed machine's heap before its nil, and its roots. -/
def cHeap (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) : List Cell × List Nat :=
  let h0 := slotHeap ρ (BT.nleaves shp) ++ region
  let e1 := pbuild (BT.nleaves shp + 2) h0 (encO shp 0)
  addStmts e1.2 (h0.length - 1) e1.1 Ps

/-- **The composed machine**: the heap, a nil, and the first segment's root
    over the empty stack. -/
def cMachine (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Ps : List Term) : Mach :=
  ⟨(cHeap ρ shp region Ps).1 ++ [.nil], (cHeap ρ shp region Ps).2.getD 0 0,
    (cHeap ρ shp region Ps).1.length⟩

/-- The slots and the region form a well-formed prefix. -/
theorem slots_wf (ρ : Nat → Bool) (N : Nat) {region : List Cell}
    (hr : ∀ i c, region[i]? = some c → cellOK (N + 3 + i) c = true) :
    WF (slotHeap ρ N ++ region) := by
  intro i c hc
  by_cases hi : i < N + 3
  · rw [List.getElem?_append_left (by rw [slotHeap_length]; exact hi)] at hc
    unfold slotHeap at hc
    by_cases h3 : i < 3
    · rw [List.getElem?_append_left (by simp; exact h3)] at hc
      match i, h3 with
      | 0, _ => simp at hc; subst hc; rfl
      | 1, _ => simp at hc; subst hc; rfl
      | 2, _ => simp at hc; subst hc; rfl
    · rw [List.getElem?_append_right (by simp; omega)] at hc
      simp only [List.length_cons, List.length_nil, List.getElem?_map, List.getElem?_range
        (show i - 3 < N by omega), Option.map_some, Option.some.injEq] at hc
      subst hc
      cases ρ (i - 3) with
      | true => rfl
      | false =>
        show (decide (0 < i) && decide (1 < i)) = true
        rw [decide_eq_true (show 0 < i by omega), decide_eq_true (show 1 < i by omega)]
        rfl
  · rw [List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length] at hc
    have := hr (i - (N + 3)) c hc
    rwa [show N + 3 + (i - (N + 3)) = i by omega] at this

/-- The witness a composed machine's region holds: the term at the region's
    last cell. -/
def cWitness (ρ : Nat → Bool) (N : Nat) (region : List Cell) : Option Term :=
  witnessOf (slotHeap ρ N ++ region)

/-- **Each root reads back as its term applied to the bits and the
    witness.** -/
theorem cMachine_decode {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Ps : List Term}
    {w : Term} (hw : cWitness ρ (BT.nleaves shp) region = some w) :
    (cHeap ρ shp region Ps).2.length = Ps.length ∧
    ∀ j P, Ps[j]? = some P →
      otermAt (cMachine ρ shp region Ps).heap ((cMachine ρ shp region Ps).heap.length + 1)
        ((cHeap ρ shp region Ps).2.getD j 0) =
        some (P.toO ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  have hW : otermAt h0 (h0.length + 1) (h0.length - 1) = some w.toO := by
    have := otermAt_of_termAt (heap := h0) hw
    exact otermAt_mono this (Nat.le_succ _)
  have henv : ∀ x, Occ x (encO shp 0) → x < N + 2 →
      otermAt h0 (h0.length + 1) (slotPtr x) = some (slotVal ρ x) := by
    intro x _ hx
    exact otermAt_grow (cs := region) (k := h0.length + 1) (slot_reads ρ N x hx)
      (by simp [h0, slotHeap_length])
  obtain ⟨cs1, e1, t1⟩ := pbuild_spec ρ (N + 2) (encO shp 0) h0 henv
  rw [encO_fill ρ N shp 0 (by simp [N])] at t1
  have hW1 : otermAt (pbuild (N + 2) h0 (encO shp 0)).1
      ((pbuild (N + 2) h0 (encO shp 0)).1.length + 1) (h0.length - 1) = some w.toO := by
    rw [e1]; exact otermAt_grow hW (by simp)
  obtain ⟨cs, e, hlen, hj⟩ := addStmts_spec (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1)
    _ _ Ps (pbuild (N + 2) h0 (encO shp 0)).1 t1 hW1
  refine ⟨hlen, fun j P hP => ?_⟩
  have := hj j P hP
  show otermAt ((cHeap ρ shp region Ps).1 ++ [Cell.nil]) _ _ = _
  refine otermAt_grow this ?_
  show _ ≤ ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).length + 1
  simp only [List.length_append, List.length_singleton]
  show _ ≤ (addStmts (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1)
    (pbuild (N + 2) h0 (encO shp 0)).1 Ps).1.length + 1 + 1
  omega

-- ---------------------------------------------------------------------------
-- The AIR with segments
-- ---------------------------------------------------------------------------

/-- **The AIR with evaluation segments accepts** a table over `M` from
    `m0`: `n` segments, segment `j` ending at row `e j` with `K` at the head
    over the empty stack; the row after an end is the next segment's start,
    its root over the nil `nilA`; every other row steps or has halted and
    repeats; the last row, `e (n - 1)`, ends the last segment. -/
structure AcceptsC (M : List Cell) (m0 : Mach) (roots : List Nat) (nilA n : Nat)
    (e : Nat → Nat) (row : Nat → Air.Row) : Prop where
  npos : 0 < n
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = roots.getD 0 0
  stk0 : (row 0).stk = nilA
  ctr0 : (row 0).ctr = m0.heap.length
  emono : ∀ j, j + 1 < n → e j < e (j + 1)
  restart : ∀ j, j + 1 < n → row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩
  trans : ∀ i, i < e (n - 1) → (∀ j, j + 1 < n → i ≠ e j) →
    Air.stepRow M (row i) = some (row (i + 1)) ∨
      (Air.haltRow M (row i) = true ∧ row (i + 1) = row i)
  ends : ∀ j, j < n → Air.rd M (row (e j)).ctr (row (e j)).hd = some .K ∧
    Air.rd M (row (e j)).ctr (row (e j)).stk = some .nil

/-- Segment `j`'s first row. -/
def segStart (e : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => e j + 1

theorem emono_le {e : Nat → Nat} {n : Nat} (h : ∀ j, j + 1 < n → e j < e (j + 1)) :
    ∀ {a b : Nat}, a ≤ b → b < n → e a ≤ e b := by
  intro a b hab hb
  induction b with
  | zero => rw [Nat.le_zero.1 hab]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with hl | hl
    · exact Nat.le_trans (ih (by omega) (by omega)) (Nat.le_of_lt (h b (by omega)))
    · rw [hl]; exact Nat.le_refl _

theorem segStart_le {e : Nat → Nat} {n : Nat} (h : ∀ j, j + 1 < n → e j < e (j + 1)) :
    ∀ j, j < n → segStart e j ≤ e j
  | 0, _ => Nat.zero_le _
  | j + 1, hj => h j hj

/-- A row inside segment `j` and not its end is no restart. -/
theorem not_end {e : Nat → Nat} {n j i : Nat} (h : ∀ j, j + 1 < n → e j < e (j + 1)) (hj : j < n)
    (h1 : segStart e j ≤ i) (h2 : i < e j) : ∀ j', j' + 1 < n → i ≠ e j' := by
  intro j' hj' hi
  subst hi
  rcases Nat.lt_or_ge j' j with hlt | hge
  · cases j with
    | zero => omega
    | succ j =>
      have := emono_le h (show j' ≤ j by omega) (by omega)
      simp only [segStart] at h1
      omega
  · have := emono_le h hge (by omega)
    omega

/-- K over the empty stack is halted. -/
theorem halt_K {M : List Cell} {r : Air.Row} (hk : Air.rd M r.ctr r.hd = some .K)
    (hn : Air.rd M r.ctr r.stk = some .nil) : Air.haltRow M r = true := by
  unfold Air.haltRow
  rw [hk]
  simp [Air.short, hn]

/-- **Segment `j` is a run of the AIR** from its first row. -/
theorem AcceptsC.segment {M : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat}
    {e : Nat → Nat} {row : Nat → Air.Row} (h : AcceptsC M m0 roots nilA n e row) {j : Nat}
    (hj : j < n) (hc : (row (segStart e j)).ctr ≤ M.length) :
    Air.AcceptsFrom M (Air.st M (row (segStart e j))) (e j - segStart e j + 1)
      (fun i => row (segStart e j + i)) := by
  have hs := segStart_le h.emono j hj
  have hen : e j ≤ e (n - 1) := emono_le h.emono (by omega) (by omega)
  refine ⟨by omega, by simp [Air.st], by simp [Air.st], by simp [Air.st], ?_, ?_, ?_⟩
  · simp [Air.st, Air.take_length hc]
  · intro i hi
    have hi' : segStart e j + i < e j := by omega
    rw [show segStart e j + (i + 1) = segStart e j + i + 1 by omega]
    exact h.trans _ (by omega) (not_end h.emono hj (by omega) hi')
  · rw [show segStart e j + (e j - segStart e j + 1 - 1) = e j by omega]
    exact halt_K (h.ends j hj).1 (h.ends j hj).2

theorem msteps_len {m m' : Mach} (h : MSteps m m') : m.heap.length ≤ m'.heap.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hm _ ih =>
    obtain ⟨cs, e⟩ := mstep_append hm
    rw [e] at ih
    simp at ih
    omega

/-- **Every segment runs**: its first row's counter lies between the
    machine's and the table's length, and its first row reaches its last by
    machine transitions. -/
theorem AcceptsC.runs {M : List Cell} {m0 : Mach} {roots : List Nat} {nilA n : Nat}
    {e : Nat → Nat} {row : Nat → Air.Row} (h : AcceptsC M m0 roots nilA n e row) :
    ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length ∧
      m0.heap.length ≤ (row (segStart e j)).ctr ∧ (row (e j)).ctr ≤ M.length ∧
      (row (segStart e j)).ctr ≤ (row (e j)).ctr ∧
      MSteps (Air.st M (row (segStart e j))) (Air.st M (row (e j))) := by
  have hc0 : (row 0).ctr ≤ M.length := by
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  -- One segment, from a first row in range.
  have seg : ∀ j, j < n → (row (segStart e j)).ctr ≤ M.length →
      (row (e j)).ctr ≤ M.length ∧ (row (segStart e j)).ctr ≤ (row (e j)).ctr ∧
      MSteps (Air.st M (row (segStart e j))) (Air.st M (row (e j))) := by
    intro j hj hc
    have hs := segStart_le h.emono j hj
    have ha := h.segment hj hc
    obtain ⟨hce, hr⟩ := ha.reach (e j - segStart e j) (by omega)
    rw [show segStart e j + (e j - segStart e j) = e j by omega] at hce hr
    have hl := msteps_len hr
    simp only [Air.st, List.length_take] at hl
    exact ⟨hce, by omega, hr⟩
  intro j
  induction j with
  | zero =>
    intro hn
    obtain ⟨a, b, c⟩ := seg 0 hn hc0
    exact ⟨hc0, by rw [show segStart e 0 = 0 from rfl, h.ctr0]; exact Nat.le_refl _, a, b, c⟩
  | succ j ih =>
    intro hn
    obtain ⟨_, hm, he, hse, _⟩ := ih (by omega)
    have hr := h.restart j hn
    have hc : (row (segStart e (j + 1))).ctr = (row (e j)).ctr := by
      show (row (e j + 1)).ctr = _
      rw [hr]
    obtain ⟨a, b, c⟩ := seg (j + 1) hn (by rw [hc]; exact he)
    exact ⟨by rw [hc]; exact he, by rw [hc]; omega, a, b, c⟩

/-- **A table the AIR accepts from the composed machine proves the
    composed statement**: with a well-formed region, its bits and the
    region's witness make every term evaluate to `K`. -/
theorem composed_sound {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Ps : List Term}
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsC M (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row) :
    ∃ w, cWitness ρ (BT.nleaves shp) region = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp ρ 0) w := by
  let N := BT.nleaves shp
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  refine ⟨w, hw, fillB_shape shp ρ 0, fun P hP => ?_⟩
  obtain ⟨j, hj, hPj⟩ := List.getElem_of_mem hP
  have hj' : Ps[j]? = some P := by rw [List.getElem?_eq_getElem hj, hPj]
  obtain ⟨_, hdec⟩ := cMachine_decode (Ps := Ps) hw
  have hroot := hdec j P hj'
  obtain ⟨hc, hm, _, _, hrun⟩ := h.runs j hj
  let m0 := cMachine ρ shp region Ps
  -- The segment's first row: the root over the nil.
  have hregs : (row (segStart e j)).hd = (cHeap ρ shp region Ps).2.getD j 0 ∧
      (row (segStart e j)).stk = (cHeap ρ shp region Ps).1.length := by
    cases j with
    | zero => exact ⟨h.hd0, h.stk0⟩
    | succ j =>
      have := h.restart j hj
      show (row (e j + 1)).hd = _ ∧ (row (e j + 1)).stk = _
      rw [this]
      exact ⟨rfl, rfl⟩
  have hm0 : m0.heap = M.take (row 0).ctr := h.heap0.symm
  have hc0 : (row 0).ctr = m0.heap.length := h.ctr0
  have hle : (row 0).ctr ≤ (row (segStart e j)).ctr := by rw [hc0]; exact hm
  have hlen : (Air.st M (row (segStart e j))).heap.length = (row (segStart e j)).ctr := by
    simp [Air.st, Air.take_length hc]
  have hstart : odecode (Air.st M (row (segStart e j))) = some (P ⬝ (fillB shp ρ 0).enc ⬝ w).toO := by
    have e1 : (P ⬝ (fillB shp ρ 0).enc ⬝ w).toO = appL (P.toO ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
    rw [e1]
    apply odecode_of
    · show otermAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).hd = _
      rw [hregs.1]
      rw [hm0] at hroot
      refine Air.otermAt_take hle ?_ hroot
      rw [← hm0, hlen]
      show m0.heap.length + 1 ≤ _
      omega
    · show ostackAt (M.take (row (segStart e j)).ctr) (_ + 1) (row (segStart e j)).stk = _
      rw [hregs.2]
      have hn : (M.take (row (segStart e j)).ctr)[(cHeap ρ shp region Ps).1.length]? = some .nil := by
        have h1 : m0.heap[(cHeap ρ shp region Ps).1.length]? = some .nil := by simp [m0, cMachine]
        rw [hm0, List.getElem?_take] at h1
        rw [List.getElem?_take]
        split at h1
        · rw [if_pos (by omega)]; exact h1
        · cases h1
      unfold ostackAt
      rw [hn]
  obtain ⟨v, hv, hsteps⟩ := omachine_run hstart hrun
  have hK : v = .K := by
    refine odecode_K hv ?_ ?_
    · rw [← (h.ends j hj).1, Air.rd_eq]; rfl
    · rw [← (h.ends j hj).2, Air.rd_eq]; rfl
  rw [hK] at hsteps
  have := hsteps.close (fun _ => K)
  rw [close_toO] at this
  exact ⟨this, .K⟩

-- ---------------------------------------------------------------------------
-- The public part
-- ---------------------------------------------------------------------------

theorem addStmts_shape (pe wr : Nat) : ∀ (Ps : List Term) (h h' : List Cell), h.length = h'.length →
    ∃ cs, (addStmts pe wr h Ps).1 = h ++ cs ∧ (addStmts pe wr h' Ps).1 = h' ++ cs ∧
      (addStmts pe wr h Ps).2 = (addStmts pe wr h' Ps).2
  | [], h, h', _ => ⟨[], by simp [addStmts], by simp [addStmts], rfl⟩
  | P :: Ps, h, h', hl => by
    obtain ⟨c1, p1, e1, e1'⟩ := build_shape P h h' hl
    have hl3 : (h ++ c1 ++ [Cell.app p1 pe, Cell.app (h ++ c1).length wr]).length =
        (h' ++ c1 ++ [Cell.app p1 pe, Cell.app (h' ++ c1).length wr]).length := by simp [hl]
    obtain ⟨cs, e2, e2', e3⟩ := addStmts_shape pe wr Ps _ _ hl3
    have u : addStmts pe wr h (P :: Ps) =
        ((addStmts pe wr (h ++ c1 ++ [Cell.app p1 pe, Cell.app (h ++ c1).length wr]) Ps).1,
          ((h ++ c1).length + 1) ::
            (addStmts pe wr (h ++ c1 ++ [Cell.app p1 pe, Cell.app (h ++ c1).length wr]) Ps).2) := by
      simp only [addStmts, e1]
    have u' : addStmts pe wr h' (P :: Ps) =
        ((addStmts pe wr (h' ++ c1 ++ [Cell.app p1 pe, Cell.app (h' ++ c1).length wr]) Ps).1,
          ((h' ++ c1).length + 1) ::
            (addStmts pe wr (h' ++ c1 ++ [Cell.app p1 pe, Cell.app (h' ++ c1).length wr]) Ps).2) := by
      simp only [addStmts, e1']
    rw [u, u']
    refine ⟨c1 ++ [Cell.app p1 pe, Cell.app (h ++ c1).length wr] ++ cs, ?_, ?_, ?_⟩
    · rw [e2]; simp
    · rw [e2']; simp [hl]
    · rw [e3]; simp [hl]

theorem getElem_agree {a a' l : List Cell} {i : Nat} (hl : a.length = a'.length)
    (h : i < a.length → a[i]? = a'[i]?) : (a ++ l)[i]? = (a' ++ l)[i]? := by
  by_cases hi : i < a.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (by omega)]; exact h hi
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]

/-- **The composed machine's public part.**  Bits and regions of the same
    sizes give machines with the same registers, heap length and roots,
    whose heaps begin with the slots of their bits and their region, and
    agree outside the bit cells and the region (addresses `3` to
    `N + 2 + W`).  So the machine with those cells blank states the machine
    for every witness of that size: what the verifier holds.  The converse
    is not claimed: an arbitrary fill of the blanks is a composed machine
    only when the bit cells are `K` or `K I` and the region's cells are
    well formed, which `checkC` checks and the circuit's witness table
    enforces. -/
theorem cMachine_public (ρ ρ' : Nat → Bool) (shp : BT) (region region' : List Cell) (Ps : List Term)
    (hl : region.length = region'.length) :
    (cMachine ρ shp region Ps).hd = (cMachine ρ' shp region' Ps).hd ∧
    (cMachine ρ shp region Ps).stk = (cMachine ρ' shp region' Ps).stk ∧
    (cHeap ρ shp region Ps).2 = (cHeap ρ' shp region' Ps).2 ∧
    (cMachine ρ shp region Ps).heap.length = (cMachine ρ' shp region' Ps).heap.length ∧
    (cMachine ρ shp region Ps).heap.take (BT.nleaves shp + 3 + region.length) =
      slotHeap ρ (BT.nleaves shp) ++ region ∧
    ∀ i, (i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i) →
      (cMachine ρ shp region Ps).heap[i]? = (cMachine ρ' shp region' Ps).heap[i]? := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  let h0' := slotHeap ρ' N ++ region'
  have h0l : h0.length = h0'.length := by simp [h0, h0', slotHeap_length, hl]
  obtain ⟨c1, p1, e1, e1'⟩ := pbuild_shape (N + 2) (encO shp 0) h0 h0' h0l
  have h1l : (h0 ++ c1).length = (h0' ++ c1).length := by simp [h0l]
  obtain ⟨cs, e2, e2', e3⟩ := addStmts_shape p1 (h0.length - 1) Ps _ _ h1l
  have hH : cHeap ρ shp region Ps = addStmts p1 (h0.length - 1) (h0 ++ c1) Ps := by
    show addStmts (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) (pbuild (N + 2) h0 (encO shp 0)).1 Ps = _
    rw [e1]
  have hH' : cHeap ρ' shp region' Ps = addStmts p1 (h0.length - 1) (h0' ++ c1) Ps := by
    show addStmts (pbuild (N + 2) h0' (encO shp 0)).2 (h0'.length - 1) (pbuild (N + 2) h0' (encO shp 0)).1 Ps = _
    rw [e1', h0l]
  have hA : (cHeap ρ shp region Ps).1 = h0 ++ (c1 ++ cs) := by rw [hH, e2]; simp
  have hA' : (cHeap ρ' shp region' Ps).1 = h0' ++ (c1 ++ cs) := by rw [hH', e2']; simp
  have hR : (cHeap ρ shp region Ps).2 = (cHeap ρ' shp region' Ps).2 := by rw [hH, hH', e3]
  have hlen : h0.length = N + 3 + region.length := by simp [h0, slotHeap_length]
  refine ⟨?_, ?_, hR, ?_, ?_, fun i hi => ?_⟩
  · show (cHeap ρ shp region Ps).2.getD 0 0 = (cHeap ρ' shp region' Ps).2.getD 0 0
    rw [hR]
  · show (cHeap ρ shp region Ps).1.length = (cHeap ρ' shp region' Ps).1.length
    rw [hA, hA']; simp [h0l]
  · show ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).length = ((cHeap ρ' shp region' Ps).1 ++ [Cell.nil]).length
    rw [hA, hA']; simp [h0l]
  · show ((cHeap ρ shp region Ps).1 ++ [Cell.nil]).take _ = _
    rw [hA, List.append_assoc, ← hlen, List.take_left']
    rfl
  · show ((cHeap ρ shp region Ps).1 ++ [Cell.nil])[i]? = ((cHeap ρ' shp region' Ps).1 ++ [Cell.nil])[i]?
    have eL : (cHeap ρ shp region Ps).1 ++ [Cell.nil] = h0 ++ ((c1 ++ cs) ++ [Cell.nil]) := by
      rw [hA, List.append_assoc]
    have eL' : (cHeap ρ' shp region' Ps).1 ++ [Cell.nil] = h0' ++ ((c1 ++ cs) ++ [Cell.nil]) := by
      rw [hA', List.append_assoc]
    rw [eL, eL']
    refine getElem_agree h0l fun hi' => ?_
    rcases hi with hi | hi
    · show (slotHeap ρ N ++ region)[i]? = (slotHeap ρ' N ++ region')[i]?
      rw [List.getElem?_append_left (by rw [slotHeap_length]; omega),
        List.getElem?_append_left (by rw [slotHeap_length]; omega)]
      unfold slotHeap
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    · omega

-- ---------------------------------------------------------------------------
-- The checker, over arrays
-- ---------------------------------------------------------------------------

/-- The bits a table's memory sets: bit `n` when the cell at `n + 3` is `K`. -/
def bitsOf (A : Array Cell) (n : Nat) : Bool := A[n + 3]? == some .K

/-- The region a table's memory holds: `W` cells after the bits. -/
def regionOf (A : Array Cell) (N W : Nat) : List Cell := (A.toList.drop (N + 3)).take W

/-- **The composed table check**: the region is `W` well-formed cells; the
    table starts from the composed machine of the bits and region its
    memory holds; the segments' ends increase and each is followed by the
    next segment's start; every other row below the last end steps or has
    halted and repeats; and every end has `K` at the head over the nil. -/
def checkC (shp : BT) (W : Nat) (Ps : List Term) (A : Array Cell) (ends : Array Nat)
    (R : Array Air.Row) : Bool :=
  let N := BT.nleaves shp
  let region := regionOf A N W
  let m0 := cMachine (bitsOf A) shp region Ps
  let roots := (cHeap (bitsOf A) shp region Ps).2
  let nilA := (cHeap (bitsOf A) shp region Ps).1.length
  let n := Ps.length
  let g := fun a => A[a]?
  let row := fun i => R.getD i ⟨0, 0, 0⟩
  let e := fun j => ends.getD j 0
  decide (0 < n) && decide (region.length = W) &&
    (List.range W).all (fun i =>
      match region[i]? with
      | some c => cellOK (N + 3 + i) c
      | none => false) &&
    decide (A.toList.take (row 0).ctr = m0.heap) && decide ((row 0).hd = roots.getD 0 0) &&
    decide ((row 0).stk = nilA) && decide ((row 0).ctr = m0.heap.length) &&
    (List.range (n - 1)).all (fun j => decide (e j < e (j + 1)) &&
      decide (row (e j + 1) = ⟨roots.getD (j + 1) 0, nilA, (row (e j)).ctr⟩)) &&
    (List.range (e (n - 1))).all (fun i => (List.range (n - 1)).any (fun j => e j == i) ||
      decide (Air.stepRowG g (row i) = some (row (i + 1))) ||
      (Air.haltRowG g (row i) && decide (row (i + 1) = row i))) &&
    (List.range n).all (fun j => Air.rdG g (row (e j)).ctr (row (e j)).hd == some .K &&
      Air.rdG g (row (e j)).ctr (row (e j)).stk == some .nil)

/-- **`checkC` is sound**: a table it accepts proves the composed statement,
    for the bits its memory sets and the witness its region holds. -/
theorem checkC_sound {shp : BT} {W : Nat} {Ps : List Term} {A : Array Cell} {ends : Array Nat}
    {R : Array Air.Row} (h : checkC shp W Ps A ends R = true) :
    ∃ w, cWitness (bitsOf A) (BT.nleaves shp) (regionOf A (BT.nleaves shp) W) = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp (bitsOf A) 0) w := by
  unfold checkC at h
  dsimp only at h
  rw [Air.getElem?_fun] at h
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hW⟩, hwf⟩, h0⟩, h1⟩, h2⟩, h3⟩, hmono⟩, htr⟩, hends⟩ := h
  refine composed_sound (fun i c hc => ?_) (e := fun j => ends.getD j 0)
    (row := fun i => R.getD i ⟨0, 0, 0⟩) (M := A.toList) ⟨hn, h0, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · have hi : i < W := by
      rcases Nat.lt_or_ge i W with hl | hl
      · exact hl
      · rw [List.getElem?_eq_none (by rw [hW]; exact hl)] at hc; cases hc
    have := List.all_eq_true.1 hwf i (List.mem_range.2 hi)
    rw [hc] at this
    exact this
  · intro j hj
    have := List.all_eq_true.1 hmono j (List.mem_range.2 (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_iff] at this
    exact this.1
  · intro j hj
    have := List.all_eq_true.1 hmono j (List.mem_range.2 (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_iff] at this
    exact this.2
  · intro i hi hne
    have := List.all_eq_true.1 htr i (List.mem_range.2 hi)
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at this
    rcases this with (ha | hs) | hh
    · obtain ⟨j, hj, e⟩ := List.any_eq_true.1 ha
      rw [beq_iff_eq] at e
      exact absurd e.symm (hne j (by have := List.mem_range.1 hj; omega))
    · left; rw [Air.stepRow_G]; exact hs
    · right; exact ⟨by rw [Air.haltRow_G]; exact hh.1, hh.2⟩
  · intro j hj
    have := List.all_eq_true.1 hends j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨by rw [Air.rd_G]; exact this.1, by rw [Air.rd_G]; exact this.2⟩

-- ---------------------------------------------------------------------------
-- For a formula
-- ---------------------------------------------------------------------------

theorem shape_of_same : ∀ (M : MF) (β : BT), SameShape (clear M) β → Shape M β
  | .atom _ _, .leaf _, _ => trivial
  | .atom _ _, .node _ _, h => h.elim
  | .and A B, .node l r, h => ⟨shape_of_same A l h.1, shape_of_same B r h.2⟩
  | .and _ _, .leaf _, h => h.elim
  | .or A B, .node l r, h => ⟨shape_of_same A l h.1, shape_of_same B r h.2⟩
  | .or _ _, .leaf _, h => h.elim

/-- **A checked table proves a formula**: for a table `checkC` accepts for
    a formula's statement (its terms, and its shape as the bits' shape),
    the bits its memory sets and the witness its region holds are accepted
    by the formula's statement, and read back as a realizer of the
    formula. -/
theorem checkC_realizes {M : MF} {W : Nat} {A : Array Cell} {ends : Array Nat} {R : Array Air.Row}
    (h : checkC (clear M) W (stmtOf M) A ends R = true) :
    ∃ w, cWitness (bitsOf A) (BT.nleaves (clear M)) (regionOf A (BT.nleaves (clear M)) W) = some w ∧
      Accepts M (fillB (clear M) (bitsOf A) 0) w ∧
      Real M.toForm (readBack M (fillB (clear M) (bitsOf A) 0) w []) := by
  obtain ⟨w, hw, hs, hall⟩ := checkC_sound h
  have hacc : Accepts M (fillB (clear M) (bitsOf A) 0) w := ⟨shape_of_same M _ hs, hall⟩
  exact ⟨w, hw, hacc, real_of_accepted hacc⟩

end CompM
