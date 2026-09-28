import Ski.BoolProbe
import Ski.AirOpen

open Term

/-!
# A statement: a Boolean formula over a hidden witness, as a machine

The prover claims to know inputs `ρ` that make a public formula `e` true.
The statement is a machine state (`stmtMachine`) whose heap has two parts:

- the **slots**, first: `K` at address 0, `I` at 1, the Scott `false`
  (`A 0 1`) at 2, and input `n`'s Boolean at `3 + n`: `K` when `ρ n` holds
  and `A 0 1` when it does not.  These input cells are the witness, and
  the only cells that depend on `ρ`;
- the **formula**, after them: the compiled formula applied to two atom
  markers, `acc` and `rej`, with every slot variable a pointer to its slot
  cell, so an input read many times is one cell.

**The theorem** (`stmt_sound`): if the AIR accepts a table started from the
statement machine, and its last row has the atom `acc` at the head, then
`e` is true under `ρ`.  So a proof of such a table proves the prover knows
a satisfying `ρ`: the circuit fixes the formula part in public and
constrains the input cells to Booleans, and this theorem does the rest.
-/

namespace Stmt

open Mach BExpr

/-- Every input of `e` is below `N`. -/
def Bounded (N : Nat) : BExpr → Prop
  | .var n => n < N
  | .tt => True
  | .ff => True
  | .and a b => Bounded N a ∧ Bounded N b
  | .or a b => Bounded N a ∧ Bounded N b
  | .not a => Bounded N a

/-- The slot cells: `K`, `I`, `false`, then the inputs. -/
def slotHeap (ρ : Nat → Bool) (N : Nat) : List Cell :=
  [.K, .I, .app 0 1] ++ (List.range N).map fun n => if ρ n then .K else .app 0 1

/-- Where a slot lives. -/
def slotPtr : Nat → Nat
  | 0 => 0
  | 1 => 2
  | n + 2 => n + 3

/-- Write an open term's cells, children first: a slot variable (below
    `bound`) is a pointer to its slot, any other variable an atom. -/
def pbuild (bound : Nat) : List Cell → OTerm → List Cell × Nat
  | h, .S => alloc h .S
  | h, .K => alloc h .K
  | h, .I => alloc h .I
  | h, .var x => if x < bound then (h, slotPtr x) else alloc h (.atom x)
  | h, .app f a =>
    let (h1, pf) := pbuild bound h f
    let (h2, pa) := pbuild bound h1 a
    alloc h2 (.app pf pa)

/-- A variable's meaning: its slot's value below `bound`, itself above. -/
def meaning (ρ : Nat → Bool) (bound : Nat) (x : Nat) : OTerm :=
  if x < bound then slotVal ρ x else .var x

theorem pbuild_spec (ρ : Nat → Bool) (bound : Nat) : ∀ (t : OTerm) (h : List Cell),
    (∀ x, Occ x t → x < bound → otermAt h (h.length + 1) (slotPtr x) = some (slotVal ρ x)) →
    ∃ cs, (pbuild bound h t).1 = h ++ cs ∧
      otermAt (pbuild bound h t).1 ((pbuild bound h t).1.length + 1) (pbuild bound h t).2 =
        some (t.subst (meaning ρ bound))
  | .S, h, _ => ⟨[.S], rfl, by simp [pbuild, alloc, otermAt, OTerm.subst]⟩
  | .K, h, _ => ⟨[.K], rfl, by simp [pbuild, alloc, otermAt, OTerm.subst]⟩
  | .I, h, _ => ⟨[.I], rfl, by simp [pbuild, alloc, otermAt, OTerm.subst]⟩
  | .var x, h, henv => by
    by_cases hx : x < bound
    · refine ⟨[], by simp [pbuild, hx], ?_⟩
      show otermAt (pbuild bound h (.var x)).1 ((pbuild bound h (.var x)).1.length + 1)
        (pbuild bound h (.var x)).2 = some (meaning ρ bound x)
      simp only [pbuild, if_pos hx, meaning]
      exact henv x (Occ.var x) hx
    · refine ⟨[.atom x], by simp [pbuild, hx, alloc], ?_⟩
      show otermAt (pbuild bound h (.var x)).1 ((pbuild bound h (.var x)).1.length + 1)
        (pbuild bound h (.var x)).2 = some (meaning ρ bound x)
      simp [pbuild, hx, alloc, otermAt, meaning]
  | .app f a, h, henv => by
    obtain ⟨cs1, e1, t1⟩ := pbuild_spec ρ bound f h (fun x hx => henv x (Occ.left a hx))
    have henv2 : ∀ x, Occ x a → x < bound →
        otermAt (pbuild bound h f).1 ((pbuild bound h f).1.length + 1) (slotPtr x) =
          some (slotVal ρ x) := by
      intro x hx hb
      rw [e1]
      exact otermAt_grow (henv x (Occ.right f hx) hb) (by simp)
    obtain ⟨cs2, e2, t2⟩ := pbuild_spec ρ bound a (pbuild bound h f).1 henv2
    refine ⟨cs1 ++ cs2 ++ [.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2], ?_, ?_⟩
    · show (pbuild bound (pbuild bound h f).1 a).1 ++ [_] = _
      rw [e2, e1]; simp
    · show otermAt ((pbuild bound (pbuild bound h f).1 a).1 ++
          [Cell.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2])
          (((pbuild bound (pbuild bound h f).1 a).1 ++
          [Cell.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2]).length + 1)
          (pbuild bound (pbuild bound h f).1 a).1.length =
          some ((f.subst (meaning ρ bound)) ⬝ₒ (a.subst (meaning ρ bound)))
      rw [length_concat]
      unfold otermAt
      rw [getElem?_concat]
      dsimp only
      have ef : otermAt ((pbuild bound (pbuild bound h f).1 a).1 ++
          [Cell.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2])
          ((pbuild bound (pbuild bound h f).1 a).1.length + 1) (pbuild bound h f).2 =
          some (f.subst (meaning ρ bound)) := by
        rw [e2, List.append_assoc]
        refine otermAt_grow t1 ?_
        simp
      have ea : otermAt ((pbuild bound (pbuild bound h f).1 a).1 ++
          [Cell.app (pbuild bound h f).2 (pbuild bound (pbuild bound h f).1 a).2])
          ((pbuild bound (pbuild bound h f).1 a).1.length + 1) (pbuild bound (pbuild bound h f).1 a).2 =
          some (a.subst (meaning ρ bound)) :=
        otermAt_grow t2 (Nat.le_refl _)
      rw [ef, ea]

-- ---------------------------------------------------------------------------
-- The slots read back as their values
-- ---------------------------------------------------------------------------

theorem slotHeap_length (ρ : Nat → Bool) (N : Nat) : (slotHeap ρ N).length = N + 3 := by
  simp [slotHeap]

theorem slotHeap_get (ρ : Nat → Bool) (N n : Nat) (hn : n < N) :
    (slotHeap ρ N)[n + 3]? = some (if ρ n then .K else .app 0 1) := by
  simp [slotHeap, hn]

theorem slot_reads (ρ : Nat → Bool) (N : Nat) :
    ∀ x, x < N + 2 → otermAt (slotHeap ρ N) ((slotHeap ρ N).length + 1) (slotPtr x) = some (slotVal ρ x)
  | 0, _ => by simp [slotHeap, slotPtr, slotVal, otermAt]
  | 1, _ => by
    rw [slotHeap_length]
    simp [slotHeap, slotPtr, slotVal, otermAt]
  | n + 2, hn => by
    rw [slotHeap_length]
    show otermAt (slotHeap ρ N) (N + 3 + 1) (n + 3) = some (sbool (ρ n))
    unfold otermAt
    rw [slotHeap_get ρ N n (by omega)]
    cases hρ : ρ n with
    | true => rfl
    | false => simp [otermAt, slotHeap, sbool]

-- ---------------------------------------------------------------------------
-- The statement machine
-- ---------------------------------------------------------------------------

/-- The probe term: the compiled formula applied to the markers. -/
def probeTerm (e : BExpr) (acc rej : Nat) : OTerm := compile e ⬝ₒ .var acc ⬝ₒ .var rej

/-- **The statement machine**: the slots, then the probe term, with an
    empty stack. -/
def stmtMachine (ρ : Nat → Bool) (N : Nat) (e : BExpr) (acc rej : Nat) : Mach :=
  let (h, p) := pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)
  ⟨h ++ [.nil], p, h.length⟩

theorem compile_occ {N : Nat} : ∀ {e : BExpr}, Bounded N e → ∀ x, Occ x (compile e) → x < N + 2
  | .var n, hb, x, hx => by cases hx; show n + 2 < N + 2; have : n < N := hb; omega
  | .tt, _, x, hx => by cases hx; show 0 < N + 2; omega
  | .ff, _, x, hx => by cases hx; show 1 < N + 2; omega
  | .and a b, hb, x, hx => by
    cases hx with
    | left _ h =>
      cases h with
      | left _ h => exact compile_occ hb.1 x h
      | right _ h => exact compile_occ hb.2 x h
    | right _ h => cases h; show 1 < N + 2; omega
  | .or a b, hb, x, hx => by
    cases hx with
    | left _ h =>
      cases h with
      | left _ h => exact compile_occ hb.1 x h
      | right _ h => cases h; show 0 < N + 2; omega
    | right _ h => exact compile_occ hb.2 x h
  | .not a, hb, x, hx => by
    cases hx with
    | left _ h =>
      cases h with
      | left _ h => exact compile_occ (e := a) hb x h
      | right _ h => cases h; show 1 < N + 2; omega
    | right _ h => cases h; show 0 < N + 2; omega

theorem subst_probe {ρ : Nat → Bool} {N : Nat} {e : BExpr} (hb : Bounded N e) {acc rej : Nat}
    (hacc : N + 2 ≤ acc) (hrej : N + 2 ≤ rej) :
    (probeTerm e acc rej).subst (meaning ρ (N + 2)) = fill ρ e ⬝ₒ .var acc ⬝ₒ .var rej := by
  show ((compile e).subst (meaning ρ (N + 2)) ⬝ₒ meaning ρ (N + 2) acc ⬝ₒ meaning ρ (N + 2) rej) = _
  have h1 : (compile e).subst (meaning ρ (N + 2)) = fill ρ e := by
    unfold fill
    apply subst_agree
    intro x hx
    unfold meaning
    rw [if_pos (compile_occ hb x hx)]
  rw [h1]
  unfold meaning
  rw [if_neg (by omega), if_neg (by omega)]

/-- The statement machine reads back as the filled formula applied to the
    markers. -/
theorem odecode_stmt {ρ : Nat → Bool} {N : Nat} {e : BExpr} (hb : Bounded N e) {acc rej : Nat}
    (hacc : N + 2 ≤ acc) (hrej : N + 2 ≤ rej) :
    odecode (stmtMachine ρ N e acc rej) = some (fill ρ e ⬝ₒ .var acc ⬝ₒ .var rej) := by
  have henv : ∀ x, Occ x (probeTerm e acc rej) → x < N + 2 →
      otermAt (slotHeap ρ N) ((slotHeap ρ N).length + 1) (slotPtr x) = some (slotVal ρ x) :=
    fun x _ hx => slot_reads ρ N x hx
  obtain ⟨cs, _, hroot⟩ := pbuild_spec ρ (N + 2) (probeTerm e acc rej) (slotHeap ρ N) henv
  rw [subst_probe hb hacc hrej] at hroot
  have hE : appL (fill ρ e ⬝ₒ .var acc ⬝ₒ .var rej) [] = fill ρ e ⬝ₒ .var acc ⬝ₒ .var rej := rfl
  rw [← hE]
  apply odecode_of
  · show otermAt ((pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1 ++ [Cell.nil])
      (((pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1 ++ [Cell.nil]).length + 1)
      (pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).2 = _
    exact otermAt_grow hroot (by simp)
  · show ostackAt ((pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1 ++ [Cell.nil])
      (((pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1 ++ [Cell.nil]).length + 1)
      (pbuild (N + 2) (slotHeap ρ N) (probeTerm e acc rej)).1.length = some []
    rw [length_concat]
    unfold ostackAt
    rw [getElem?_concat]

/-- **A table proves the formula.**  If the AIR accepts a table started from
    the statement machine for `ρ`, and its last row has the marker `acc` at
    the head, then `e` is true under `ρ`. -/
theorem stmt_sound {ρ : Nat → Bool} {N : Nat} {e : BExpr} (hb : Bounded N e) {acc rej : Nat}
    (hacc : N + 2 ≤ acc) (hrej : N + 2 ≤ rej) (hne : acc ≠ rej)
    {M : List Cell} {k : Nat} {row : Nat → Air.Row}
    (h : Air.AcceptsFrom M (stmtMachine ρ N e acc rej) k row)
    (hi : Air.rd M (row (k - 1)).ctr (row (k - 1)).hd = some (.atom acc)) :
    eval ρ e = true := by
  obtain ⟨_, hr⟩ := h.reach (k - 1) (by have := h.pos; omega)
  obtain ⟨v, hv, hsteps⟩ := omachine_run (odecode_stmt hb hacc hrej) hr
  have hcell : (Air.st M (row (k - 1))).heap[(Air.st M (row (k - 1))).hd]? = some (.atom acc) := by
    rw [← hi, Air.rd_eq]
    rfl
  obtain ⟨args, hva, _⟩ := atom_head hv hcell
  rw [hva] at hsteps
  exact probe_true hne hsteps

-- ---------------------------------------------------------------------------
-- The public part of the statement machine
-- ---------------------------------------------------------------------------

/-- `pbuild` writes the same cells and returns the same pointer after any
    heap of the same length. -/
theorem pbuild_shape (bound : Nat) : ∀ (t : OTerm) (h h' : List Cell), h.length = h'.length →
    ∃ cs p, pbuild bound h t = (h ++ cs, p) ∧ pbuild bound h' t = (h' ++ cs, p)
  | .S, h, h', hl => ⟨[.S], h.length, by simp [pbuild, alloc], by simp [pbuild, alloc, hl]⟩
  | .K, h, h', hl => ⟨[.K], h.length, by simp [pbuild, alloc], by simp [pbuild, alloc, hl]⟩
  | .I, h, h', hl => ⟨[.I], h.length, by simp [pbuild, alloc], by simp [pbuild, alloc, hl]⟩
  | .var x, h, h', hl => by
    by_cases hx : x < bound
    · exact ⟨[], slotPtr x, by simp [pbuild, hx], by simp [pbuild, hx]⟩
    · exact ⟨[.atom x], h.length, by simp [pbuild, hx, alloc], by simp [pbuild, hx, alloc, hl]⟩
  | .app f a, h, h', hl => by
    obtain ⟨c1, p1, e1, e1'⟩ := pbuild_shape bound f h h' hl
    obtain ⟨c2, p2, e2, e2'⟩ := pbuild_shape bound a (h ++ c1) (h' ++ c1) (by simp [hl])
    refine ⟨c1 ++ c2 ++ [.app p1 p2], (h ++ c1 ++ c2).length, ?_, ?_⟩
    · show (let (h1, pf) := pbuild bound h f
        let (h2, pa) := pbuild bound h1 a
        alloc h2 (.app pf pa)) = _
      rw [e1]; dsimp only; rw [e2]; simp [alloc]
    · show (let (h1, pf) := pbuild bound h' f
        let (h2, pa) := pbuild bound h1 a
        alloc h2 (.app pf pa)) = _
      rw [e1']; dsimp only; rw [e2']; simp [alloc, hl]

/-- **The statement machine's public part.**  Two inputs give machines
    with the same registers and heap length, whose heaps differ only at
    the input cells, addresses `3` to `N + 2`.  So the machine for all-false
    inputs, with the input cells blank, states the machine for every input:
    what `lake exe sudoku emit` publishes. -/
theorem stmtMachine_public (ρ ρ' : Nat → Bool) (N : Nat) (e : BExpr) (acc rej : Nat) :
    (stmtMachine ρ N e acc rej).hd = (stmtMachine ρ' N e acc rej).hd ∧
    (stmtMachine ρ N e acc rej).stk = (stmtMachine ρ' N e acc rej).stk ∧
    (stmtMachine ρ N e acc rej).heap.length = (stmtMachine ρ' N e acc rej).heap.length ∧
    ∀ i, (i < 3 ∨ N + 3 ≤ i) →
      (stmtMachine ρ N e acc rej).heap[i]? = (stmtMachine ρ' N e acc rej).heap[i]? := by
  have hl : (slotHeap ρ N).length = (slotHeap ρ' N).length := by
    rw [slotHeap_length, slotHeap_length]
  obtain ⟨cs, p, e1, e2⟩ := pbuild_shape (N + 2) (probeTerm e acc rej) _ _ hl
  unfold stmtMachine
  rw [e1, e2]
  refine ⟨rfl, by simp [hl], by simp [hl], fun i hi => ?_⟩
  simp only [List.append_assoc]
  rcases hi with hi | hi
  · rw [List.getElem?_append_left (by rw [slotHeap_length]; omega),
      List.getElem?_append_left (by rw [slotHeap_length]; omega)]
    simp only [slotHeap]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
  · rw [List.getElem?_append_right (l₁ := slotHeap ρ N) (by rw [slotHeap_length]; omega),
      List.getElem?_append_right (l₁ := slotHeap ρ' N) (by rw [slotHeap_length]; omega), hl]

end Stmt
