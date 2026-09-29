import Ski.AirCheck
import Ski.AirOpen
import Ski.SudokuCheck
import Ski.Realize
import Ski.InstOpen

open Term

/-!
# A statement over a hidden term: knowing a realizer of an atom

Part II's atoms are NP relations given by verifier terms: `w` realizes
`atom V x` exactly when `V ⬝ x ⬝ w` evaluates to `K` (`real_atom_iff`).
A proof of knowledge of such a `w` is the primitive every composed proof
reduces to.  `Ski/Statement.lean` hides Boolean inputs; this module hides
a whole term.

**The witness machine** (`wMachine ws P`) has two parts:

- the **witness region**, first: `W` cells at addresses `0 … W - 1`,
  private.  Each is `S`, `K`, `I`, or an application of two cells below
  it (`WF`), so the region reads back as a closed term at every address
  (`wf_termAt`); the witness is the term at `W - 1`;
- the **public part**, after it: the public term `P` (for an atom,
  `V ⬝ x`), then the application of `P` to the witness, with an empty
  stack.

**The theorems.**
- `wit_sound`: if the AIR accepts a table started from the witness
  machine, and its last row has `K` at the head and an empty stack, then
  the witness `w` satisfies `Eval (P ⬝ w) K`.
- `wit_realizes`: for `P = V ⬝ x`, the witness realizes `atom V x`.
- `wMachine_public`: two regions of the same length give machines that
  differ only in the region, so the machine with the region blank states
  the machine for every witness of that size.
- `witCheck_sound`: a table `witCheck` accepts, over an array, has in its
  region a realizer of the atom.

That a proof of such a table shows the prover *knows* the realizer rests
on the STARK's knowledge soundness, which is not proved here.
-/

namespace Wit

open Mach

-- ---------------------------------------------------------------------------
-- The witness region
-- ---------------------------------------------------------------------------

/-- A witness cell at address `i`: a combinator, or an application of two
    cells below it. -/
def cellOK (i : Nat) : Cell → Bool
  | .S | .K | .I => true
  | .app a b => decide (a < i) && decide (b < i)
  | _ => false

/-- A well-formed witness region. -/
def WF (ws : List Cell) : Prop := ∀ i c, ws[i]? = some c → cellOK i c = true

/-- `WF`, decided. -/
def wfB (ws : List Cell) : Bool :=
  (List.range ws.length).all fun i =>
    match ws[i]? with
    | some c => cellOK i c
    | none => false

theorem wfB_sound {ws : List Cell} (h : wfB ws = true) : WF ws := by
  intro i c hc
  have hi : i < ws.length := by
    rcases Nat.lt_or_ge i ws.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at hc; cases hc
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [hc] at this
  exact this

/-- **A well-formed region reads back as a closed term** at every address. -/
theorem wf_termAt {ws : List Cell} (hwf : WF ws) :
    ∀ i, i < ws.length → ∃ t, termAt ws (i + 1) i = some t := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    have hc : ws[i]? = some ws[i] := List.getElem?_eq_getElem hi
    have hok := hwf i ws[i] hc
    unfold termAt
    rw [hc]
    cases hcell : ws[i] with
    | S => exact ⟨.S, rfl⟩
    | K => exact ⟨.K, rfl⟩
    | I => exact ⟨.I, rfl⟩
    | app a b =>
      rw [hcell] at hok
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_iff] at hok
      obtain ⟨ta, hta⟩ := ih a hok.1 (Nat.lt_trans hok.1 hi)
      obtain ⟨tb, htb⟩ := ih b hok.2 (Nat.lt_trans hok.2 hi)
      dsimp only
      rw [termAt_mono hta hok.1, termAt_mono htb hok.2]
      exact ⟨_, rfl⟩
    | nil => rw [hcell] at hok; cases hok
    | cons _ _ => rw [hcell] at hok; cases hok
    | atom _ => rw [hcell] at hok; cases hok

-- ---------------------------------------------------------------------------
-- The witness machine
-- ---------------------------------------------------------------------------

/-- **The witness machine**: the region, then `P`'s cells, then `P` applied
    to the region's last cell, with an empty stack. -/
def wMachine (ws : List Cell) (P : Term) : Mach :=
  let (h1, pp) := build ws P
  ⟨h1 ++ [.app pp (ws.length - 1), .nil], h1.length, h1.length + 1⟩

/-- The witness a region holds: the term at its last cell. -/
def witnessOf (ws : List Cell) : Option Term := termAt ws ws.length (ws.length - 1)

theorem witnessOf_some {ws : List Cell} (hwf : WF ws) (hne : 0 < ws.length) :
    ∃ w, witnessOf ws = some w := by
  obtain ⟨w, hw⟩ := wf_termAt hwf (ws.length - 1) (by omega)
  rw [show ws.length - 1 + 1 = ws.length by omega] at hw
  exact ⟨w, hw⟩

/-- The witness machine reads back as `P` applied to the witness. -/
theorem odecode_wMachine {ws : List Cell} {P w : Term}
    (hw : witnessOf ws = some w) : odecode (wMachine ws P) = some (P ⬝ w).toO := by
  obtain ⟨cs, e1, lp, tp⟩ := build_spec P ws
  have eb : build ws P = (ws ++ cs, (build ws P).2) := by rw [← e1]
  unfold wMachine
  rw [eb]
  rw [e1] at lp tp
  dsimp only
  have hA : ((ws ++ cs) ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil]).length =
      (ws ++ cs).length + 2 := by simp; omega
  -- `P` at its root, the witness at the region's last cell, in the final heap.
  have hP : otermAt ((ws ++ cs) ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil])
      ((ws ++ cs).length) (build ws P).2 = some P.toO := by
    have h0 := otermAt_append (cs := [Cell.app (build ws P).2 (ws.length - 1), Cell.nil])
      (otermAt_of_termAt tp)
    exact otermAt_mono h0 (by omega)
  have hW : otermAt ((ws ++ cs) ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil])
      ((ws ++ cs).length) (ws.length - 1) = some w.toO := by
    have := otermAt_of_termAt (heap := ws) hw
    rw [List.append_assoc]
    exact otermAt_mono (otermAt_append this) (by simp)
  have happ : ((ws ++ cs) ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil])[(ws ++ cs).length]? =
      some (Cell.app (build ws P).2 (ws.length - 1)) := by
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  have hnil : ((ws ++ cs) ++ [Cell.app (build ws P).2 (ws.length - 1), Cell.nil])[(ws ++ cs).length + 1]? =
      some Cell.nil := by
    rw [List.getElem?_append_right (by omega)]
    simp
  have e : (P ⬝ w).toO = appL (P.toO ⬝ₒ w.toO) [] := rfl
  rw [e]
  apply odecode_of
  · show otermAt _ (_ + 1) (ws ++ cs).length = _
    rw [hA]
    unfold otermAt
    rw [happ]
    dsimp only
    rw [otermAt_mono hP (by omega), otermAt_mono hW (by omega)]
  · show ostackAt _ (_ + 1) ((ws ++ cs).length + 1) = _
    rw [hA]
    unfold ostackAt
    rw [hnil]

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

/-- A state with `K` at the head and an empty stack reads back as `K`. -/
theorem odecode_K {m : Mach} {v : OTerm} (hv : odecode m = some v)
    (hk : m.heap[m.hd]? = some .K) (hn : m.heap[m.stk]? = some .nil) : v = .K := by
  obtain ⟨hdT, args, h1, h2, e⟩ := odecode_eq hv
  have hh : hdT = .K := by
    rcases otermAt_cell h1 with ⟨c, eh⟩ | ⟨c, eh⟩ | ⟨c, eh⟩ | ⟨_, c, _⟩ | ⟨_, _, _, _, c, _⟩
    · rw [hk] at c; cases c
    · exact eh
    · rw [hk] at c; cases c
    · rw [hk] at c; cases c
    · rw [hk] at c; cases c
  have ha : args = [] := by
    rcases ostackAt_cell h2 with ⟨_, ea⟩ | ⟨_, _, _, _, c, _⟩
    · exact ea
    · rw [hn] at c; cases c
  rw [e, hh, ha]
  rfl

/-- **A table proves knowledge of a satisfying witness.**  If the AIR
    accepts a table started from the witness machine of a well-formed
    region, and its last row has `K` at the head and an empty stack, then
    the region's witness `w` satisfies `Eval (P ⬝ w) K`. -/
theorem wit_sound {ws : List Cell} {P : Term} (hwf : WF ws) (hne : 0 < ws.length)
    {M : List Cell} {k : Nat} {row : Nat → Air.Row}
    (h : Air.AcceptsFrom M (wMachine ws P) k row)
    (hk : Air.rd M (row (k - 1)).ctr (row (k - 1)).hd = some .K)
    (hn : Air.rd M (row (k - 1)).ctr (row (k - 1)).stk = some .nil) :
    ∃ w, witnessOf ws = some w ∧ Eval (P ⬝ w) K := by
  obtain ⟨w, hw⟩ := witnessOf_some hwf hne
  refine ⟨w, hw, ?_⟩
  obtain ⟨_, hr⟩ := h.reach (k - 1) (by have := h.pos; omega)
  obtain ⟨v, hv, hsteps⟩ := omachine_run (odecode_wMachine hw) hr
  have hK : v = .K := by
    refine odecode_K hv ?_ ?_
    · rw [← hk, Air.rd_eq]; rfl
    · rw [← hn, Air.rd_eq]; rfl
  rw [hK] at hsteps
  have := hsteps.close (fun _ => K)
  rw [close_toO] at this
  exact ⟨this, .K⟩

/-- **The witness realizes the atom.**  For the public term `V ⬝ x`, an
    accepted table's witness is a realizer of `atom V x`. -/
theorem wit_realizes {ws : List Cell} {V x : Term} (hwf : WF ws) (hne : 0 < ws.length)
    {M : List Cell} {k : Nat} {row : Nat → Air.Row}
    (h : Air.AcceptsFrom M (wMachine ws (V ⬝ x)) k row)
    (hk : Air.rd M (row (k - 1)).ctr (row (k - 1)).hd = some .K)
    (hn : Air.rd M (row (k - 1)).ctr (row (k - 1)).stk = some .nil) :
    ∃ w, witnessOf ws = some w ∧ Real (.atom V x) w := by
  obtain ⟨w, hw, he⟩ := wit_sound hwf hne h hk hn
  exact ⟨w, hw, real_atom_iff.2 he⟩

-- ---------------------------------------------------------------------------
-- The public part
-- ---------------------------------------------------------------------------

/-- `build` writes the same cells and returns the same pointer after any
    heap of the same length. -/
theorem build_shape : ∀ (t : Term) (h h' : List Cell), h.length = h'.length →
    ∃ cs p, build h t = (h ++ cs, p) ∧ build h' t = (h' ++ cs, p)
  | .S, h, h', hl => ⟨[.S], h.length, by simp [build, alloc], by simp [build, alloc, hl]⟩
  | .K, h, h', hl => ⟨[.K], h.length, by simp [build, alloc], by simp [build, alloc, hl]⟩
  | .I, h, h', hl => ⟨[.I], h.length, by simp [build, alloc], by simp [build, alloc, hl]⟩
  | .app f a, h, h', hl => by
    obtain ⟨c1, p1, e1, e1'⟩ := build_shape f h h' hl
    obtain ⟨c2, p2, e2, e2'⟩ := build_shape a (h ++ c1) (h' ++ c1) (by simp [hl])
    refine ⟨c1 ++ c2 ++ [.app p1 p2], (h ++ c1 ++ c2).length, ?_, ?_⟩
    · show (let (h1, pf) := build h f
        let (h2, pa) := build h1 a
        alloc h2 (.app pf pa)) = _
      rw [e1]; dsimp only; rw [e2]; simp [alloc]
    · show (let (h1, pf) := build h' f
        let (h2, pa) := build h1 a
        alloc h2 (.app pf pa)) = _
      rw [e1']; dsimp only; rw [e2']; simp [alloc, hl]

/-- **The witness machine's public part.**  Two regions of the same length
    give machines with the same registers and heap length, whose heaps
    begin with their regions and agree past them.  So the machine with the region blank states
    the machine for every witness of that size: what the verifier holds. -/
theorem wMachine_public (ws ws' : List Cell) (P : Term) (hl : ws.length = ws'.length) :
    (wMachine ws P).hd = (wMachine ws' P).hd ∧ (wMachine ws P).stk = (wMachine ws' P).stk ∧
    (wMachine ws P).heap.length = (wMachine ws' P).heap.length ∧
    (wMachine ws P).heap.take ws.length = ws ∧
    ∀ i, ws.length ≤ i → (wMachine ws P).heap[i]? = (wMachine ws' P).heap[i]? := by
  obtain ⟨cs, p, e1, e2⟩ := build_shape P ws ws' hl
  unfold wMachine
  rw [e1, e2]
  refine ⟨by simp [hl], by simp [hl], by simp [hl], by simp, fun i hi => ?_⟩
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := ws) hi, List.getElem?_append_right (l₁ := ws') (by omega), hl]

-- ---------------------------------------------------------------------------
-- The checker, over an array
-- ---------------------------------------------------------------------------

/-- The last row's head and stack cells, read against the memory table. -/
def lastCells (A : Array Cell) (rows : List Air.Row) : Option Cell × Option Cell :=
  let r := Air.rowFn rows (rows.length - 1)
  (Air.rdG (fun a => A[a]?) r.ctr r.hd, Air.rdG (fun a => A[a]?) r.ctr r.stk)

/-- **The witness table check**: the table's first `W` memory cells are a
    well-formed region, the table satisfies the AIR from the witness
    machine of that region and `P`, and its last row has `K` at the head
    and an empty stack. -/
def witCheck (P : Term) (W : Nat) (A : Array Cell) (rows : List Air.Row) : Bool :=
  decide (0 < W) && decide (W ≤ A.size) && wfB (A.toList.take W) &&
    Air.checkFromA A (wMachine (A.toList.take W) P) rows &&
    lastCells A rows == (some .K, some .nil)

/-- **A table `witCheck` accepts proves knowledge of a witness**: the term
    its region holds satisfies `Eval (P ⬝ w) K`. -/
theorem witCheck_sound {P : Term} {W : Nat} {A : Array Cell} {rows : List Air.Row}
    (h : witCheck P W A rows = true) :
    ∃ w, witnessOf (A.toList.take W) = some w ∧ Eval (P ⬝ w) K := by
  unfold witCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, hW⟩, hwf⟩, hc⟩, hl⟩ := h
  have hlen : 0 < (A.toList.take W).length := by simp; omega
  have hacc := Air.checkFromA_sound hc
  unfold lastCells at hl
  simp only [Prod.mk.injEq] at hl
  refine wit_sound (wfB_sound hwf) hlen hacc ?_ ?_
  · rw [Air.rd_G, ← Air.getElem?_fun]; exact hl.1
  · rw [Air.rd_G, ← Air.getElem?_fun]; exact hl.2

/-- For an atom: a table `witCheck` accepts for `V ⬝ x` has a realizer of
    `atom V x` in its region. -/
theorem witCheck_realizes {V x : Term} {W : Nat} {A : Array Cell} {rows : List Air.Row}
    (h : witCheck (V ⬝ x) W A rows = true) :
    ∃ w, witnessOf (A.toList.take W) = some w ∧ Real (.atom V x) w := by
  obtain ⟨w, hw, he⟩ := witCheck_sound h
  exact ⟨w, hw, real_atom_iff.2 he⟩

end Wit
