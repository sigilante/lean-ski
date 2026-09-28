import Ski.Air
import Ski.HeapOpen

open Term

/-!
# The AIR on open terms: probe outputs, bound

`Air.Accepts` starts from a loaded closed term.  `AcceptsFrom` starts from
any machine state and is otherwise the same constraint set: `Accepts M t`
is `AcceptsFrom M (load t)` (`accepts_iff`).  Started from an open term
loaded with atoms (`Mach.oload`), it proves open head reduction.

**The theorems.**
- `air_sound_open`: a table accepted from `oload t` ends on a halted state
  that reads back as an open-head-reduct of `t`.
- `air_probe`: if, in addition, the last row's head cell is the atom `i`,
  then `t` reduces to the variable `i` applied to some arguments.  So a
  table of `t X₁ … Xₙ`, with `t` closed and the markers atoms, whose last
  row reads an atom at the head binds its output to that atom: the
  constructor the probe names.

The circuit's output check is then one read on the last row: its head cell
is the public atom `i`.
-/

namespace Air

open Mach

/-- **The AIR accepts** a table of `k` rows over `M`, started from the
    machine state `m0`. -/
structure AcceptsFrom (M : List Cell) (m0 : Mach) (k : Nat) (row : Nat → Row) : Prop where
  pos : 0 < k
  heap0 : M.take (row 0).ctr = m0.heap
  hd0 : (row 0).hd = m0.hd
  stk0 : (row 0).stk = m0.stk
  ctr0 : (row 0).ctr = m0.heap.length
  trans : ∀ i, i + 1 < k →
    stepRow M (row i) = some (row (i + 1)) ∨ (haltRow M (row i) = true ∧ row (i + 1) = row i)
  final : haltRow M (row (k - 1)) = true

/-- `Accepts` is `AcceptsFrom` the loaded term. -/
theorem accepts_iff {M : List Cell} {t : Term} {k : Nat} {row : Nat → Row} :
    Accepts M t k row ↔ AcceptsFrom M (load t) k row :=
  ⟨fun h => ⟨h.pos, h.heap0, h.hd0, h.stk0, h.ctr0, h.trans, h.final⟩,
   fun h => ⟨h.pos, h.heap0, h.hd0, h.stk0, h.ctr0, h.trans, h.final⟩⟩

theorem AcceptsFrom.st0 {M : List Cell} {m0 : Mach} {k : Nat} {row : Nat → Row}
    (h : AcceptsFrom M m0 k row) : st M (row 0) = m0 := by
  unfold st
  rw [h.heap0, h.hd0, h.stk0]

/-- Every accepted row is a state the machine reaches, within the table. -/
theorem AcceptsFrom.reach {M : List Cell} {m0 : Mach} {k : Nat} {row : Nat → Row}
    (h : AcceptsFrom M m0 k row) : ∀ i, i < k → (row i).ctr ≤ M.length ∧ MSteps m0 (st M (row i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨?_, by rw [h.st0]; exact .refl _⟩
    have := congrArg List.length h.heap0
    rw [List.length_take, ← h.ctr0] at this
    omega
  | succ i ih =>
    intro hi
    obtain ⟨hc, hr⟩ := ih (by omega)
    cases h.trans i hi with
    | inl hs =>
      obtain ⟨hm, hc'⟩ := stepRow_mstep hc hs
      exact ⟨hc', hr.snoc hm⟩
    | inr hh =>
      rw [hh.2]
      exact ⟨hc, hr⟩

/-- **Soundness on open terms.**  A table accepted from `oload t` ends on a
    halted state that reads back as an open-head-reduct of `t`. -/
theorem air_sound_open {M : List Cell} {t : OTerm} {k : Nat} {row : Nat → Row}
    (h : AcceptsFrom M (oload t) k row) :
    ∃ v, odecode (st M (row (k - 1))) = some v ∧ OSteps t v ∧ mstep (st M (row (k - 1))) = none := by
  obtain ⟨_, hr⟩ := h.reach (k - 1) (by have := h.pos; omega)
  obtain ⟨v, hv, hsteps⟩ := omachine_run (odecode_oload t) hr
  exact ⟨v, hv, hsteps, haltRow_mstep h.final⟩

/-- **The probe binding.**  If the last row's head cell is the atom `i`, the
    table proves that `t` reduces to the variable `i` applied to some
    arguments, a spine no rule applies to. -/
theorem air_probe {M : List Cell} {t : OTerm} {k : Nat} {row : Nat → Row} {i : Nat}
    (h : AcceptsFrom M (oload t) k row)
    (hi : rd M (row (k - 1)).ctr (row (k - 1)).hd = some (.atom i)) :
    ∃ args, OSteps t (appL (.var i) args) ∧ ONeutral (appL (.var i) args) := by
  obtain ⟨v, hv, hsteps, _⟩ := air_sound_open h
  have hcell : (st M (row (k - 1))).heap[(st M (row (k - 1))).hd]? = some (.atom i) := by
    rw [← hi, rd_eq]
    rfl
  obtain ⟨args, hva, hn⟩ := atom_head hv hcell
  rw [hva] at hsteps hn
  exact ⟨args, hsteps, hn⟩

end Air
