import Ski.ZK.LogUpBase
import Ski.Circuit.CompStep
import Ski.Circuit.SudSound
import Ski.Circuit.WitSound

/-!
# The hiding circuits' AIRs meet the composed PCS's checks

`tabsHonest_corpus` and `pcsCloseN_fri_corpus` ask one fact of an AIR,
`AirP3`: its constraints guarded, in its window, of Plonky3 degree at
most 2 with at most one transition factor, and its interactions'
elements and multiplicities in its columns, of degree at most 1 and 2.
The kernel checks it for every AIR of the Sudoku, hidden-term and
composed circuits, at every parameter: the parameters enter only as
constants, which none of these checks read (`sud_P3`, `wit_P3`,
`comp_P3`).

The transcript commits each private table blinded (`Table.setBlind`: an
edge's tuple and the flag 1 in row 0).  Blinding keeps `Sat` when each
constraint avoids the blinding columns or is the flag's boolean check
(`sat_setBlind`), and the kernel checks that for every blinding block of
these circuits (`blind_ok`).
-/

namespace Circuit

set_option maxRecDepth 100000 in
/-- **The Sudoku circuit's AIRs.** -/
theorem sud_P3 (hd0 stk0 ctr0 : Nat) (heap : List Cell) (C Mm Pg Wt : Table) :
    ∀ p ∈ sudTables hd0 stk0 ctr0 heap C Mm Pg Wt, AirP3 p.1 = true := by
  intro p hp
  simp only [sudTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
/-- **The hidden-term circuit's AIRs.** -/
theorem wit_P3 (hd0 stk0 ctr0 : Nat) (heap : List Cell) (W : Nat) (C Mm Pg Wt : Table) :
    ∀ p ∈ witTables hd0 stk0 ctr0 heap W C Mm Pg Wt, AirP3 p.1 = true := by
  intro p hp
  simp only [witTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 100000 in
/-- **The composed circuit's AIRs.** -/
theorem comp_P3 (hd0 stk0 ctr0 n nilA : Nat) (heap : List Cell) (N W : Nat) (roots : List Nat)
    (C Mm Pg Wt Sg : Table) :
    ∀ p ∈ compTables hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg, AirP3 p.1 = true := by
  intro p hp
  simp only [compTables, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> rfl

-- ---------------------------------------------------------------------------
-- Blinding keeps `Sat`
-- ---------------------------------------------------------------------------

/-- The flag's boolean check, `f (f - 1)` with `f` column `c + 4`. -/
def isFlagBool (c : Nat) : E → Bool
  | .mul (.atom (.main 0 i)) (.sub (.atom (.main 0 j)) (.const one)) =>
    decide (i = c + 4) && decide (j = c + 4) && decide (one = 1)
  | _ => false

/-- Each constraint avoids the blinding columns at `c`, or is the flag's
    boolean check. -/
def blindOK (A : AirD) (c : Nat) : Bool := A.cons.all fun e => e.onlyAtoms (avoid c) || isFlagBool c e

theorem flag_of_isFlagBool {c : Nat} : ∀ {e : E}, isFlagBool c e = true →
    e = .mul (.atom (.main 0 (c + 4))) (.sub (.atom (.main 0 (c + 4))) (.const 1))
  | .mul (.atom (.main 0 i)) (.sub (.atom (.main 0 j)) (.const one)), h => by
    simp only [isFlagBool, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl

/-- **Blinding keeps `Sat`** when each constraint avoids the blinding
    columns `c, …, c + 4` or is the flag's boolean check: blinding
    rewrites only those columns of row 0, and sets the flag to 1. -/
theorem sat_setBlind {A : AirD} {T : Table} {c : Nat} (h : Sat A T) (hok : blindOK A c = true) (a : Tup) :
    Sat A (T.setBlind c a) := by
  refine ⟨h.1, fun con hc r hr => ?_⟩
  have hc' := List.all_eq_true.1 hok con hc
  rcases Bool.or_eq_true_iff.1 hc' with hav | hfl
  · rw [E.eval_congr (p := avoid c) (ρ' := T.env r) (fun t ht => env_setBlind a r ht) con hav]
    exact h.2 con hc r hr
  · have e := flag_of_isFlagBool hfl
    subst e
    show (T.setBlind c a).main ((r + 0) % T.h) (c + 4) * ((T.setBlind c a).main ((r + 0) % T.h) (c + 4) - 1) = 0
    by_cases h0 : (r + 0) % T.h = 0
    · rw [h0]
      have v4 : (T.setBlind c a).main 0 (c + 4) = 1 := by
        dsimp only [Table.setBlind]
        rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      rw [v4, sub_self', mul_zero']
    · have := h.2 _ hc r hr
      have e2 : (T.setBlind c a).main ((r + 0) % T.h) (c + 4) = T.main ((r + 0) % T.h) (c + 4) := by
        show (if (r + 0) % T.h = 0 then _ else T.main ((r + 0) % T.h) (c + 4)) = _
        rw [if_neg h0]
      rw [e2]; exact this

set_option maxRecDepth 100000 in
/-- **The hiding circuits' blinding blocks keep `Sat`**: at each block,
    every constraint avoids the blinding columns or is the flag's boolean
    check, at every parameter. -/
theorem blind_ok (hd0 stk0 ctr0 n nilA N W : Nat) :
    blindOK (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) BLA = true ∧ blindOK (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) BLB = true ∧
    blindOK (cpuAirW hd0 stk0 ctr0) BLA = true ∧ blindOK (cpuAirW hd0 stk0 ctr0) BLB = true ∧
    blindOK (cpuAirC hd0 stk0 ctr0 n nilA) BLA = true ∧ blindOK (cpuAirC hd0 stk0 ctr0 n nilA) BLB = true ∧
    blindOK memAirC 5 = true ∧ blindOK witAirS 1 = true ∧ blindOK (witAirW W) WT_BLIND = true ∧
    blindOK (witAir N W) WT_BLIND = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Circuit
