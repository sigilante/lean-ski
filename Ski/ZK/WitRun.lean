import Ski.ZK.HideWire
import Ski.ZK.Honest
import Ski.Circuit.WitComplete

/-!
# One hidden-term run, for the composed PCS

An accepting run of the hidden-term statement `V ⬝ x`, its witness `ws`
in the region, gives its tables: `cpuTableW`, `memTableC`, `witTableG`.
`wit_honest_zk` proves they are `Balanced` and `Unblinded`, which the
transcript theorem asks.  `wit_run_sats` proves they meet `Sat`, at the
heights `2^10`, `2^10` and `2^9`, which the composed PCS asks, for the
same tables.
-/

namespace Circuit

open B Air Wit Mach

/-- **The run's tables meet `Sat`**: the CPU, memory and witness tables an
    accepting run of the hidden-term statement builds, the witness table
    `2^9` rows high. -/
theorem wit_run_sats {V x : Term} {W : Nat} {ws : List Cell} (hwf : WF ws) (hwl : ws.length = W)
    (hW8 : W ≤ 2 ^ 8) {A : List Cell} {k : Nat} {row : Nat → Air.Row} (hA : AcceptsFrom A (wMachine ws (V ⬝ x)) k row)
    (hK : rd A (row (k - 1)).ctr (row (k - 1)).hd = some .K ∧ rd A (row (k - 1)).ctr (row (k - 1)).stk = some .nil)
    (hlen : A.length = 2 ^ 10) (hk : k ≤ 2 ^ 10) :
    let blank := wMachine (List.replicate W .S) (V ⬝ x)
    let C := cpuTableW A row k (2 ^ 10)
    let Pg := progTableW blank.heap W
    let Wt := witTableG 0 A 0 W
    let Mm := memTableC A (cpuAirW blank.hd blank.stk blank.heap.length) (progAirW blank.heap W) (witAirW W) C Pg Wt
    Sat (cpuAirW blank.hd blank.stk blank.heap.length) C ∧ Sat memAirC Mm ∧ Sat (witAirW W) Wt ∧ Wt.h = 2 ^ 9 := by
  intro blank C Pg Wt Mm
  have hl : ws.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hwl]
  obtain ⟨hhd, hstk, hlenm, htake, _⟩ := wMachine_public ws (List.replicate W .S) (V ⬝ x) hl
  obtain ⟨m0, hm0⟩ : ∃ m, wMachine ws (V ⬝ x) = m := ⟨_, rfl⟩
  rw [hm0] at hA hhd hstk hlenm htake
  have hk0 := hA.pos
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hWl : W ≤ m0.heap.length := by
    have := congrArg List.length htake; rw [List.length_take, hwl] at this; omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hfin5 : kindOf A (row (k - 1)) = 5 := by simp only [kindOf, hK.1, hK.2]
  have hreg : ∀ i, i < W → cellOK (0 + 0 + i) (A.getD (0 + 0 + i) .nil) = true := by
    intro i hi
    simp only [Nat.zero_add]
    rw [hAm i (by omega)]
    have := congrArg (fun l => l[i]?) htake
    simp only [List.getElem?_take, if_pos (show i < ws.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, this, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hwf i _ (List.getElem?_eq_getElem (by omega))
  have hcpu : Sat (cpuAirW blank.hd blank.stk blank.heap.length) C := by
    have := cpuW_sat hA hk (by omega) (by omega) (by decide) hfin5
    have e0 : rowQ row k 0 = row 0 := by unfold rowQ; rw [if_pos hk0]
    rw [e0, hA.hd0, hA.stk0, hA.ctr0, hhd, hstk, hlenm] at this
    exact this
  exact ⟨hcpu, memC_sat A _ _ _ _ _ _ (by omega),
    wit_sat (a0 := 0) (N := 0) (fun h => absurd h (Nat.lt_irrefl 0)) (fun i hi => absurd hi (Nat.not_lt_zero _))
      hreg (by omega), witRowsG_len (by omega)⟩

end Circuit
