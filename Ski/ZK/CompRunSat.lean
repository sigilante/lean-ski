import Ski.ZK.HideWire
import Ski.ZK.Honest
import Ski.Circuit.CompComplete

/-!
# One composed run's tables meet `Sat`

An accepting run of the composed statement, its bits `ρ` and region in
the private addresses, gives its tables: `cpuTableC`, `memTableC`,
`witTable`, with the public program and segments tables.
`comp_honest_zk` proves the private ones `Balanced` and `Unblinded`,
which the transcript theorem asks.  `comp_run_sats` proves the CPU,
memory and witness tables and the public segments table meet `Sat`, the
witness table `2^9` rows high, which the composed PCS asks, for the same
tables.
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

/-- **The run's tables meet `Sat`**: the CPU, memory and witness tables an
    accepting composed run builds, and the public segments table. -/
theorem comp_run_sats {R Lm : Nat} (hR : R ≤ 20) {shp : BT} {Ps : List Term} {W : Nat}
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsC A (cMachine ρ shp region Ps) (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hLm : Lm ≤ 20) (hK : e (Ps.length - 1) < 2 ^ R)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    let m := blankM shp W Ps
    let roots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let C := cpuTableC A row e Ps.length roots (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Mm := memTableC A (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) (progAirC m.heap N W)
      (witAir N W) C Pg Wt
    Sat (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) C ∧ Sat memAirC Mm ∧ Sat (witAir N W) Wt ∧
      Wt.h = 2 ^ 9 ∧ Sat (segsAir roots) (segsPub roots) := by
  intro m roots N C Pg Wt Mm
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots, hlenm, htake, _⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  obtain ⟨m0, hm0⟩ : ∃ m, cMachine ρ shp region Ps = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hlenm
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
  have hctr := Circuit.AcceptsC.ctr_le hA
  have h0 : A.take m0.heap.length = m0.heap := by rw [← hA.ctr0]; exact hA.heap0
  have hmlen : m0.heap.length ≤ A.length := by
    have := congrArg List.length h0; rw [List.length_take] at this; omega
  have hpre : BT.nleaves shp + 3 + W ≤ m0.heap.length := by
    have := congrArg List.length htake
    simp only [List.length_take, List.length_append, slotHeap_length, hrl] at this
    omega
  have hAm : ∀ i, i < m0.heap.length → A.getD i .nil = m0.heap.getD i .nil := by
    intro i hi
    have := congrArg (fun l => l[i]?) h0
    simp only [List.getElem?_take, if_pos hi] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hslot : ∀ k, k < BT.nleaves shp + 3 + W →
      A.getD k .nil = (slotHeap ρ (BT.nleaves shp) ++ region).getD k .nil := by
    intro k hk
    rw [hAm k (by omega)]
    have := congrArg (fun l => l[k]?) htake
    simp only [List.getElem?_take, if_pos (show k < BT.nleaves shp + 3 + region.length by omega)] at this
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, this]
  have hbits : ∀ i, i < BT.nleaves shp → A.getD (3 + i) .nil = .K ∨ A.getD (3 + i) .nil = .app 0 1 := by
    intro i hi
    rw [hslot (3 + i) (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [slotHeap_length]; omega)]
    unfold slotHeap
    rw [List.getElem?_append_right (by simp),
      show 3 + i - ([Cell.K, Cell.I, Cell.app 0 1] : List Cell).length = i by simp, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    cases ρ i
    · exact .inr rfl
    · exact .inl rfl
  have hreg : ∀ i, i < W → cellOK (3 + BT.nleaves shp + i) (A.getD (3 + BT.nleaves shp + i) .nil) = true := by
    intro i hi
    rw [hslot _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [slotHeap_length]; omega), slotHeap_length,
      show 3 + BT.nleaves shp + i - (BT.nleaves shp + 3) = i by omega]
    have hri : i < region.length := by omega
    rw [List.getElem?_eq_getElem hri, Option.getD_some]
    have := hr i region[i] (List.getElem?_eq_getElem hri)
    rwa [show BT.nleaves shp + 3 + i = 3 + BT.nleaves shp + i by omega] at this
  have hsmall : 3 + BT.nleaves shp + W ≤ 2 ^ 24 := by omega
  have hbl : (blankM shp W Ps).heap.length = m0.heap.length := hlenm.symm
  have hb : ∀ i, i < 2 ^ R → (rowP row e Ps.length i).ctr ≤ 2 ^ 24 := by
    intro i _
    unfold rowP
    split
    · exact Nat.le_trans (hctr i (by assumption)) (by omega)
    · exact Nat.le_trans (hctr _ (Nat.le_refl _)) (by omega)
  have hcpu : Sat (cpuAirC m.hd m.stk m.heap.length roots.length m.stk) C := by
    have := cpuC_sat hA hK hb
    have eAir : cpuAirC ((blankRoots shp W Ps).getD 0 0) (blankM shp W Ps).stk
        m0.heap.length Ps.length (blankM shp W Ps).stk = cpuAirC m.hd m.stk m.heap.length roots.length m.stk := by
      show _ = cpuAirC _ _ _ _ _
      rw [hbl, hnR]; rfl
    rw [eAir] at this
    exact this
  exact ⟨hcpu, memC_sat A _ _ _ _ _ _ (by omega), wit_sat (a0 := 3) (fun _ => by decide) hbits hreg hsmall,
    witRowsG_len hNW, ⟨segRows_pos _, fun c hc => nomatch hc⟩⟩

end Circuit
