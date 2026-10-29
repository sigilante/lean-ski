import Ski.ZK.CompJInst

/-!
# The composed proof with jets is zero knowledge over its hiding PCS

`compJ_run_facts`: for an accepting run with jets (the hypotheses of
`compJ_complete_log`), the honest tables meet `compJ_transcript`'s
hypotheses (`CRun.honest_zk`), each meets its AIR (`Sat`), and each has
the height its quotient group needs: the CPU `2^R`, the memory `2^Lm`, the
witness `2^9`, POP and INSTW their budgets `2^Lp`, `2^Li`, and the
provider tables and the public ones powers of two `2^(tp + 1)`, `tp ≤ 23`
(`provCJ_height`, `comp_pub_heights`).

`compJ_hiding`: `comp_hiding` with jets, `compJ_transcriptG` over the PCS
of `compJ_pcs`, its PCS term zero.  `compJ_pcsX`: that PCS with FRI's
randomness split off (`comp_pcsX`).
-/

namespace Circuit

open ZKF B Air JetTable Compose CompM Stmt Mach Wit

-- ---------------------------------------------------------------------------
-- The provider tables' heights
-- ---------------------------------------------------------------------------

/-- A provider table's height, as a group's `tp`: `2^(tp + 1)` rows. -/
def provTpCJ (rows : List (List F)) : Nat := lgF 64 rows.length - 1

/-- **A provider table's padded rows are a power of two**, at least `2^9`,
    when they fit `2^24`. -/
theorem provCJ_height {raw : List (List F)} (h0 : 0 < (padCopiesMin raw).length)
    (h24 : (padCopiesMin raw).length ≤ 2 ^ 24) :
    provTpCJ (padCopiesMin raw) ≤ 23 ∧ (padCopiesMin raw).length = 2 ^ (provTpCJ (padCopiesMin raw) + 1) := by
  match raw, h0 with
  | r :: rs, _ =>
    have hle : (r :: rs).length ≤ 2 ^ 24 := Nat.le_trans (padCopiesMin_length_ge (r :: rs)) h24
    obtain ⟨d, h9, hd24, hd⟩ := padPow (r :: rs) r (e := 9) (by decide) hle
    have hd' : (padCopiesMin (r :: rs)).length = 2 ^ d := hd
    have ht : provTpCJ (padCopiesMin (r :: rs)) = d - 1 := by unfold provTpCJ; rw [hd', lgF_pow 64 d (by omega)]
    refine ⟨by omega, ?_⟩
    rw [ht, hd', Nat.sub_add_cancel (by omega)]

-- ---------------------------------------------------------------------------
-- The honest run's facts
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
/-- **An accepting run with jets meets the hiding PCS's hypotheses**: the
    honest tables (`compJ_complete_log`'s) are balanced and unblinded
    (`CRun.honest_zk`), each private table meets its AIR, and the heights
    are the budgets', `2^9`, and powers of two `2^(tp + 1)`, `tp ≤ 23`. -/
theorem compJ_run_facts {R Lm Lp Li : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLp : Lp ≤ 20) (hLi : Li ≤ 20)
    {shp : BT} {Ps : List Term} {W : Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet}
    (hprov : 0 < (rootsRowsCJ roots).length ∧ 0 < (hdrRowsCJ jets).length ∧ 0 < (tmplRowsCJ jets).length)
    (hprov24 : (rootsRowsCJ roots).length ≤ 2 ^ 24 ∧ (hdrRowsCJ jets).length ≤ 2 ^ 24 ∧
      (tmplRowsCJ jets).length ≤ 2 ^ 24)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    (hroots : RootsOK (cMachine ρ shp region Ps).heap roots jets)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCJ A (cMachine ρ shp region Ps) roots jets (cHeap ρ shp region Ps).2
      (cHeap ρ shp region Ps).1.length Ps.length e row)
    (hlen : A.length = 2 ^ Lm) (hK : e (Ps.length - 1) < 2 ^ R)
    (hHP : (JRun.popRows ⟨A, roots, jets, e (Ps.length - 1) + 1, row, isRestart e Ps.length⟩ (2 ^ R)).length ≤
      2 ^ Lp)
    (hHW : (JRun.instwRows ⟨A, roots, jets, e (Ps.length - 1) + 1, row, isRestart e Ps.length⟩ (2 ^ R)).length ≤
      2 ^ Li)
    (hNW : BT.nleaves shp + W ≤ 2 ^ 8) :
    let m := blankM shp W Ps
    let segRoots := blankRoots shp W Ps
    let N := BT.nleaves shp
    let Rn : CRun := ⟨A, roots, jets, segRoots, e, Ps.length, row⟩
    let cpu := cpuAirCJ m.hd m.stk m.heap.length Ps.length m.stk
    let C := Rn.cpuTableCJ (2 ^ R)
    let Pg := progTableC m.heap N W
    let Wt := witTable A N W
    let Po := Rn.J.popTable (2 ^ R) (2 ^ Lp)
    let Iw := Rn.J.instwTable (2 ^ R) (2 ^ Li)
    let Mm := memTable5 A cpu (progAirC m.heap N W) popAirCJ instwAirCJ (witAir N W) C Pg Po Iw Wt
    let Rt := provTableCJ (rootsRowsCJ roots) (Rn.J.cntRoots (2 ^ R))
    let Hd := provTableCJ (hdrRowsCJ jets) (Rn.J.cntHdr (2 ^ R))
    let Tm := provTableCJ (tmplRowsCJ jets) (Rn.J.cntTmpl (2 ^ R))
    (Balanced (compJTables m.hd m.stk m.heap.length Ps.length m.stk m.heap N W segRoots roots jets C Mm Pg Wt
        (segsPub segRoots) Rt Hd Tm Po Iw) ∧
      UnblindedCJ roots jets C Mm Wt Rt Hd Tm Po Iw) ∧
    (Sat cpu C ∧ Sat memAirC Mm ∧ Sat (witAir N W) Wt ∧ Sat popAirCJ Po ∧ Sat instwAirCJ Iw ∧
      Sat (tmplAirCJ jets) Tm ∧ Sat (hdrAirCJ jets) Hd ∧ Sat (rootsAirCJ roots) Rt) ∧
    (C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ Wt.h = 2 ^ 9 ∧ Po.h = 2 ^ Lp ∧ Iw.h = 2 ^ Li ∧
      provTpCJ (tmplRowsCJ jets) ≤ 23 ∧ Tm.h = 2 ^ (provTpCJ (tmplRowsCJ jets) + 1) ∧
      provTpCJ (hdrRowsCJ jets) ≤ 23 ∧ Hd.h = 2 ^ (provTpCJ (hdrRowsCJ jets) + 1) ∧
      provTpCJ (rootsRowsCJ roots) ≤ 23 ∧ Rt.h = 2 ^ (provTpCJ (rootsRowsCJ roots) + 1) ∧
      progTpC m.heap N W ≤ 23 ∧ Pg.h = 2 ^ (progTpC m.heap N W + 1) ∧
      segTp segRoots ≤ 23 ∧ (segsPub segRoots).h = 2 ^ (segTp segRoots + 1)) := by
  intro m segRoots N Rn cpu C Pg Wt Po Iw Mm Rt Hd Tm
  have hRb : 2 ^ R ≤ 1048576 := Nat.pow_le_pow_right (by decide) hR
  have hLb : 2 ^ Lm ≤ 1048576 := Nat.pow_le_pow_right (by decide) hLm
  have hP0 : 0 < 2 ^ Lp := Nat.two_pow_pos _
  have hI0 : 0 < 2 ^ Li := Nat.two_pow_pos _
  have hl : region.length = (List.replicate W Cell.S).length := by rw [List.length_replicate, hrl]
  obtain ⟨_, hstk, hroots', hlenm, htake, hpub⟩ :=
    cMachine_public ρ (fun _ => false) shp region (List.replicate W .S) Ps hl
  have eR : (cHeap ρ shp region Ps).2 = blankRoots shp W Ps := hroots'
  have eN : (cHeap ρ shp region Ps).1.length = (blankM shp W Ps).stk := hstk
  rw [eR, eN] at hA
  obtain ⟨m0, hm0⟩ : ∃ m, cMachine ρ shp region Ps = m := ⟨_, rfl⟩
  rw [hm0] at hA htake hpub hlenm hroots
  have hn : 0 < Ps.length := hA.npos
  have hnR : (blankRoots shp W Ps).length = Ps.length := blankRoots_length _ _ _
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
  have hPP : P = 2013265921 := rfl
  have hAl : A.length < P := by rw [hlen, hPP]; omega
  have hnK : Ps.length ≤ 2 ^ R := by
    have := emono_ge hA.emono (Ps.length - 1) (by omega); omega
  have hsmall : 3 + BT.nleaves shp + W ≤ 2 ^ 24 := by omega
  have hlenW : 3 + BT.nleaves shp + W ≤ A.length := by omega
  have hbl : (blankM shp W Ps).heap.length = m0.heap.length := hlenm.symm
  have hl24 : A.length ≤ 2 ^ 24 := by omega
  have hA' : AcceptsCJ Rn.A m0 Rn.jroots Rn.jets Rn.segRoots (blankM shp W Ps).stk Rn.n Rn.e Rn.row := hA
  have hK' : Rn.e (Rn.n - 1) < 2 ^ R := hK
  have hJ : JOK Rn.J := hA.jok hroots
  have hcpu : Sat cpu C := by
    have := CRun.cpuCJ_sat hA' hroots hK' hl24
    have eAir : cpuAirCJ (Rn.row 0).hd (Rn.row 0).stk (Rn.row 0).ctr Rn.n (blankM shp W Ps).stk = cpu := by
      show cpuAirCJ (row 0).hd (row 0).stk (row 0).ctr Ps.length _ = _
      rw [hA.hd0, hA.stk0, hA.ctr0, ← hbl]; rfl
    rw [eAir] at this
    exact this
  have hpubA : ∀ i, i < (blankM shp W Ps).heap.length →
      ¬ (3 ≤ i ∧ i < 3 + BT.nleaves shp + W) →
      i < A.length ∧ A.getD i .nil = (blankM shp W Ps).heap.getD i .nil := by
    intro i hi hp
    have hi' : i < m0.heap.length := by omega
    refine ⟨by omega, ?_⟩
    have hor : i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i := by
      rcases Nat.lt_or_ge i 3 with h3 | h3
      · exact .inl h3
      · refine .inr ?_
        have := Nat.le_of_not_lt (fun hlt => hp ⟨h3, hlt⟩)
        omega
    rw [hAm i hi', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hpub i hor]
    rfl
  have hA0 : 0 < A.length := by rw [hlen]; exact Nat.two_pow_pos _
  have hz := CRun.honest_zk hA' hroots hK' m.hd m.stk m.heap.length (heap := m.heap) (N := N) (W := W)
    hA0 hAl hnR (show Ps.length < P by omega) hHP hHW hP0 hI0 hprov hpubA
    (fun i hi => hbits i hi) (fun i hi => hreg i hi) hlenW hNW
  obtain ⟨t1, t2⟩ := provCJ_height hprov.2.2 hprov24.2.2
  obtain ⟨h1, h2⟩ := provCJ_height hprov.2.1 hprov24.2.1
  obtain ⟨r1, r2⟩ := provCJ_height hprov.1 hprov24.1
  have hmh : m.heap.length ≤ 2 ^ 24 := by show (blankM shp W Ps).heap.length ≤ _; omega
  have hsr : segRoots.length ≤ 2 ^ 24 := by
    show (blankRoots shp W Ps).length ≤ _
    have : 2 ^ R ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨p1, p2⟩ := progC_height (heap := m.heap) (N := N) (W := W) hmh
  obtain ⟨s1, s2⟩ := segsC_height (roots := segRoots) hsr
  refine ⟨hz, ⟨hcpu, memC5_sat A _ _ _ _ _ _ _ _ _ _ (by omega),
    wit_sat (a0 := 3) (fun _ => by decide) hbits hreg hsmall,
    sat_withBlocks (Rn.J.pop_sat hJ hl24 hP0) Rn.J.pop_wide, sat_withBlocks (Rn.J.instw_sat hI0) Rn.J.instw_wide,
    (provCJ_sat hprov.2.2).1, (provCJ_sat hprov.2.1).1, (provCJ_sat hprov.1).1⟩,
    rfl, hlen, witRows_len hNW, rfl, rfl, t1, (t2 : Tm.h = _), h1, (h2 : Hd.h = _), r1, (r2 : Rt.h = _), p1, p2,
    s1, s2⟩

end Circuit
