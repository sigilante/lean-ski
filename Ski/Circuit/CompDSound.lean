import Ski.Circuit.CompDPrefix
import Ski.Circuit.CompSound
import Ski.Circuit.CompPSound
import Ski.ComposedD

/-!
# Soundness of the circuit with the `dec` jet

Tables accepted for the circuit of a statement with the `dec` jet decode to
a run the Lean AIR with segments and the jet accepts (`CompDOK.acceptsCD`),
from the open composed machine of the bits and the region the memory
holds: each row within a segment steps, halts, or, once its state decodes,
takes the jet's step (`CompDOK.jetRow`).  As `Ski/Circuit/CompPSound.lean`.
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

section

variable {L : Layout} {shp : BT} {W : Nat} {Vs : List OTerm} {J Bd : Nat} {C Mm Pg Wt Sg D : Table}
  (h : CompDOK (L.blankM shp W Vs).hd (L.blankM shp W Vs).stk (L.blankM shp W Vs).heap.length
    (L.blankRoots shp W Vs).length (L.blankM shp W Vs).stk J (L.blankM shp W Vs).heap (BT.nleaves shp) W
    (L.blankRoots shp W Vs) C Mm Pg Wt Sg D)
  (hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < Bd)
include h

theorem CompDOK.rs_le : ∀ r, rsF C r ≤ 1 := by
  intro r
  unfold rsF
  split
  · next hr =>
    obtain ⟨k, hk⟩ := kind_ofD h.cpu hr
    rw [hk.2.2.1]
    split <;> decide
  · exact Nat.zero_le _

theorem CompDOK.sg_h : Sg.h ≤ 2 ^ 27 := h.two (segsAir (L.blankRoots shp W Vs), Sg) (by simp [compDTables])

/-- The segment counter counts the restarts before the row. -/
theorem CompDOK.cnt : ∀ r, r < C.h → C.main r CNT = ofN (cntS (rsF C) r)
  | 0, h0 => (cnt_rowsD h.cpu h0).1 rfl
  | r + 1, hr => by
    have hr' : r < C.h := Nat.lt_of_succ_lt hr
    rw [(cnt_rowsD h.cpu hr').2.1 hr, CompDOK.cnt r hr']
    show ofN (cntS (rsF C) r) + C.main r RS = ofN (cntS (rsF C) r + rsF C r)
    rw [ofN_add]
    congr 1
    unfold rsF; rw [if_pos hr', ofN_val]

theorem CompDOK.cnt_val {r : Nat} (hr : r < C.h) : (C.main r CNT).val = cntS (rsF C) r := by
  rw [h.cnt r hr]
  exact val_ofN (Nat.lt_of_le_of_lt (cntS_le _ h.rs_le r) (Nat.lt_of_lt_of_le hr
    (Nat.le_trans h.cpu_h (by decide))))

theorem CompDOK.roots_le : (L.blankRoots shp W Vs).length ≤ 2 ^ 27 := by
  have := h.sgpre.1
  have := h.sg_h
  have : (L.blankRoots shp W Vs).length ≤ (segRows (L.blankRoots shp W Vs)).length := by unfold segRows; simp
  simp only [segsAir] at *
  omega

/-- The last row has counted every segment but the last. -/
theorem CompDOK.cnt_last : cntS (rsF C) (C.h - 1) = (L.blankRoots shp W Vs).length - 1 := by
  have h0 := h.cpu.1
  have hl : C.h - 1 < C.h := by omega
  have e := (cnt_rowsD h.cpu hl).2.2 (by omega)
  have := h.cnt_val hl
  rw [e, val_ofN (by have := h.roots_le; have : P = 2013265921 := rfl; omega)] at this
  exact this.symm

theorem CompDOK.kind11 {r : Nat} (hr : r < C.h) (hrs : C.main r RS = 1) : IsKindD C r 11 := by
  obtain ⟨k, hk⟩ := kind_ofD h.cpu hr
  have e := hk.2.2.1
  rw [hrs] at e
  by_cases hk11 : k = 11
  · subst hk11; exact hk
  · rw [if_neg hk11] at e; exact absurd e (by decide)

include hv in
/-- **A restart jumps** to the next segment's root, over the nil, the
    counter unchanged. -/
theorem CompDOK.restart {r j : Nat} (hr : r + 1 < C.h) (hrs : C.main r RS = 1)
    (hc : C.main r CNT = ofN j) (hj : j + 1 < (L.blankRoots shp W Vs).length) :
    rowOf C (r + 1) = ⟨(L.blankRoots shp W Vs).getD (j + 1) 0, (L.blankM shp W Vs).stk, (rowOf C r).ctr⟩ := by
  have hr' : r < C.h := Nat.lt_of_succ_lt hr
  have hk := h.kind11 hr' hrs
  obtain ⟨_, _, _, _, _, _, _, nh, ns, nc⟩ := kind_factsD hr' hk
  obtain ⟨m1, m2, m3⟩ := next_regsD h.cpu hr' hr
  have hp0 : C.main r DECSEL = 0 := by rw [hk.2.2.2]; rfl
  have z : (nextHdOfD 11).eval (C.env r) = 0 := rfl
  have zs : (nextStkOfD 11).eval (C.env r) = 0 := rfl
  have zc : (nextCtrOfD 11).eval (C.env r) = C.main r CTR := env_main0 hr'
  rw [nh, z, hrs, zero_add', one_mul', hp0, zero_mul', add_zero'] at m1
  rw [ns, zs, hrs, zero_add', one_mul', hp0, zero_mul', add_zero'] at m2
  rw [nc, zc, hp0, zero_mul', add_zero'] at m3
  -- the segment table's root
  have hn : 0 < (L.blankRoots shp W Vs).length := by omega
  have hit := h.segHit (v := [C.main r CNT + 1, C.main r ROOT])
    ⟨(cpuAirDec (L.blankM shp W Vs).hd (L.blankM shp W Vs).stk (L.blankM shp W Vs).heap.length
        (L.blankRoots shp W Vs).length (L.blankM shp W Vs).stk J, C), by simp [compDTables], rfl, r, hr',
      ⟨"segs", 1, sRS, [.add (col CNT) one, col ROOT]⟩,
      by show _ ∈ cpuIntersD; rw [cpuIntersD_eq]; simp only [List.mem_cons, true_or, or_true], rfl,
      by simp only [List.map_cons, List.map_nil, E.eval, B.col, B.one, B.c, ofN_one, env_main0 hr'],
      by show (col RS).eval _ = 1; rw [B.col, E.eval, env_main0 hr', hrs]⟩
  obtain ⟨i, hi, e⟩ := hit
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1⟩ := e
  have hiS : i < (segRows (L.blankRoots shp W Vs)).length := by have := h.sgpre.1; simp only [segsAir] at this; omega
  have pv : ∀ k, k < 2 → Sg.pre i k = ((segRows (L.blankRoots shp W Vs)).getD i []).getD k 0 :=
    fun k hk => h.sgpre.2 i k hi hk
  rw [pv 0 (by decide)] at e0
  rw [pv 1 (by decide)] at e1
  rw [hc, ← ofN_one, ← ofN_add] at e0
  have hP := h.roots_le
  have hPP : P = 2013265921 := rfl
  rcases segRows_get hn hiS with ⟨hin, ge⟩ | ⟨_, ge⟩
  · rw [ge] at e0 e1
    have hij : i = j + 1 := ofN_inj (by omega) (by omega) e0
    subst hij
    have hroot : (L.blankRoots shp W Vs).getD (j + 1) 0 < (L.blankM shp W Vs).heap.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin]
      exact (L.fitsB Bd _ shp _ Vs (fun i c h' => blank_region W i c h' _) hv).2.1 _ (List.getElem_mem hin)
    have hstk : (L.blankM shp W Vs).stk < (L.blankM shp W Vs).heap.length := by
      show (L.heap _ shp _ Vs).1.length < ((L.heap _ shp _ Vs).1 ++ [Cell.nil]).length
      simp
    have hH := h.heap_lt
    show (⟨(C.main (r + 1) HD).val, (C.main (r + 1) STK).val, (C.main (r + 1) CTR).val⟩ : Air.Row) = _
    rw [m1, m2, m3, ← e1, List.getD_cons_succ, List.getD_cons_zero,
      val_ofN (n := (L.blankRoots shp W Vs).getD (j + 1) 0) (by omega),
      val_ofN (n := (L.blankM shp W Vs).stk) (by omega)]
    rfl
  · rw [ge] at e0
    exact absurd (ofN_inj (by omega) (by omega) e0) (by omega)


/-- **A row that is no restart steps or halts, with `DECSEL = 0`, or takes
    the jet's step, with `DECSEL = 1`.** -/
theorem CompDOK.normRowSel {r : Nat} (hr : r + 1 < C.h) (hrs : C.main r RS = 0) (hJ : J < P)
    (h3 : 3 ≤ (L.blankM shp W Vs).heap.length) :
    (C.main r DECSEL = 0 ∧ Air.NormRow (memOf Mm) [] [] (rowOf C r) (rowOf C (r + 1))) ∨
      (C.main r DECSEL = 1 ∧ ∀ t, odecode (Air.st (memOf Mm) (rowOf C r)) = some t →
        DecJet.decRowI (memOf Mm) J (rowOf C r) = some (rowOf C (r + 1))) := by
  have hr' : r < C.h := Nat.lt_of_succ_lt hr
  obtain ⟨k, hk⟩ := kind_ofD h.cpu hr'
  have hk11 : k ≠ 11 := fun e => by
    have := hk.2.2.1; rw [hrs, if_pos e] at this; exact absurd this (by decide)
  by_cases hk12 : k = 12
  · -- the jet's row
    have hp : C.main r DECSEL = 1 := by rw [hk.2.2.2, if_pos hk12]
    have h0 : 0 < C.h := h.cpu.1
    obtain ⟨_, _, c0⟩ := first_regsD h.cpu h0 rfl
    have hle := h.ctr_le (r := 0) r (by omega)
    rw [Nat.zero_add, c0, val_ofN h.heap_lt] at hle
    exact .inr ⟨hp, fun t hdec => h.jetRow hr hp hJ (by omega) hdec⟩
  · have hk11' : k < 11 := by have := hk.1; omega
    have hp0 : C.main r DECSEL = 0 := by rw [hk.2.2.2, if_neg hk12]
    obtain ⟨_, _, _, _, _, _, _, nh, ns, nc⟩ := kind_factsD hr' hk
    obtain ⟨m1, m2, m3⟩ := next_regsD h.cpu hr' hr
    rw [nh, hrs, zero_mul', add_zero', hp0, zero_mul', add_zero'] at m1
    rw [ns, hrs, zero_mul', add_zero', hp0, zero_mul', add_zero'] at m2
    rw [nc, hp0, zero_mul', add_zero'] at m3
    simp only [nextHdOfD, nextStkOfD, nextCtrOfD, if_neg hk12] at m1 m2 m3
    have hnext : rowOf C (r + 1) = ⟨((nextHdOfC k).eval (C.env r)).val, ((nextStkOfC k).eval (C.env r)).val,
        ((nextCtrOfC k).eval (C.env r)).val⟩ := by
      simp only [rowOf, m1, m2, m3]
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · exact .inl ⟨hp0, .inl (by rw [hnext]; exact h.step hr' hk h4)⟩
    · refine .inl ⟨hp0, .inr (.inr ⟨h.halt hr' hk h4 hk11', ?_⟩)⟩
      rw [hnext]
      simp only [nextHdOfC, nextStkOfC, nextCtrOfC, if_neg hk11, nextHdOf_halt h4, nextStkOf_halt h4,
        nextCtrOf_halt h4]
      simp only [rowOf, B.col, E.eval, env_main0 hr']

/-- **A row that does not restart steps**: plainly, or by the jet. -/
theorem CompDOK.normRowL {r : Nat} (hr : r + 1 < C.h) (hrs : C.main r RS = 0) (hJ : J < P)
    (h3 : 3 ≤ (L.blankM shp W Vs).heap.length) :
    NormRowD (memOf Mm) J (rowOf C r) (rowOf C (r + 1)) :=
  (h.normRowSel hr hrs hJ h3).imp (fun a => a.2) (fun a => a.2)

/-- A segment's end reads `K` at the head over a nil: a restart (`11`) or
    the last row's `HK1` (`5`). -/
theorem CompDOK.endReads {r k : Nat} (hr : r < C.h) (hk : IsKindD C r k) (hk5 : k = 11 ∨ k = 5) :
    rd (memOf Mm) (rowOf C r).ctr (rowOf C r).hd = some .K ∧
      rd (memOf Mm) (rowOf C r).ctr (rowOf C r).stk = some .nil := by
  rcases hk5 with rfl | rfl
  · exact ⟨h.read hr hk (j := 0) (by decide) rfl, h.read hr hk (j := 1) (by decide) rfl⟩
  · exact ⟨h.read hr hk (j := 0) (by decide) rfl, h.read hr hk (j := 1) (by decide) rfl⟩

include hv in
/-- **The decoded run is accepted by the AIR with segments and the
    Poseidon2 jet.** -/
theorem CompDOK.acceptsCDL (hVs : 0 < Vs.length) (hBd : Bd < P) (hJ : J < P)
    (h3 : 3 ≤ (L.blankM shp W Vs).heap.length) :
    AcceptsCD (memOf Mm) (L.mach (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Vs) J
      (L.blankRoots shp W Vs) (L.blankM shp W Vs).stk Vs.length
      (endRow (rsF C) (C.h - 1) Vs.length) (rowOf C) := by
  have hn : (L.blankRoots shp W Vs).length = Vs.length := L.blankRoots_length shp W Vs
  have hc := h.cnt_last
  rw [hn] at hc
  have h0 : 0 < C.h := h.cpu.1
  obtain ⟨r1, r2, r3⟩ := first_regsD h.cpu h0 rfl
  have hH := h.heap_lt
  have hfit := L.fitsB Bd (fun _ => false) shp (List.replicate W .S) Vs (fun i c h' => blank_region W i c h' _) hv
  have hl : (regionM (memOf Mm) (BT.nleaves shp) W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, _, _, hlen, _, _⟩ := L.pub (bitsM (memOf Mm)) (fun _ => false) shp
    (regionM (memOf Mm) (BT.nleaves shp) W) (List.replicate W .S) Vs hl
  have ctr0 : (rowOf C 0).ctr = (L.blankM shp W Vs).heap.length := by
    show (C.main 0 CTR).val = _; rw [r3, val_ofN hH]
  have hstk : (L.blankM shp W Vs).stk < (L.blankM shp W Vs).heap.length := by
    show (L.heap _ shp _ Vs).1.length < ((L.heap _ shp _ Vs).1 ++ [Cell.nil]).length
    simp
  have hhd : (L.blankM shp W Vs).hd < (L.blankM shp W Vs).heap.length := by
    show (L.blankRoots shp W Vs).getD 0 0 < _
    have : 0 < (L.blankRoots shp W Vs).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact hfit.2.1 _ (List.getElem_mem this)
  have hf := h.rs_le
  refine ⟨hVs, ?_, ?_, ?_, ?_, endRow_mono _ hf hc, fun j hj => ?_, fun i hi hne => ?_, fun j hj => ?_⟩
  · rw [ctr0]; exact h.heap0L hBd hfit.1
  · show (C.main 0 HD).val = _; rw [r1, val_ofN (by omega)]; rfl
  · show (C.main 0 STK).val = _; rw [r2, val_ofN (by omega)]
  · rw [ctr0]; exact hlen.symm
  · -- a restart
    obtain ⟨a1, a2, a3⟩ := endRow_spec _ hf hc hj
    have hlt : endRow (rsF C) (C.h - 1) Vs.length j + 1 < C.h := by omega
    have hrs : C.main (endRow (rsF C) (C.h - 1) Vs.length j) RS = 1 := by
      have : rsF C (endRow (rsF C) (C.h - 1) Vs.length j) = 1 := a2
      have hb : endRow (rsF C) (C.h - 1) Vs.length j < C.h := by omega
      rw [rsF_eq hb] at this
      rw [← ofN_val (C.main _ RS), this]; rfl
    have hcnt : C.main (endRow (rsF C) (C.h - 1) Vs.length j) CNT = ofN j := by
      rw [h.cnt _ (by omega), a3]
    exact h.restart hv hlt hrs hcnt (by omega)
  · -- no restart: a step, a halt, or the jet
    rw [endRow_last _ _ _ hVs] at hi
    have hrs : rsF C i = 0 := by
      have := hf i
      rcases Nat.lt_or_ge (rsF C i) 1 with h1 | h1
      · omega
      · obtain ⟨j, hj, e⟩ := endRow_of_one _ hf hc hi (by omega)
        exact absurd e.symm (hne j hj)
    have hrs' : C.main i RS = 0 := by
      have hb : i < C.h := by omega
      rw [rsF_eq hb] at hrs
      rw [← ofN_val (C.main i RS), hrs]; rfl
    exact h.normRowL (by omega) hrs' hJ h3
  · -- a segment's end
    by_cases hj1 : j + 1 < Vs.length
    · obtain ⟨a1, a2, _⟩ := endRow_spec _ hf hc hj1
      have hrs : C.main (endRow (rsF C) (C.h - 1) Vs.length j) RS = 1 := by
        have : rsF C (endRow (rsF C) (C.h - 1) Vs.length j) = 1 := a2
        have hb : endRow (rsF C) (C.h - 1) Vs.length j < C.h := by omega
        rw [rsF_eq hb] at this
        rw [← ofN_val (C.main _ RS), this]; rfl
      exact h.endReads (by omega) (h.kind11 (by omega) hrs) (.inl rfl)
    · have e : j = Vs.length - 1 := by omega
      rw [e, endRow_last _ _ _ hVs]
      have hl' : C.h - 1 < C.h := by omega
      obtain ⟨k, hk⟩ := kind_ofD h.cpu hl'
      obtain ⟨_, hk1⟩ := last_rowD h.cpu hl' (by omega)
      have hk5 : k = 5 := by
        have := hk.2.1 5 (by decide)
        rw [hk1] at this
        by_cases e5 : 5 = k
        · exact e5.symm
        · rw [if_neg (fun h' => e5 h'.1)] at this; exact absurd this (by decide)
      exact h.endReads hl' hk (.inr hk5)

end


section

/-! The audited statements, the statement as a tree. -/

variable {shp : BT} {W : Nat} {Vs : List OTerm} {J Bd : Nat} {C Mm Pg Wt Sg D : Table}
  (h : CompDOK (blankMO shp W Vs).hd (blankMO shp W Vs).stk (blankMO shp W Vs).heap.length
    (blankRootsO shp W Vs).length (blankMO shp W Vs).stk J (blankMO shp W Vs).heap (BT.nleaves shp) W
    (blankRootsO shp W Vs) C Mm Pg Wt Sg D)
  (hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < Bd)
include h

theorem CompDOK.normRow {r : Nat} (hr : r + 1 < C.h) (hrs : C.main r RS = 0) (hJ : J < P)
    (h3 : 3 ≤ (blankMO shp W Vs).heap.length) :
    NormRowD (memOf Mm) J (rowOf C r) (rowOf C (r + 1)) :=
  CompDOK.normRowL (L := treeL) h hr hrs hJ h3

include hv in
theorem CompDOK.acceptsCD (hVs : 0 < Vs.length) (hBd : Bd < P) (hJ : J < P)
    (h3 : 3 ≤ (blankMO shp W Vs).heap.length) :
    AcceptsCD (memOf Mm) (cMachineO (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Vs) J
      (blankRootsO shp W Vs) (blankMO shp W Vs).stk Vs.length
      (endRow (rsF C) (C.h - 1) Vs.length) (rowOf C) :=
  CompDOK.acceptsCDL (L := treeL) h hv hVs hBd hJ h3

end

end Circuit
