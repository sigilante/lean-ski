import Ski.Circuit.CompJPrefix
import Ski.Circuit.CompSound
import Ski.ComposedJ

/-!
# Soundness of the composed circuit with jets

Tables accepted for the composed circuit with jets decode to a run the Lean
AIR with jets and segments accepts (`CJOK.acceptsCJ`), from the composed
machine of the bits and the region the memory holds: a restart jumps to
the next segment's root over the nil (as without jets); every other row
steps, instantiates a jet at a listed root (`JetCore.inst`, through
`CJOK.core`), or has halted and repeats.  With the jet roots licensed over
that machine's heap, every term evaluates to `K` on those bits and that
region's witness (`CJOK.sound`, by `CompM.composedJ_sound`).
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

/-- The restart bits, as numbers. -/
def rsFJ (C : Table) (r : Nat) : Nat := if r < C.h then (C.main r RSJ).val else 0

theorem rsFJ_eq {C : Table} {r : Nat} (hr : r < C.h) : rsFJ C r = (C.main r RSJ).val := if_pos hr

section

variable {shp : BT} {W : Nat} {Ps : List Term} {roots : List (Nat × Nat)} {jets : List Air.Jet}
  {C Mm Pg Wt Sg Rt Hd Tm Po Iw : Table}
  (h : CJOK (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
    (blankRoots shp W Ps).length (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
    (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw)
include h

theorem CJOK.rs_le : ∀ r, rsFJ C r ≤ 1 := by
  intro r
  unfold rsFJ
  split
  · next hr =>
    obtain ⟨k, hk⟩ := kind_ofCJ h.cpu hr
    rw [hk.2.2]
    split <;> decide
  · exact Nat.zero_le _

/-- The segment counter counts the restarts before the row. -/
theorem CJOK.cnt : ∀ r, r < C.h → C.main r CNTJ = ofN (cntS (rsFJ C) r)
  | 0, h0 => (cnt_rowsCJ h.cpu h0).1 rfl
  | r + 1, hr => by
    have hr' : r < C.h := Nat.lt_of_succ_lt hr
    rw [(cnt_rowsCJ h.cpu hr').2.1 hr, CJOK.cnt r hr']
    show ofN (cntS (rsFJ C) r) + C.main r RSJ = ofN (cntS (rsFJ C) r + rsFJ C r)
    rw [ofN_add]
    congr 1
    unfold rsFJ; rw [if_pos hr', ofN_val]

theorem CJOK.cnt_val {r : Nat} (hr : r < C.h) : (C.main r CNTJ).val = cntS (rsFJ C) r := by
  rw [h.cnt r hr]
  exact val_ofN (Nat.lt_of_le_of_lt (cntS_le _ h.rs_le r) (Nat.lt_of_lt_of_le hr
    (Nat.le_trans h.cpu_h (by decide))))

theorem CJOK.roots_le : (blankRoots shp W Ps).length ≤ 2 ^ 27 := by
  have := h.sgpre.1
  have := h.sg_h
  have : (blankRoots shp W Ps).length ≤ (segRows (blankRoots shp W Ps)).length := by unfold segRows; simp
  simp only [segsAir] at *
  omega

/-- The last row has counted every segment but the last. -/
theorem CJOK.cnt_last : cntS (rsFJ C) (C.h - 1) = (blankRoots shp W Ps).length - 1 := by
  have h0 := h.cpu.1
  have hl : C.h - 1 < C.h := by omega
  have e := (cnt_rowsCJ h.cpu hl).2.2 (by omega)
  have := h.cnt_val hl
  rw [e, val_ofN (by have := h.roots_le; have : P = 2013265921 := rfl; omega)] at this
  exact this.symm

theorem CJOK.kind12 {r : Nat} (hr : r < C.h) (hrs : C.main r RSJ = 1) : IsKindCJ C r 12 := by
  obtain ⟨k, hk⟩ := kind_ofCJ h.cpu hr
  have e := hk.2.2
  rw [hrs] at e
  by_cases hk12 : k = 12
  · subst hk12; exact hk
  · rw [if_neg hk12] at e; exact absurd e (by decide)

/-- A row other than an instantiation has no jet parts in its transition. -/
theorem CJOK.noJet {r k : Nat} (hr : r < C.h) (hk : IsKindCJ C r k) (hk11 : k ≠ 11) :
    C.main r (SEL + 11) = 0 ∧ jetHd.eval (C.env r) = 0 := by
  have h11 : C.main r (SEL + 11) = 0 := by
    rw [hk.2.1 11 (by decide), if_neg (fun e => hk11 e.1.symm)]
  obtain ⟨z1, z2, z3⟩ := flags_zeroCJ h.cpu hr h11
  refine ⟨h11, ?_⟩
  simp only [jetHd, E.eval, B.col, env_main0 hr, z1, z2, z3, zero_mul', add_zero']

/-- **A restart jumps** to the next segment's root, over the nil, the
    counter unchanged. -/
theorem CJOK.restart {r j : Nat} (hr : r + 1 < C.h) (hrs : C.main r RSJ = 1)
    (hc : C.main r CNTJ = ofN j) (hj : j + 1 < (blankRoots shp W Ps).length) :
    rowOf C (r + 1) = ⟨(blankRoots shp W Ps).getD (j + 1) 0, (blankM shp W Ps).stk, (rowOf C r).ctr⟩ := by
  have hr' : r < C.h := Nat.lt_of_succ_lt hr
  have hk := h.kind12 hr' hrs
  obtain ⟨_, _, _, _, _, _, _, nh, ns, nc⟩ := kind_factsCJ hr' hk
  obtain ⟨h11, hjet⟩ := h.noJet hr' hk (by decide)
  obtain ⟨m1, m2, m3⟩ := next_regsCJ h.cpu hr' hr
  have z : (nextHdOfCJ 12).eval (C.env r) = 0 := rfl
  have zs : (nextStkOfCJ 12).eval (C.env r) = 0 := rfl
  have zc : (nextCtrOfCJ 12).eval (C.env r) = C.main r CTR := env_main0 hr'
  rw [nh, z, hjet, hrs, zero_add', zero_add', one_mul'] at m1
  rw [ns, zs, h11, hrs, zero_mul', zero_add', zero_add', one_mul'] at m2
  rw [nc, zc, h11, zero_mul', add_zero'] at m3
  -- the segment table's root
  have hn : 0 < (blankRoots shp W Ps).length := by omega
  have hit := h.segHit (v := [C.main r CNTJ + 1, C.main r ROOTJ])
    ⟨(cpuAirCJ (blankM shp W Ps).hd (blankM shp W Ps).stk (blankM shp W Ps).heap.length
        (blankRoots shp W Ps).length (blankM shp W Ps).stk, C), by simp [compJTables], rfl, r, hr',
      ⟨"segs", 1, sRSJ, [.add (col CNTJ) one, col ROOTJ]⟩,
      by show _ ∈ cpuIntersCJ; rw [cpuIntersCJ_eq]; simp only [List.mem_cons, true_or, or_true], rfl,
      by simp only [List.map_cons, List.map_nil, E.eval, B.col, B.one, B.c, ofN_one, env_main0 hr'],
      by show (col RSJ).eval _ = 1; rw [B.col, E.eval, env_main0 hr', hrs]⟩
  obtain ⟨i, hi, e⟩ := hit
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1⟩ := e
  have hiS : i < (segRows (blankRoots shp W Ps)).length := by have := h.sgpre.1; simp only [segsAir] at this; omega
  have pv : ∀ k, k < 2 → Sg.pre i k = ((segRows (blankRoots shp W Ps)).getD i []).getD k 0 :=
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
    have hroot : (blankRoots shp W Ps).getD (j + 1) 0 < (blankM shp W Ps).heap.length := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin]
      exact (blank_fits shp W Ps).2 _ (List.getElem_mem hin)
    have hstk : (blankM shp W Ps).stk < (blankM shp W Ps).heap.length := by
      show (cHeap _ shp _ Ps).1.length < ((cHeap _ shp _ Ps).1 ++ [Cell.nil]).length
      simp
    have hH := h.heap_lt
    show (⟨(C.main (r + 1) HD).val, (C.main (r + 1) STK).val, (C.main (r + 1) CTR).val⟩ : Air.Row) = _
    rw [m1, m2, m3, ← e1, List.getD_cons_succ, List.getD_cons_zero,
      val_ofN (n := (blankRoots shp W Ps).getD (j + 1) 0) (by omega),
      val_ofN (n := (blankM shp W Ps).stk) (by omega)]
    rfl
  · rw [ge] at e0
    exact absurd (ofN_inj (by omega) (by omega) e0) (by omega)

/-- **A row that is no restart steps, instantiates a jet at a listed root,
    or has halted**, given the roots licensed over a heap that fits. -/
theorem CJOK.norm {heap' : List Cell} (hheap : heap'.length ≤ 2 ^ 27) (hroots : RootsOK heap' roots jets)
    (hfit : jets.all jetFitB = true) {r : Nat} (hr : r + 1 < C.h) (hrs : C.main r RSJ = 0) :
    NormRow (memOf Mm) roots jets (rowOf C r) (rowOf C (r + 1)) := by
  have hr' : r < C.h := Nat.lt_of_succ_lt hr
  obtain ⟨k, hk⟩ := kind_ofCJ h.cpu hr'
  have hk12 : k ≠ 12 := fun e => by
    have := hk.2.2; rw [hrs, if_pos e] at this; exact absurd this (by decide)
  by_cases hk11 : k = 11
  · subst hk11
    have hi : C.main r (SEL + 11) = 1 := by rw [hk.2.1 11 (by decide), if_pos ⟨rfl, by decide⟩]
    exact .inr (.inl ((h.core hheap).inst hr hi hroots hfit))
  have hk11' : k < 11 := by have := hk.1; omega
  obtain ⟨_, _, _, _, _, _, _, nh, ns, nc⟩ := kind_factsCJ hr' hk
  obtain ⟨h11, hjet⟩ := h.noJet hr' hk hk11
  obtain ⟨m1, m2, m3⟩ := next_regsCJ h.cpu hr' hr
  rw [nh, hjet, hrs, zero_mul', add_zero', add_zero'] at m1
  rw [ns, h11, hrs, zero_mul', zero_mul', add_zero', add_zero'] at m2
  rw [nc, h11, zero_mul', add_zero'] at m3
  have hnext : rowOf C (r + 1) = ⟨((nextHdOfCJ k).eval (C.env r)).val, ((nextStkOfCJ k).eval (C.env r)).val,
      ((nextCtrOfCJ k).eval (C.env r)).val⟩ := by
    simp only [rowOf, m1, m2, m3]
  have hn12 : ¬ (k = 11 ∨ k = 12) := fun e => by omega
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · exact .inl (by rw [hnext]; exact h.step hr' hk h4)
  · refine .inr (.inr ⟨h.halt hr' hk h4 hk11', ?_⟩)
    rw [hnext]
    simp only [nextHdOfCJ, nextStkOfCJ, nextCtrOfCJ, if_neg hn12, nextHdOf_halt h4, nextStkOf_halt h4,
      nextCtrOf_halt h4]
    simp only [rowOf, B.col, E.eval, env_main0 hr']

/-- A segment's end reads `K` at the head over a nil: a restart (`12`) or
    the last row's `HK1` (`5`). -/
theorem CJOK.endReads {r k : Nat} (hr : r < C.h) (hk : IsKindCJ C r k) (hk5 : k = 12 ∨ k = 5) :
    rd (memOf Mm) (rowOf C r).ctr (rowOf C r).hd = some .K ∧
      rd (memOf Mm) (rowOf C r).ctr (rowOf C r).stk = some .nil := by
  rcases hk5 with rfl | rfl
  · exact ⟨h.read hr hk (j := 0) (by decide) rfl, h.read hr hk (j := 1) (by decide) rfl⟩
  · exact ⟨h.read hr hk (j := 0) (by decide) rfl, h.read hr hk (j := 1) (by decide) rfl⟩

/-- **The decoded run is accepted by the AIR with jets and segments**, given
    the jet roots licensed over the composed machine the memory holds and a
    jet table whose numbers fit. -/
theorem CJOK.acceptsCJ (hPs : 0 < Ps.length)
    (hroots : RootsOK (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).heap roots jets)
    (hfit : jets.all jetFitB = true) :
    AcceptsCJ (memOf Mm) (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps)
      roots jets (blankRoots shp W Ps) (blankM shp W Ps).stk Ps.length
      (endRow (rsFJ C) (C.h - 1) Ps.length) (rowOf C) := by
  have hn : (blankRoots shp W Ps).length = Ps.length := blankRoots_length shp W Ps
  have hc := h.cnt_last
  rw [hn] at hc
  have h0 : 0 < C.h := h.cpu.1
  obtain ⟨r1, r2, r3⟩ := first_regsCJ h.cpu h0 rfl
  have hH := h.heap_lt
  have hl : (regionM (memOf Mm) (BT.nleaves shp) W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, _, _, hlen, _, _⟩ := cMachine_public (bitsM (memOf Mm)) (fun _ => false) shp
    (regionM (memOf Mm) (BT.nleaves shp) W) (List.replicate W .S) Ps hl
  have hheap : (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).heap.length ≤ 2 ^ 27 := by
    rw [hlen]; exact Nat.le_trans h.blank_le h.mem_h
  have ctr0 : (rowOf C 0).ctr = (blankM shp W Ps).heap.length := by
    show (C.main 0 CTR).val = _; rw [r3, val_ofN hH]
  have hstk : (blankM shp W Ps).stk < (blankM shp W Ps).heap.length := by
    show (cHeap _ shp _ Ps).1.length < ((cHeap _ shp _ Ps).1 ++ [Cell.nil]).length
    simp
  have hhd : (blankM shp W Ps).hd < (blankM shp W Ps).heap.length := by
    show (blankRoots shp W Ps).getD 0 0 < _
    have : 0 < (blankRoots shp W Ps).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]
    exact (blank_fits shp W Ps).2 _ (List.getElem_mem this)
  have hf := h.rs_le
  refine ⟨hPs, ?_, ?_, ?_, ?_, endRow_mono _ hf hc, fun j hj => ?_, fun i hi hne => ?_, fun j hj => ?_⟩
  · rw [ctr0]; exact h.heap0
  · show (C.main 0 HD).val = _; rw [r1, val_ofN (by omega)]; rfl
  · show (C.main 0 STK).val = _; rw [r2, val_ofN (by omega)]
  · rw [ctr0]; exact hlen.symm
  · -- a restart
    obtain ⟨a1, a2, a3⟩ := endRow_spec _ hf hc hj
    have hlt : endRow (rsFJ C) (C.h - 1) Ps.length j + 1 < C.h := by omega
    have hrs : C.main (endRow (rsFJ C) (C.h - 1) Ps.length j) RSJ = 1 := by
      have : rsFJ C (endRow (rsFJ C) (C.h - 1) Ps.length j) = 1 := a2
      have hb : endRow (rsFJ C) (C.h - 1) Ps.length j < C.h := by omega
      rw [rsFJ_eq hb] at this
      rw [← ofN_val (C.main _ RSJ), this]; rfl
    have hcnt : C.main (endRow (rsFJ C) (C.h - 1) Ps.length j) CNTJ = ofN j := by
      rw [h.cnt _ (by omega), a3]
    exact h.restart hlt hrs hcnt (by omega)
  · -- no restart: a step, an instantiation, or a halt
    rw [endRow_last _ _ _ hPs] at hi
    have hrs : rsFJ C i = 0 := by
      have := hf i
      rcases Nat.lt_or_ge (rsFJ C i) 1 with h1 | h1
      · omega
      · obtain ⟨j, hj, e⟩ := endRow_of_one _ hf hc hi (by omega)
        exact absurd e.symm (hne j hj)
    have hrs' : C.main i RSJ = 0 := by
      have hb : i < C.h := by omega
      rw [rsFJ_eq hb] at hrs
      rw [← ofN_val (C.main i RSJ), hrs]; rfl
    exact h.norm hheap hroots hfit (by omega) hrs'
  · -- a segment's end
    by_cases hj1 : j + 1 < Ps.length
    · obtain ⟨a1, a2, _⟩ := endRow_spec _ hf hc hj1
      have hrs : C.main (endRow (rsFJ C) (C.h - 1) Ps.length j) RSJ = 1 := by
        have : rsFJ C (endRow (rsFJ C) (C.h - 1) Ps.length j) = 1 := a2
        have hb : endRow (rsFJ C) (C.h - 1) Ps.length j < C.h := by omega
        rw [rsFJ_eq hb] at this
        rw [← ofN_val (C.main _ RSJ), this]; rfl
      exact h.endReads (by omega) (h.kind12 (by omega) hrs) (.inl rfl)
    · have e : j = Ps.length - 1 := by omega
      rw [e, endRow_last _ _ _ hPs]
      have hl' : C.h - 1 < C.h := by omega
      obtain ⟨k, hk⟩ := kind_ofCJ h.cpu hl'
      obtain ⟨_, hk1⟩ := last_rowCJ h.cpu hl' (by omega)
      have hk5 : k = 5 := by
        have := hk.2.1 5 (by decide)
        rw [hk1] at this
        by_cases e5 : 5 = k
        · exact e5.symm
        · rw [if_neg (fun h' => e5 h'.1)] at this; exact absurd this (by decide)
      exact h.endReads hl' hk (.inr hk5)

/-- **Soundness of the composed circuit with jets**: given the jet roots
    licensed over the composed machine the memory holds and a jet table
    whose numbers fit, the bits and the region the memory holds make every
    statement term evaluate to `K`. -/
theorem CJOK.sound (hPs : 0 < Ps.length)
    (hroots : RootsOK (cMachine (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).heap roots jets)
    (hfit : jets.all jetFitB = true) :
    ∃ w, cWitness (bitsM (memOf Mm)) (BT.nleaves shp) (regionM (memOf Mm) (BT.nleaves shp) W) = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp (bitsM (memOf Mm)) 0) w := by
  have hl : (regionM (memOf Mm) (BT.nleaves shp) W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact h.region_len
  obtain ⟨_, hstk, hroots', _, _, _⟩ := cMachine_public (bitsM (memOf Mm)) (fun _ => false) shp
    (regionM (memOf Mm) (BT.nleaves shp) W) (List.replicate W .S) Ps hl
  have ha := h.acceptsCJ hPs hroots hfit
  have e1 : (cHeap (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).2 = blankRoots shp W Ps :=
    hroots'
  have e2 : (cHeap (bitsM (memOf Mm)) shp (regionM (memOf Mm) (BT.nleaves shp) W) Ps).1.length =
      (blankM shp W Ps).stk := hstk
  rw [← e1, ← e2] at ha
  exact composedJ_sound h.regionWF hroots ha

end

end Circuit
