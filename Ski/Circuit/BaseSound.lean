import Ski.Circuit.BaseStep

/-!
# Soundness of the corpus circuit

**`base_sound`**: tables that the corpus circuit for `t` accepts, under
`Air.lean`'s assumptions of the proof system (`BaseOK`), decode to a
memory table and a table of rows that the Lean AIR accepts
(`Air.Accepts`): the first row is the loaded term, each row steps by the
rule table or has halted, and the last row has halted.  With
`Air.air_sound_eval`, the term evaluates.
-/

namespace Circuit

open B Air Mach

-- ---------------------------------------------------------------------------
-- The loaded heap's cells point into it
-- ---------------------------------------------------------------------------

/-- Every cell's fields are addresses within the heap. -/
def Fits (h : List Cell) : Prop := ∀ c ∈ h, (cellFields c).1 < h.length ∧ (cellFields c).2 < h.length

theorem fits_push {h : List Cell} {c : Cell} (hh : Fits h)
    (hc : (cellFields c).1 < h.length + 1 ∧ (cellFields c).2 < h.length + 1) : Fits (h ++ [c]) := by
  intro c' hc'
  rw [List.length_append, List.length_singleton]
  rcases List.mem_append.1 hc' with hc' | hc'
  · have := hh c' hc'; exact ⟨Nat.lt_succ_of_lt this.1, Nat.lt_succ_of_lt this.2⟩
  · rw [List.mem_singleton.1 hc']; exact hc

theorem build_fits : ∀ (t : Term) (h : List Cell), Fits h →
    Fits (build h t).1 ∧ (build h t).2 < (build h t).1.length ∧ h.length ≤ (build h t).1.length
  | .S, h, hh => ⟨fits_push hh ⟨Nat.succ_pos _, Nat.succ_pos _⟩, by simp [build, alloc], by simp [build, alloc]⟩
  | .K, h, hh => ⟨fits_push hh ⟨Nat.succ_pos _, Nat.succ_pos _⟩, by simp [build, alloc], by simp [build, alloc]⟩
  | .I, h, hh => ⟨fits_push hh ⟨Nat.succ_pos _, Nat.succ_pos _⟩, by simp [build, alloc], by simp [build, alloc]⟩
  | .app f a, h, hh => by
    obtain ⟨f1, p1, l1⟩ := build_fits f h hh
    obtain ⟨f2, p2, l2⟩ := build_fits a (build h f).1 f1
    show Fits ((build (build h f).1 a).1 ++ [.app (build h f).2 (build (build h f).1 a).2]) ∧
      (build (build h f).1 a).1.length < ((build (build h f).1 a).1 ++ [_]).length ∧
      h.length ≤ ((build (build h f).1 a).1 ++ [_]).length
    rw [List.length_append, List.length_singleton]
    refine ⟨fits_push f2 ⟨?_, ?_⟩, Nat.lt_succ_self _, ?_⟩
    · show (build h f).2 < _; omega
    · show (build (build h f).1 a).2 < _; omega
    · omega

/-- **The loaded heap fits**, and its registers point into it. -/
theorem load_fits (t : Term) :
    Fits (load t).heap ∧ (load t).hd < (load t).heap.length ∧ (load t).stk < (load t).heap.length := by
  obtain ⟨f, p, _⟩ := build_fits t [] (fun _ h => nomatch h)
  show Fits ((build [] t).1 ++ [Cell.nil]) ∧ (build [] t).2 < ((build [] t).1 ++ [Cell.nil]).length ∧
    (build [] t).1.length < ((build [] t).1 ++ [Cell.nil]).length
  rw [List.length_append, List.length_singleton]
  exact ⟨fits_push f ⟨Nat.succ_pos _, Nat.succ_pos _⟩, Nat.lt_succ_of_lt p, Nat.lt_succ_self _⟩

-- ---------------------------------------------------------------------------
-- The program table's rows
-- ---------------------------------------------------------------------------

theorem programRows_get {heap : List Cell} {i : Nat} (hi : i < heap.length) :
    (programRows heap).getD i [] =
      [ofN i, ofN (cellTag heap[i]), ofN (cellFields heap[i]).1, ofN (cellFields heap[i]).2, ofN 1] := by
  unfold programRows
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi]), List.getElem?_map,
    List.getElem?_eq_getElem (by simp [hi]), List.getElem_zipIdx]
  simp

theorem programRows_length (heap : List Cell) : heap.length ≤ (programRows heap).length := by
  simp [programRows]

-- ---------------------------------------------------------------------------
-- Soundness
-- ---------------------------------------------------------------------------

theorem nextHdOf_halt {k : Nat} (hk : 4 ≤ k) : nextHdOf k = col HD := by
  simp [nextHdOf, show k ≠ 0 by omega, show ¬ k < 4 by omega]
theorem nextStkOf_halt {k : Nat} (hk : 4 ≤ k) : nextStkOf k = col STK := by
  simp [nextStkOf, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega]
theorem nextCtrOf_halt {k : Nat} (hk : 4 ≤ k) : nextCtrOf k = col CTR := by
  simp [nextCtrOf, show k ≠ 0 by omega, show k ≠ 3 by omega]

section

variable {t : Term} {C Mm Pg : Table}
  (h : BaseOK (load t).hd (load t).stk (load t).heap.length (load t).heap C Mm Pg)
include h

theorem BaseOK.heap_lt : (load t).heap.length < P := by
  have e := h.pre.1
  have hl := programRows_length (load t).heap
  have hH := heights h.hts
  rw [show (progAir (load t).heap).pretrace = programRows (load t).heap from rfl] at e
  omega

/-- The program table puts the loaded heap in the memory. -/
theorem BaseOK.heap0 : (memOf Mm).take (load t).heap.length = (load t).heap := by
  obtain ⟨hfit, _, _⟩ := load_fits t
  have hP := h.heap_lt
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take]
  split
  · next hi =>
    have hPg : i < Pg.h := by
      have := h.pre.1
      have := programRows_length (load t).heap
      rw [show (progAir (load t).heap).pretrace = programRows (load t).heap from rfl] at *
      omega
    have hc := hfit _ (List.getElem_mem hi)
    have hpre : ∀ j, j < 5 → (prec j).eval (Pg.env i) = ((programRows (load t).heap).getD i []).getD j 0 := by
      intro j hj
      show Pg.pre ((i + 0) % Pg.h) j = _
      rw [Nat.add_zero, Nat.mod_eq_of_lt hPg, h.pre.2 i j hPg hj]; rfl
    have hm := h.cell (lookup h.cpu h.pre h.bal h.hts [ofN i, ofN (cellTag (load t).heap[i]),
      ofN (cellFields (load t).heap[i]).1, ofN (cellFields (load t).heap[i]).2] (.inr ⟨i, hPg, by
      simp only [List.map_cons, List.map_nil, hpre 0 (by decide), hpre 1 (by decide), hpre 2 (by decide),
        hpre 3 (by decide), programRows_get hi]; rfl,
      by rw [hpre 4 (by decide), programRows_get hi]; rfl⟩))
    rw [val_ofN (Nat.lt_trans hi hP), cellOf_enc _ (Nat.lt_trans hc.1 hP) (Nat.lt_trans hc.2 hP)] at hm
    rw [hm.2, List.getElem?_eq_getElem hi]
  · next hi => rw [List.getElem?_eq_none (Nat.le_of_not_lt hi)]

/-- **Soundness of the corpus circuit**: accepted tables decode to a run
    the Lean AIR accepts. -/
theorem base_sound : Accepts (memOf Mm) t C.h (rowOf C) := by
  obtain ⟨_, hhd, hstk⟩ := load_fits t
  have hP := h.heap_lt
  have h0 : 0 < C.h := h.cpu.1
  obtain ⟨e1, e2, e3⟩ := first_regs h.cpu h0 rfl
  have ctr0 : (rowOf C 0).ctr = (load t).heap.length := by
    show (C.main 0 CTR).val = _; rw [e3, val_ofN hP]
  refine ⟨h0, ?_, ?_, ?_, ctr0, ?_, ?_⟩
  · rw [ctr0]; exact h.heap0
  · show (C.main 0 HD).val = _; rw [e1, val_ofN (Nat.lt_trans hhd hP)]
  · show (C.main 0 STK).val = _; rw [e2, val_ofN (Nat.lt_trans hstk hP)]
  · intro i hi
    have hi' : i < C.h := Nat.lt_of_succ_lt hi
    obtain ⟨k, hk, hsel⟩ := kind_of h.cpu hi'
    have hK : IsKind C i k := ⟨hk, hsel⟩
    obtain ⟨_, _, _, _, n1, n2, n3⟩ := kind_facts hi' hK
    obtain ⟨m1, m2, m3⟩ := next_regs h.cpu hi' hi
    have hnext : rowOf C (i + 1) = ⟨((nextHdOf k).eval (C.env i)).val,
        ((nextStkOf k).eval (C.env i)).val, ((nextCtrOf k).eval (C.env i)).val⟩ := by
      simp only [rowOf, m1, m2, m3, n1, n2, n3]
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · exact .inl (by rw [hnext]; exact h.step hi' hK hk4)
    · refine .inr ⟨h.halt hi' hK hk4, ?_⟩
      rw [hnext, nextHdOf_halt hk4, nextStkOf_halt hk4, nextCtrOf_halt hk4]
      simp only [rowOf, col_eval hi']
  · have hl : C.h - 1 < C.h := Nat.sub_lt h0 (by decide)
    obtain ⟨k, hk, hsel⟩ := kind_of h.cpu hl
    have hK : IsKind C (C.h - 1) k := ⟨hk, hsel⟩
    have hh := last_halt h.cpu hl (Nat.sub_add_cancel h0)
    obtain ⟨_, hhalt, _⟩ := kind_facts hl hK
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · rw [hhalt, if_neg (Nat.not_le_of_lt hk4)] at hh
      exact absurd hh (by decide)
    · exact h.halt hl hK hk4

end

/-- **Soundness of the corpus circuit, as AIR data**: tables accepted for
    the circuit the verifier builds for `t` decode to a run of the Lean
    AIR. -/
theorem baseAirs_sound {t : Term} {ts : List Table} (h : Accepted (baseAirs t) ts) :
    ∃ C Mm Pg, ts = [C, Mm, Pg] ∧ Accepts (memOf Mm) t C.h (rowOf C) := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := h
  match ts, hl with
  | [C, Mm, Pg], _ =>
    refine ⟨C, Mm, Pg, rfl, base_sound ⟨?_, ?_, ?_, ?_, hbal, hht, htwo⟩⟩
    · exact (hsat (cpuAir (load t).hd (load t).stk (load t).heap.length, C) (by simp [baseAirs])).1
    · exact (hsat (memAir, Mm) (by simp [baseAirs])).1
    · exact (hsat (progAir (load t).heap, Pg) (by simp [baseAirs])).1
    · rcases (hsat (progAir (load t).heap, Pg) (by simp [baseAirs])).2 with h0 | h0
      · exact absurd h0 (by show ¬ (5 = 0); decide)
      · exact h0

/-- **Soundness of the Rust circuit**: AIRs with the normal forms of the
    verifier's (what `lake exe circuit compare` checks of the Rust export)
    accept only tables that decode to a run of the Lean AIR, so `t`
    evaluates, to the value the run ends on. -/
theorem export_sound {t : Term} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (baseAirs t) = true) (h : Accepted Rs ts) :
    ∃ C Mm Pg, ts = [C, Mm, Pg] ∧ Accepts (memOf Mm) t C.h (rowOf C) ∧
      ∃ v, decode (st (memOf Mm) (rowOf C (C.h - 1))) = some v ∧ Eval t v := by
  obtain ⟨C, Mm, Pg, e, ha⟩ := baseAirs_sound (accepted_transfer hs h)
  exact ⟨C, Mm, Pg, e, ha, air_sound_eval ha⟩

end Circuit
