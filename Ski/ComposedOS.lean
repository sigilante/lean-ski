import Ski.HeapShared
import Ski.Circuit.CompPPrefix

set_option linter.unusedSimpArgs false

/-!
# The composed heap, shared

`cHeapO` writes each statement as a tree (`obuild`); `cHeapOS` writes the
same statements hash-consed (`obuildS`), one memo across all of them,
started empty past the bits' encoding, so that no public cell aliases a
slot, a bit or the region.  It meets the three facts the composed circuits
read off `cHeapO`, in the same form:

- `cMachineOS_decode`: each root reads back as its verifier applied to the
  bits and the witness (`cMachineO_decode`);
- `cMachineOS_public`: bits and regions of the same sizes give the same
  registers, roots, heap length and public cells (`cMachineO_public`);
- `cMachineOS_fitsB`: every field below the heap's length or `Bd`
  (`cMachineO_fitsB`).
-/

namespace CompM

open Mach Stmt Compose Wit BExpr

/-- `addStmtsO`, hash-consed: one memo across the statements. -/
def addStmtsOS (pe wr : Nat) : List Cell → Memo → List OTerm → List Cell × List Nat
  | h, _, [] => (h, [])
  | h, m, P :: Ps =>
    let r := obuildS h m P
    let h3 := r.1 ++ [.app r.2.2 pe, .app r.1.length wr]
    ((addStmtsOS pe wr h3 r.2.1 Ps).1, (r.1.length + 1) :: (addStmtsOS pe wr h3 r.2.1 Ps).2)

theorem addStmtsOS_spec (pe wr : Nat) (E Wt : OTerm) : ∀ (Ps : List OTerm) (h : List Cell) (m : Memo),
    MemoOK h m → otermAt h (h.length + 1) pe = some E → otermAt h (h.length + 1) wr = some Wt →
    ∃ cs, (addStmtsOS pe wr h m Ps).1 = h ++ cs ∧ (addStmtsOS pe wr h m Ps).2.length = Ps.length ∧
      ∀ j (P : OTerm), Ps[j]? = some P →
        otermAt (addStmtsOS pe wr h m Ps).1 ((addStmtsOS pe wr h m Ps).1.length + 1)
          ((addStmtsOS pe wr h m Ps).2.getD j 0) = some (P ⬝ₒ E ⬝ₒ Wt)
  | [], h, _, _, _, _ => ⟨[], by simp [addStmtsOS], rfl, fun j P hP => by simp at hP⟩
  | P :: Ps, h, m, hm, hE, hW => by
    obtain ⟨c1, e1, lp, tp, mp⟩ := obuildS_spec P h m hm
    let r := obuildS h m P
    let h3 := r.1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr]
    have hl3 : h3.length = r.1.length + 2 := by simp [h3]
    have e3 : h3 = h ++ (c1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr]) := by
      simp [h3, show r.1 = h ++ c1 from e1]
    have hEg : ∀ F, h.length + 1 ≤ F → otermAt h3 F pe = some E := fun F hF => by
      rw [e3]; exact otermAt_grow hE hF
    have hWg : ∀ F, h.length + 1 ≤ F → otermAt h3 F wr = some Wt := fun F hF => by
      rw [e3]; exact otermAt_grow hW hF
    have hPg : ∀ F, r.2.2 + 1 ≤ F → otermAt h3 F r.2.2 = some P := fun F hF => otermAt_grow tp hF
    have hr1 : r.1.length = h.length + c1.length := by rw [show r.1 = h ++ c1 from e1]; simp
    have lp' : r.2.2 < r.1.length := lp
    have h1 : h3[r.1.length]? = some (Cell.app r.2.2 pe) := by simp [h3]
    have h2 : h3[r.1.length + 1]? = some (Cell.app r.1.length wr) := by simp [h3]
    have r1 : ∀ F, r.1.length + 1 ≤ F → otermAt h3 (F + 1) r.1.length = some (P ⬝ₒ E) := fun F hF => by
      unfold otermAt
      rw [h1]
      dsimp only
      rw [hPg F (by omega), hEg F (by omega)]
    have r2 : ∀ F, r.1.length + 1 ≤ F → otermAt h3 (F + 2) (r.1.length + 1) = some (P ⬝ₒ E ⬝ₒ Wt) := fun F hF => by
      unfold otermAt
      rw [h2]
      dsimp only
      rw [r1 F hF, hWg (F + 1) (by omega)]
    obtain ⟨cs, e, hlen, hj⟩ := addStmtsOS_spec pe wr E Wt Ps h3 r.2.1 (mp.grow _)
      (hEg _ (by omega)) (hWg _ (by omega))
    refine ⟨c1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr] ++ cs, ?_, ?_, ?_⟩
    · show (addStmtsOS pe wr h3 r.2.1 Ps).1 = _
      rw [e, e3]; simp
    · show ((r.1.length + 1) :: (addStmtsOS pe wr h3 r.2.1 Ps).2).length = _
      simp [hlen]
    · intro j Q hQ
      cases j with
      | zero =>
        simp at hQ
        subst hQ
        show otermAt (addStmtsOS pe wr h3 r.2.1 Ps).1 _ (r.1.length + 1) = _
        rw [e]
        refine otermAt_grow (cs := cs) (r2 (r.1.length + 1) (Nat.le_refl _)) ?_
        show _ ≤ (addStmtsOS pe wr h3 r.2.1 Ps).1.length + 1
        rw [e, List.length_append, hl3]; omega
      | succ j =>
        simp at hQ
        exact hj j Q hQ

/-- The composed heap of an open statement, shared. -/
def cHeapOS (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm) : List Cell × List Nat :=
  let h0 := slotHeap ρ (BT.nleaves shp) ++ region
  let e1 := pbuild (BT.nleaves shp + 2) h0 (encO shp 0)
  addStmtsOS e1.2 (h0.length - 1) e1.1 Memo.empty Vs

/-- The composed machine of an open statement, shared. -/
def cMachineOS (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm) : Mach :=
  ⟨(cHeapOS ρ shp region Vs).1 ++ [.nil], (cHeapOS ρ shp region Vs).2.getD 0 0,
    (cHeapOS ρ shp region Vs).1.length⟩

/-- **The shared machine's roots read back as the verifiers applied to the
    bits and the witness**, as `cMachineO_decode`. -/
theorem cMachineOS_decode {ρ : Nat → Bool} {shp : BT} {region : List Cell} {Vs : List OTerm}
    {w : Term} (hw : cWitness ρ (BT.nleaves shp) region = some w) :
    (cHeapOS ρ shp region Vs).2.length = Vs.length ∧
    ∀ j V, Vs[j]? = some V →
      otermAt (cMachineOS ρ shp region Vs).heap ((cMachineOS ρ shp region Vs).heap.length + 1)
        ((cHeapOS ρ shp region Vs).2.getD j 0) =
        some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  have hW : otermAt h0 (h0.length + 1) (h0.length - 1) = some w.toO := by
    have := otermAt_of_termAt (heap := h0) hw
    exact otermAt_mono this (Nat.le_succ _)
  have henv : ∀ x, Occ x (encO shp 0) → x < N + 2 →
      otermAt h0 (h0.length + 1) (slotPtr x) = some (slotVal ρ x) := by
    intro x _ hx
    exact otermAt_grow (cs := region) (k := h0.length + 1) (slot_reads ρ N x hx)
      (by simp [h0, slotHeap_length])
  obtain ⟨cs1, e1, t1⟩ := pbuild_spec ρ (N + 2) (encO shp 0) h0 henv
  rw [encO_fill ρ N shp 0 (by simp [N])] at t1
  have hW1 : otermAt (pbuild (N + 2) h0 (encO shp 0)).1
      ((pbuild (N + 2) h0 (encO shp 0)).1.length + 1) (h0.length - 1) = some w.toO := by
    rw [e1]; exact otermAt_grow hW (by simp)
  obtain ⟨cs, e, hlen, hj⟩ := addStmtsOS_spec (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1)
    _ _ Vs (pbuild (N + 2) h0 (encO shp 0)).1 Memo.empty (MemoOK.empty _) t1 hW1
  refine ⟨hlen, fun j V hV => ?_⟩
  have := hj j V hV
  show otermAt ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil]) _ _ = _
  refine otermAt_grow this ?_
  show _ ≤ ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil]).length + 1
  simp only [List.length_append, List.length_singleton]
  show _ ≤ (addStmtsOS (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1)
    (pbuild (N + 2) h0 (encO shp 0)).1 Memo.empty Vs).1.length + 1 + 1
  omega

theorem addStmtsOS_shape (pe wr : Nat) : ∀ (Vs : List OTerm) (m : Memo) (h h' : List Cell),
    h.length = h'.length →
    ∃ cs, (addStmtsOS pe wr h m Vs).1 = h ++ cs ∧ (addStmtsOS pe wr h' m Vs).1 = h' ++ cs ∧
      (addStmtsOS pe wr h m Vs).2 = (addStmtsOS pe wr h' m Vs).2
  | [], _, h, h', _ => ⟨[], by simp [addStmtsOS], by simp [addStmtsOS], rfl⟩
  | P :: Vs, m, h, h', hl => by
    obtain ⟨c1, e1, e1', r1⟩ := obuildS_shape P m hl
    have hm : (obuildS h' m P).2.1 = (obuildS h m P).2.1 := by rw [r1]
    have hp : (obuildS h' m P).2.2 = (obuildS h m P).2.2 := by rw [r1]
    have hl3 : ((obuildS h m P).1 ++ [Cell.app (obuildS h m P).2.2 pe,
          Cell.app (obuildS h m P).1.length wr]).length =
        ((obuildS h' m P).1 ++ [Cell.app (obuildS h m P).2.2 pe,
          Cell.app (obuildS h' m P).1.length wr]).length := by
      rw [e1, e1']; simp [hl]
    obtain ⟨cs, e2, e2', e3⟩ := addStmtsOS_shape pe wr Vs (obuildS h m P).2.1 _ _ hl3
    have u : addStmtsOS pe wr h' m (P :: Vs) =
        ((addStmtsOS pe wr ((obuildS h' m P).1 ++ [Cell.app (obuildS h m P).2.2 pe,
            Cell.app (obuildS h' m P).1.length wr]) (obuildS h m P).2.1 Vs).1,
          ((obuildS h' m P).1.length + 1) ::
            (addStmtsOS pe wr ((obuildS h' m P).1 ++ [Cell.app (obuildS h m P).2.2 pe,
              Cell.app (obuildS h' m P).1.length wr]) (obuildS h m P).2.1 Vs).2) := by
      show ((addStmtsOS pe wr ((obuildS h' m P).1 ++ [Cell.app (obuildS h' m P).2.2 pe,
          Cell.app (obuildS h' m P).1.length wr]) (obuildS h' m P).2.1 Vs).1, _) = _
      rw [hm, hp]
    have hlen : (obuildS h m P).1.length = (obuildS h' m P).1.length := by rw [e1, e1']; simp [hl]
    rw [u]
    refine ⟨c1 ++ [Cell.app (obuildS h m P).2.2 pe, Cell.app (obuildS h m P).1.length wr] ++ cs, ?_, ?_, ?_⟩
    · show (addStmtsOS pe wr _ _ Vs).1 = _
      rw [e2, e1]; simp
    · rw [e2', e1', e1]; simp [hl]
    · show ((obuildS h m P).1.length + 1) :: (addStmtsOS pe wr _ _ Vs).2 = _
      rw [e3, hlen]

/-- **The shared machine's public part**, as `cMachineO_public`. -/
theorem cMachineOS_public (ρ ρ' : Nat → Bool) (shp : BT) (region region' : List Cell) (Vs : List OTerm)
    (hl : region.length = region'.length) :
    (cMachineOS ρ shp region Vs).hd = (cMachineOS ρ' shp region' Vs).hd ∧
    (cMachineOS ρ shp region Vs).stk = (cMachineOS ρ' shp region' Vs).stk ∧
    (cHeapOS ρ shp region Vs).2 = (cHeapOS ρ' shp region' Vs).2 ∧
    (cMachineOS ρ shp region Vs).heap.length = (cMachineOS ρ' shp region' Vs).heap.length ∧
    (cMachineOS ρ shp region Vs).heap.take (BT.nleaves shp + 3 + region.length) =
      slotHeap ρ (BT.nleaves shp) ++ region ∧
    ∀ i, (i < 3 ∨ BT.nleaves shp + 3 + region.length ≤ i) →
      (cMachineOS ρ shp region Vs).heap[i]? = (cMachineOS ρ' shp region' Vs).heap[i]? := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  let h0' := slotHeap ρ' N ++ region'
  have h0l : h0.length = h0'.length := by simp [h0, h0', slotHeap_length, hl]
  obtain ⟨c1, p1, e1, e1'⟩ := pbuild_shape (N + 2) (encO shp 0) h0 h0' h0l
  have h1l : (h0 ++ c1).length = (h0' ++ c1).length := by simp [h0l]
  obtain ⟨cs, e2, e2', e3⟩ := addStmtsOS_shape p1 (h0.length - 1) Vs Memo.empty _ _ h1l
  have hH : cHeapOS ρ shp region Vs = addStmtsOS p1 (h0.length - 1) (h0 ++ c1) Memo.empty Vs := by
    show addStmtsOS (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) (pbuild (N + 2) h0 (encO shp 0)).1 Memo.empty Vs = _
    rw [e1]
  have hH' : cHeapOS ρ' shp region' Vs = addStmtsOS p1 (h0.length - 1) (h0' ++ c1) Memo.empty Vs := by
    show addStmtsOS (pbuild (N + 2) h0' (encO shp 0)).2 (h0'.length - 1) (pbuild (N + 2) h0' (encO shp 0)).1 Memo.empty Vs = _
    rw [e1', h0l]
  have hA : (cHeapOS ρ shp region Vs).1 = h0 ++ (c1 ++ cs) := by rw [hH, e2]; simp
  have hA' : (cHeapOS ρ' shp region' Vs).1 = h0' ++ (c1 ++ cs) := by rw [hH', e2']; simp
  have hR : (cHeapOS ρ shp region Vs).2 = (cHeapOS ρ' shp region' Vs).2 := by rw [hH, hH', e3]
  have hlen : h0.length = N + 3 + region.length := by simp [h0, slotHeap_length]
  refine ⟨?_, ?_, hR, ?_, ?_, fun i hi => ?_⟩
  · show (cHeapOS ρ shp region Vs).2.getD 0 0 = (cHeapOS ρ' shp region' Vs).2.getD 0 0
    rw [hR]
  · show (cHeapOS ρ shp region Vs).1.length = (cHeapOS ρ' shp region' Vs).1.length
    rw [hA, hA']; simp [h0l]
  · show ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil]).length = ((cHeapOS ρ' shp region' Vs).1 ++ [Cell.nil]).length
    rw [hA, hA']; simp [h0l]
  · show ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil]).take _ = _
    rw [hA, List.append_assoc, ← hlen, List.take_left']
    rfl
  · show ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil])[i]? = ((cHeapOS ρ' shp region' Vs).1 ++ [Cell.nil])[i]?
    have eL : (cHeapOS ρ shp region Vs).1 ++ [Cell.nil] = h0 ++ ((c1 ++ cs) ++ [Cell.nil]) := by
      rw [hA, List.append_assoc]
    have eL' : (cHeapOS ρ' shp region' Vs).1 ++ [Cell.nil] = h0' ++ ((c1 ++ cs) ++ [Cell.nil]) := by
      rw [hA', List.append_assoc]
    rw [eL, eL']
    refine getElem_agree h0l fun hi' => ?_
    rcases hi with hi | hi
    · show (slotHeap ρ N ++ region)[i]? = (slotHeap ρ' N ++ region')[i]?
      rw [List.getElem?_append_left (by rw [slotHeap_length]; omega),
        List.getElem?_append_left (by rw [slotHeap_length]; omega)]
      unfold slotHeap
      rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
    · omega

end CompM

namespace Circuit

open B Compose CompM Stmt Mach Wit

/-- `sput` keeps the fields small. -/
theorem sput_fitsB {Bd : Nat} {h : List Cell} {m : Memo} {c : Cell} (hf : FitsB Bd h) (hm : MemoOK h m)
    (hc : (cellFields c).1 < max (h.length + 1) Bd ∧ (cellFields c).2 < max (h.length + 1) Bd) :
    FitsB Bd (sput h m c).1 ∧ (sput h m c).2.2 < (sput h m c).1.length ∧ h.length ≤ (sput h m c).1.length := by
  unfold sput
  split
  · next q hq =>
    have := (hm c q hq).1
    exact ⟨hf, (List.getElem?_eq_some_iff.mp this).1, Nat.le_refl _⟩
  · exact ⟨fitsB_push hf hc, by simp, by simp⟩

/-- **The shared builder keeps the fields small**: a pointer below the
    heap's length, an atom below `Bd`. -/
theorem obuildS_fitsB (Bd : Nat) : ∀ (t : OTerm) (h : List Cell) (m : Memo), FitsB Bd h → MemoOK h m →
    (∀ x, Occ x t → x < Bd) →
    FitsB Bd (obuildS h m t).1 ∧ (obuildS h m t).2.2 < (obuildS h m t).1.length ∧
      h.length ≤ (obuildS h m t).1.length
  | .S, h, m, hf, hm, _ => sput_fitsB hf hm ⟨lt_max_left (Nat.succ_pos _), lt_max_left (Nat.succ_pos _)⟩
  | .K, h, m, hf, hm, _ => sput_fitsB hf hm ⟨lt_max_left (Nat.succ_pos _), lt_max_left (Nat.succ_pos _)⟩
  | .I, h, m, hf, hm, _ => sput_fitsB hf hm ⟨lt_max_left (Nat.succ_pos _), lt_max_left (Nat.succ_pos _)⟩
  | .var x, h, m, hf, hm, hv =>
    sput_fitsB hf hm ⟨lt_max_right (hv x (.var x)), lt_max_left (Nat.succ_pos _)⟩
  | .app f a, h, m, hf, hm, hv => by
    obtain ⟨f1, p1, l1⟩ := obuildS_fitsB Bd f h m hf hm (fun x hx => hv x (.left _ hx))
    obtain ⟨_, _, _, _, m1⟩ := obuildS_spec f h m hm
    obtain ⟨f2, p2, l2⟩ := obuildS_fitsB Bd a (obuildS h m f).1 (obuildS h m f).2.1 f1 m1
      (fun x hx => hv x (.right _ hx))
    obtain ⟨_, _, _, _, m2⟩ := obuildS_spec a (obuildS h m f).1 (obuildS h m f).2.1 m1
    obtain ⟨f3, p3, l3⟩ := sput_fitsB (c := .app (obuildS h m f).2.2
        (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.2) f2 m2
      ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩
    have e : obuildS h m (.app f a) = sput (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).1
        (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.1
        (.app (obuildS h m f).2.2 (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.2) := rfl
    rw [e]
    exact ⟨f3, p3, by omega⟩

/-- `addStmtsOS` keeps the fields small, and its roots point into the heap. -/
theorem addStmtsOS_fitsB (Bd pe wr : Nat) : ∀ (Vs : List OTerm) (h : List Cell) (m : Memo), FitsB Bd h →
    MemoOK h m → pe < h.length → wr < h.length → (∀ V ∈ Vs, ∀ x, Occ x V → x < Bd) →
    FitsB Bd (addStmtsOS pe wr h m Vs).1 ∧
      (∀ r ∈ (addStmtsOS pe wr h m Vs).2, r < (addStmtsOS pe wr h m Vs).1.length) ∧
      h.length ≤ (addStmtsOS pe wr h m Vs).1.length
  | [], h, _, hf, _, _, _, _ => by
    simp only [addStmtsOS]
    exact ⟨hf, (fun _ h' => nomatch h'), Nat.le_refl _⟩
  | P :: Vs, h, m, hf, hm, hpe, hwr, hv => by
    obtain ⟨f2, p2, l2⟩ := obuildS_fitsB Bd P h m hf hm (hv P List.mem_cons_self)
    obtain ⟨_, _, _, _, mP⟩ := obuildS_spec P h m hm
    let r := obuildS h m P
    have p2' : r.2.2 < r.1.length := p2
    have l2' : h.length ≤ r.1.length := l2
    have f2' : FitsB Bd r.1 := f2
    have mP' : MemoOK r.1 r.2.1 := mP
    have a1 : (cellFields (Cell.app r.2.2 pe)).1 < max (r.1.length + 1) Bd ∧
        (cellFields (Cell.app r.2.2 pe)).2 < max (r.1.length + 1) Bd := by
      simp only [cellFields]; exact ⟨lt_max_left (by omega), lt_max_left (by omega)⟩
    have g1 := fitsB_push f2' a1
    have a2 : (cellFields (Cell.app r.1.length wr)).1 < max ((r.1 ++ [Cell.app r.2.2 pe]).length + 1) Bd ∧
        (cellFields (Cell.app r.1.length wr)).2 < max ((r.1 ++ [Cell.app r.2.2 pe]).length + 1) Bd := by
      simp only [cellFields, List.length_append, List.length_singleton]
      exact ⟨lt_max_left (by omega), lt_max_left (by omega)⟩
    have g2 := fitsB_push g1 a2
    have hl : (r.1 ++ [Cell.app r.2.2 pe] ++ [Cell.app r.1.length wr]).length = r.1.length + 2 := by simp
    have e : r.1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr] =
        r.1 ++ [Cell.app r.2.2 pe] ++ [Cell.app r.1.length wr] := by simp
    obtain ⟨i1, i2, i3⟩ := addStmtsOS_fitsB Bd pe wr Vs _ r.2.1 g2
      (by rw [← e]; exact mP'.grow _) (by rw [hl]; omega) (by rw [hl]; omega)
      (fun V hV => hv V (List.mem_cons_of_mem _ hV))
    show FitsB Bd (addStmtsOS pe wr (r.1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr]) r.2.1 Vs).1 ∧
      (∀ x ∈ (r.1.length + 1) :: (addStmtsOS pe wr (r.1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr]) r.2.1 Vs).2,
          x < (addStmtsOS pe wr (r.1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr]) r.2.1 Vs).1.length) ∧
      h.length ≤ (addStmtsOS pe wr (r.1 ++ [Cell.app r.2.2 pe, Cell.app r.1.length wr]) r.2.1 Vs).1.length
    rw [e]
    refine ⟨i1, fun x hx => ?_, by rw [hl] at i3; omega⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hl] at i3; omega
    · exact i2 x hx

/-- **The shared machine's fields are small**, as `cMachineO_fitsB`. -/
theorem cMachineOS_fitsB (Bd : Nat) (ρ : Nat → Bool) (shp : BT) (region : List Cell) (Vs : List OTerm)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    (hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < Bd) :
    FitsB Bd (cMachineOS ρ shp region Vs).heap ∧
      (∀ r ∈ (cHeapOS ρ shp region Vs).2, r < (cMachineOS ρ shp region Vs).heap.length) ∧
      combRoot ρ shp region < (cMachineOS ρ shp region Vs).heap.length := by
  let N := BT.nleaves shp
  let h0 := slotHeap ρ N ++ region
  have hwf := slots_wf ρ N hr
  have hl0 : N + 3 ≤ h0.length := by simp [h0, slotHeap_length]
  have f0 : FitsB Bd h0 := by
    intro c hc
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hc
    have := hwf i c (by rw [List.getElem?_eq_getElem hi, e])
    cases c with
    | app a b =>
      simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩
    | S | K | I => exact ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩
    | nil | cons _ _ | atom _ => simp [cellOK] at this
  have hv0 : ∀ x, Occ x (encO shp 0) → (x < N + 2 → slotPtr x < h0.length) ∧ (¬ x < N + 2 → x < Bd) := by
    intro x hx
    have := encO_occ shp 0 x hx
    have hN : BT.nleaves shp = N := rfl
    rw [hN] at this
    refine ⟨fun _ => ?_, fun hn => absurd (by omega) hn⟩
    rcases x with _ | _ | x
    · show 0 < h0.length; omega
    · show 2 < h0.length; omega
    · show x + 3 < h0.length; omega
  obtain ⟨f1, p1, l1⟩ := pbuild_fitsB (N + 2) Bd (encO shp 0) h0 f0 hv0
  obtain ⟨f2, rts, l2⟩ := addStmtsOS_fitsB Bd (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) Vs _ Memo.empty f1
    (MemoOK.empty _) p1 (by omega) hv
  refine ⟨fitsB_push f2 ⟨lt_max_left (by simp only [cellFields]; omega), lt_max_left (by simp only [cellFields]; omega)⟩,
    fun r hr => ?_, ?_⟩
  · have := rts r hr
    show r < ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil]).length
    rw [List.length_append, List.length_singleton]
    exact Nat.lt_succ_of_lt this
  · have e : (cHeapOS ρ shp region Vs).1 =
        (addStmtsOS (pbuild (N + 2) h0 (encO shp 0)).2 (h0.length - 1) (pbuild (N + 2) h0 (encO shp 0)).1 Memo.empty Vs).1 := rfl
    show (pbuild (N + 2) h0 (encO shp 0)).2 < ((cHeapOS ρ shp region Vs).1 ++ [Cell.nil]).length
    rw [List.length_append, List.length_singleton, e]
    omega

end Circuit
