import Ski.Circuit.CompDTraceMem

/-!
# A jet call's writes are in memory

**`DecT.call_writes`**: for a jet row `DecJet.decRowI` accepts, the memory
holds, from its counter, the cells `DecJet.outCells` lays out (`wrs`), so
every row of the call writes memory cells (`WritesOK`): the subject's
wrapper and `errT`, the head's wrapper or filler, and along the head's
bits' chain each rewritten bit's `Cons` and the link to it.
-/

namespace Circuit

open B Air

namespace DecT

section
variable {A : List Cell}

theorem wrs_cells : ∀ {c : Nat} {L : List Cell}, wrs A c L = true → Cells A c L
  | _, [], _ => fun i h => absurd h (Nat.not_lt_zero _)
  | c, w :: ws, h => by
    unfold wrs at h
    rw [Bool.and_eq_true] at h
    have h1 : A[c]? = some w := beq_iff_eq.1 h.1
    have ih := wrs_cells h.2
    intro i hi
    cases i with
    | zero =>
      obtain ⟨hl, _⟩ := List.getElem?_eq_some_iff.1 h1
      exact ⟨by omega, by rw [Nat.add_zero, List.getD_eq_getElem?_getD, h1]; rfl⟩
    | succ i =>
      have := ih i (by simp at hi; omega)
      rw [show c + (i + 1) = c + 1 + i by omega]
      exact this

theorem Cells_l {c : Nat} {L1 L2 : List Cell} (h : Cells A c (L1 ++ L2)) : Cells A c L1 := fun i hi => by
  have := h i (by rw [List.length_append]; omega)
  rw [List.getElem_append_left hi] at this
  exact this

theorem Cells_r {c : Nat} {L1 L2 : List Cell} (h : Cells A c (L1 ++ L2)) : Cells A (c + L1.length) L2 := fun i hi => by
  have := h (L1.length + i) (by rw [List.length_append]; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rw [Nat.add_assoc]; exact this

theorem Cells_congr {c c' : Nat} {L L' : List Cell} (hc : c = c') (hL : L = L') (h : Cells A c L) : Cells A c' L' := by
  subst hc hL; exact h

theorem At_congr {a a' : Nat} {x x' : Cell} (ha : a = a') (hx : x = x') (h : At A a x) : At A a' x' := by
  subst ha hx; exact h

theorem Cells_at {c : Nat} {L : List Cell} (h : Cells A c L) (i : Nat) (hi : i < L.length) {a : Nat} {x : Cell}
    (ha : c + i = a) (hx : L[i] = x) : At A a x := by
  subst ha hx; exact h i hi

end

/-- A row that writes nothing. -/
theorem quietW {A : List Cell} {d : DR} (h1 : d.kind = 1 ∨ d.kind = 2 → d.ro = 2) (h3 : d.kind = 3 ∨ d.kind = 4 → d.bw = false) :
    WritesOK A d := by
  refine ⟨fun hk hr => ?_, fun hk hr => ?_, fun hk hr => ?_, fun hk hr => ?_, fun hk hr => ?_, fun hk hb => ?_,
    fun hk hb => ?_, fun hk hb => ?_, fun hk hb => ?_⟩ <;>
  first
    | (have := h1 (.inl hk); rw [this] at hr; exact absurd hr (by decide))
    | (have := h1 (.inr hk); rw [this] at hr; exact absurd hr (by decide))
    | (have := h3 (.inl hk); rw [this] at hb; cases hb)
    | (have := h3 (.inr hk); rw [this] at hb; cases hb)

section
variable {A : List Cell} {key : Nat}

theorem bits_quiet {m : Bool} : ∀ (n p lvl : Nat) (wc : Nat) (term : Bool),
    ∀ d ∈ bitsRows A key m n p lvl false wc term, WritesOK A d
  | 0, _, _, _, _ => by intro d hd; cases hd
  | n + 1, p, lvl, wc, term => by
    intro d hd
    unfold bitsRows at hd
    split at hd
    · rw [List.mem_singleton] at hd; subst hd; exact quietW (fun h => by simp only [nilRow] at h; exact absurd h (by decide)) (fun _ => rfl)
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact quietW (fun h => by simp only [consRow] at h; exact absurd h (by decide)) (fun _ => rfl)
        · rw [show (false && !_) = false from rfl] at hd
          exact bits_quiet n _ _ _ _ d hd
      · split at hd
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact quietW (fun h => by simp only [indRow] at h; exact absurd h (by decide)) (fun h => by simp only [indRow] at h; exact absurd h (by decide))
          · exact bits_quiet n _ _ _ _ d hd
        · cases hd

theorem noun2_quiet : ∀ (n p : Nat), ∀ d ∈ nounRows A key n p 2, WritesOK A d
  | 0, _ => by intro d hd; cases hd
  | n + 1, p => by
    intro d hd
    unfold nounRows at hd
    split at hd
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact quietW (fun _ => rfl) (fun h => by simp only [atomRow] at h; exact absurd h (by decide))
      · exact bits_quiet _ _ _ _ _ d hd
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact quietW (fun _ => rfl) (fun h => by simp only [cellRow] at h; exact absurd h (by decide))
        · rcases List.mem_append.1 hd with hd | hd
          · exact noun2_quiet n _ d hd
          · exact noun2_quiet n _ d hd
      · split at hd
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact quietW (fun _ => rfl) (fun h => by simp only [indRow] at h; exact absurd h (by decide))
          · exact noun2_quiet n _ d hd
        · cases hd

theorem dropped_iff (b : Bool) (bs : List Bool) : DecJet.dropped (b :: bs) = (b && bs.isEmpty) := by
  unfold DecJet.dropped
  cases b <;> cases bs <;> rfl

/-- **The head's bits' chain writes its `Cons` cells and links**, given them
    in memory from its level on, and the empty head's link. -/
theorem bitsW : ∀ (n p l : Nat) (bw : Bool) (wc : Nat) (term : Bool) {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.readBitsI (A.take key) n p = some (bs, sks) → DecJet.canonB bs = true →
    (bw = true → bs ≠ [] → Cells A (key + 12 + 6 * l) (DecJet.bitCells (key + 12 + 6 * l) bs sks) ∧
      At A (key + 11 + 6 * l) (.app 0 (if DecJet.dropped bs then 0 else key + 12 + 6 * l))) →
    (bw = true → bs = [] → At A (key + 11) (.app 0 0)) →
    ∀ d ∈ bitsRows A key false n p l bw wc term, WritesOK A d
  | 0, _, _, _, _, _, _, _, h, _, _, _ => by cases h
  | n + 1, p, l, bw, wc, term, bs, sks, h, hcn, hinv, hnil => by
    intro d hd
    rcases readBitsI_cases h with ⟨hK, rfl⟩ | ⟨b, sk, bs', sks', hK, hr, hb, rfl, rfl⟩ | ⟨R, hK, hr, hi, hb⟩
    · rw [bitsRows_K hK, List.mem_singleton] at hd; subst hd
      refine ⟨fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun h => by simp only [nilRow] at h; exact absurd h (by decide), fun _ hbw => hnil hbw rfl⟩
    · rw [bitsRows_cons hK hr, restNil_eq hb] at hd
      obtain ⟨_, h3, h5, h14⟩ := consReads (d := consRow key p false l bw wc b bs'.isEmpty) rfl hr rfl
      rcases List.mem_cons.1 hd with rfl | hd
      · -- the row itself
        refine ⟨fun h => by simp only [consRow] at h; exact absurd h (by decide), fun h => by simp only [consRow] at h; exact absurd h (by decide), fun h => by simp only [consRow] at h; exact absurd h (by decide), fun h => by simp only [consRow] at h; exact absurd h (by decide), fun h => by simp only [consRow] at h; exact absurd h (by decide), fun _ hbw hnl => ?_, fun _ hbw hbit hl => ?_, fun _ hbw => ?_,
          fun h => by simp only [consRow] at h; exact absurd h (by decide)⟩
        · obtain ⟨hC, _⟩ := hinv hbw (List.cons_ne_nil _ _)
          rw [h3, h5]
          simp only [consRow] at hbw hnl ⊢
          cases b with
          | false =>
            simp only [DecJet.bitCells] at hC
            have := Cells_l (L2 := [.app 0 (if DecJet.dropped bs' then 0 else key + 12 + 6 * l + 6)] ++
              DecJet.bitCells (key + 12 + 6 * l + 6) bs' sks')
              (L1 := [.app 0 (key + 12 + 6 * l + 1), .app (key + 12 + 6 * l + 2) (key + 12 + 6 * l + 5),
                .app sk.s (key + 12 + 6 * l + 3), .app sk.c5 (key + 12 + 6 * l + 4), .app 0 0]) hC
            exact this
          | true =>
            have hne' : bs' ≠ [] := fun e => hnl ⟨rfl, by rw [e]; rfl⟩
            simp only [DecJet.bitCells, if_neg hne'] at hC
            exact Cells_l (L2 := [.app 0 sk.t]) hC
        · obtain ⟨hC, _⟩ := hinv hbw (List.cons_ne_nil _ _)
          rw [h14]
          simp only [consRow] at hbw hbit hl ⊢
          subst hbit
          have hne' : bs' ≠ [] := fun e => by rw [e] at hl; cases hl
          simp only [DecJet.bitCells, if_neg hne'] at hC
          exact Cells_at hC 5 (by simp) rfl rfl
        · obtain ⟨_, hL⟩ := hinv hbw (List.cons_ne_nil _ _)
          simp only [consRow] at hbw ⊢
          rw [dropped_iff] at hL
          exact hL
      · by_cases he : bs' = []
        · subst he
          have hbt : b = true := by simpa [DecJet.canonB] using hcn
          subst hbt
          have e : (bw && !true) = false := by cases bw <;> rfl
          rw [e] at hd
          exact bits_quiet _ _ _ _ _ d hd
        · have hne' := he
          have hl : bs'.isEmpty = false := by cases bs' with | nil => exact absurd rfl he | cons _ _ => rfl
          rw [hl] at hd
          refine bitsW n sk.t (l + 1) _ _ _ hb (DecJet.canonB_tail hcn) (fun hbw _ => ?_)
            (fun _ e => absurd e hne') d hd
          have hbw' : bw = true ∧ b = false := by cases bw <;> cases b <;> simp at hbw ⊢
          obtain ⟨rfl, rfl⟩ := hbw'
          obtain ⟨hC, _⟩ := hinv rfl (List.cons_ne_nil _ _)
          simp only [DecJet.bitCells] at hC
          have e6 : key + 12 + 6 * l + 6 = key + 12 + 6 * (l + 1) := by omega
          constructor
          · have := Cells_r (L1 := [.app 0 (key + 12 + 6 * l + 1), .app (key + 12 + 6 * l + 2) (key + 12 + 6 * l + 5),
              .app sk.s (key + 12 + 6 * l + 3), .app sk.c5 (key + 12 + 6 * l + 4), .app 0 0,
              .app 0 (if DecJet.dropped bs' then 0 else key + 12 + 6 * l + 6)]) hC
            exact Cells_congr (by simp; omega) (by rw [e6]) this
          · exact Cells_at hC 5 (by simp) (by omega) (by simp [e6])
    · rw [bitsRows_ind hK hr hi] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact quietW (fun h => by simp only [indRow] at h; exact absurd h (by decide)) (fun h => by simp only [indRow] at h; exact absurd h (by decide))
      · exact bitsW n R l bw wc term hb hcn hinv hnil d hd

/-- **The head's rows write**, its atom through thunks: the `Atom` wrapper
    and the bits' chain. -/
theorem headW : ∀ {n q a : Nat} {ask : DecJet.AtomSk} {bs : List Bool} {sks : List DecJet.ConsSk} {rt : Nat},
    DecJet.headAtom (A.take key) n q = some (a, ask) →
    DecJet.readBitsI (A.take key) (A.take key).length ask.b = some (bs, sks) → DecJet.canonB bs = true →
    Cells A (key + 7) (DecJet.atomCells (key + 7) ask rt) →
    (bs ≠ [] → Cells A (key + 12) (DecJet.bitCells (key + 12) bs sks) ∧
      At A (key + 11) (.app 0 (if DecJet.dropped bs then 0 else key + 12))) →
    (bs = [] → At A (key + 11) (.app 0 0)) →
    ∀ d ∈ nounRows A key n q 1, WritesOK A d
  | 0, _, _, _, _, _, _, h, _, _, _, _, _ => nomatch h
  | n + 1, q, a, ask, bs, sks, rt, h, hb, hcn, hA, hB, hN => by
    intro d hd
    unfold DecJet.headAtom at h
    cases ha : DecJet.readAtom (A.take key) q with
    | some ask' =>
      rw [ha] at h; cases h
      rw [nounRows_atom ha] at hd
      obtain ⟨_, h0, h6, h12, h18, _⟩ := atomReads (d := atomRow key q 1) rfl ha
      rcases List.mem_cons.1 hd with rfl | hd
      · refine ⟨fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun _ _ => ?_, fun _ h => by simp only [atomRow] at h; exact absurd h (by decide),
          fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide)⟩
        have := Cells_l (L1 := [.app ask.a1 (key + 7 + 1), .app ask.a2 (key + 7 + 2), .app ask.a3 (key + 7 + 3),
          .app ask.si (key + 7 + 4)]) (L2 := [.app 0 rt]) hA
        show Cells A (key + 7) [.app (sl A (atomRow key q 1) 0).2.2.1 (key + 8), _, _, _]
        rw [h0, h6, h12, h18]
        exact this
      · refine bitsW _ _ 0 true 0 false hb hcn (fun _ hne => ⟨?_, ?_⟩) (fun _ he => hN he) d hd
        · exact Cells_congr (by omega) rfl (hB hne).1
        · exact At_congr (by omega) (by simp) (hB hne).2
    | none =>
      rw [ha] at h; dsimp only at h
      cases hi : DecJet.readInd (A.take key) q with
      | none => rw [hi] at h; cases h
      | some R =>
        rw [hi] at h; dsimp only at h
        rw [nounRows_ind ha (DecJet.readInd_cellI hi) hi] at hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact quietW (fun h => by simp only [indRow] at h; exact absurd h (by decide)) (fun h => by simp only [indRow] at h; exact absurd h (by decide))
        · exact headW h hb hcn hA hB hN d hd

/-- **The head's rows write**, a cell through thunks: the filler. -/
theorem headCW : ∀ {n q : Nat} {s : DecJet.Nn}, DecJet.readNnI (A.take key) n q = some s →
    DecJet.headAtom (A.take key) n q = none → Cells A (key + 7) (List.replicate 5 (.app 0 0)) → ∀ d ∈ nounRows A key n q 1, WritesOK A d
  | 0, _, _, h, _, _ => nomatch h
  | n + 1, q, s, h, hh, hF => by
    intro d hd
    rcases readNnI_cases h with ⟨sk, bs, sks, ha, hb, hc, rfl⟩ | ⟨sk, hh', tt, ha, hc, h1, h2, rfl⟩ |
      ⟨R, ha, hc, hi, hR⟩
    · unfold DecJet.headAtom at hh; rw [ha] at hh; cases hh
    · rw [nounRows_cell ha hc] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact ⟨fun _ h => by simp only [cellRow] at h; exact absurd h (by decide),
          fun _ h => by simp only [cellRow] at h; exact absurd h (by decide), fun _ _ => hF,
          fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide)⟩
      · rcases List.mem_append.1 hd with hd | hd
        · exact noun2_quiet _ _ d hd
        · exact noun2_quiet _ _ d hd
    · rw [nounRows_ind ha hc hi] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact quietW (fun h => by simp only [indRow] at h; exact absurd h (by decide)) (fun h => by simp only [indRow] at h; exact absurd h (by decide))
      · unfold DecJet.headAtom at hh; rw [ha] at hh; dsimp only at hh; rw [hi] at hh; dsimp only at hh
        exact headCW hR hh hF d hd

end

/-- The subject's `Cell` row writes the wrapper, and `errT` on a crash. -/
theorem subjW {A : List Cell} {key p : Nat} {csk : DecJet.CellSk} {err : Bool} {wc : Nat}
    (hc : DecJet.readCellI (A.take key) p = some csk) {rest : List Cell}
    (hC : Cells A key (DecJet.cellCells key csk ++ rest))
    (hE : err = true → Cells A (key + 12) (DecJet.errCells (key + 12))) :
    WritesOK A (cellRow key p 0 err wc (iktOf (A.take key) csk.kt)) := by
  obtain ⟨_, h2, h8, h14, h15, h17, _, _⟩ := cellReads (d := cellRow key p 0 err wc (iktOf (A.take key) csk.kt)) rfl hc rfl
  refine ⟨fun _ _ => ?_, fun _ _ he => ?_, fun _ h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide),
    fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide),
    fun h => by simp only [cellRow] at h; exact absurd h (by decide), fun h => by simp only [cellRow] at h; exact absurd h (by decide)⟩
  · rw [h2, h8, h14, h15, h17]
    exact Cells_l hC
  · exact hE he

theorem subjRows_W {A : List Cell} {key : Nat} : ∀ {n p : Nat} {s : DecJet.Nn}
    {csk : Option DecJet.CellSk} {ask : Option DecJet.AtomSk} {sks : List DecJet.ConsSk} {cells : List Cell}
    {root : Nat},
    DecJet.readSubjI (A.take key) n p = some (s, csk, ask, sks) →
    DecJet.outCells key s csk ask sks = some (cells, root) → Cells A key cells →
    ∀ d ∈ subjRows A key n p, WritesOK A d
  | 0, _, _, _, _, _, _, _, h, _, _ => nomatch h
  | n + 1, p, s, csk, ask, sks, cells, root, hrd, hout, hC => by
    intro d hd
    rcases readSubjI_cases hrd with ⟨R, ha, hc, hi, hR⟩ | ⟨sk, bs, ha, hb, hcn, rfl, rfl, rfl⟩ |
      ⟨csk', a, ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ | ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl, rfl⟩
    · rw [subjRows_ind ha hc hi] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact quietW (fun h => by simp only [indRow] at h; exact absurd h (by decide)) (fun h => by simp only [indRow] at h; exact absurd h (by decide))
      · exact subjRows_W hR hout hC d hd
    · -- an atom subject: `errT` at the key
      rw [subjRows_atom ha] at hd
      simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      rcases List.mem_cons.1 hd with rfl | hd
      · refine ⟨fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun _ h => by simp only [atomRow] at h; exact absurd h (by decide),
          fun _ _ => hC, fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide), fun h => by simp only [atomRow] at h; exact absurd h (by decide)⟩
      · exact bits_quiet _ _ _ _ _ d hd
    · -- a cell subject, its head an atom
      rw [subjRows_cell ha hc] at hd
      cases bs with
      | nil =>
        simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        rcases List.mem_cons.1 hd with rfl | hd
        · refine subjW hc (rest := DecJet.atomCells (key + 7) ask' 0 ++ DecJet.errCells (key + 12))
            (by rw [← List.append_assoc]; exact hC) (fun _ => ?_)
          have := Cells_r hC
          simp only [List.length_append, DecJet.cellCells_length, DecJet.atomCells_length] at this
          exact this
        · rcases List.mem_append.1 hd with hd | hd
          · refine headW (rt := 0) hah hb hcn ?_ (fun h => absurd rfl h) (fun _ => ?_) d hd
            · have := Cells_r (Cells_l hC); rw [DecJet.cellCells_length] at this; exact this
            · exact Cells_at (Cells_l hC) 11 (by simp [DecJet.cellCells, DecJet.atomCells]) rfl rfl
          · exact noun2_quiet _ _ d hd
      | cons b bs =>
        simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        have hv : headV A key csk'.h = (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length) := by
          unfold headV; rw [hah]; dsimp only; rw [hb]
        rcases List.mem_cons.1 hd with rfl | hd
        · rw [hv]
          exact subjW hc (rest := DecJet.atomCells (key + 7) ask' (DecJet.bitsRoot (key + 12) (b :: bs)) ++
            DecJet.bitCells (key + 12) (b :: bs) sks) (by rw [← List.append_assoc]; exact hC) (fun h => by cases h)
        · rcases List.mem_append.1 hd with hd | hd
          · refine headW (rt := DecJet.bitsRoot (key + 12) (b :: bs)) hah hb hcn ?_ (fun _ => ⟨?_, ?_⟩)
              (fun e => absurd e (List.cons_ne_nil _ _)) d hd
            · have := Cells_r (Cells_l hC); rw [DecJet.cellCells_length] at this; exact this
            · have := Cells_r hC
              simp only [List.length_append, DecJet.cellCells_length, DecJet.atomCells_length] at this
              exact Cells_congr (by omega) rfl this
            · exact Cells_at (Cells_l hC) 11 (by simp [DecJet.cellCells, DecJet.atomCells]) (by omega)
                (by simp [DecJet.cellCells, DecJet.atomCells, DecJet.bitsRoot])
          · exact noun2_quiet _ _ d hd
    · -- a cell subject, its head a cell
      rw [subjRows_cell ha hc] at hd
      cases hh with
      | atom bs => exact (nn_cell_noatom hh' (Nat.le_refl _) hah).elim
      | cell x y =>
        simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        have hv : headV A key csk'.h = (true, 0) := by unfold headV; rw [hah]
        rcases List.mem_cons.1 hd with rfl | hd
        · rw [hv]
          refine subjW hc (rest := List.replicate 5 (.app 0 0) ++ DecJet.errCells (key + 12))
            (by rw [← List.append_assoc]; exact hC) (fun _ => ?_)
          have := Cells_r hC
          simp only [List.length_append, DecJet.cellCells_length, List.length_replicate] at this
          exact this
        · rcases List.mem_append.1 hd with hd | hd
          · refine headCW hh' hah ?_ d hd
            have := Cells_r (Cells_l hC)
            rw [DecJet.cellCells_length] at this
            exact this
          · exact noun2_quiet _ _ d hd

/-- **Every row of a jet call writes memory cells.** -/
theorem call_writes {M : List Cell} {J : Nat} {r r' : Air.Row} (h : DecJet.decRowI M J r = some r') :
    ∀ d ∈ callRows M r.ctr (subj M r), WritesOK M d := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, _, _, hpop, hrd, _, hout, hw, rfl⟩ := DecJet.decRowI_unfold h
  rw [popN_subj hpop]
  exact subjRows_W hrd hout (wrs_cells hw)

end DecT

end Circuit
