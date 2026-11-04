import Ski.Circuit.CompDTraceMem

/-!
# A jet call's writes are in memory

**`DecT.call_writes`**: for a jet row `DecJet.decRow` accepts, the memory
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
    | (have := h1 (.inl hk); omega)
    | (have := h1 (.inr hk); omega)
    | (have := h3 (.inl hk); rw [this] at hb; cases hb)
    | (have := h3 (.inr hk); rw [this] at hb; cases hb)

section
variable {A : List Cell} {key : Nat}

theorem bits_quiet {m : Bool} : ∀ (n p lvl : Nat) (wc : Nat), ∀ d ∈ bitsRows A key m n p lvl false wc, WritesOK A d
  | 0, _, _, _ => by intro d hd; cases hd
  | n + 1, p, lvl, wc => by
    intro d hd
    unfold bitsRows at hd
    split at hd
    · rw [List.mem_singleton] at hd; subst hd; exact quietW (fun h => by simp [nilRow] at h) (fun _ => rfl)
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact quietW (fun h => by simp [consRow] at h) (fun _ => rfl)
        · split at hd
          · cases hd
          · rw [show (false && !_) = false from rfl] at hd
            exact bits_quiet n _ _ _ d hd
      · cases hd

theorem noun2_quiet : ∀ (n p : Nat), ∀ d ∈ nounRows A key n p 2, WritesOK A d
  | 0, _ => by intro d hd; cases hd
  | n + 1, p => by
    intro d hd
    unfold nounRows at hd
    split at hd
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact quietW (fun _ => rfl) (fun h => by simp [atomRow] at h)
      · exact bits_quiet _ _ _ _ d hd
    · split at hd
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact quietW (fun _ => rfl) (fun h => by simp [cellRow] at h)
        · rcases List.mem_append.1 hd with hd | hd
          · exact noun2_quiet n _ d hd
          · exact noun2_quiet n _ d hd
      · cases hd

theorem dropped_iff (b : Bool) (bs : List Bool) : DecJet.dropped (b :: bs) = (b && bs.isEmpty) := by
  unfold DecJet.dropped
  cases b <;> cases bs <;> rfl

/-- **The head's bits' chain writes its `Cons` cells and links**, given them
    in memory from its level on. -/
theorem bitsW : ∀ (n p l : Nat) (bw : Bool) (wc : Nat) {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.readBits (A.take key) n p = some (bs, sks) → bs ≠ [] →
    (bw = true → Cells A (key + 12 + 6 * l) (DecJet.bitCells (key + 12 + 6 * l) bs sks) ∧
      At A (key + 11 + 6 * l) (.app 0 (if DecJet.dropped bs then 0 else key + 12 + 6 * l))) →
    ∀ d ∈ bitsRows A key false n p l bw wc, WritesOK A d
  | 0, _, _, _, _, _, _, h, _, _ => by cases h
  | n + 1, p, l, bw, wc, bs, sks, h, hne, hinv => by
    intro d hd
    unfold bitsRows at hd
    unfold DecJet.readBits at h
    by_cases hK : DecJet.isK (A.take key) p = true
    · rw [if_pos hK] at h; cases h; exact absurd rfl hne
    · rw [if_neg hK] at hd h
      cases hr : DecJet.readCons (A.take key) p with
      | none => rw [hr] at h; cases h
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hr] at hd h
        simp only at hd h
        cases hb : DecJet.readBits (A.take key) n sk.t with
        | none => rw [hb] at h; cases h
        | some q2 =>
          obtain ⟨bs', sks'⟩ := q2
          rw [hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hlast : DecJet.isK (A.take key) sk.t = bs'.isEmpty := by
            cases hk : DecJet.isK (A.take key) sk.t
            · cases bs' with
              | nil => exact absurd rfl (readBits_ne hb hk)
              | cons _ _ => rfl
            · rw [readBits_K hb hk]; rfl
          obtain ⟨_, h3, h5, h14⟩ := consReads (d := consRow key p false l bw wc b (DecJet.isK (A.take key) sk.t)) rfl hr
            rfl rfl (fun hK' => readBits_tail hb hK')
          rcases List.mem_cons.1 hd with rfl | hd
          · -- the row itself
            refine ⟨fun h => by simp [consRow] at h, fun h => by simp [consRow] at h, fun h => by simp [consRow] at h,
              fun h => by simp [consRow] at h, fun h => by simp [consRow] at h,
              fun _ hbw hnl => ?_, fun _ hbw hbit hl => ?_, fun _ hbw => ?_, fun h => by simp [consRow] at h⟩
            · obtain ⟨hC, _⟩ := hinv hbw
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
                have hne' : bs' ≠ [] := fun e => hnl ⟨rfl, by rw [hlast, e]; rfl⟩
                simp only [DecJet.bitCells, if_neg hne'] at hC
                exact Cells_l (L2 := [.app 0 sk.t]) hC
            · obtain ⟨hC, _⟩ := hinv hbw
              rw [h14]
              simp only [consRow] at hbw hbit hl ⊢
              subst hbit
              have hne' : bs' ≠ [] := fun e => by rw [hlast, e] at hl; cases hl
              simp only [DecJet.bitCells, if_neg hne'] at hC
              exact Cells_at hC 5 (by simp) rfl rfl
            · obtain ⟨_, hL⟩ := hinv hbw
              simp only [consRow] at hbw ⊢
              rw [dropped_iff, ← hlast] at hL
              exact hL
          · by_cases hl : DecJet.isK (A.take key) sk.t = true
            · rw [if_pos hl] at hd; cases hd
            · rw [if_neg hl] at hd
              have hne' : bs' ≠ [] := readBits_ne hb (by simpa using hl)
              refine bitsW n sk.t (l + 1) _ _ hb hne' (fun hbw => ?_) d hd
              have hbw' : bw = true ∧ b = false := by cases bw <;> cases b <;> simp at hbw ⊢
              obtain ⟨rfl, rfl⟩ := hbw'
              obtain ⟨hC, _⟩ := hinv rfl
              simp only [DecJet.bitCells] at hC
              have e6 : key + 12 + 6 * l + 6 = key + 12 + 6 * (l + 1) := by omega
              constructor
              · have := Cells_r (L1 := [.app 0 (key + 12 + 6 * l + 1), .app (key + 12 + 6 * l + 2) (key + 12 + 6 * l + 5),
                  .app sk.s (key + 12 + 6 * l + 3), .app sk.c5 (key + 12 + 6 * l + 4), .app 0 0,
                  .app 0 (if DecJet.dropped bs' then 0 else key + 12 + 6 * l + 6)]) hC
                exact Cells_congr (by simp; omega) (by rw [e6]) this
              · exact Cells_at hC 5 (by simp) (by omega) (by simp [e6])

end

theorem nounRows_atom1 {A : List Cell} {key n h : Nat} {ask : DecJet.AtomSk}
    (hah : DecJet.readAtom (A.take key) h = some ask) :
    nounRows A key (n + 1) h 1 = atomRow key h 1 :: bitsRows A key false (n + 1) ask.b 0 true 0 := by
  simp only [nounRows, hah]; rfl

theorem nounRows_cell1 {A : List Cell} {key n h : Nat} {sk : DecJet.CellSk}
    (hah : DecJet.readAtom (A.take key) h = none) (hc : DecJet.readCell (A.take key) h = some sk) :
    nounRows A key (n + 1) h 1 = cellRow key h 1 false 0 :: (nounRows A key n sk.h 2 ++ nounRows A key n sk.t 2) := by
  simp only [nounRows, hah, hc]

theorem bitsRows_K {A : List Cell} {key n p lvl wc : Nat} {m bw : Bool} (hK : DecJet.isK (A.take key) p = true) :
    bitsRows A key m (n + 1) p lvl bw wc = [nilRow key p m lvl bw wc] := by
  simp only [bitsRows, hK, if_true]

theorem readBits_nilK {H : List Cell} {n p : Nat} {sks : List DecJet.ConsSk}
    (h : DecJet.readBits H n p = some ([], sks)) : DecJet.isK H p = true := by
  cases n with
  | zero => cases h
  | succ n =>
    unfold DecJet.readBits at h
    by_cases hK : DecJet.isK H p = true
    · exact hK
    · rw [if_neg hK] at h
      split at h
      · split at h
        · cases h
        · cases h
      · cases h

/-- The subject's `Cell` row writes the wrapper, and `errT` on a crash. -/
theorem subjW {A : List Cell} {key p : Nat} {csk : DecJet.CellSk} {err : Bool} {wc : Nat}
    (hc : DecJet.readCell (A.take key) p = some csk) {rest : List Cell}
    (hC : Cells A key (DecJet.cellCells key csk ++ rest))
    (hE : err = true → Cells A (key + 12) (DecJet.errCells (key + 12))) :
    WritesOK A (cellRow key p 0 err wc) := by
  obtain ⟨_, h2, h8, h14, h15, h17, _, _⟩ := cellReads (d := cellRow key p 0 err wc) rfl hc
  refine ⟨fun _ _ => ?_, fun _ _ he => ?_, fun _ h => by simp [cellRow] at h, fun h => by simp [cellRow] at h,
    fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h,
    fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h⟩
  · rw [h2, h8, h14, h15, h17]
    exact Cells_l hC
  · exact hE he

/-- **Every row of a jet call writes memory cells.** -/
theorem call_writes {M : List Cell} {J : Nat} {r r' : Air.Row} (h : DecJet.decRow M J r = some r') :
    ∀ d ∈ callRows M r.ctr (subj M r), WritesOK M d := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, _, _, hpop, hrd, _, hout, hw, rfl⟩ := DecJet.decRow_unfold h
  rw [popN_subj hpop]
  have hC := wrs_cells hw
  generalize r.ctr = key at hpop hrd hout hC ⊢
  intro d hd
  unfold callRows at hd
  rcases readSubj_cases hrd with ⟨sk, bs, ha, hb, hcn, rfl⟩ | ⟨csk', ask', bs, rr, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ |
    ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl⟩
  · -- an atom subject: `errT` at the key
    rw [ha] at hd
    simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
    obtain ⟨rfl, rfl⟩ := hout
    rcases List.mem_cons.1 hd with rfl | hd
    · refine ⟨fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h,
        fun _ h => by simp [atomRow] at h, fun _ _ => hC, fun h => by simp [atomRow] at h,
        fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h⟩
    · exact bits_quiet _ _ _ _ d hd
  · -- a cell subject, its head an atom
    rw [ha] at hd; simp only at hd; rw [hc] at hd; simp only at hd
    obtain ⟨n, hL⟩ : ∃ n, (M.take key).length = n + 1 := by
      cases hl : (M.take key).length with
      | zero => rw [hl] at hb; cases hb
      | succ k => exact ⟨k, rfl⟩
    rw [hL, nounRows_atom1 hah] at hd
    have hb0 := hb
    rw [hL] at hb
    obtain ⟨_, h0, h6, h12, h18, _⟩ := atomReads (d := atomRow key csk'.h 1) rfl hah
    have hhat : ∀ rt : Nat, Cells M key (DecJet.cellCells key csk' ++ DecJet.atomCells (key + 7) ask' rt ++ []) →
        WritesOK M (atomRow key csk'.h 1) := by
      intro rt hC'
      refine ⟨fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h,
        fun _ _ => ?_, fun _ h => by simp [atomRow] at h, fun h => by simp [atomRow] at h,
        fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h, fun h => by simp [atomRow] at h⟩
      have := Cells_r (Cells_l hC')
      rw [DecJet.cellCells_length] at this
      have := Cells_l (L1 := [.app ask'.a1 (key + 7 + 1), .app ask'.a2 (key + 7 + 2), .app ask'.a3 (key + 7 + 3),
        .app ask'.si (key + 7 + 4)]) (L2 := [.app 0 rt]) this
      show Cells M (key + 7) [.app (sl M (atomRow key csk'.h 1) 0).2.2.1 (key + 8), _, _, _]
      rw [h0, h6, h12, h18]
      exact this
    cases bs with
    | nil =>
      simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      have hK := readBits_nilK hb
      rw [bitsRows_K hK] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · refine subjW hc (rest := DecJet.atomCells (key + 7) ask' 0 ++ DecJet.errCells (key + 12))
          (by rw [← List.append_assoc]; exact hC) (fun _ => ?_)
        have := Cells_r hC
        simp only [List.length_append, DecJet.cellCells_length, DecJet.atomCells_length] at this
        exact this
      · rcases List.mem_append.1 hd with hd | hd
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact hhat 0 (by rw [List.append_nil]; exact Cells_l hC)
          · rw [List.mem_singleton] at hd; subst hd
            refine ⟨fun h => by simp [nilRow] at h, fun h => by simp [nilRow] at h, fun h => by simp [nilRow] at h,
              fun h => by simp [nilRow] at h, fun h => by simp [nilRow] at h, fun h => by simp [nilRow] at h,
              fun h => by simp [nilRow] at h, fun h => by simp [nilRow] at h, fun _ _ => ?_⟩
            exact Cells_at (Cells_l hC) 11 (by simp [DecJet.cellCells, DecJet.atomCells]) rfl rfl
        · exact noun2_quiet _ _ d hd
    | cons b bs =>
      simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      have hv : headV M key csk'.h = (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length) := by
        unfold headV; rw [hah]; simp only; rw [hb0]
      rcases List.mem_cons.1 hd with rfl | hd
      · rw [hv]
        exact subjW hc (rest := DecJet.atomCells (key + 7) ask' (DecJet.bitsRoot (key + 12) (b :: bs)) ++
          DecJet.bitCells (key + 12) (b :: bs) sks) (by rw [← List.append_assoc]; exact hC) (fun h => by cases h)
      · rcases List.mem_append.1 hd with hd | hd
        · rcases List.mem_cons.1 hd with rfl | hd
          · exact hhat _ (by rw [List.append_nil]; exact Cells_l hC)
          · refine bitsW _ _ 0 true 0 hb (List.cons_ne_nil _ _) (fun _ => ⟨?_, ?_⟩) d hd
            · have := Cells_r hC
              simp only [List.length_append, DecJet.cellCells_length, DecJet.atomCells_length] at this
              exact Cells_congr (by omega) rfl this
            · exact Cells_at (Cells_l hC) 11 (by simp [DecJet.cellCells, DecJet.atomCells]) (by omega) rfl
        · exact noun2_quiet _ _ d hd
  · -- a cell subject, its head a cell
    rw [ha] at hd; simp only at hd; rw [hc] at hd; simp only at hd
    cases hh with
    | atom bs => exact absurd hh' (fun h' => readNn_cell h' hah)
    | cell x y =>
      simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      obtain ⟨n, hL⟩ : ∃ n, (M.take key).length = n + 1 := by
        cases hl : (M.take key).length with
        | zero => rw [hl] at hh'; cases hh'
        | succ k => exact ⟨k, rfl⟩
      have hh2 := hh'
      rw [hL] at hh2
      unfold DecJet.readNn at hh2
      rw [hah] at hh2
      simp only at hh2
      cases hc2 : DecJet.readCell (M.take key) csk'.h with
      | none => rw [hc2] at hh2; cases hh2
      | some sk2 =>
        rw [hL, nounRows_cell1 hah hc2] at hd
        have hv : headV M key csk'.h = (true, 0) := by unfold headV; rw [hah]
        rcases List.mem_cons.1 hd with rfl | hd
        · rw [hv]
          refine subjW hc (rest := List.replicate 5 (.app 0 0) ++ DecJet.errCells (key + 12))
            (by rw [← List.append_assoc]; exact hC) (fun _ => ?_)
          have := Cells_r hC
          simp only [List.length_append, DecJet.cellCells_length, List.length_replicate] at this
          exact this
        · rcases List.mem_append.1 hd with hd | hd
          · rcases List.mem_cons.1 hd with rfl | hd
            · refine ⟨fun _ h => by simp [cellRow] at h, fun _ h => by simp [cellRow] at h, fun _ _ => ?_,
                fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h,
                fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h, fun h => by simp [cellRow] at h⟩
              have := Cells_r (Cells_l hC)
              rw [DecJet.cellCells_length] at this
              exact this
            · rcases List.mem_append.1 hd with hd | hd
              · exact noun2_quiet _ _ d hd
              · exact noun2_quiet _ _ d hd
          · exact noun2_quiet _ _ d hd

end DecT

end Circuit
