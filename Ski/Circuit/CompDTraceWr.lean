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

end DecT

end Circuit
