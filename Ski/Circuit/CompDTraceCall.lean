import Ski.Circuit.CompDTraceTel
set_option linter.unusedSimpArgs false

/-!
# A jet call's DEC rows on the jet's buses

**`DecT.call_sends`**: on every bus but `mem`, the rows of a jet call
(`DecT.callRows` at the jet row's counter, on its subject) send exactly
the negation of what the honest CPU's jet row sends: they receive the
subject's need on `decn` and send the result's root and the next counter
on `decx`; every chain between them telescopes.
-/

namespace Circuit

open B Air

namespace DecT

/-- **The subject, read once**, by cases: an atom; a cell whose head is an
    atom; a cell whose head is a cell. -/
theorem readSubj_cases {H : List Cell} {p : Nat} {s : DecJet.Nn} {csk : Option DecJet.CellSk}
    {ask : Option DecJet.AtomSk} {sks : List DecJet.ConsSk}
    (h : DecJet.readSubj H p = some (s, csk, ask, sks)) :
    (∃ sk bs, DecJet.readAtom H p = some sk ∧ DecJet.readBits H H.length sk.b = some (bs, sks) ∧
      DecJet.canonB bs = true ∧ s = .atom bs) ∨
    (∃ csk' ask' bs r, DecJet.readAtom H p = none ∧ DecJet.readCell H p = some csk' ∧
      DecJet.readAtom H csk'.h = some ask' ∧ DecJet.readBits H H.length ask'.b = some (bs, sks) ∧
      DecJet.canonB bs = true ∧ DecJet.readNn H H.length csk'.t = some r ∧ s = .cell (.atom bs) r ∧
      csk = some csk' ∧ ask = some ask') ∨
    (∃ csk' hh tt, DecJet.readAtom H p = none ∧ DecJet.readCell H p = some csk' ∧
      DecJet.readAtom H csk'.h = none ∧ DecJet.readNn H H.length csk'.h = some hh ∧
      DecJet.readNn H H.length csk'.t = some tt ∧ s = .cell hh tt ∧ csk = some csk') := by
  unfold DecJet.readSubj at h
  cases ha : DecJet.readAtom H p with
  | some sk =>
    rw [ha] at h; simp only at h
    cases hb : DecJet.readBits H H.length sk.b with
    | none => rw [hb] at h; cases h
    | some q =>
      obtain ⟨bs, sks'⟩ := q
      rw [hb] at h; simp only at h
      by_cases hc : DecJet.canonB bs = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -, rfl⟩ := h
        exact .inl ⟨sk, bs, rfl, hb, hc, rfl⟩
      · rw [if_neg hc] at h; cases h
  | none =>
    rw [ha] at h; simp only at h
    cases hc : DecJet.readCell H p with
    | none => rw [hc] at h; cases h
    | some csk' =>
      rw [hc] at h; simp only at h
      cases hah : DecJet.readAtom H csk'.h with
      | some ask' =>
        rw [hah] at h; simp only at h
        cases hb : DecJet.readBits H H.length ask'.b with
        | none => rw [hb] at h; cases h
        | some q =>
          obtain ⟨bs, sks'⟩ := q
          rw [hb] at h; simp only at h
          by_cases hcn : DecJet.canonB bs = true
          · rw [if_pos hcn] at h
            cases ht : DecJet.readNn H H.length csk'.t with
            | none => rw [ht] at h; cases h
            | some r =>
              rw [ht] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact .inr (.inl ⟨csk', ask', bs, r, rfl, rfl, hah, hb, hcn, ht, rfl, rfl, rfl⟩)
          · rw [if_neg hcn] at h; cases h
      | none =>
        rw [hah] at h; simp only at h
        cases hh : DecJet.readNn H H.length csk'.h with
        | none => rw [hh] at h; cases h
        | some hn =>
          cases ht : DecJet.readNn H H.length csk'.t with
          | none => rw [hh, ht] at h; cases h
          | some tn =>
            rw [hh, ht] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -, -⟩ := h
            exact .inr (.inr ⟨csk', hn, tn, rfl, rfl, hah, hh, ht, rfl, rfl⟩)

theorem readNn_atomHead {H : List Cell} {h : Nat} {ask : DecJet.AtomSk} {bs : List Bool} {sks : List DecJet.ConsSk}
    (hah : DecJet.readAtom H h = some ask) (hb : DecJet.readBits H H.length ask.b = some (bs, sks))
    (hcn : DecJet.canonB bs = true) : DecJet.readNn H H.length h = some (.atom bs) := by
  have hL : H.length = H.length - 1 + 1 := by
    cases hl : H.length with
    | zero => rw [hl] at hb; cases hb
    | succ k => rfl
  rw [hL]; unfold DecJet.readNn; rw [hah]; simp only; rw [← hL, hb]; simp only [if_pos hcn]

/-- The jet row's subject: the first field of its stack cell. -/
def subj (M : List Cell) (r : Air.Row) : Nat := (fieldsAt M r 1).1

theorem popN_subj {M : List Cell} {r : Air.Row} {p rest : Nat}
    (h : Mach.popN (M.take r.ctr) 1 r.stk = some ([p], rest)) : subj M r = p := by
  unfold Mach.popN at h
  cases hc : (M.take r.ctr)[r.stk]? with
  | none => rw [hc] at h; cases h
  | some c1 =>
    rw [hc] at h
    cases c1 with
    | cons x s =>
      simp only [Mach.popN, Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at h
      obtain ⟨rfl, rfl⟩ := h
      show (cellFields ((rd M r.ctr r.stk).getD .nil)).1 = x
      rw [rd_of_take hc]; rfl
    | _ => cases h

section
variable {A : List Cell} {key : Nat} {v : List F}

/-- The head noun's chain on `decd`: its verdict, as the subject's row
    holds it. -/
theorem S_head_d {h : Nat} {hh : DecJet.Nn} (hn : DecJet.readNn (A.take key) (A.take key).length h = some hh) :
    S A "decd" v (nounRows A key (A.take key).length h 1) =
      ind ([ofN key, bF (headV A key h).1, ofN (headV A key h).2] = v) := by
  obtain ⟨n, hL⟩ : ∃ n, (A.take key).length = n + 1 := by
    cases hl : (A.take key).length with
    | zero => rw [hl] at hn; cases hn
    | succ k => exact ⟨k, rfl⟩
  cases hah : DecJet.readAtom (A.take key) h with
  | some ask =>
    have hn' := hn
    rw [hL] at hn'
    unfold DecJet.readNn at hn'
    rw [hah] at hn'
    simp only at hn'
    rw [← hL] at hn'
    have : ∃ bs sks, DecJet.readBits (A.take key) (A.take key).length ask.b = some (bs, sks) := by
      revert hn'
      cases DecJet.readBits (A.take key) (A.take key).length ask.b with
      | none => intro h; cases h
      | some q => intro _; exact ⟨q.1, q.2, rfl⟩
    obtain ⟨bs, sks, hb⟩ := this
    have hrows : nounRows A key (A.take key).length h 1 =
        atomRow key h 1 :: bitsRows A key false (A.take key).length ask.b 0 true 0 := by
      rw [hL]; unfold nounRows; rw [hah]; rfl
    rw [hrows, S_cons, d_zero (d := atomRow key h 1) (by simp only [atomRow]; decide) (fun h => by simp only [atomRow] at h; exact absurd h (by decide))
      (fun h => by simp only [atomRow] at h; exact absurd h (by decide)), zero_add', S_bits_d _ _ _ _ _ hb]
    cases bs with
    | nil =>
      have hv : headV A key h = (true, 0) := by unfold headV; rw [hah]; simp only; rw [hb]
      rw [if_pos rfl, hv]; rfl
    | cons b bs =>
      have hv : headV A key h = (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length) := by
        unfold headV; rw [hah]; simp only; rw [hb]
      rw [if_neg (List.cons_ne_nil _ _), hv, ← wcAdd_cells (key + 12) _ sks (DecJet.readBits_length hb), Nat.zero_add]
      rfl
  | none =>
    have hn' := hn
    rw [hL] at hn'
    unfold DecJet.readNn at hn'
    rw [hah] at hn'
    simp only at hn'
    cases hc : DecJet.readCell (A.take key) h with
    | none => rw [hc] at hn'; cases hn'
    | some sk =>
      have hrows : nounRows A key (A.take key).length h 1 =
          cellRow key h 1 false 0 :: (nounRows A key n sk.h 2 ++ nounRows A key n sk.t 2) := by
        rw [hL]; simp only [nounRows, hah, hc]
      have hv : headV A key h = (true, 0) := by unfold headV; rw [hah]
      rw [hrows, S_cons, d_cellH (d := cellRow key h 1 false 0) rfl rfl, S_append, S_noun2_d, S_noun2_d, add_zero',
        add_zero', hv]
      rfl

end

theorem ofN_add3 (a b : Nat) : ofN a + ofN b = ofN (a + b) := (ofN_add a b).symm

theorem ind_congr {t t' v : List F} (h : t = t') : ind (t = v) = ind (t' = v) := by subst h; rfl

theorem tup3 {a b c a' b' c' : F} (h1 : a = a') (h2 : b = b') (h3 : c = c') : [a, b, c] = [a', b', c'] := by
  rw [h1, h2, h3]

theorem crash_tup (key n : Nat) (hn : n = 15) :
    [ofN key, ofN key + ofN 12 * bF true, ofN key + ofN 12 + ofN 0 + ofN 3 * bF true] =
      [ofN key, ofN (key + 12), ofN (key + n)] := by
  subst hn
  refine tup3 rfl (by rw [ofN_add]; rfl) ?_
  rw [show key + 15 = key + 12 + 3 from rfl, ofN_add, ofN_add]
  show ofN key + ofN 12 + 0 + ofN 3 * 1 = _
  rw [add_zero', mul_one']

theorem ok_tup (key wc n : Nat) (hn : n = 12 + wc) :
    [ofN key, ofN key + ofN 12 * bF false, ofN key + ofN 12 + ofN wc + ofN 3 * bF false] =
      [ofN key, ofN key, ofN (key + n)] := by
  subst hn
  refine tup3 rfl ?_ ?_
  · show ofN key + ofN 12 * 0 = _; rw [mul_zero', add_zero']
  · show ofN key + ofN 12 + ofN wc + ofN 3 * 0 = _
    rw [mul_zero', add_zero', ← Nat.add_assoc, ofN_add, ofN_add]

/-- **A call's rows on every bus but `mem`**: the negation of the honest
    CPU's jet row. -/
theorem call_sends {M : List Cell} {J : Nat} {r r' : Air.Row} (h : DecJet.decRow M J r = some r')
    {B : String} (hB : B ≠ "mem") (v : List F) :
    S M B v (callRows M r.ctr (subj M r)) =
      -((if B = "decn" ∧ [ofN r.ctr, ofN (subj M r), 0] = v then 1 else 0) +
        (if B = "decx" ∧ [ofN r.ctr, ofN r'.hd, ofN r'.ctr] = v then -1 else 0)) := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, _, _, hpop, hrd, _, hout, _, rfl⟩ := DecJet.decRow_unfold h
  rw [popN_subj hpop]
  generalize r.ctr = key at hpop hrd hout ⊢
  simp only
  -- the four chains, and the others
  have hN : S M "decn" v (callRows M key p) = -ind ([ofN key, ofN p, 0] = v) := by
    unfold callRows
    rcases readSubj_cases hrd with ⟨sk, bs, ha, hb, hc, rfl⟩ | ⟨csk', ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ |
      ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl⟩
    · rw [ha]; simp only
      rw [S_cons, n_atom (d := atomRow key p 0) rfl, S_bits_n, add_zero']; rfl
    · rw [ha]; simp only; rw [hc]; simp only
      obtain ⟨_, _, _, _, _, _, h21, h23⟩ := cellReads (d := cellRow key p 0 (headV M key csk'.h).1 (headV M key csk'.h).2) rfl hc
      rw [S_cons, n_cell (d := cellRow key p 0 _ _) rfl h21 h23, S_append,
        S_noun_n _ csk'.h 1 (by decide) (readNn_atomHead hah hb hcn), S_noun_n _ csk'.t 2 (by decide) ht]
      rw [show h0 (cellRow key p 0 (headV M key csk'.h).1 (headV M key csk'.h).2) = 1 from rfl,
        show (ofN 2 - 1 : F) = ofN 1 from rfl]
      exact tel3 _ _ _
    · rw [ha]; simp only; rw [hc]; simp only
      obtain ⟨_, _, _, _, _, _, h21, h23⟩ := cellReads (d := cellRow key p 0 (headV M key csk'.h).1 (headV M key csk'.h).2) rfl hc
      rw [S_cons, n_cell (d := cellRow key p 0 _ _) rfl h21 h23, S_append,
        S_noun_n _ csk'.h 1 (by decide) hh', S_noun_n _ csk'.t 2 (by decide) ht]
      rw [show h0 (cellRow key p 0 (headV M key csk'.h).1 (headV M key csk'.h).2) = 1 from rfl,
        show (ofN 2 - 1 : F) = ofN 1 from rfl]
      exact tel3 _ _ _
  have hBb : S M "decb" v (callRows M key p) = 0 := by
    unfold callRows
    rcases readSubj_cases hrd with ⟨sk, bs, ha, hb, hc, rfl⟩ | ⟨csk', ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ |
      ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl⟩
    · rw [ha]; simp only
      obtain ⟨_, _, _, _, _, h22⟩ := atomReads (d := atomRow key p 0) rfl ha
      rw [S_cons, b_atom (d := atomRow key p 0) rfl h22, S_bits_b _ _ _ _ _ hb]
      exact tel0 _
    · rw [ha]; simp only; rw [hc]; simp only
      rw [S_cons, b_cell (d := cellRow key p 0 _ _) rfl, S_append, S_noun_b _ _ _ (readNn_atomHead hah hb hcn),
        S_noun_b _ _ _ ht]
      simp only [zero_add']
    · rw [ha]; simp only; rw [hc]; simp only
      rw [S_cons, b_cell (d := cellRow key p 0 _ _) rfl, S_append, S_noun_b _ _ _ hh', S_noun_b _ _ _ ht]
      simp only [zero_add']
  have hD : S M "decd" v (callRows M key p) = 0 := by
    unfold callRows
    rcases readSubj_cases hrd with ⟨sk, bs, ha, hb, hc, rfl⟩ | ⟨csk', ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ |
      ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl⟩
    · rw [ha]; simp only
      rw [S_cons, d_zero (d := atomRow key p 0) (by simp only [atomRow]; decide) (fun h => by simp only [atomRow] at h; exact absurd h (by decide))
        (fun h => by simp only [atomRow] at h; exact absurd h (by decide)), S_bits_d1]
      exact add_zero' 0
    · rw [ha]; simp only; rw [hc]; simp only
      rw [S_cons, d_cellS (d := cellRow key p 0 _ _) rfl rfl, S_append, S_head_d (readNn_atomHead hah hb hcn),
        S_noun2_d, add_zero']
      exact neg_add_cancel' _
    · rw [ha]; simp only; rw [hc]; simp only
      rw [S_cons, d_cellS (d := cellRow key p 0 _ _) rfl rfl, S_append, S_head_d hh', S_noun2_d, add_zero']
      exact neg_add_cancel' _
  have hX : S M "decx" v (callRows M key p) = ind ([ofN key, ofN root, ofN (key + cells.length)] = v) := by
    unfold callRows
    rcases readSubj_cases hrd with ⟨sk, bs, ha, hb, hc, rfl⟩ | ⟨csk', ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ |
      ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl⟩
    · rw [ha]; simp only
      simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      rw [S_cons, x_atom (d := atomRow key p 0) rfl rfl, S_bits_x, add_zero']
      exact ind_congr (by rw [DecJet.errCells_length, ofN_add]; rfl)
    · rw [ha]; simp only; rw [hc]; simp only
      rw [S_cons, x_cell (d := cellRow key p 0 _ _) rfl rfl, S_append, S_noun_x _ _ _ (by decide),
        S_noun_x _ _ _ (by decide), add_zero', add_zero']
      cases bs with
      | nil =>
        have hv : headV M key csk'.h = (true, 0) := by unfold headV; rw [hah]; simp only; rw [hb]
        simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        rw [hv]
        refine ind_congr ?_
        exact crash_tup _ _ (by rw [List.length_append, List.length_append, DecJet.cellCells_length, DecJet.atomCells_length,
          DecJet.errCells_length])
      | cons b bs =>
        have hv : headV M key csk'.h = (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length) := by
          unfold headV; rw [hah]; simp only; rw [hb]
        simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        rw [hv]
        refine ind_congr ?_
        exact ok_tup _ _ _ (by rw [List.length_append, List.length_append, DecJet.cellCells_length, DecJet.atomCells_length]; rfl)
    · rw [ha]; simp only; rw [hc]; simp only
      rw [S_cons, x_cell (d := cellRow key p 0 _ _) rfl rfl, S_append, S_noun_x _ _ _ (by decide),
        S_noun_x _ _ _ (by decide), add_zero', add_zero']
      have hv : headV M key csk'.h = (true, 0) := by unfold headV; rw [hah]
      rw [hv]
      cases hh with
      | atom bs => exact absurd hh' (fun h' => readNn_cell h' hah)
      | cell x y =>
        simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        refine ind_congr ?_
        exact crash_tup _ _ (by rw [List.length_append, List.length_append, DecJet.cellCells_length, List.length_replicate,
          DecJet.errCells_length])
  -- assemble
  by_cases h1 : B = "decn"
  · subst h1
    rw [hN]
    simp only [true_and, show ("decn" = "decx") = False from by decide, false_and, if_false, add_zero']
    rfl
  · by_cases h4 : B = "decx"
    · subst h4
      rw [hX]
      simp only [true_and, show ("decx" = "decn") = False from by decide, false_and, if_false, zero_add']
      unfold ind; repeat' split
      all_goals first | contradiction | decide
    · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h4 h.1), zero_add', neg_zero_eq]
      by_cases h2 : B = "decb"
      · subst h2; exact hBb
      · by_cases h3 : B = "decd"
        · subst h3; exact hD
        · exact S_zero (fun d _ => sendO M d v hB h1 h2 h3 h4)

end DecT

end Circuit
