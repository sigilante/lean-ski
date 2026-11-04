import Ski.Circuit.CompDTraceTel
set_option linter.unusedSimpArgs false

/-!
# A jet call's DEC rows on the jet's buses

**`DecT.call_sends`**: on every bus but `mem`, the rows of a jet call
(`DecT.callRows` at the jet row's counter, on its subject) send exactly
the negation of what the honest CPU's jet row sends: they receive the
subject's need on `decn` and send the result's root and the next counter
on `decx`; every chain between them telescopes, through the thunks at the
subject's root.
-/

namespace Circuit

open B Air

namespace DecT

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

/-- The head noun's chain on `decd` when the head is an atom through thunks:
    its verdict. -/
theorem S_headA_d : ∀ {n q a : Nat} {ask : DecJet.AtomSk} {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.headAtom (A.take key) n q = some (a, ask) →
    DecJet.readBitsI (A.take key) (A.take key).length ask.b = some (bs, sks) →
    S A "decd" v (nounRows A key n q 1) =
      if bs = [] then ind ([ofN key, ofN 1, ofN 0] = v) else ind ([ofN key, ofN 0, ofN (0 + wcAdd true bs)] = v)
  | 0, _, _, _, _, _, h, _ => nomatch h
  | n + 1, q, a, ask, bs, sks, h, hb => by
    unfold DecJet.headAtom at h
    cases ha : DecJet.readAtom (A.take key) q with
    | some ask' =>
      rw [ha] at h; cases h
      rw [nounRows_atom ha, S_cons, d_zero (d := atomRow key q 1) (by simp only [atomRow]; decide)
        (fun h => by simp only [atomRow] at h; exact absurd h (by decide))
        (fun h => by simp only [atomRow] at h; exact absurd h (by decide)), zero_add',
        show ((1 : Nat) != 1) = false from rfl, show ((1 : Nat) == 1) = true from rfl,
        S_bits_d _ _ _ _ _ false hb (fun h => absurd h (by decide)), if_neg (by decide)]
    | none =>
      rw [ha] at h; dsimp only at h
      cases hi : DecJet.readInd (A.take key) q with
      | none => rw [hi] at h; cases h
      | some R =>
        rw [hi] at h; dsimp only at h
        rw [nounRows_ind ha (DecJet.readInd_cellI hi) hi, S_cons, d_ind (d := indRow key q 1 false false 0 false 0 false) rfl,
          zero_add']
        exact S_headA_d h hb

/-- The head noun's need and chain, when the head is an atom through thunks. -/
theorem S_headA_nb : ∀ {n q a : Nat} {ask : DecJet.AtomSk} {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.headAtom (A.take key) n q = some (a, ask) →
    DecJet.readBitsI (A.take key) (A.take key).length ask.b = some (bs, sks) →
    S A "decn" v (nounRows A key n q 1) = -ind ([ofN key, ofN q, ofN 1] = v) ∧
    S A "decb" v (nounRows A key n q 1) = 0
  | 0, _, _, _, _, _, h, _ => nomatch h
  | n + 1, q, a, ask, bs, sks, h, hb => by
    unfold DecJet.headAtom at h
    cases ha : DecJet.readAtom (A.take key) q with
    | some ask' =>
      rw [ha] at h; cases h
      obtain ⟨_, _, _, _, _, h22⟩ := atomReads (d := atomRow key q 1) rfl ha
      rw [nounRows_atom ha, S_cons, S_cons, n_atom (d := atomRow key q 1) rfl, S_bits_n, add_zero',
        b_atom (d := atomRow key q 1) rfl h22, S_bits_b _ _ _ _ _ false hb (fun h => absurd h (by decide)), mf_false]
      exact ⟨rfl, tel0 _⟩
    | none =>
      rw [ha] at h; dsimp only at h
      cases hi : DecJet.readInd (A.take key) q with
      | none => rw [hi] at h; cases h
      | some R =>
        rw [hi] at h; dsimp only at h
        obtain ⟨_, h1⟩ := indReads (d := indRow key q 1 false false 0 false 0 false) rfl hi
        obtain ⟨e1, e2⟩ := S_headA_nb h hb
        rw [nounRows_ind ha (DecJet.readInd_cellI hi) hi, S_cons, S_cons,
          n_ind (d := indRow key q 1 false false 0 false 0 false) rfl rfl h1, e1,
          b_indN (d := indRow key q 1 false false 0 false 0 false) rfl rfl, e2]
        exact ⟨tel2 _ _, zero_add' 0⟩

/-- The head noun's chain on `decd` when the head is a cell through thunks. -/
theorem S_headC_d : ∀ {n q : Nat} {s : DecJet.Nn}, DecJet.readNnI (A.take key) n q = some s →
    DecJet.headAtom (A.take key) n q = none →
    S A "decd" v (nounRows A key n q 1) = ind ([ofN key, ofN 1, ofN 0] = v)
  | 0, _, _, h, _ => nomatch h
  | n + 1, q, s, h, hh => by
    rcases readNnI_cases h with ⟨sk, bs, sks, ha, hb, hc, rfl⟩ | ⟨sk, hh', tt, ha, hc, h1, h2, rfl⟩ |
      ⟨R, ha, hc, hi, hR⟩
    · unfold DecJet.headAtom at hh; rw [ha] at hh; cases hh
    · rw [nounRows_cell ha hc, S_cons, d_cellH (d := cellRow key q 1 false 0 _) rfl rfl, S_append, S_noun2_d,
        S_noun2_d, add_zero', add_zero']
      rfl
    · unfold DecJet.headAtom at hh; rw [ha] at hh; dsimp only at hh; rw [hi] at hh; dsimp only at hh
      rw [nounRows_ind ha hc hi, S_cons, d_ind (d := indRow key q 1 false false 0 false 0 false) rfl, zero_add']
      exact S_headC_d hR hh

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

/-- The subject's rows on the four chains, by the fuel of its root's thunks. -/
theorem subj_chains {A : List Cell} {key : Nat} {v : List F} : ∀ {n p : Nat} {s : DecJet.Nn}
    {csk : Option DecJet.CellSk} {ask : Option DecJet.AtomSk} {sks : List DecJet.ConsSk} {cells : List Cell}
    {root : Nat},
    DecJet.readSubjI (A.take key) n p = some (s, csk, ask, sks) →
    DecJet.outCells key s csk ask sks = some (cells, root) →
    S A "decn" v (subjRows A key n p) = -ind ([ofN key, ofN p, 0] = v) ∧
    S A "decb" v (subjRows A key n p) = 0 ∧ S A "decd" v (subjRows A key n p) = 0 ∧
    S A "decx" v (subjRows A key n p) = ind ([ofN key, ofN root, ofN (key + cells.length)] = v)
  | 0, _, _, _, _, _, _, _, h, _ => nomatch h
  | n + 1, p, s, csk, ask, sks, cells, root, hrd, hout => by
    rcases readSubjI_cases hrd with ⟨R, ha, hc, hi, hR⟩ | ⟨sk, bs, ha, hb, hcn, rfl, rfl, rfl⟩ |
      ⟨csk', a, ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, rfl, rfl⟩ | ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, rfl, rfl⟩
    · obtain ⟨e1, e2, e3, e4⟩ := subj_chains hR hout
      obtain ⟨_, h1⟩ := indReads (d := indRow key p 0 false false 0 false 0 false) rfl hi
      rw [subjRows_ind ha hc hi]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [S_cons, n_ind (d := indRow key p 0 false false 0 false 0 false) rfl rfl h1, e1]
        exact tel2 _ _
      · rw [S_cons, b_indN (d := indRow key p 0 false false 0 false 0 false) rfl rfl, e2]; exact zero_add' 0
      · rw [S_cons, d_ind (d := indRow key p 0 false false 0 false 0 false) rfl, e3]; exact zero_add' 0
      · rw [S_cons, x_zero (d := indRow key p 0 false false 0 false 0 false) (fun h => by simp only [indRow] at h; omega), e4]
        exact zero_add' _
    · simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
      obtain ⟨rfl, rfl⟩ := hout
      rw [subjRows_atom ha]
      obtain ⟨_, _, _, _, _, h22⟩ := atomReads (d := atomRow key p 0) rfl ha
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [S_cons, n_atom (d := atomRow key p 0) rfl, S_bits_n, add_zero']; rfl
      · rw [S_cons, b_atom (d := atomRow key p 0) rfl h22,
          S_bits_b _ _ _ _ _ false hb (fun h => absurd h (by decide)), mf_false]
        exact tel0 _
      · rw [S_cons, d_zero (d := atomRow key p 0) (by simp only [atomRow]; decide)
          (fun h => by simp only [atomRow] at h; exact absurd h (by decide))
          (fun h => by simp only [atomRow] at h; exact absurd h (by decide)), S_bits_d1]
        exact add_zero' 0
      · rw [S_cons, x_atom (d := atomRow key p 0) rfl rfl, S_bits_x, add_zero']
        exact ind_congr (by rw [DecJet.errCells_length, ofN_add]; rfl)
    · rw [subjRows_cell ha hc]
      obtain ⟨_, _, _, _, _, _, h21, h26⟩ :=
        cellReads (d := cellRow key p 0 (headV A key csk'.h).1 (headV A key csk'.h).2 (iktOf (A.take key) csk'.kt))
          rfl hc rfl
      obtain ⟨hHn, hHb⟩ := S_headA_nb (v := v) hah hb
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [S_cons, n_cell (d := cellRow key p 0 _ _ _) rfl h21 h26, S_append,
          hHn, S_noun_n _ csk'.t 2 (by decide) ht]
        rw [show h0 (cellRow key p 0 (headV A key csk'.h).1 (headV A key csk'.h).2 (iktOf (A.take key) csk'.kt)) = 1
          from rfl, show (ofN 2 - 1 : F) = ofN 1 from rfl]
        exact tel3 _ _ _
      · rw [S_cons, b_cell (d := cellRow key p 0 _ _ _) rfl, S_append, hHb,
          S_noun_b _ _ _ (Nat.le_refl _) ht]
        simp only [zero_add']
      · rw [S_cons, d_cellS (d := cellRow key p 0 _ _ _) rfl rfl, S_append, S_headA_d hah hb, S_noun2_d, add_zero']
        cases bs with
        | nil =>
          have hv : headV A key csk'.h = (true, 0) := by unfold headV; rw [hah]; dsimp only; rw [hb]
          rw [if_pos rfl, hv]
          exact neg_add_cancel' _
        | cons b bs =>
          have hv : headV A key csk'.h = (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length) := by
            unfold headV; rw [hah]; dsimp only; rw [hb]
          rw [if_neg (List.cons_ne_nil _ _), hv, ← wcAdd_cells (key + 12) _ sks (DecJet.readBitsI_length hb),
            Nat.zero_add]
          exact neg_add_cancel' _
      · rw [S_cons, x_cell (d := cellRow key p 0 _ _ _) rfl rfl, S_append, S_noun_x _ _ _ (by decide),
          S_noun_x _ _ _ (by decide), add_zero', add_zero']
        cases bs with
        | nil =>
          have hv : headV A key csk'.h = (true, 0) := by unfold headV; rw [hah]; dsimp only; rw [hb]
          simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
          obtain ⟨rfl, rfl⟩ := hout
          rw [hv]
          refine ind_congr ?_
          exact crash_tup _ _ (by rw [List.length_append, List.length_append, DecJet.cellCells_length,
            DecJet.atomCells_length, DecJet.errCells_length])
        | cons b bs =>
          have hv : headV A key csk'.h = (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length) := by
            unfold headV; rw [hah]; dsimp only; rw [hb]
          simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
          obtain ⟨rfl, rfl⟩ := hout
          rw [hv]
          refine ind_congr ?_
          exact ok_tup _ _ _ (by rw [List.length_append, List.length_append, DecJet.cellCells_length,
            DecJet.atomCells_length]; rfl)
    · rw [subjRows_cell ha hc]
      obtain ⟨_, _, _, _, _, _, h21, h26⟩ :=
        cellReads (d := cellRow key p 0 (headV A key csk'.h).1 (headV A key csk'.h).2 (iktOf (A.take key) csk'.kt))
          rfl hc rfl
      have hv : headV A key csk'.h = (true, 0) := by unfold headV; rw [hah]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [S_cons, n_cell (d := cellRow key p 0 _ _ _) rfl h21 h26, S_append,
          S_noun_n _ csk'.h 1 (by decide) hh', S_noun_n _ csk'.t 2 (by decide) ht]
        rw [show h0 (cellRow key p 0 (headV A key csk'.h).1 (headV A key csk'.h).2 (iktOf (A.take key) csk'.kt)) = 1
          from rfl, show (ofN 2 - 1 : F) = ofN 1 from rfl]
        exact tel3 _ _ _
      · rw [S_cons, b_cell (d := cellRow key p 0 _ _ _) rfl, S_append, S_noun_b _ _ _ (Nat.le_refl _) hh',
          S_noun_b _ _ _ (Nat.le_refl _) ht]
        simp only [zero_add']
      · rw [S_cons, d_cellS (d := cellRow key p 0 _ _ _) rfl rfl, S_append, S_headC_d hh' hah, S_noun2_d, add_zero',
          hv]
        exact neg_add_cancel' _
      · rw [S_cons, x_cell (d := cellRow key p 0 _ _ _) rfl rfl, S_append, S_noun_x _ _ _ (by decide),
          S_noun_x _ _ _ (by decide), add_zero', add_zero', hv]
        cases hh with
        | atom bs => exact (nn_cell_noatom hh' (Nat.le_refl _) hah).elim
        | cell x y =>
          simp only [DecJet.outCells, Option.some.injEq, Prod.mk.injEq] at hout
          obtain ⟨rfl, rfl⟩ := hout
          refine ind_congr ?_
          exact crash_tup _ _ (by rw [List.length_append, List.length_append, DecJet.cellCells_length,
            List.length_replicate, DecJet.errCells_length])

/-- **A call's rows on every bus but `mem`**: the negation of the honest
    CPU's jet row. -/
theorem call_sends {M : List Cell} {J : Nat} {r r' : Air.Row} (h : DecJet.decRowI M J r = some r')
    {B : String} (hB : B ≠ "mem") (v : List F) :
    S M B v (callRows M r.ctr (subj M r)) =
      -((if B = "decn" ∧ [ofN r.ctr, ofN (subj M r), 0] = v then 1 else 0) +
        (if B = "decx" ∧ [ofN r.ctr, ofN r'.hd, ofN r'.ctr] = v then -1 else 0)) := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, _, _, hpop, hrd, _, hout, _, rfl⟩ := DecJet.decRowI_unfold h
  rw [popN_subj hpop]
  generalize r.ctr = key at hpop hrd hout ⊢
  simp only
  obtain ⟨hN, hBb, hD, hX⟩ := subj_chains (v := v) hrd hout
  unfold callRows
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
