import Ski.Circuit.CompDVerd

/-!
# The circuit with the `dec` jet: the jet's row

**`CompDOK.jetRow`**: a CPU row of the jet's kind whose state decodes takes
`DecJet.decRow`'s step over the memory: the head is the atom `J`, the
stack's top the subject's pointer, and below the counter the subject is a
noun `readSubj` reads (the need tree, at the decoded state's fuel), its
head atom within `32` bits (the chain's levels); the cells from the
counter are the outcome `outCells` lays out (the rows' writes), and the
next row's registers are its root, the rest of the stack, and the counter
past the cells (the result on `decx`).
-/

namespace DecJet

theorem readNn_cell {H : List Cell} {n p : Nat} {s : Nn} (ha : readAtom H p = none) (h : readNn H n p = some s) :
    ∃ a b, s = .cell a b := by
  cases n with
  | zero => cases h
  | succ n =>
    unfold readNn at h
    rw [ha] at h
    dsimp only at h
    cases hc : readCell H p with
    | none => rw [hc] at h; cases h
    | some sk =>
      rw [hc] at h; dsimp only at h
      cases hh : readNn H n sk.h with
      | none => rw [hh] at h; cases h
      | some sh =>
        cases ht : readNn H n sk.t with
        | none => rw [hh, ht] at h; cases h
        | some st => rw [hh, ht] at h; cases h; exact ⟨_, _, rfl⟩

theorem nwr_le : ∀ (bw : Bool) (bs : List Bool), nwr bw bs ≤ bs.length
  | _, [] => Nat.le_refl _
  | bw, b :: bs => by
    simp only [nwr, List.length_cons]
    have := nwr_le (bw && !b) bs
    split <;> omega

theorem wrs_append (M : List Cell) : ∀ (c : Nat) (xs ys : List Cell),
    Air.wrs M c (xs ++ ys) = (Air.wrs M c xs && Air.wrs M (c + xs.length) ys)
  | _, [], _ => by simp [Air.wrs]
  | c, x :: xs, ys => by
    simp only [List.cons_append, wrs_cons, wrs_append M (c + 1) xs ys, List.length_cons, Bool.and_assoc]
    rw [show c + 1 + xs.length = c + (xs.length + 1) by omega]

theorem wrs_eq_true {M : List Cell} : ∀ {c : Nat} {xs : List Cell},
    (∀ i, i < xs.length → M[c + i]? = xs[i]?) → Air.wrs M c xs = true
  | _, [], _ => rfl
  | c, x :: xs, h => wrs_of (by have := h 0 (by simp); simpa using this)
      (wrs_eq_true (fun i hi => by have := h (i + 1) (by simp; omega); rw [← Nat.add_assoc, Nat.add_right_comm] at this; simpa using this))

/-- A run of thunks peeled from a read-back: two fuels a thunk. -/
theorem iterI_peel {H : List Cell} : ∀ (m : Nat) {x y F : Nat} {u : OTerm}, iterI H m x = some y →
    Mach.otermAt H F x = some u → ∃ F' u', F' + 2 * m ≤ F ∧ Mach.otermAt H F' y = some u'
  | 0, x, y, F, u, h, hu => by cases h; exact ⟨F, u, by omega, hu⟩
  | m + 1, x, y, F, u, h, hu => by
    cases hi : readInd H x with
    | none =>
      have : iterI H (m + 1) x = none := by
        show (match readInd H x with | some y => iterI H m y | none => none) = _
        rw [hi]
      rw [this] at h; cases h
    | some R =>
      rw [iterI_succ hi] at h
      obtain ⟨f, tr, rfl, hR, _⟩ := readInd_peel hi hu
      obtain ⟨F', u', hF', hy⟩ := iterI_peel m h hR
      exact ⟨F', u', by omega, hy⟩

/-- The subject read through a run of thunks. -/
theorem readSubjI_iter {H : List Cell} : ∀ (m n : Nat) {x y : Nat}, iterI H m x = some y →
    readSubjI H (n + m) x = readSubjI H n y
  | 0, n, x, y, h => by cases h; rfl
  | m + 1, n, x, y, h => by
    cases hi : readInd H x with
    | none =>
      have : iterI H (m + 1) x = none := by
        show (match readInd H x with | some y => iterI H m y | none => none) = _
        rw [hi]
      rw [this] at h; cases h
    | some R =>
      rw [iterI_succ hi] at h
      rw [show n + (m + 1) = (n + m) + 1 by omega]
      conv => lhs; unfold readSubjI
      rw [readInd_atom hi, readInd_cellI hi]
      dsimp only
      rw [hi]
      exact readSubjI_iter m n h

theorem headAtom_iter {H : List Cell} : ∀ (m n : Nat) {x y : Nat}, iterI H m x = some y →
    headAtom H (n + m) x = headAtom H n y
  | 0, n, x, y, h => by cases h; rfl
  | m + 1, n, x, y, h => by
    cases hi : readInd H x with
    | none =>
      have : iterI H (m + 1) x = none := by
        show (match readInd H x with | some y => iterI H m y | none => none) = _
        rw [hi]
      rw [this] at h; cases h
    | some R =>
      rw [iterI_succ hi] at h
      rw [show n + (m + 1) = (n + m) + 1 by omega]
      conv => lhs; unfold headAtom
      rw [readInd_atom hi]
      dsimp only
      rw [hi]
      exact headAtom_iter m n h

theorem headAtom_at {H : List Cell} {n y : Nat} (hn : 1 ≤ n) :
    headAtom H n y = match readAtom H y with
      | some ask => some (y, ask)
      | none => match readInd H y with
        | some R => headAtom H (n - 1) R
        | none => none := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rfl

/-- A noun with no head atom is a cell. -/
theorem readNnI_cell {H : List Cell} : ∀ {n x : Nat} {s : Nn}, readNnI H n x = some s → headAtom H n x = none →
    ∃ a b, s = .cell a b
  | 0, _, _, h, _ => nomatch h
  | n + 1, x, s, h, ha => by
    unfold readNnI at h
    unfold headAtom at ha
    cases hr : readAtom H x with
    | some sk => rw [hr] at ha; cases ha
    | none =>
      rw [hr] at h ha
      dsimp only at h ha
      cases hc : readCellI H x with
      | some sk =>
        rw [hc] at h; dsimp only at h
        cases hh : readNnI H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNnI H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st => rw [hh, ht] at h; cases h; exact ⟨_, _, rfl⟩
      | none =>
        rw [hc] at h; dsimp only at h
        cases hi : readInd H x with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h ha; exact readNnI_cell h ha


end DecJet

namespace Circuit

open B Air DecJet

theorem rd_takeD {M : List Cell} {c a : Nat} {x : Cell} (h : rd M c a = some x) : (M.take c)[a]? = some x := by
  unfold rd at h
  split at h
  · rw [List.getElem?_take, if_pos (by assumption)]; exact h
  · cases h

/-- **`decRow` from its parts.** -/
theorem decRow_of {M : List Cell} {J : Nat} {r r' : Air.Row} {p rest : Nat} {s : Nn} {csk : Option CellSk}
    {ask : Option AtomSk} {sks : List ConsSk} {cells : List Cell} {root : Nat}
    (h1 : (M.take r.ctr)[r.hd]? = some (.atom J)) (h2 : slotsOK (M.take r.ctr) = true)
    (h3 : Mach.popN (M.take r.ctr) 1 r.stk = some ([p], rest))
    (h4 : readSubj (M.take r.ctr) p = some (s, csk, ask, sks)) (h5 : headFits s = true)
    (h6 : outCells r.ctr s csk ask sks = some (cells, root)) (h7 : wrs M r.ctr cells = true)
    (h8 : r' = ⟨root, rest, r.ctr + cells.length⟩) : decRow M J r = some r' := by
  unfold decRow
  simp only [h1, h2, and_self, if_true, h3, h4, h5, h6, h7, h8]

/-- **`decRowI` from its parts.** -/
theorem decRowI_of {M : List Cell} {J : Nat} {r r' : Air.Row} {p rest : Nat} {s : Nn} {csk : Option CellSk}
    {ask : Option AtomSk} {sks : List ConsSk} {cells : List Cell} {root : Nat}
    (h1 : (M.take r.ctr)[r.hd]? = some (.atom J)) (h2 : slotsOK (M.take r.ctr) = true)
    (h3 : Mach.popN (M.take r.ctr) 1 r.stk = some ([p], rest))
    (h4 : readSubjI (M.take r.ctr) (M.take r.ctr).length p = some (s, csk, ask, sks)) (h5 : headFits s = true)
    (h6 : outCells r.ctr s csk ask sks = some (cells, root)) (h7 : wrs M r.ctr cells = true)
    (h8 : r' = ⟨root, rest, r.ctr + cells.length⟩) : decRowI M J r = some r' := by
  unfold decRowI
  simp only [h1, h2, and_self, if_true, h3, h4, h5, h6, h7, h8]

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

theorem CompDOK.dkind_of_eq {q dk : Nat} (hq : q < D.h) (hx : D.main q (match dk with
    | 1 => Dec.KCELL | 2 => Dec.KATOM | 3 => Dec.KCONS | _ => Dec.KNIL) = 1) (hdk : 1 ≤ dk ∧ dk ≤ 4) :
    DKind D q dk := by
  obtain ⟨dk', hd⟩ := dkind_of (decRowF_of h.dec hq)
  rcases (show dk = 1 ∨ dk = 2 ∨ dk = 3 ∨ dk = 4 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show dk' = 0 ∨ dk' = 1 ∨ dk' = 2 ∨ dk' = 3 ∨ dk' = 4 ∨ dk' = 5 by have := hd.1; omega) with
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hd
    | (simp only [hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1] at hx; exact absurd hx (by decide))

end

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

theorem CompDOK.ka_noind' {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1) :
    readInd ((memOf Mm).take (D.main q Dec.KEY).val) (D.main q Dec.PC).val = none := by
  rcases h.kind_of_ka hq hk with hd | hd
  · exact (h.cellRead hq hd).2.2.2.1
  · exact readAtom_ind (h.atomRead hq hd).1

/-- **A need travels along a run of thunks.** -/
theorem CompDOK.need_run : ∀ (j : Nat) (k a ρ : F) {x : Nat}, NeedSent C D [k, a, ρ] →
    iterI ((memOf Mm).take k.val) j a.val = some x → ∃ x' : F, x'.val = x ∧ NeedSent C D [k, x', ρ] := by
  intro j
  induction j with
  | zero => intro k a ρ x hs hj; cases hj; exact ⟨a, rfl, hs⟩
  | succ j ih =>
    intro k a ρ x hs hj
    cases hi : readInd ((memOf Mm).take k.val) a.val with
    | none =>
      have : iterI ((memOf Mm).take k.val) (j + 1) a.val = none := by
        show (match readInd _ a.val with | some y => iterI _ j y | none => none) = _
        rw [hi]
      rw [this] at hj; cases hj
    | some R =>
      rw [iterI_succ hi] at hj
      obtain ⟨q, hq, hka, e⟩ := h.need_recv hs
      simp only [List.cons.injEq, and_true] at e
      obtain ⟨e0, e1, e2⟩ := e
      rcases hka with hka | hkn
      · rw [e0, e1, (h.ka_noind' hq hka)] at hi; cases hi
      · obtain ⟨hi', _⟩ := h.indRead hq (kind_of_inn (decRowF_of h.dec hq) hkn)
        rw [← e0, ← e1, hi] at hi'
        cases hi'
        have hsent : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3), D.main q Dec.RO] :=
          .inr (.inr ⟨q, hq, hkn, rfl⟩)
        rw [← e0, ← e2] at hsent
        exact ih _ _ _ hsent hj

/-- A row whose kind column `X` is `1` is of that kind. -/
theorem CompDOK.kind1 {q : Nat} (hq : q < D.h) (hx : D.main q Dec.KCELL = 1) : DKind D q 1 := by
  obtain ⟨dk, hd⟩ := dkind_of (decRowF_of h.dec hq)
  rw [hd.2.1] at hx
  have : dk = 1 := by by_cases e : dk = 1; exact e; rw [if_neg e] at hx; exact absurd hx (by decide)
  subst this; exact hd

theorem CompDOK.kind2 {q : Nat} (hq : q < D.h) (hx : D.main q Dec.KATOM = 1) : DKind D q 2 := by
  obtain ⟨dk, hd⟩ := dkind_of (decRowF_of h.dec hq)
  rw [hd.2.2.1] at hx
  have : dk = 2 := by by_cases e : dk = 2; exact e; rw [if_neg e] at hx; exact absurd hx (by decide)
  subst this; exact hd

theorem CompDOK.subj_bits {q : Nat} (hq : q < D.h) (hs : D.main q Dec.SUB = 1 ∨ D.main q Dec.ASUB = 1) :
    D.main q Dec.H0 = 1 ∧ (D.main q Dec.SUB = 1 → DKind D q 1) ∧ (D.main q Dec.ASUB = 1 → DKind D q 2) ∧
      D.main q Dec.KCELL + D.main q Dec.KATOM = 1 ∧ D.main q Dec.RO = 0 ∧ D.main q Dec.H1 = 0 := by
  have hf := decRowF_of h.dec hq
  have hx : (D.main q Dec.KCELL = 1 ∨ D.main q Dec.KATOM = 1) ∧ D.main q Dec.H0 = 1 := by
    rcases hs with hs | hs
    · rw [hf.sub] at hs
      rcases hf.kcell with a | a <;> rcases hf.h0 with b | b <;> rw [a, b] at hs
      all_goals first | exact absurd hs (by decide) | exact ⟨.inl a, b⟩
    · rw [hf.asub] at hs
      rcases hf.katom with a | a <;> rcases hf.h0 with b | b <;> rw [a, b] at hs
      all_goals first | exact absurd hs (by decide) | exact ⟨.inr a, b⟩
  have hsum : D.main q Dec.KCELL + D.main q Dec.KATOM = 1 := by
    rcases hx.1 with a | a
    · have := h.kind1 hq a; rw [this.2.1, this.2.2.1]; decide
    · have := h.kind2 hq a; rw [this.2.1, this.2.2.1]; decide
  have hro : D.main q Dec.RO = 0 ∧ D.main q Dec.H1 = 0 := by
    rcases h.role_of hq hsum with ⟨_, b, r⟩ | ⟨z, _, _⟩ | ⟨z, _, _⟩
    · exact ⟨r, b⟩
    · rw [hx.2] at z; exact absurd z (by decide)
    · rw [hx.2] at z; exact absurd z (by decide)
  refine ⟨hx.2, fun hs' => ?_, fun hs' => ?_, hsum, hro⟩
  · rw [hf.sub] at hs'
    rcases hf.kcell with a | a
    · rw [a, zero_mul'] at hs'; exact absurd hs' (by decide)
    · exact h.kind1 hq a
  · rw [hf.asub] at hs'
    rcases hf.katom with a | a
    · rw [a, zero_mul'] at hs'; exact absurd hs' (by decide)
    · exact h.kind2 hq a

/-- **The jet's row is `decRowI`'s step**, once its state decodes: the
    subject read through `K`-thunks. -/
theorem CompDOK.jetRow {r0 : Nat} (hn : r0 + 1 < C.h) (hp : C.main r0 DECSEL = 1) (hJ : J < P)
    (hctr : 3 ≤ (C.main r0 CTR).val) {t : OTerm} (hdec : Mach.odecode (Air.st (memOf Mm) (rowOf C r0)) = some t) :
    decRowI (memOf Mm) J (rowOf C r0) = some (rowOf C (r0 + 1)) := by
  have hr0 : r0 < C.h := Nat.lt_of_succ_lt hn
  obtain ⟨rd0, rd1, m0, m1, m2⟩ := h.jetReads hr0 hp hJ
  obtain ⟨n1, n2, n3⟩ := h.jetNext hn hp
  have hkl := h.key_lt hr0
  have hPP : P = 2013265921 := rfl
  -- the reads
  have hhd := rd_takeD rd0
  have hstk := rd_takeD rd1
  have hH : ∀ a, a < (C.main r0 CTR).val → ((memOf Mm).take (C.main r0 CTR).val)[a]? = (memOf Mm)[a]? :=
    fun a ha => by rw [List.getElem?_take, if_pos ha]
  have hslots : slotsOK ((memOf Mm).take (C.main r0 CTR).val) = true := by
    unfold slotsOK
    rw [hH 0 (by omega), hH 1 (by omega), hH 2 (by omega), m0, m1, m2]; rfl
  have hpop : Mach.popN ((memOf Mm).take (C.main r0 CTR).val) 1 (C.main r0 STK).val =
      some ([(C.main r0 (FLD + 2)).val], (C.main r0 (FLD + 3)).val) := by
    simp [Mach.popN, hstk]
  -- the subject's read-back is finite
  obtain ⟨Nt, hN⟩ : ∃ Nt, Mach.otermAt ((memOf Mm).take (C.main r0 CTR).val)
      (((memOf Mm).take (C.main r0 CTR).val).length + 1) (C.main r0 (FLD + 2)).val = some Nt := by
    obtain ⟨_, args, _, h2, _⟩ := Mach.odecode_eq hdec
    change Mach.ostackAt ((memOf Mm).take (C.main r0 CTR).val) (((memOf Mm).take (C.main r0 CTR).val).length + 1)
      (C.main r0 STK).val = some args at h2
    unfold Mach.ostackAt at h2
    rw [hstk] at h2
    dsimp only at h2
    cases ho : Mach.otermAt ((memOf Mm).take (C.main r0 CTR).val)
      (((memOf Mm).take (C.main r0 CTR).val).length + 1) (C.main r0 (FLD + 2)).val with
    | none => rw [ho] at h2; cases h2
    | some N => exact ⟨N, rfl⟩
  generalize hHd : (memOf Mm).take (C.main r0 CTR).val = H at hhd hslots hpop hN hH
  have hrow : rowOf C r0 = ⟨(C.main r0 HD).val, (C.main r0 STK).val, (C.main r0 CTR).val⟩ := rfl
  have hrow1 : rowOf C (r0 + 1) = ⟨(C.main r0 DROOT).val, (C.main r0 (FLD + 3)).val, (C.main r0 DCTR).val⟩ := by
    show (⟨(C.main (r0 + 1) HD).val, (C.main (r0 + 1) STK).val, (C.main (r0 + 1) CTR).val⟩ : Air.Row) = _
    rw [n1, n2, n3]
  rw [hrow1]
  have hpre1' : ((memOf Mm).take (C.main r0 CTR).val)[(C.main r0 HD).val]? = some (.atom J) := by rw [hHd]; exact hhd
  have hpre2' : slotsOK ((memOf Mm).take (C.main r0 CTR).val) = true := by rw [hHd]; exact hslots
  have hpre3' : Mach.popN ((memOf Mm).take (C.main r0 CTR).val) 1 (C.main r0 STK).val =
      some ([(C.main r0 (FLD + 2)).val], (C.main r0 (FLD + 3)).val) := by rw [hHd]; exact hpop
  have hL : H.length ≤ (C.main r0 CTR).val := by rw [← hHd]; exact List.length_take_le _ _
  -- the result's sender is the subject's row
  obtain ⟨q, hq, ⟨hsub, ev⟩ | ⟨hasub, ev⟩⟩ := h.res_sent ⟨r0, hr0, hp, rfl⟩ <;>
    simp only [List.cons.injEq, and_true] at ev <;> obtain ⟨e0, e1, e2⟩ := ev
  · -- a cell subject
    obtain ⟨h0q, hk1, _, hsumq, hroq, _⟩ := h.subj_bits hq (.inl hsub)
    have hk1 := hk1 hsub
    have hkc : D.main q Dec.KCELL = 1 := by rw [hk1.2.1]; rfl
    have hkq : (D.main q Dec.KEY).val < 2 ^ 28 := by rw [← e0]; exact hkl
    obtain ⟨m0, hm0, hpc⟩ := h.subj_pc hr0 hp hq hsumq hroq e0.symm
    obtain ⟨hrc, hra, _, _, hkt⟩ := h.cellRead hq hk1
    rw [← e0, hHd] at hrc hra hkt
    rw [hHd] at hpc hm0
    obtain ⟨FR, uR, hFR, hNR⟩ := iterI_peel m0 hpc hN
    obtain ⟨f, th, tt, tk, hF, _, hth, htk, _, _⟩ := readCellI_peel hrc hNR
    obtain ⟨g, tt', hg, htt', _⟩ := ktAt_peel hkt htk
    have nh : NeedSent C D [C.main r0 CTR, D.main q (Dec.DFLD + 43), 1] := by
      have := (Or.inr (Or.inl ⟨q, hq, hkc, .inl rfl⟩) : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 43),
        ofN 2 - D.main q Dec.H0])
      rwa [← e0, h0q, show ofN 2 - (1 : F) = 1 by decide] at this
    have nt : NeedSent C D [C.main r0 CTR, D.main q (Dec.DFLD + 53), ofN 2] := by
      have := (Or.inr (Or.inl ⟨q, hq, hkc, .inr rfl⟩) : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 53),
        ofN 2])
      rwa [← e0] at this
    obtain ⟨rt, hrt⟩ := h.need_nn g _ _ _ tt' nt (by rw [hHd]; exact htt') (by omega)
    rw [hHd] at hrt
    have hrt' := readNnI_mono hrt (show g ≤ H.length by omega)
    -- the verdict
    have hv := h.verd_sent ⟨q, hq, hsub, rfl⟩
    rw [← e0] at hv
    have hver := h.verdict hr0 hp (by rw [hHd]; exact hpc) (by rw [hHd]; exact hrc) hv
    simp only [hHd] at hver
    -- the cell wrapper's writes
    obtain ⟨w0, w1, w2, w3, w4, w5, w6⟩ := h.subWrites hq hkq hsub
    simp only [← e0] at w0 w1 w2 w3 w4 w5 w6
    have hcw : wrs (memOf Mm) (C.main r0 CTR).val (cellCells (C.main r0 CTR).val ⟨(D.main q (Dec.DFLD + 4)).val,
        (D.main q (Dec.DFLD + 16)).val, (D.main q (Dec.DFLD + 30)).val, (D.main q (Dec.DFLD + 34)).val,
        (D.main q (Dec.DFLD + 29)).val, (D.main q (Dec.DFLD + 43)).val, (D.main q (Dec.DFLD + 53)).val⟩) = true :=
      wrs_of w0 (wrs_of w1 (wrs_of w2 (wrs_of w3 (wrs_of w4 (wrs_of w5 (wrs_of w6 rfl))))))
    -- the subject read through its run of thunks
    have hsubj : readSubjI H H.length (C.main r0 (FLD + 2)).val = readSubjI H (H.length - m0 - 1 + 1)
        (D.main q Dec.PC).val := by
      rw [← readSubjI_iter m0 _ hpc]; congr 1; omega
    -- the head's row at the end of its run, of the kind its column says
    have headRow : ∀ (ma A : Nat), iterI H ma (D.main q (Dec.DFLD + 43)).val = some A →
        ∃ qb, qb < D.h ∧ D.main qb Dec.KEY = C.main r0 CTR ∧ (D.main qb Dec.PC).val = A ∧
          (D.main qb Dec.KCELL + D.main qb Dec.KATOM = 1 ∨ D.main qb Dec.INN = 1) ∧ D.main qb Dec.RO = 1 := by
      intro ma A hA
      obtain ⟨x', hx', hs'⟩ := h.need_run ma _ _ _ nh (by rw [hHd]; exact hA)
      obtain ⟨qb, hqb, hsumb, eb⟩ := h.need_recv hs'
      simp only [List.cons.injEq, and_true] at eb
      obtain ⟨eb0, eb1, eb2⟩ := eb
      exact ⟨qb, hqb, eb0.symm, by rw [← eb1, hx'], hsumb, eb2.symm⟩
    have hpre1 := hpre1'
    have hpre2 := hpre2'
    have hpre3 := hpre3'
    have hroot1 : (C.main r0 DROOT).val = (C.main r0 CTR).val + 12 * (D.main q Dec.ERR).val ∧
        (D.main q Dec.ERR = 1 → D.main q Dec.WC = 0 → (C.main r0 DCTR).val = (C.main r0 CTR).val + 15) := by
      have hb := (decRowF_of h.dec hq).err
      refine ⟨?_, fun he hw => ?_⟩
      · rw [e1, ← e0]
        rcases hb with z | z <;> rw [z]
        · rw [show ofN 12 * (0 : F) = 0 by decide, add_zero']; rfl
        · rw [show ofN 12 * (1 : F) = ofN 12 by decide, val_key_add hkl (by decide)]; rfl
      · rw [e2, ← e0, he, hw, add_zero', show ofN 3 * (1 : F) = ofN 3 by decide, ← val_key_add hkl (n := 15) (by decide)]
        congr 1
        rw [add_assoc']; rfl
    -- an atom head: its row is an `Atom` row, its bits a chain
    have atomHead : ∀ (ma A : Nat) (ask : AtomSk), iterI H ma (D.main q (Dec.DFLD + 43)).val = some A →
        readAtom H A = some ask →
        headAtom H H.length (D.main q (Dec.DFLD + 43)).val = some (A, ask) ∧
        ∃ bs sks g, readBitsI H g ask.b = some (bs, sks) ∧ canonB bs = true ∧ g ≤ H.length ∧
          (bs ≠ [] → bs.length ≤ 32) ∧
          (bs ≠ [] → wrs (memOf Mm) ((C.main r0 CTR).val + 7) (atomCells ((C.main r0 CTR).val + 7) ask
            (bitsRoot ((C.main r0 CTR).val + 12) bs) ++ bitCells ((C.main r0 CTR).val + 12) bs sks) = true) ∧
          (bs = [] → wrs (memOf Mm) ((C.main r0 CTR).val + 7) (atomCells ((C.main r0 CTR).val + 7) ask 0) = true) := by
      intro ma A ask hA hask
      have hAlt : A < H.length := by
        unfold readAtom at hask
        cases e : H[A]? with
        | none => rw [e] at hask; cases hask
        | some c => exact (List.getElem?_eq_some_iff.1 e).1
      have hma := iterI_bound hA hAlt (readAtom_ind hask)
      have hha : headAtom H H.length (D.main q (Dec.DFLD + 43)).val = some (A, ask) := by
        rw [show H.length = (H.length - ma) + ma by omega, headAtom_iter ma _ hA, headAtom_at (by omega), hask]
      refine ⟨hha, ?_⟩
      obtain ⟨qb, hqb, hkb, hpcb, hsumb, hrob⟩ := headRow ma A hA
      have hkqb : (D.main qb Dec.KEY).val < 2 ^ 28 := by rw [hkb]; exact hkl
      have hk2b : DKind D qb 2 := by
        rcases hsumb with hsumb | hinn
        · rcases h.kind_of_ka hqb hsumb with hd | hd
          · have := (h.cellRead hqb hd).2.1
            rw [hkb, hHd, hpcb, hask] at this; cases this
          · exact hd
        · have := (h.indRead hqb (kind_of_inn (decRowF_of h.dec hqb) hinn)).2.1
          rw [hkb, hHd, hpcb, hask] at this; cases this
      have hsumb' : D.main qb Dec.KCELL + D.main qb Dec.KATOM = 1 := by rw [hk2b.2.1, hk2b.2.2.1]; decide
      have h1b : D.main qb Dec.H1 = 1 := by
        rcases h.role_of hqb hsumb' with ⟨_, _, r⟩ | ⟨_, b1, _⟩ | ⟨_, _, r⟩
        · rw [hrob] at r; exact absurd r (by decide)
        · exact b1
        · rw [hrob] at r; exact absurd r (by decide)
      have hkab : D.main qb Dec.KATOM = 1 := by rw [hk2b.2.2.1]; rfl
      have hhat : D.main qb Dec.HAT = 1 := by rw [(decRowF_of h.dec hqb).hat, hkab, h1b]; decide
      have hrab := (h.atomRead hqb hk2b).1
      rw [hkb, hHd, hpcb, hask] at hrab
      cases hrab
      obtain ⟨fA, uA, hfA, hthA⟩ := iterI_peel ma hA hth
      obtain ⟨g, tb, hg, _, htb, _⟩ := readAtom_peel hask hthA
      have hsent : ChainSent D [C.main r0 CTR, D.main qb (Dec.DFLD + 45), 0, 0, 1, 0] := by
        have := (Or.inl ⟨qb, hqb, hkab, rfl⟩ : ChainSent D [D.main qb Dec.KEY, D.main qb (Dec.DFLD + 45),
          1 - D.main qb Dec.H1, 0, D.main qb Dec.H1, 0])
        rwa [hkb, h1b, show (1 : F) - 1 = 0 by decide] at this
      obtain ⟨bs, sks, hrb, hcan, _⟩ := h.chain_bits g _ _ 0 0 _ _ _ tb
        (by rw [show (0 : F) + ofN 2 * 0 = 0 by decide]; exact hsent) (.inl rfl) (.inl rfl) (by rw [hHd]; exact htb)
        (by show 0 + g < _; omega)
      rw [hHd] at hrb
      obtain ⟨hlen, hw, hw0⟩ := h.head_fwd hr0 g bs sks _ _ _ _ hsent (by rw [hHd]; exact hrb) hcan (.inr rfl)
      obtain ⟨a0, a1, a2, a3⟩ := h.hatWrites hqb hkqb hhat
      simp only [hkb] at a0 a1 a2 a3
      simp only [show (0 : F).val = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hlen hw
      refine ⟨bs, sks, g, hrb, hcan, by omega, fun hne => by have := hlen hne; omega, fun hne => ?_, fun he => ?_⟩
      · rw [show atomCells ((C.main r0 CTR).val + 7) ⟨(D.main qb Dec.DFLD).val, (D.main qb (Dec.DFLD + 12)).val,
            (D.main qb (Dec.DFLD + 24)).val, (D.main qb (Dec.DFLD + 36)).val, (D.main qb (Dec.DFLD + 45)).val⟩
            (bitsRoot ((C.main r0 CTR).val + 12) bs) ++ bitCells ((C.main r0 CTR).val + 12) bs sks =
          [.app (D.main qb Dec.DFLD).val ((C.main r0 CTR).val + 7 + 1),
           .app (D.main qb (Dec.DFLD + 12)).val ((C.main r0 CTR).val + 7 + 2),
           .app (D.main qb (Dec.DFLD + 24)).val ((C.main r0 CTR).val + 7 + 3),
           .app (D.main qb (Dec.DFLD + 36)).val ((C.main r0 CTR).val + 7 + 4)] ++
          (.app 0 (bitsRoot ((C.main r0 CTR).val + 12) bs) :: bitCells ((C.main r0 CTR).val + 12) bs sks) from rfl]
        rw [wrs_append]
        simp only [List.length_cons, List.length_nil]
        rw [show (C.main r0 CTR).val + 7 + (0 + 1 + 1 + 1 + 1) = (C.main r0 CTR).val + 11 by omega, hw trivial hne]
        rw [show (C.main r0 CTR).val + 7 + 1 = (C.main r0 CTR).val + 8 by omega,
          show (C.main r0 CTR).val + 7 + 2 = (C.main r0 CTR).val + 9 by omega,
          show (C.main r0 CTR).val + 7 + 3 = (C.main r0 CTR).val + 10 by omega,
          show (C.main r0 CTR).val + 7 + 4 = (C.main r0 CTR).val + 11 by omega]
        simp only [Bool.and_true]
        exact wrs_of a0 (wrs_of a1 (wrs_of a2 (wrs_of a3 rfl)))
      · have b4 := hw0 rfl he
        exact wrs_of a0 (wrs_of a1 (wrs_of a2 (wrs_of a3 (wrs_of b4 rfl))))
    rcases hver with ⟨ma, A, ask, hA, hask, hall⟩ | ⟨ma, A, ask, hA, hask, hK, herr, hwc⟩ |
        ⟨ma, A, hA, hna, ⟨csk', hc'⟩, herr, hwc⟩
    · -- an atom head with bits: the decrement
      obtain ⟨hha, bs, sks, g, hrb, hcan, hg, hlen, hwne, _⟩ := atomHead ma A ask hA hask
      obtain ⟨hne, herr, hwc⟩ := hall g bs sks hrb
      have hsl := readBitsI_length hrb
      obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
        cases bs with
        | nil => exact absurd rfl hne
        | cons b bs' => exact ⟨b, bs', rfl⟩
      refine decRowI_of hpre1 hpre2 hpre3 (s := .cell (.atom (b :: bs')) rt) (csk := some ⟨(D.main q (Dec.DFLD + 4)).val,
        (D.main q (Dec.DFLD + 16)).val, (D.main q (Dec.DFLD + 30)).val,
        (D.main q (Dec.DFLD + 34)).val, (D.main q (Dec.DFLD + 29)).val, (D.main q (Dec.DFLD + 43)).val,
        (D.main q (Dec.DFLD + 53)).val⟩)
        (ask := some ask) (sks := sks) ?_ ?_ rfl ?_ ?_
      · simp only [rowOf]
        rw [hHd, hsubj]
        unfold readSubjI
        simp only [hra, hrc, hha, readBitsI_mono hrb hg, hcan, if_true, hrt']
      · simp only [headFits, decide_eq_true_eq]; exact hlen hne
      · simp only [rowOf]
        rw [List.append_assoc, wrs_append, hcw, cellCells_length]
        exact hwne hne
      · simp only [Air.Row.mk.injEq, true_and]
        refine ⟨by rw [hroot1.1, herr]; rfl, ?_⟩
        have hnw : nwr true (b :: bs') ≤ 32 := Nat.le_trans (nwr_le _ _) (hlen hne)
        rw [e2, ← e0, herr, show ofN 3 * (0 : F) = 0 by decide, add_zero',
          val_add_of_lt (by rw [val_key_add hkl (by decide), hwc]; omega), val_key_add hkl (by decide), hwc]
        simp only [rowOf, List.length_append, cellCells_length, atomCells_length, bitCells_len _ _ _ hsl]
        omega
    · -- the empty head: a crash
      obtain ⟨hha, bs, sks, g, hrb, hcan, hg, _, _, hw0⟩ := atomHead ma A ask hA hask
      have hbs := hK g bs sks hrb
      subst hbs
      have hsk : sks = [] := by have := readBitsI_length hrb; cases sks with
        | nil => rfl
        | cons _ _ => cases this
      subst hsk
      have hse : D.main q Dec.SUBERR = 1 := by rw [(decRowF_of h.dec hq).suberr, hsub, herr]; decide
      obtain ⟨x0, x1, x2⟩ := h.errWrites hq hkq hse
      simp only [← e0] at x0 x1 x2
      refine decRowI_of hpre1 hpre2 hpre3 (s := .cell (.atom []) rt) (csk := some ⟨(D.main q (Dec.DFLD + 4)).val,
        (D.main q (Dec.DFLD + 16)).val, (D.main q (Dec.DFLD + 30)).val,
        (D.main q (Dec.DFLD + 34)).val, (D.main q (Dec.DFLD + 29)).val, (D.main q (Dec.DFLD + 43)).val,
        (D.main q (Dec.DFLD + 53)).val⟩)
        (ask := some ask) (sks := []) ?_ rfl rfl ?_ ?_
      · simp only [rowOf]
        rw [hHd, hsubj]
        unfold readSubjI
        simp only [hra, hrc, hha, readBitsI_mono hrb hg, hcan, if_true, hrt']
      · simp only [rowOf]
        rw [List.append_assoc, wrs_append, hcw, cellCells_length, wrs_append, hw0 rfl, atomCells_length]
        exact wrs_of x0 (wrs_of x1 (wrs_of x2 rfl))
      · simp only [Air.Row.mk.injEq, true_and]
        exact ⟨by rw [hroot1.1, herr]; rfl, by rw [hroot1.2 herr hwc]; rfl⟩
    · -- a cell head: a crash
      have hAlt : A < H.length := by
        unfold readCellI at hc'
        cases e : H[A]? with
        | none => rw [e] at hc'; cases hc'
        | some c => exact (List.getElem?_eq_some_iff.1 e).1
      have hAi := readCellI_ind hc'
      have hma := iterI_bound hA hAlt hAi
      have hha : headAtom H H.length (D.main q (Dec.DFLD + 43)).val = none := by
        rw [show H.length = (H.length - ma) + ma by omega, headAtom_iter ma _ hA, headAtom_at (by omega), hna]
        dsimp only; rw [hAi]
      obtain ⟨qb, hqb, hkb, hpcb, hsumb, hrob⟩ := headRow ma A hA
      have hkqb : (D.main qb Dec.KEY).val < 2 ^ 28 := by rw [hkb]; exact hkl
      have hk1b : DKind D qb 1 := by
        rcases hsumb with hsumb | hinn
        · rcases h.kind_of_ka hqb hsumb with hd | hd
          · exact hd
          · have := (h.atomRead hqb hd).1
            rw [hkb, hHd, hpcb, hna] at this; cases this
        · have := (h.indRead hqb (kind_of_inn (decRowF_of h.dec hqb) hinn)).1
          rw [hkb, hHd, hpcb, hAi] at this; cases this
      have hkcb : D.main qb Dec.KCELL = 1 := by rw [hk1b.2.1]; rfl
      have hsumb' : D.main qb Dec.KCELL + D.main qb Dec.KATOM = 1 := by rw [hk1b.2.1, hk1b.2.2.1]; decide
      have h1b : D.main qb Dec.H1 = 1 := by
        rcases h.role_of hqb hsumb' with ⟨_, _, r⟩ | ⟨_, b1, _⟩ | ⟨_, _, r⟩
        · rw [hrob] at r; exact absurd r (by decide)
        · exact b1
        · rw [hrob] at r; exact absurd r (by decide)
      have hhc : D.main qb Dec.HC = 1 := by rw [(decRowF_of h.dec hqb).hc, hkcb, h1b]; decide
      have hz := h.hcWrites hqb hkqb hhc
      simp only [hkb] at hz
      obtain ⟨sh, hsh⟩ := h.need_nn f _ _ _ th nh (by rw [hHd]; exact hth) (by omega)
      rw [hHd] at hsh
      have hsh' := readNnI_mono hsh (show f ≤ H.length by omega)
      obtain ⟨a, b, rfl⟩ := readNnI_cell hsh' hha
      have hse : D.main q Dec.SUBERR = 1 := by rw [(decRowF_of h.dec hq).suberr, hsub, herr]; decide
      obtain ⟨x0, x1, x2⟩ := h.errWrites hq hkq hse
      simp only [← e0] at x0 x1 x2
      refine decRowI_of hpre1 hpre2 hpre3 (s := .cell (.cell a b) rt) (csk := some ⟨(D.main q (Dec.DFLD + 4)).val,
        (D.main q (Dec.DFLD + 16)).val, (D.main q (Dec.DFLD + 30)).val,
        (D.main q (Dec.DFLD + 34)).val, (D.main q (Dec.DFLD + 29)).val, (D.main q (Dec.DFLD + 43)).val,
        (D.main q (Dec.DFLD + 53)).val⟩)
        (ask := none) (sks := []) ?_ rfl rfl ?_ ?_
      · simp only [rowOf]
        rw [hHd, hsubj]
        unfold readSubjI
        simp only [hra, hrc, hha, hsh', hrt']
      · simp only [rowOf]
        rw [List.append_assoc, wrs_append, hcw, cellCells_length, wrs_append, List.length_replicate]
        rw [wrs_eq_true (fun i hi => by
          rw [List.length_replicate] at hi
          rw [List.getElem?_replicate, if_pos hi, show (C.main r0 CTR).val + 7 + i = (C.main r0 CTR).val + 7 + i from rfl]
          exact hz i hi)]
        exact wrs_of x0 (wrs_of x1 (wrs_of x2 rfl))
      · simp only [Air.Row.mk.injEq, true_and]
        exact ⟨by rw [hroot1.1, herr]; rfl, by rw [hroot1.2 herr hwc]; rfl⟩
  · -- an atom subject: a crash
    obtain ⟨h0q, _, hk2, hsumq, hroq, h1q⟩ := h.subj_bits hq (.inr hasub)
    have hk2 := hk2 hasub
    have hka : D.main q Dec.KATOM = 1 := by rw [hk2.2.2.1]; rfl
    have hkq : (D.main q Dec.KEY).val < 2 ^ 28 := by rw [← e0]; exact hkl
    obtain ⟨m0, hm0, hpc⟩ := h.subj_pc hr0 hp hq hsumq hroq e0.symm
    have hra := (h.atomRead hq hk2).1
    rw [← e0, hHd] at hra
    rw [hHd] at hpc hm0
    obtain ⟨FR, uR, hFR, hNR⟩ := iterI_peel m0 hpc hN
    obtain ⟨f, tb, hF, _, htb, _⟩ := readAtom_peel hra hNR
    have hsent : ChainSent D [C.main r0 CTR, D.main q (Dec.DFLD + 45), 1 + ofN 2 * 0, 0, 0, 0] := by
      have := (Or.inl ⟨q, hq, hka, rfl⟩ : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 45),
        1 - D.main q Dec.H1, 0, D.main q Dec.H1, 0])
      rwa [← e0, h1q, show (1 : F) - 0 = 1 + ofN 2 * 0 by decide] at this
    obtain ⟨bs, sks, hrb, hcan, _⟩ := h.chain_bits f _ _ _ _ _ _ _ tb hsent (.inr rfl) (.inl rfl)
      (by rw [hHd]; exact htb) (by show 0 + f < _; omega)
    rw [hHd] at hrb
    have hsubj : readSubjI H H.length (C.main r0 (FLD + 2)).val = readSubjI H (H.length - m0 - 1 + 1)
        (D.main q Dec.PC).val := by
      rw [← readSubjI_iter m0 _ hpc]; congr 1; omega
    obtain ⟨x0, x1, x2⟩ := h.asubWrites hq hkq hasub
    simp only [← e0] at x0 x1 x2
    refine decRowI_of hpre1' hpre2' hpre3' (s := .atom bs) (csk := none)
      (ask := some ⟨(D.main q Dec.DFLD).val, (D.main q (Dec.DFLD + 12)).val, (D.main q (Dec.DFLD + 24)).val,
        (D.main q (Dec.DFLD + 36)).val, (D.main q (Dec.DFLD + 45)).val⟩) (sks := sks) ?_ rfl rfl ?_ ?_
    · simp only [rowOf]
      rw [hHd, hsubj]
      unfold readSubjI
      simp only [hra, readBitsI_mono hrb (show f ≤ H.length by omega), hcan, if_true]
    · simp only [rowOf]
      exact wrs_of x0 (wrs_of x1 (wrs_of x2 rfl))
    · simp only [Air.Row.mk.injEq, true_and]
      refine ⟨by rw [e1, ← e0]; rfl, ?_⟩
      rw [e2, ← e0, val_key_add hkl (by decide)]
      rfl
end

end Circuit
