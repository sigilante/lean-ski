import Ski.Circuit.CompDCtr

/-!
# The circuit with the `dec` jet: the subject's need tree

At a jet row's key `k`, with `H` the memory below `k`:

- the subject's rows (role `0`) read the CPU's pointer after a run of
  thunks (`CompDOK.subj_pc`), and the head's rows (role `1`) the subject's
  head after one (`head_pc`);
- **the need tree is finite**: a need on `decn` at a pointer whose read-back
  is finite is a noun `DecJet.readNnI` reads, at the same fuel
  (`CompDOK.need_nn`).  A need is received by a `Cell` row, which reads the
  pointer as `readCellI` and needs its halves, or by an `Atom` row, which
  reads `readAtom` and starts its bits' chain, or by an indirection row,
  which passes it on two fuels below;
- **a chain is a canonical bit list**: a chain's step at a pointer whose
  read-back is finite is `DecJet.readBitsI` there, canonical
  (`CompDOK.chain_bits`): empty when the step is marked as a list's end,
  non-empty when it is not and its level is not `0`.  A `Cons` row passes
  to its tail three fuels below, marking the step when it is the last, whose
  bit is then set; a nil row reads `K`; an indirection row passes the step
  on.

The fuel is the read-back's: the CPU state decodes, so the subject's
read-back is finite, and each row peels its pattern from it.  No
acyclicity of the heap is assumed: a cycle has no finite read-back.
-/

namespace DecJet

theorem readNn_mono {H : List Cell} : ∀ {n m p : Nat} {s : Nn}, readNn H n p = some s → n ≤ m → readNn H m p = some s
  | 0, _, _, _, h, _ => nomatch h
  | n + 1, m, p, s, h, hnm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold readNn at h ⊢
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h; dsimp only at h ⊢
      cases hb : readBits H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q => rw [hb] at h; rw [readBits_mono hb hnm]; exact h
    | none =>
      rw [ha] at h; dsimp only at h ⊢
      cases hc : readCell H p with
      | none => rw [hc] at h; cases h
      | some sk =>
        rw [hc] at h; dsimp only at h ⊢
        cases hh : readNn H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNn H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st =>
            rw [hh, ht] at h
            rw [readNn_mono hh (by omega), readNn_mono ht (by omega)]
            exact h

theorem readBits_K {H : List Cell} {p n : Nat} (hk : isK H p = true) (hn : 1 ≤ n) : readBits H n p = some ([], []) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold readBits; rw [if_pos hk]

theorem readBits_cons {H : List Cell} {p n : Nat} {b : Bool} {sk : ConsSk} {bs : List Bool} {sks : List ConsSk}
    (hk : isK H p = false) (hc : readCons H p = some (b, sk)) (hr : readBits H n sk.t = some (bs, sks)) :
    readBits H (n + 1) p = some (b :: bs, sk :: sks) := by
  unfold readBits; rw [if_neg (by rw [hk]; decide), hc]; dsimp only; rw [hr]

theorem readBits_nil_K {H : List Cell} : ∀ {n p : Nat} {sks : List ConsSk}, readBits H n p = some ([], sks) → isK H p = true
  | 0, _, _, h => nomatch h
  | n + 1, p, sks, h => by
    unfold readBits at h
    split at h
    · assumption
    · cases hc : readCons H p with
      | none => rw [hc] at h; cases h
      | some q =>
        rw [hc] at h; dsimp only at h
        cases hr : readBits H n q.2.t with
        | none => rw [hr] at h; cases h
        | some q' => rw [hr] at h; cases h

theorem canonB_cons_cons {b : Bool} {bs : List Bool} (hne : bs ≠ []) (h : canonB bs = true) : canonB (b :: bs) = true := by
  cases bs with
  | nil => exact absurd rfl hne
  | cons c cs => exact h

theorem isK_app {H : List Cell} {a x y : Nat} (h : H[a]? = some (.app x y)) : isK H a = false := by
  simp [isK, h]

theorem readBitsI_mono {H : List Cell} : ∀ {n m p : Nat} {x : List Bool × List ConsSk},
    readBitsI H n p = some x → n ≤ m → readBitsI H m p = some x
  | 0, _, _, _, h, _ => nomatch h
  | n + 1, m, p, x, h, hnm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold readBitsI at h ⊢
    split at h
    · rename_i hk; rw [if_pos hk]; exact h
    · rename_i hk
      rw [if_neg hk]
      cases hc : readCons H p with
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h
        dsimp only at h ⊢
        cases hr : readBitsI H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          rw [hr] at h
          rw [readBitsI_mono hr (by omega)]
          exact h
      | none =>
        rw [hc] at h
        dsimp only at h ⊢
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h; dsimp only at h ⊢; exact readBitsI_mono h (by omega)

theorem readBitsI_K {H : List Cell} {p n : Nat} (hk : isK H p = true) (hn : 1 ≤ n) :
    readBitsI H n p = some ([], []) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  unfold readBitsI; rw [if_pos hk]

theorem readBitsI_cons {H : List Cell} {p n : Nat} {b : Bool} {sk : ConsSk} {bs : List Bool} {sks : List ConsSk}
    (hk : isK H p = false) (hc : readCons H p = some (b, sk)) (hr : readBitsI H n sk.t = some (bs, sks)) :
    readBitsI H (n + 1) p = some (b :: bs, sk :: sks) := by
  unfold readBitsI; rw [if_neg (by rw [hk]; decide), hc]; dsimp only; rw [hr]

theorem readBitsI_ind {H : List Cell} {p n R : Nat} {x : List Bool × List ConsSk} (hi : readInd H p = some R)
    (hr : readBitsI H n R = some x) : readBitsI H (n + 1) p = some x := by
  unfold readBitsI
  rw [if_neg (by rw [readInd_isK hi]; decide), readInd_cons hi]
  dsimp only; rw [hi]; exact hr

theorem readCellI_ind {H : List Cell} {p : Nat} {sk : CellSk} (h : readCellI H p = some sk) : readInd H p = none := by
  unfold readCellI at h
  split at h <;> try cases h
  rename_i k0 y1 hp
  repeat (split at h <;> try cases h)
  all_goals
    have hall := ‹(isK H k0 && _ && _ && _ && _ && _) = true›
    simp only [Bool.and_eq_true] at hall
    exact readInd_none_of_K hp hall.1.1.1.1.1

theorem readInd_atom {H : List Cell} {p R : Nat} (hi : readInd H p = some R) : readAtom H p = none := by
  cases ha : readAtom H p with
  | none => rfl
  | some sk => rw [readAtom_ind ha] at hi; cases hi

theorem readInd_cellI {H : List Cell} {p R : Nat} (hi : readInd H p = some R) : readCellI H p = none := by
  cases ha : readCellI H p with
  | none => rfl
  | some sk => rw [readCellI_ind ha] at hi; cases hi

theorem readNnI_mono {H : List Cell} : ∀ {n m p : Nat} {s : Nn}, readNnI H n p = some s → n ≤ m → readNnI H m p = some s
  | 0, _, _, _, h, _ => nomatch h
  | n + 1, m, p, s, h, hnm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold readNnI at h ⊢
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h; dsimp only at h ⊢
      cases hb : readBitsI H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q => rw [hb] at h; rw [readBitsI_mono hb hnm]; exact h
    | none =>
      rw [ha] at h; dsimp only at h ⊢
      cases hc : readCellI H p with
      | some sk =>
        rw [hc] at h; dsimp only at h ⊢
        cases hh : readNnI H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNnI H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st =>
            rw [hh, ht] at h
            rw [readNnI_mono hh (by omega), readNnI_mono ht (by omega)]
            exact h
      | none =>
        rw [hc] at h; dsimp only at h ⊢
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h; dsimp only at h ⊢; exact readNnI_mono h (by omega)

end DecJet

namespace Circuit

open B Air DecJet

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

/-- A wrapper row's role, from its kind's columns. -/
theorem CompDOK.role_of {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1) :
    (D.main q Dec.H0 = 1 ∧ D.main q Dec.H1 = 0 ∧ D.main q Dec.RO = 0) ∨
    (D.main q Dec.H0 = 0 ∧ D.main q Dec.H1 = 1 ∧ D.main q Dec.RO = 1) ∨
    (D.main q Dec.H0 = 0 ∧ D.main q Dec.H1 = 0 ∧ D.main q Dec.RO = 2) := dec_role h.dec hq hk

variable {r0 : Nat} (hr0 : r0 < C.h) (hp0 : C.main r0 DECSEL = 1)
include hr0 hp0

/-- A wrapper row's pointer is not a thunk, and is in the memory below its key. -/
theorem CompDOK.ka_noind {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1) :
    readInd ((memOf Mm).take (D.main q Dec.KEY).val) (D.main q Dec.PC).val = none ∧
      (D.main q Dec.PC).val < ((memOf Mm).take (D.main q Dec.KEY).val).length := by
  rcases h.kind_of_ka hq hk with hd | hd
  · exact ⟨(h.cellRead hq hd).2.2.2.1, h.pc_lt hq hd (by decide)⟩
  · exact ⟨readAtom_ind (h.atomRead hq hd).1, h.pc_lt hq hd (by decide)⟩

/-- **The subject's rows read the CPU's pointer**, after a run of thunks. -/
theorem CompDOK.subj_pc {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1)
    (hro : D.main q Dec.RO = 0) (hkey : D.main q Dec.KEY = C.main r0 CTR) :
    ∃ m, m < ((memOf Mm).take (C.main r0 CTR).val).length ∧
      iterI ((memOf Mm).take (C.main r0 CTR).val) m (C.main r0 (FLD + 2)).val = some (D.main q Dec.PC).val := by
  obtain ⟨hni, hlt⟩ := h.ka_noind hr0 hp0 hq hk
  have hs := h.need_sent ⟨q, hq, .inl hk, rfl⟩
  obtain ⟨m, p, hm, h0, hp⟩ := h.need_back' hs hni hlt
  rw [hkey] at hm hp
  rcases h0 with ⟨r1, hr1, hp1, e⟩ | ⟨q', hq', _, e | e⟩ <;> simp only [List.cons.injEq, and_true] at e
  · obtain ⟨e0, e1, _⟩ := e
    have := h.jet_key_unique hr0 hr1 hp0 hp1 (by rw [← hkey, e0])
    subst this
    rw [e1] at hp
    exact ⟨m, hm, hp⟩
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2
    rcases (decRowF_of h.dec hq').h0 with z | z <;> rw [z] at e2 <;> exact absurd e2 (by decide)
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2; exact absurd e2 (by decide)

/-- **The head's rows read the subject's head**, after a run of thunks:
    the subject is the `Cell` at the end of the CPU pointer's run. -/
theorem CompDOK.head_pc {R m0 : Nat} {csk : CellSk}
    (hR : iterI ((memOf Mm).take (C.main r0 CTR).val) m0 (C.main r0 (FLD + 2)).val = some R)
    (hc : readCellI ((memOf Mm).take (C.main r0 CTR).val) R = some csk)
    {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1)
    (hro : D.main q Dec.RO = 1) (hkey : D.main q Dec.KEY = C.main r0 CTR) :
    ∃ m, m < ((memOf Mm).take (C.main r0 CTR).val).length ∧
      iterI ((memOf Mm).take (C.main r0 CTR).val) m csk.h = some (D.main q Dec.PC).val := by
  obtain ⟨hni, hlt⟩ := h.ka_noind hr0 hp0 hq hk
  have hs := h.need_sent ⟨q, hq, .inl hk, rfl⟩
  obtain ⟨m, p, hm, h0, hp⟩ := h.need_back' hs hni hlt
  rw [hkey] at hm hp
  rcases h0 with ⟨r1, hr1, hp1, e⟩ | ⟨q', hq', hkc, e | e⟩ <;> simp only [List.cons.injEq, and_true] at e
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2; exact absurd e2 (by decide)
  · obtain ⟨e0, e1, e2⟩ := e
    have hf' := decRowF_of h.dec hq'
    have h0' : D.main q' Dec.H0 = 1 := by
      rw [hro] at e2
      rcases hf'.h0 with z | z <;> rw [z] at e2
      · exact absurd e2 (by decide)
      · exact z
    have hk' : DKind D q' 1 := by
      obtain ⟨dk, hd⟩ := dkind_of hf'
      rw [hd.2.1] at hkc
      have : dk = 1 := by by_cases e : dk = 1; exact e; rw [if_neg e] at hkc; exact absurd hkc (by decide)
      subst this; exact hd
    have hka' : D.main q' Dec.KCELL + D.main q' Dec.KATOM = 1 := by rw [hk'.2.1, hk'.2.2.1]; decide
    have hro' : D.main q' Dec.RO = 0 := by
      rcases h.role_of hq' hka' with ⟨_, _, r⟩ | ⟨z, _, _⟩ | ⟨z, _, _⟩
      · exact r
      · rw [h0'] at z; exact absurd z (by decide)
      · rw [h0'] at z; exact absurd z (by decide)
    have hkey' : D.main q' Dec.KEY = C.main r0 CTR := by rw [← hkey, e0]
    obtain ⟨m', _, hpc'⟩ := h.subj_pc hr0 hp0 hq' hka' hro' hkey'
    have hcr := h.cellRead hq' hk'
    dsimp only at hcr
    rw [hkey'] at hcr
    have eR : R = (D.main q' Dec.PC).val := iterI_det hR (readCellI_ind hc) hpc' hcr.2.2.2.1
    rw [← eR, hc] at hcr
    obtain ⟨hcr1, _⟩ := hcr
    cases hcr1
    rw [e1] at hp
    exact ⟨m, hm, hp⟩
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2; exact absurd e2 (by decide)

omit hr0 hp0 in
/-- **A chain's step reads a canonical bit list** at its pointer, at the
    pointer's read-back fuel, through thunks: a list's end when the step is
    marked so, a non-empty list when it is not and its level is not `0`. -/
theorem CompDOK.chain_bits : ∀ (G : Nat) (k a m t l bw wc : F) (u : OTerm),
    ChainSent D [k, a, m + ofN 2 * t, l, bw, wc] → (m = 0 ∨ m = 1) → (t = 0 ∨ t = 1) →
    Mach.otermAt ((memOf Mm).take k.val) G a.val = some u → l.val + G < 2 ^ 29 →
    ∃ bs sks, readBitsI ((memOf Mm).take k.val) G a.val = some (bs, sks) ∧ canonB bs = true ∧
      (t = 1 → bs = []) ∧ (t = 0 → l ≠ 0 → bs ≠ []) := by
  intro G
  induction G using Nat.strongRecOn with
  | _ G ih =>
    intro k a m t l bw wc u hs hm ht hu hlG
    obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
    have hf := decRowF_of h.dec hq
    have hmt := bits2 hm ht hf.mode hf.term e2
    rcases hkn with hkc | hkn | hkb
    · -- a `Cons`: its tail is the next step
      have hk : DKind D q 3 := by
        rcases h.kind_of_cn hq (.inl hkc) with hd | hd
        · exact hd
        · rw [hd.2.2.2.1] at hkc; exact absurd hkc (by decide)
      have htm : D.main q Dec.TERM = 0 := by have := hf.consTerm; rwa [hkc, one_mul'] at this
      have ht0 : t = 0 := by rw [hmt.2, htm]
      obtain ⟨hnk, hrc⟩ := h.consRead hq hk
      rw [← e0, ← e1] at hnk hrc
      obtain ⟨f, tt, hF, _, _, htt, _, _⟩ := readCons_peel hrc hu
      have hcs : D.main q Dec.CSEND = 1 := by rw [hf.csend, hkc]
      have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 29),
          D.main q Dec.MODE + ofN 2 * D.main q Dec.ISLAST, D.main q Dec.LVL + 1, D.main q Dec.NBW,
          D.main q Dec.WCN] := .inr (.inl ⟨q, hq, hcs, rfl⟩)
      rw [← e0] at hsent
      have hlP : (D.main q Dec.LVL + 1).val = (D.main q Dec.LVL).val + 1 := by
        apply val_add_of_lt; have hPP : P = 2013265921 := rfl; rw [← e3]; show l.val + 1 < P; omega
      obtain ⟨bs, sks, hrb, hcan, hend, hne⟩ := ih (f + 1) (by omega) _ _ _ _ _ _ _ tt hsent hf.mode hf.last htt
        (by rw [hlP, ← e3]; omega)
      refine ⟨decide (D.main q Dec.BIT = 1) :: bs, ⟨(D.main q (Dec.DFLD + 6)).val, (D.main q (Dec.DFLD + 10)).val,
        (D.main q (Dec.DFLD + 29)).val⟩ :: sks, ?_, ?_, fun h1 => by rw [ht0] at h1; exact absurd h1 (by decide), fun _ _ => List.cons_ne_nil _ _⟩
      · rw [hF]; exact readBitsI_cons hnk hrc (readBitsI_mono hrb (by omega))
      · rcases hf.last with hl | hl
        · have hb : D.main q Dec.LVL + 1 ≠ 0 := by
            intro z; have := congrArg Fin.val z; rw [hlP] at this; exact absurd this (by show _ + 1 ≠ 0; omega)
          exact canonB_cons_cons (hne hl hb) hcan
        · have hb : D.main q Dec.BIT = 1 := by
            have := hf.canon
            rw [hkc, hl] at this
            rcases hf.bit with z | z
            · rw [z] at this; exact absurd this (by decide)
            · exact z
          rw [hend hl, hb]; rfl
    · -- a nil: a list's end, or the empty list at level `0`
      have hk : DKind D q 4 := by
        rcases h.kind_of_cn hq (.inr hkn) with hd | hd
        · rw [hd.2.2.2.2.1] at hkn; exact absurd hkn (by decide)
        · exact hd
      have hK := h.nilRead hq hk
      rw [← e0, ← e1] at hK
      refine ⟨[], [], readBitsI_K hK (otermAt_pos hu), rfl, fun _ => rfl, fun h0 hl => ?_⟩
      have hz := hf.nilLvl
      rw [hkn, one_mul', ← hmt.2, h0, show (1 : F) - 0 = 1 by decide, one_mul'] at hz
      exact absurd (by rw [e3, hz]) hl
    · -- an indirection: the same step at its target
      have hk := kind_of_inb hf hkb
      obtain ⟨hi, _⟩ := h.indRead hq hk
      rw [← e0, ← e1] at hi
      obtain ⟨f, tr, hF, hR, _⟩ := readInd_peel hi hu
      have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3),
          D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM, D.main q Dec.LVL, D.main q Dec.BW,
          D.main q Dec.WC] := .inr (.inr ⟨q, hq, hkb, rfl⟩)
      rw [← e0, ← hmt.1, ← hmt.2, ← e3] at hsent
      obtain ⟨bs, sks, hrb, hcan, hend, hne⟩ := ih f (by omega) _ _ _ _ _ _ _ tr hsent hm ht hR (by omega)
      refine ⟨bs, sks, ?_, hcan, hend, hne⟩
      rw [hF]; exact readBitsI_ind hi (readBitsI_mono hrb (by omega))

omit hr0 hp0 in
/-- **The need tree is finite**: a need at a pointer whose read-back is
    finite is a noun read there through thunks, at the read-back's fuel. -/
theorem CompDOK.need_nn : ∀ (G : Nat) (k a ρ : F) (u : OTerm),
    NeedSent C D [k, a, ρ] → Mach.otermAt ((memOf Mm).take k.val) G a.val = some u → G < 2 ^ 29 →
    ∃ s, readNnI ((memOf Mm).take k.val) G a.val = some s := by
  intro G
  induction G using Nat.strongRecOn with
  | _ G ih =>
    intro k a ρ u hs hu hG
    obtain ⟨q, hq, hka, e⟩ := h.need_recv hs
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2⟩ := e
    rcases hka with hka | hkn
    · rcases h.kind_of_ka hq hka with hk | hk
      · -- a `Cell`: its halves are needs
        obtain ⟨hrc, hra, _, _, hkt⟩ := h.cellRead hq hk
        rw [← e0, ← e1] at hrc hra
        rw [← e0] at hkt
        obtain ⟨f, th, tt, tk, hF, _, hth, htk, _, _⟩ := readCellI_peel hrc hu
        obtain ⟨g, tt', hg, htt', _⟩ := ktAt_peel hkt htk
        have hkc : D.main q Dec.KCELL = 1 := by rw [hk.2.1]; rfl
        have n1 : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 43), ofN 2 - D.main q Dec.H0] :=
          .inr (.inl ⟨q, hq, hkc, .inl rfl⟩)
        have n2 : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 53), ofN 2] :=
          .inr (.inl ⟨q, hq, hkc, .inr rfl⟩)
        rw [← e0] at n1 n2
        obtain ⟨sh, hsh⟩ := ih f (by omega) _ _ _ th n1 hth (by omega)
        obtain ⟨st, hst⟩ := ih g (by omega) _ _ _ tt' n2 htt' (by omega)
        refine ⟨.cell sh st, ?_⟩
        rw [hF]
        unfold readNnI
        rw [hra, hrc]
        dsimp only
        rw [readNnI_mono hsh (by omega), readNnI_mono hst (by omega)]
      · -- an `Atom`: its bits are a chain
        obtain ⟨hra, _⟩ := h.atomRead hq hk
        rw [← e0, ← e1] at hra
        obtain ⟨f, tb, hF, _, htb, _⟩ := readAtom_peel hra hu
        have hka' : D.main q Dec.KATOM = 1 := by rw [hk.2.2.1]; rfl
        have hc : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 45), (1 - D.main q Dec.H1) + ofN 2 * 0, 0,
            D.main q Dec.H1, 0] := by
          rw [show ofN 2 * (0 : F) = 0 by decide, add_zero']; exact .inl ⟨q, hq, hka', rfl⟩
        rw [← e0] at hc
        obtain ⟨bs, sks, hrb, hcan, _⟩ := h.chain_bits f _ _ _ _ _ _ _ tb hc
          (bit_one_sub (decRowF_of h.dec hq).h1) (.inl rfl) htb (by show 0 + f < _; omega)
        refine ⟨.atom bs, ?_⟩
        rw [hF]
        unfold readNnI
        rw [hra]
        dsimp only
        rw [readBitsI_mono hrb (by omega)]
        dsimp only
        rw [if_pos hcan]
    · -- an indirection: the same need at its target
      have hk := kind_of_inn (decRowF_of h.dec hq) hkn
      obtain ⟨hi, hra, hrc, _, _⟩ := h.indRead hq hk
      rw [← e0, ← e1] at hi hra hrc
      obtain ⟨f, tr, hF, hR, _⟩ := readInd_peel hi hu
      have hsent : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3), D.main q Dec.RO] :=
        .inr (.inr ⟨q, hq, hkn, rfl⟩)
      rw [← e0] at hsent
      obtain ⟨s, hs'⟩ := ih f (by omega) _ _ _ tr hsent hR (by omega)
      refine ⟨s, ?_⟩
      rw [hF]
      unfold readNnI
      rw [hra, hrc]
      dsimp only
      rw [hi]
      exact readNnI_mono hs' (by omega)

end

end Circuit
