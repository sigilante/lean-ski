import Ski.Circuit.CompDFwd

/-!
# The circuit with the `dec` jet: the verdict

The subject's row receives one verdict on `decd`, and it is the head's
(`CompDOK.verdict`): the head chain's last `Cons` with its count of written
cells, `6 · nwr true bs` (`DecJet.walkS_end`, `bitCells_len`), when the head
is an atom with bits `bs ≠ []`; its nil, with nothing written, when the head
is the empty atom; or a cell head's row, each at the end of a run of thunks
from the subject's head.  A verdict from elsewhere would have to come from a
stray chain row, and there is none (`on_walk`).
-/

namespace DecJet

theorem nwr_false : ∀ bs : List Bool, nwr false bs = 0
  | [] => rfl
  | _ :: bs => by simp only [nwr, Bool.false_and, Bool.false_eq_true, if_false, Nat.zero_add]; exact nwr_false bs

theorem bitCells_len : ∀ (c : Nat) (bs : List Bool) (sks : List ConsSk), sks.length = bs.length →
    (bitCells c bs sks).length = 6 * nwr true bs
  | _, [], _, _ => rfl
  | _, _ :: _, [], h => nomatch h
  | c, false :: bs, sk :: sks, h => by
    rw [bitCells_cons_false, List.length_append, bitCells_len (c + 6) bs sks (Nat.succ.inj h)]
    simp only [nwr, Bool.false_and, Bool.not_false, Bool.and_self, if_true, List.length_cons, List.length_nil]
    omega
  | c, true :: bs, sk :: sks, _ => by
    simp only [bitCells, nwr, Bool.true_and, Bool.not_true, nwr_false, Nat.add_zero]
    cases bs with
    | nil => rfl
    | cons _ _ => simp

theorem readCons_K {H : List Cell} {a : Nat} (hk : isK H a = true) : readCons H a = none := by
  have := isK_eq hk
  unfold readCons; rw [this]

end DecJet

namespace Circuit

open B Air DecJet

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
  {r0 : Nat} (hr0 : r0 < C.h) (hp0 : C.main r0 DECSEL = 1)
include h hr0 hp0

/-- **The verdict is the head's.** -/
theorem CompDOK.verdict {R m0 : Nat} {csk : CellSk}
    (hR : iterI ((memOf Mm).take (C.main r0 CTR).val) m0 (C.main r0 (FLD + 2)).val = some R)
    (hc : readCellI ((memOf Mm).take (C.main r0 CTR).val) R = some csk)
    {e w : F} (hv : VerdSent D [C.main r0 CTR, e, w]) :
    let H := (memOf Mm).take (C.main r0 CTR).val
    (∃ ma A ask, iterI H ma csk.h = some A ∧ readAtom H A = some ask ∧ ∀ nb bs sks, readBitsI H nb ask.b = some (bs, sks) →
        bs ≠ [] ∧ e = 0 ∧ w.val = 6 * nwr true bs) ∨
    (∃ ma A ask, iterI H ma csk.h = some A ∧ readAtom H A = some ask ∧
        (∀ nb bs sks, readBitsI H nb ask.b = some (bs, sks) → bs = []) ∧ e = 1 ∧ w = 0) ∨
    (∃ ma A, iterI H ma csk.h = some A ∧ readAtom H A = none ∧ (∃ csk', readCellI H A = some csk') ∧ e = 1 ∧ w = 0) := by
  intro H
  have hkl := h.key_lt hr0
  obtain ⟨q, hq, ⟨hd, ev⟩ | ⟨hd, ev⟩ | ⟨hd, ev⟩⟩ := hv <;> simp only [List.cons.injEq, and_true] at ev <;>
    obtain ⟨e0, e1, e2⟩ := ev <;> have hf := decRowF_of h.dec hq
  · -- the head chain's last `Cons`
    rw [hf.done0] at hd
    have hkc : D.main q Dec.KCONS = 1 ∧ D.main q Dec.ISLAST = 1 ∧ D.main q Dec.MODE = 0 := by
      rcases hf.kcons with a | a <;> rcases hf.last with b | b <;> rcases hf.mode with c' | c' <;> rw [a, b, c'] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, b, c'⟩
    have hmf : D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM = 0 := by rw [← h.cons_mf hq hkc.1, hkc.2.2]
    obtain ⟨ma, A, ask, hA, hask, j, hw⟩ := h.on_walk hr0 hp0 hR hc _ q hq (.inl hkc.1) e0.symm hmf rfl
    refine .inl ⟨ma, A, ask, hA, hask, fun nb bs sks hrb => ?_⟩
    have hk3 : DKind D q 3 := by
      obtain ⟨dk, hdk⟩ := dkind_of hf
      have := hkc.1; rw [hdk.2.2.2.1] at this
      have : dk = 3 := by by_cases e : dk = 3; exact e; rw [if_neg e] at this; exact absurd this (by decide)
      subst this; exact hdk
    obtain ⟨_, hrc⟩ := h.consRead hq hk3
    rw [← e0] at hrc
    -- its tail is a list's end
    have hcs : D.main q Dec.CSEND = 1 := by rw [hf.csend, hkc.1]
    have hsent : ChainSent D [C.main r0 CTR, D.main q (Dec.DFLD + 29), 0 + ofN 2 * 1, D.main q Dec.LVL + 1,
        D.main q Dec.NBW, D.main q Dec.WCN] := by
      have := (Or.inr (Or.inl ⟨q, hq, hcs, rfl⟩) : ChainSent D _)
      rwa [← e0, hkc.2.2, hkc.2.1] at this
    have hend : ∀ n bs sks, readBitsI H n (D.main q (Dec.DFLD + 29)).val = some (bs, sks) → bs = [] :=
      fun n bs sks hr => h.chain_term _ _ _ _ _ _ _ _ _ hsent (.inl rfl) hr
    obtain ⟨hne, hend'⟩ := walkS_end nb bs sks 0 ask.b 0 true 0 hrb rfl _ _ _ _ _ _ _
      (by rw [Nat.zero_add]; exact hw) (readCons_noind hrc) hrc hend
    refine ⟨hne, e1, ?_⟩
    rw [e2, hf.wcn, hf.writes, hf.dropped, hkc.2.1, mul_one']
    have hwc := (h.chain_wc _ q hq (.inl hkc.1) hmf rfl).2
    have hlv := dec_level h.dec hq hkc.1 hkc.2.2
    unfold DecJet.W at hlv
    have hPP : P = 2013265921 := rfl
    rcases hf.bw with a | a <;> rcases hf.bit with b | b <;> rw [a, b] at hend' ⊢ <;>
      simp only [show decide ((0 : F) = 1) = false by decide, show decide ((1 : F) = 1) = true by decide,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        Nat.add_zero, decide_true, decide_false, Bool.and_true, Bool.and_false, Nat.zero_add] at hend' <;> rw [← hend']
    · rw [show (0 : F) - 0 * 0 = 0 by decide, show ofN 6 * (0 : F) = 0 by decide, add_zero']
    · rw [show (0 : F) - 0 * 1 = 0 by decide, show ofN 6 * (0 : F) = 0 by decide, add_zero']
    · rw [show (1 : F) - 1 * 0 = 1 by decide, show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]
    · rw [show (1 : F) - 1 * 1 = 0 by decide, show ofN 6 * (0 : F) = 0 by decide, add_zero']
  · -- the head chain's nil: the empty head
    rw [hf.done1] at hd
    have hkn : D.main q Dec.KNIL = 1 ∧ D.main q Dec.MODE = 0 ∧ D.main q Dec.TERM = 0 := by
      rcases hf.knil with a | a <;> rcases hf.mode with c' | c' <;> rcases hf.term with t | t <;> rw [a, c', t] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, c', t⟩
    have hk4 : DKind D q 4 := by
      rcases h.kind_of_cn hq (.inr hkn.1) with hd | hd
      · rw [hd.2.2.2.2.1] at hkn; exact absurd hkn.1 (by decide)
      · exact hd
    have hK := h.nilRead hq hk4
    rw [← e0] at hK
    have hl0 : D.main q Dec.LVL = 0 := by
      have hz := hf.nilLvl
      rwa [hkn.1, one_mul', hkn.2.2, show (1 : F) - 0 = 1 by decide, one_mul'] at hz
    obtain ⟨ma, A, ask, hA, hask, j, hw⟩ := h.on_walk hr0 hp0 hR hc _ q hq (.inr hkn.1) e0.symm
      (by rw [hkn.2.1, hkn.2.2]; decide) rfl
    rw [hl0] at hw
    obtain ⟨hit, hbw, hwc⟩ := walkS_level0 j hw
    refine .inr (.inl ⟨ma, A, ask, hA, hask, fun nb bs sks hrb => readBitsI_run_K hrb hit hK, e1, ?_⟩)
    rw [e2]
    exact Fin.ext hwc
  · -- a cell head's row
    rw [hf.hc] at hd
    have hkc : D.main q Dec.KCELL = 1 ∧ D.main q Dec.H1 = 1 := by
      rcases hf.kcell with a | a <;> rcases hf.h1 with b | b <;> rw [a, b] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, b⟩
    have hk1 : DKind D q 1 := by
      obtain ⟨dk, hdk⟩ := dkind_of hf
      have := hkc.1; rw [hdk.2.1] at this
      have : dk = 1 := by by_cases e : dk = 1; exact e; rw [if_neg e] at this; exact absurd this (by decide)
      subst this; exact hdk
    have hsum : D.main q Dec.KCELL + D.main q Dec.KATOM = 1 := by rw [hk1.2.1, hk1.2.2.1]; decide
    have hro : D.main q Dec.RO = 1 := by
      rcases h.role_of hq hsum with ⟨_, z, _⟩ | ⟨_, _, r⟩ | ⟨_, z, _⟩
      · rw [hkc.2] at z; exact absurd z (by decide)
      · exact r
      · rw [hkc.2] at z; exact absurd z (by decide)
    obtain ⟨ma, _, hpc⟩ := h.head_pc hr0 hp0 hR hc hq hsum hro e0.symm
    obtain ⟨hrc, hra, _⟩ := h.cellRead hq hk1
    rw [← e0] at hrc hra
    exact .inr (.inr ⟨ma, _, hpc, hra, ⟨_, hrc⟩, e1, e2⟩)

end

end Circuit
