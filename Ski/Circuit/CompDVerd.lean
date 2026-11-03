import Ski.Circuit.CompDFwd

/-!
# The circuit with the `dec` jet: the verdict

The subject's row receives one verdict on `decd`, and it is the head's
(`CompDOK.verdict`): the head chain's last `Cons` with its count of written
cells, `6 · nwr true bs` (`DecJet.walk_end`, `bitCells_len`), when the head
is an atom with bits `bs ≠ []`; its nil, with nothing written, when the head
is the empty atom; or a cell head's row.  A verdict from elsewhere would
have to come from a stray chain row, and there is none (`on_walk`).
-/

namespace DecJet

/-- The rewritten `Cons` cells of a decrement under the borrow `bw`. -/
def nwr : Bool → List Bool → Nat
  | _, [] => 0
  | bw, b :: bs => (if bw && !(b && bs.isEmpty) then 1 else 0) + nwr (bw && !b) bs

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

theorem walk_none {H : List Cell} {b0 : Nat} : ∀ {m : Nat}, walk H b0 m = none → ∀ i, walk H b0 (m + i) = none := by
  intro m hm i
  induction i with
  | zero => exact hm
  | succ i ih =>
    show (match walk H b0 (m + i) with
      | some (a, bw, wc) =>
        match readCons H a with
        | some (b, sk) => some (sk.t, bw && !b, wc + if bw && !(b && isK H sk.t) then 6 else 0)
        | none => none
      | none => none) = none
    rw [ih]

theorem isK_iff_nil {H : List Cell} {n a : Nat} {bs : List Bool} {sks : List ConsSk}
    (hr : readBits H n a = some (bs, sks)) : isK H a = bs.isEmpty := by
  cases bs with
  | nil => rw [readBits_nil_K hr]; rfl
  | cons b bs =>
    obtain ⟨_, _, _, _, hnk, _⟩ := readBits_cons_inv hr
    rw [hnk]; rfl

/-- **The head chain's last `Cons` counts every rewritten cell.** -/
theorem walk_end {H : List Cell} {b0 : Nat} : ∀ (bs : List Bool) (sks : List ConsSk) (n j a : Nat) (bw : Bool) (wc : Nat),
    readBits H n a = some (bs, sks) → walk H b0 j = some (a, bw, wc) →
    ∀ (i a' : Nat) (bw' : Bool) (wc' : Nat) (b' : Bool) (sk' : ConsSk),
      walk H b0 (j + i) = some (a', bw', wc') → readCons H a' = some (b', sk') → isK H sk'.t = true →
      bs ≠ [] ∧ wc' + (if bw' && !b' then 6 else 0) = wc + 6 * nwr bw bs := by
  intro bs
  induction bs with
  | nil =>
    intro sks n j a bw wc hr hw i a' bw' wc' b' sk' hw' hc' _
    have hK := readBits_nil_K hr
    exfalso
    cases i with
    | zero =>
      rw [Nat.add_zero, hw] at hw'
      cases hw'
      rw [readCons_K hK] at hc'; cases hc'
    | succ i =>
      have h1 : walk H b0 (j + 1) = none := by
        show (match walk H b0 j with
          | some (a, bw, wc) =>
            match readCons H a with
            | some (b, sk) => some (sk.t, bw && !b, wc + if bw && !(b && isK H sk.t) then 6 else 0)
            | none => none
          | none => none) = none
        rw [hw]; dsimp only; rw [readCons_K hK]
      have := walk_none h1 i
      rw [show j + 1 + i = j + (i + 1) by omega, hw'] at this
      cases this
  | cons b bs ih =>
    intro sks n j a bw wc hr hw i a' bw' wc' b' sk' hw' hc' hk'
    obtain ⟨n', sk, sks', _, _, hc, hr', _⟩ := readBits_cons_inv hr
    have hstep := walk_succ hw hc
    rw [isK_iff_nil hr'] at hstep
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    cases i with
    | zero =>
      rw [Nat.add_zero, hw] at hw'
      cases hw'
      rw [hc] at hc'
      cases hc'
      have hnil : bs = [] := by
        have := isK_iff_nil hr'; rw [hk'] at this
        cases bs with
        | nil => rfl
        | cons _ _ => cases this
      subst hnil
      cases bw <;> cases b <;> rfl
    | succ i =>
      rw [show j + (i + 1) = (j + 1) + i by omega] at hw'
      obtain ⟨_, e⟩ := ih sks' n' (j + 1) sk.t _ _ hr' hstep i a' bw' wc' b' sk' hw' hc' hk'
      rw [e]
      simp only [nwr]
      cases bw <;> cases b <;> cases bs.isEmpty <;> simp <;> omega

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
theorem CompDOK.verdict {csk : CellSk}
    (hc : readCell ((memOf Mm).take (C.main r0 CTR).val) (C.main r0 (FLD + 2)).val = some csk)
    {e w : F} (hv : VerdSent D [C.main r0 CTR, e, w]) :
    let H := (memOf Mm).take (C.main r0 CTR).val
    (∃ ask, readAtom H csk.h = some ask ∧ ∀ nb bs sks, readBits H nb ask.b = some (bs, sks) →
        bs ≠ [] ∧ e = 0 ∧ w.val = 6 * nwr true bs) ∨
    (∃ ask, readAtom H csk.h = some ask ∧ isK H ask.b = true ∧ e = 1 ∧ w = 0) ∨
    (readAtom H csk.h = none ∧ (∃ csk', readCell H csk.h = some csk') ∧ e = 1 ∧ w = 0) := by
  intro H
  have hkl := h.key_lt hr0
  obtain ⟨q, hq, ⟨hd, ev⟩ | ⟨hd, ev⟩ | ⟨hd, ev⟩⟩ := hv <;> simp only [List.cons.injEq, and_true] at ev <;>
    obtain ⟨e0, e1, e2⟩ := ev <;> have hf := decRowF_of h.dec hq
  · -- the head chain's last `Cons`
    rw [hf.done0] at hd
    have hkc : D.main q Dec.KCONS = 1 ∧ D.main q Dec.ISLAST = 1 ∧ D.main q Dec.MODE = 0 := by
      rcases hf.kcons with a | a <;> rcases hf.last with b | b <;> rcases hf.mode with c' | c' <;> rw [a, b, c'] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, b, c'⟩
    obtain ⟨ask, hra, hw⟩ := h.on_walk hr0 hp0 hc _ q hq (.inl hkc.1) e0.symm hkc.2.2 rfl
    refine .inl ⟨ask, hra, fun nb bs sks hrb => ?_⟩
    have hk3 : DKind D q 3 := by
      obtain ⟨dk, hdk⟩ := dkind_of hf
      have := hkc.1; rw [hdk.2.2.2.1] at this
      have : dk = 3 := by by_cases e : dk = 3; exact e; rw [if_neg e] at this; exact absurd this (by decide)
      subst this; exact hdk
    obtain ⟨_, hrc, hlast, _⟩ := h.consRead hq hk3
    rw [← e0] at hrc hlast
    obtain ⟨hne, hend⟩ := walk_end bs sks nb 0 ask.b true 0 hrb rfl _ _ _ _ _ _
      (by rw [Nat.zero_add]; exact hw) hrc (hlast hkc.2.1)
    refine ⟨hne, e1, ?_⟩
    rw [e2, hf.wcn, hf.writes, hf.dropped, hkc.2.1, mul_one']
    have hwc := (h.chain_wc _ _ _ _ _ _ (by rw [← hkc.2.2]; exact h.chain_sent ⟨q, hq, .inl hkc.1, rfl⟩) rfl).2
    have hlv := dec_level h.dec hq hkc.1 hkc.2.2
    unfold DecJet.W at hlv
    have hPP : P = 2013265921 := rfl
    rw [Nat.zero_add] at hend
    rcases hf.bw with a | a <;> rcases hf.bit with b | b <;> rw [a, b] at hend ⊢ <;>
      simp only [show decide ((0 : F) = 1) = false by decide, show decide ((1 : F) = 1) = true by decide,
        Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true,
        Nat.add_zero, decide_true, decide_false, Bool.and_true, Bool.and_false] at hend <;> rw [← hend]
    · rw [show (0 : F) - 0 * 0 = 0 by decide, show ofN 6 * (0 : F) = 0 by decide, add_zero']
    · rw [show (0 : F) - 0 * 1 = 0 by decide, show ofN 6 * (0 : F) = 0 by decide, add_zero']
    · rw [show (1 : F) - 1 * 0 = 1 by decide, show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]
    · rw [show (1 : F) - 1 * 1 = 0 by decide, show ofN 6 * (0 : F) = 0 by decide, add_zero']
  · -- the head chain's nil
    rw [hf.done1] at hd
    have hkn : D.main q Dec.KNIL = 1 ∧ D.main q Dec.MODE = 0 := by
      rcases hf.knil with a | a <;> rcases hf.mode with c' | c' <;> rw [a, c'] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, c'⟩
    have hk4 : DKind D q 4 := by
      obtain ⟨dk, hdk⟩ := dkind_of hf
      have := hkn.1; rw [hdk.2.2.2.2] at this
      have : dk = 4 := by by_cases e : dk = 4; exact e; rw [if_neg e] at this; exact absurd this (by decide)
      subst this; exact hdk
    have hK := h.nilRead hq hk4
    rw [← e0] at hK
    rcases h.chain_sent ⟨q, hq, .inr hkn.1, rfl⟩ with ⟨qa, hqa, hka, ev⟩ | ⟨q', hq', hcs, ev⟩ <;>
      simp only [List.cons.injEq, and_true] at ev
    · obtain ⟨f0, f1, f2, f3, f4, f5⟩ := ev
      have hfa := decRowF_of h.dec hqa
      have hk2 : DKind D qa 2 := by
        obtain ⟨dk, hdk⟩ := dkind_of hfa
        rw [hdk.2.2.1] at hka
        have : dk = 2 := by by_cases e : dk = 2; exact e; rw [if_neg e] at hka; exact absurd hka (by decide)
        subst this; exact hdk
      have hsum : D.main qa Dec.KCELL + D.main qa Dec.KATOM = 1 := by rw [hk2.2.1, hk2.2.2.1]; decide
      have h1 : D.main qa Dec.H1 = 1 := by
        rw [hkn.2] at f2
        rcases hfa.h1 with z | z <;> rw [z] at f2
        · exact absurd f2 (by decide)
        · exact z
      have hro : D.main qa Dec.RO = 1 := by
        rcases h.role_of hqa hsum with ⟨_, z, _⟩ | ⟨_, _, r⟩ | ⟨_, z, _⟩
        · rw [h1] at z; exact absurd z (by decide)
        · exact r
        · rw [h1] at z; exact absurd z (by decide)
      have hkey' : D.main qa Dec.KEY = C.main r0 CTR := by rw [← f0, ← e0]
      have hpc := h.head_pc hr0 hp0 hc hqa hsum hro hkey'
      have hra := (h.atomRead hqa hk2).1
      rw [hkey', hpc] at hra
      refine .inr (.inl ⟨_, hra, ?_, e1, ?_⟩)
      · show isK H (D.main qa (Dec.DFLD + 45)).val = true
        rw [← f1]; exact hK
      · rw [e2, f5]
    · obtain ⟨f0, f1, _, _, _, _⟩ := ev
      have hf' := decRowF_of h.dec hq'
      obtain ⟨hkc', hl'⟩ := cons_of_csend hf' hcs
      have hk3 : DKind D q' 3 := by
        obtain ⟨dk, hdk⟩ := dkind_of hf'
        rw [hdk.2.2.2.1] at hkc'
        have : dk = 3 := by by_cases e : dk = 3; exact e; rw [if_neg e] at hkc'; exact absurd hkc' (by decide)
        subst this; exact hdk
      have hnl := (h.consRead hq' hk3).2.2.2 hl'
      rw [← f0, ← e0, ← f1] at hnl
      rw [isK_app hnl] at hK; exact absurd hK (by decide)
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
    have hpc := h.head_pc hr0 hp0 hc hq hsum hro e0.symm
    obtain ⟨hrc, hra, _⟩ := h.cellRead hq hk1
    rw [← e0, hpc] at hrc hra
    exact .inr (.inr ⟨hra, ⟨_, hrc⟩, e1, e2⟩)

end

end Circuit
