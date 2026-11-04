import Ski.Circuit.CompDCtr

/-!
# The circuit with the `dec` jet: the subject's need tree

At a jet row's key `k`, with `H` the memory below `k`:

- the subject's rows (role `0`) read the CPU's pointer (`CompDOK.subj_pc`),
  and the head's rows (role `1`) the subject's head (`head_pc`);
- **the need tree is finite**: a need on `decn` at a pointer whose read-back
  is finite is a noun `DecJet.readNn` reads, at the same fuel
  (`CompDOK.need_nn`).  A need is received by a `Cell` row, which reads the
  pointer as `readCell` and needs its halves, seven and five fuels below,
  or by an `Atom` row, which reads `readAtom` and starts its bits' chain;
- **a chain is a canonical bit list**: a chain's step at a pointer whose
  read-back is finite is `DecJet.readBits` there, canonical
  (`CompDOK.chain_bits`).  A `Cons` row passes to its tail three fuels
  below unless it is the last, whose tail is `K` and whose bit is set; a
  nil row reads `K`.

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

/-- **The subject's rows read the CPU's pointer.** -/
theorem CompDOK.subj_pc {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1)
    (hro : D.main q Dec.RO = 0) (hkey : D.main q Dec.KEY = C.main r0 CTR) :
    D.main q Dec.PC = C.main r0 (FLD + 2) := by
  rcases h.need_sent ⟨q, hq, hk, rfl⟩ with ⟨r1, hr1, hp1, e⟩ | ⟨q', hq', _, e | e⟩ <;>
    simp only [List.cons.injEq, and_true] at e
  · obtain ⟨e0, e1, _⟩ := e
    have := h.jet_key_unique hr0 hr1 hp0 hp1 (by rw [← hkey, e0])
    subst this
    exact e1
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2
    rcases (decRowF_of h.dec hq').h0 with z | z <;> rw [z] at e2 <;> exact absurd e2 (by decide)
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2; exact absurd e2 (by decide)

/-- **The head's rows read the subject's head.** -/
theorem CompDOK.head_pc {csk : CellSk}
    (hc : readCell ((memOf Mm).take (C.main r0 CTR).val) (C.main r0 (FLD + 2)).val = some csk)
    {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1)
    (hro : D.main q Dec.RO = 1) (hkey : D.main q Dec.KEY = C.main r0 CTR) :
    (D.main q Dec.PC).val = csk.h := by
  rcases h.need_sent ⟨q, hq, hk, rfl⟩ with ⟨r1, hr1, hp1, e⟩ | ⟨q', hq', hkc, e | e⟩ <;>
    simp only [List.cons.injEq, and_true] at e
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
      rcases h.kind_of_ka hq' (by
        obtain ⟨dk, hd⟩ := dkind_of hf'
        rw [hd.2.1] at hkc
        have : dk = 1 := by by_cases e : dk = 1; exact e; rw [if_neg e] at hkc; exact absurd hkc (by decide)
        subst this; rw [hd.2.1, hd.2.2.1]; decide) with hd | hd
      · exact hd
      · rw [hd.2.1] at hkc; exact absurd hkc (by decide)
    have hka' : D.main q' Dec.KCELL + D.main q' Dec.KATOM = 1 := by rw [hk'.2.1, hk'.2.2.1]; decide
    have hro' : D.main q' Dec.RO = 0 := by
      rcases h.role_of hq' hka' with ⟨_, _, r⟩ | ⟨z, _, _⟩ | ⟨z, _, _⟩
      · exact r
      · rw [h0'] at z; exact absurd z (by decide)
      · rw [h0'] at z; exact absurd z (by decide)
    have hpc' := h.subj_pc hr0 hp0 hq' hka' hro' (by rw [← hkey, e0])
    have hcr := (h.cellRead hq' hk').1
    rw [← e0, hkey, hpc', hc] at hcr
    cases hcr
    rw [e1]
  · obtain ⟨_, _, e2⟩ := e
    rw [hro] at e2; exact absurd e2 (by decide)

omit hr0 hp0 in
/-- **A chain's step reads a canonical bit list** at its pointer, at the
    pointer's read-back fuel. -/
theorem CompDOK.chain_bits : ∀ (G : Nat) (k a m l bw wc : F) (u : OTerm),
    ChainSent D [k, a, m, l, bw, wc] → Mach.otermAt ((memOf Mm).take k.val) G a.val = some u →
    ∃ bs sks, readBits ((memOf Mm).take k.val) G a.val = some (bs, sks) ∧ canonB bs = true := by
  intro G
  induction G using Nat.strongRecOn with
  | _ G ih =>
    intro k a m l bw wc u hs hu
    obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
    rcases h.kind_of_cn hq hkn with hk | hk
    · -- a `Cons`
      obtain ⟨hnk, hrc, hlast, hnl⟩ := h.consRead hq hk
      rw [← e0, ← e1] at hnk hrc
      rw [← e0] at hlast hnl
      obtain ⟨f, tt, hF, hf2, _, htt, _, _⟩ := readCons_peel hrc hu
      have hf := decRowF_of h.dec hq
      rcases hf.last with hl | hl
      · -- not the last: the chain goes on at the tail
        have hcs : D.main q Dec.CSEND = 1 := by rw [hf.csend, hk.2.2.2.1, hl]; decide
        have hs' := h.chain_recv (h.chain_sent ⟨q, hq, hkn, rfl⟩)
        have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 29), D.main q Dec.MODE, D.main q Dec.LVL + 1,
            D.main q Dec.NBW, D.main q Dec.WCN] := .inr ⟨q, hq, hcs, rfl⟩
        rw [← e0] at hsent
        obtain ⟨bs, sks, hrb, hcan⟩ := ih (f + 1) (by omega) _ _ _ _ _ _ tt hsent htt
        have hne : bs ≠ [] := by
          intro e
          subst e
          have := readBits_nil_K hrb
          rw [isK_app (hnl hl)] at this
          exact absurd this (by decide)
        refine ⟨_, ⟨(D.main q (Dec.DFLD + 6)).val, (D.main q (Dec.DFLD + 10)).val, (D.main q (Dec.DFLD + 29)).val⟩ :: sks,
          ?_, canonB_cons_cons (b := decide (D.main q Dec.BIT = 1)) hne hcan⟩
        rw [hF]
        exact readBits_cons hnk hrc (readBits_mono hrb (by omega))
      · -- the last: its tail is `K` and its bit is set
        have hb : D.main q Dec.BIT = 1 := by
          have := hf.canon
          rw [hk.2.2.2.1, hl] at this
          rcases hf.bit with z | z
          · rw [z] at this; exact absurd this (by decide)
          · exact z
        rw [hb] at hrc
        refine ⟨[true], [⟨(D.main q (Dec.DFLD + 6)).val, (D.main q (Dec.DFLD + 10)).val,
          (D.main q (Dec.DFLD + 29)).val⟩], ?_, rfl⟩
        rw [hF]
        exact readBits_cons hnk hrc (readBits_K (hlast hl) (by omega))
    · -- a nil
      have hK := h.nilRead hq hk
      rw [← e0, ← e1] at hK
      exact ⟨[], [], readBits_K hK (otermAt_pos hu), rfl⟩

omit hr0 hp0 in
/-- **The need tree is finite**: a need at a pointer whose read-back is
    finite is a noun read there, at the read-back's fuel. -/
theorem CompDOK.need_nn : ∀ (G : Nat) (k a ρ : F) (u : OTerm),
    NeedSent C D [k, a, ρ] → Mach.otermAt ((memOf Mm).take k.val) G a.val = some u →
    ∃ s, readNn ((memOf Mm).take k.val) G a.val = some s := by
  intro G
  induction G using Nat.strongRecOn with
  | _ G ih =>
    intro k a ρ u hs hu
    obtain ⟨q, hq, hka, e⟩ := h.need_recv hs
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, _⟩ := e
    rcases h.kind_of_ka hq hka with hk | hk
    · -- a `Cell`: its halves are needs
      obtain ⟨hrc, hra, _⟩ := h.cellRead hq hk
      rw [← e0, ← e1] at hrc hra
      obtain ⟨f, th, tt, hF, _, hth, htt, _⟩ := readCell_peel hrc hu
      have hkc : D.main q Dec.KCELL = 1 := by rw [hk.2.1]; rfl
      have n1 : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 43), ofN 2 - D.main q Dec.H0] :=
        .inr ⟨q, hq, hkc, .inl rfl⟩
      have n2 : NeedSent C D [D.main q Dec.KEY, D.main q (Dec.DFLD + 47), ofN 2] := .inr ⟨q, hq, hkc, .inr rfl⟩
      rw [← e0] at n1 n2
      obtain ⟨sh, hsh⟩ := ih f (by omega) _ _ _ th n1 hth
      obtain ⟨st, hst⟩ := ih (f + 2) (by omega) _ _ _ tt n2 htt
      refine ⟨.cell sh st, ?_⟩
      rw [hF]
      unfold readNn
      rw [hra, hrc]
      dsimp only
      rw [readNn_mono hsh (by omega), readNn_mono hst (by omega)]
    · -- an `Atom`: its bits are a chain
      obtain ⟨hra, _⟩ := h.atomRead hq hk
      rw [← e0, ← e1] at hra
      obtain ⟨f, tb, hF, _, htb, _⟩ := readAtom_peel hra hu
      have hka' : D.main q Dec.KATOM = 1 := by rw [hk.2.2.1]; rfl
      have hc : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 45), 1 - D.main q Dec.H1, 0, D.main q Dec.H1, 0] :=
        .inl ⟨q, hq, hka', rfl⟩
      rw [← e0] at hc
      obtain ⟨bs, sks, hrb, hcan⟩ := h.chain_bits f _ _ _ _ _ _ tb hc htb
      refine ⟨.atom bs, ?_⟩
      rw [hF]
      unfold readNn
      rw [hra]
      dsimp only
      rw [readBits_mono hrb (by omega)]
      dsimp only
      rw [if_pos hcan]

end

end Circuit
