import Ski.Circuit.CompDWrite

/-!
# The circuit with the `dec` jet: the head's chain writes the decrement

`CompDOK.head_fwd`: a mode-`0` chain step at level `l` over the bits `bs`
is received, level by level, by `Cons` rows below `32` that, under the
borrow, write the link to their rewritten `Cons` and the `Cons` itself,
exactly `DecJet.bitCells` from `key + 12 + 6 l`, and stop where the decrement
stops: at the first set bit, rewritten clear over its tail, or dropped when
it is the top.  An empty head's nil writes the `Atom` wrapper's last cell.
-/

namespace DecJet

theorem readBits_cons_inv {H : List Cell} : ∀ {n p : Nat} {b : Bool} {bs : List Bool} {sks : List ConsSk},
    readBits H n p = some (b :: bs, sks) →
    ∃ n' sk sks', n = n' + 1 ∧ isK H p = false ∧ readCons H p = some (b, sk) ∧
      readBits H n' sk.t = some (bs, sks') ∧ sks = sk :: sks'
  | 0, _, _, _, _, h => nomatch h
  | n + 1, p, b, bs, sks, h => by
    unfold readBits at h
    split at h
    · cases h
    · rename_i hk
      cases hc : readCons H p with
      | none => rw [hc] at h; cases h
      | some q =>
        obtain ⟨b', sk⟩ := q
        rw [hc] at h
        dsimp only at h
        cases hr : readBits H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          obtain ⟨bs', sks'⟩ := q'
          rw [hr] at h
          cases h
          exact ⟨n, sk, sks', rfl, by simpa using hk, rfl, hr, rfl⟩

theorem readBits_K_eq {H : List Cell} {n p : Nat} {x : List Bool × List ConsSk} (hk : isK H p = true)
    (h : readBits H n p = some x) : x = ([], []) := by
  cases n with
  | zero => cases h
  | succ n => unfold readBits at h; rw [if_pos hk] at h; cases h; rfl

theorem wrs_cons (M : List Cell) (c : Nat) (x : Cell) (xs : List Cell) :
    Air.wrs M c (x :: xs) = ((M[c]? == some x) && Air.wrs M (c + 1) xs) := rfl

theorem wrs_of {M : List Cell} {c : Nat} {x : Cell} {xs : List Cell} (h1 : M[c]? = some x)
    (h2 : Air.wrs M (c + 1) xs = true) : Air.wrs M c (x :: xs) = true := by
  rw [wrs_cons, h1, h2]; simp

end DecJet

namespace Circuit

open B Air DecJet

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
  {r0 : Nat} (hr0 : r0 < C.h)
include h hr0

theorem CompDOK.key_lt : (C.main r0 CTR).val < 2 ^ 28 := by
  have := h.ctr_lt hr0; omega

/-- **The head's chain writes the decrement**, through thunks. -/
theorem CompDOK.head_fwd : ∀ (nf : Nat) (bs : List Bool) (sks : List ConsSk) (A L BW WC : F),
    ChainSent D [C.main r0 CTR, A, 0, L, BW, WC] →
    readBitsI ((memOf Mm).take (C.main r0 CTR).val) nf A.val = some (bs, sks) → canonB bs = true →
    (BW = 0 ∨ BW = 1) →
    (bs ≠ [] → L.val + bs.length ≤ 32) ∧
    (BW = 1 → bs ≠ [] → wrs (memOf Mm) ((C.main r0 CTR).val + 11 + 6 * L.val)
        (.app 0 (bitsRoot ((C.main r0 CTR).val + 12 + 6 * L.val) bs) ::
          bitCells ((C.main r0 CTR).val + 12 + 6 * L.val) bs sks) = true) ∧
    (BW = 1 → bs = [] → (memOf Mm)[(C.main r0 CTR).val + 11]? = some (.app 0 0)) := by
  have hkl := h.key_lt hr0
  intro nf
  induction nf using Nat.strongRecOn with
  | _ nf ih =>
  intro bs sks A L BW WC hs hrb hcan hbw
  obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
  have hf := decRowF_of h.dec hq
  obtain ⟨nf', rfl, hcs⟩ := readBitsI_inv hrb
  rcases hcs with ⟨hK, hx⟩ | ⟨b, sk, bs', sks', hnk, hrc, hrb', hx⟩ | ⟨R, hi, hrb'⟩
  · -- `K`: the empty head
    cases hx
    refine ⟨fun hne => absurd rfl hne, fun _ hne => absurd rfl hne, fun hb _ => ?_⟩
    rcases hkn with hkc | hkn | hkb
    · rcases h.kind_of_cn hq (.inl hkc) with hk | hk
      · have := (h.consRead hq hk).1
        rw [← e0, ← e1, hK] at this; exact absurd this (by decide)
      · rw [hk.2.2.2.1] at hkc; exact absurd hkc (by decide)
    · rcases h.kind_of_cn hq (.inr hkn) with hk | hk
      · rw [hk.2.2.2.2.1] at hkn; exact absurd hkn (by decide)
      · have hn : D.main q Dec.NLK = 1 := by rw [hf.nlk, hkn, ← e4, hb]; decide
        have := h.nlkWrite hq (by rw [← e0]; exact hkl) hn
        rw [← e0] at this; exact this
    · have := readInd_isK (h.indRead hq (kind_of_inb hf hkb)).1
      rw [← e0, ← e1, hK] at this; cases this
  · cases hx
    have hk : DKind D q 3 := by
      rcases hkn with hkc | hkn | hkb
      · rcases h.kind_of_cn hq (.inl hkc) with hk | hk
        · exact hk
        · rw [hk.2.2.2.1] at hkc; exact absurd hkc (by decide)
      · rcases h.kind_of_cn hq (.inr hkn) with hk | hk
        · rw [hk.2.2.2.2.1] at hkn; exact absurd hkn (by decide)
        · have := h.nilRead hq hk
          rw [← e0, ← e1, hnk] at this; exact absurd this (by decide)
      · have := (h.indRead hq (kind_of_inb hf hkb)).1
        rw [← e0, ← e1, readCons_noind hrc] at this; cases this
    have hkc : D.main q Dec.KCONS = 1 := by rw [hk.2.2.2.1]; rfl
    have htm : D.main q Dec.TERM = 0 := by have := hf.consTerm; rwa [hkc, one_mul'] at this
    have e2' : D.main q Dec.MODE = 0 := by rw [h.cons_mf hq hkc]; exact e2.symm
    obtain ⟨_, hrc'⟩ := h.consRead hq hk
    rw [← e0, ← e1, hrc] at hrc'
    cases hrc'
    have hlv := dec_level h.dec hq hkc e2'
    unfold DecJet.W at hlv
    rw [← e3] at hlv
    have hkq : (D.main q Dec.KEY).val < 2 ^ 28 := by rw [← e0]; exact hkl
    have hlq : (D.main q Dec.LVL).val < 32 := by rw [← e3]; exact hlv
    obtain ⟨wclk, wcw, wcwl⟩ := h.consWrites hq hkq hlq
    rw [← e0, ← e3] at wclk wcw wcwl
    have hnextl : ∀ dr : F, D.main q Dec.DROPPED = dr → (dr = 0 → (D.main q Dec.NEXTL).val =
        (C.main r0 CTR).val + 12 + 6 * L.val) ∧ (dr = 1 → (D.main q Dec.NEXTL).val = 0) := by
      intro dr hdr
      refine ⟨fun h0 => ?_, fun h1 => ?_⟩
      · rw [hf.nextl, hkc, hdr, h0, ← e0, ← e3, show (1 : F) * (1 - 0) = 1 by decide, one_mul']
        exact val_aE hkl (by omega)
      · rw [hf.nextl, hkc, hdr, h1, show (1 : F) * (1 - 1) = 0 by decide, zero_mul']; rfl
    have hcs : D.main q Dec.CSEND = 1 := by rw [hf.csend, hkc]
    have hsent : ChainSent D [C.main r0 CTR, D.main q (Dec.DFLD + 29), 0 + ofN 2 * D.main q Dec.ISLAST, L + 1,
        D.main q Dec.NBW, D.main q Dec.WCN] := by
      have := (Or.inr (Or.inl ⟨q, hq, hcs, rfl⟩) : ChainSent D _)
      rwa [← e0, e2', ← e3] at this
    have hL1 : (L + 1).val = L.val + 1 := val_succ_lt hlv
    rcases hf.last with hl | hl
    · -- not the last: the chain goes on
      rw [hl, show (0 : F) + ofN 2 * 0 = 0 by decide] at hsent
      have hne : bs' ≠ [] := h.chain_nonterm _ _ _ _ _ _ _ _ _ hsent (.inl rfl)
        (by intro z; rw [z] at hL1; exact absurd hL1 (by show ¬ (0 = _ + 1); omega)) hrb'
      have hbw' : D.main q Dec.NBW = 0 ∨ D.main q Dec.NBW = 1 := by rw [hf.nbw]; exact bit_mul hf.bw (bit_one_sub hf.bit)
      obtain ⟨ihl, ihw, _⟩ := ih nf' (by omega) _ _ _ _ _ _ hsent hrb' (canonB_tail hcan) hbw'
      rw [hL1] at ihl ihw
      have hdr0 : D.main q Dec.DROPPED = 0 := by rw [hf.dropped, hl, mul_zero']
      refine ⟨fun _ => ?_, fun hb _ => ?_, fun _ he => nomatch he⟩
      · have := ihl hne; simp only [List.length_cons]; omega
      · have hclk : D.main q Dec.CLK = 1 := by rw [hf.clk, hkc, ← e4, hb]; decide
        have hw1 := wclk hclk
        rw [(hnextl 0 hdr0).1 rfl] at hw1
        have hroot : bitsRoot ((C.main r0 CTR).val + 12 + 6 * L.val) (decide (D.main q Dec.BIT = 1) :: bs') =
            (C.main r0 CTR).val + 12 + 6 * L.val := by
          unfold bitsRoot dropped
          rw [if_neg]
          intro hd
          cases bs' with
          | nil => exact hne rfl
          | cons _ _ => simp at hd
        rw [hroot]
        have hwr : D.main q Dec.WRITES = 1 := by rw [hf.writes, hdr0, ← e4, hb]; decide
        have hcw : D.main q Dec.CW = 1 := by rw [hf.cw, hkc, hwr]; decide
        obtain ⟨w0, w1, w2, w3, w4⟩ := wcw hcw
        refine wrs_of hw1 ?_
        rw [show (C.main r0 CTR).val + 11 + 6 * L.val + 1 = (C.main r0 CTR).val + 12 + 6 * L.val by omega]
        rcases hf.bit with hb0 | hb1
        · -- a clear bit under the borrow: rewritten set, the borrow goes on
          rw [hb0, show decide ((0 : F) = 1) = false by decide, bitCells_cons_false]
          have hptr : (D.main q Dec.PTR).val = 0 := by rw [hf.ptr, hkc, hb0, ← e4, hb]; decide
          rw [hptr] at w4
          have hnbw : D.main q Dec.NBW = 1 := by rw [hf.nbw, ← e4, hb, hb0]; decide
          have hrest := ihw hnbw hne
          rw [show (C.main r0 CTR).val + 11 + 6 * (L.val + 1) = (C.main r0 CTR).val + 12 + 6 * L.val + 5 by omega,
            show (C.main r0 CTR).val + 12 + 6 * (L.val + 1) = (C.main r0 CTR).val + 12 + 6 * L.val + 6 by omega]
            at hrest
          simp only [List.cons_append, List.nil_append]
          exact wrs_of w0 (wrs_of w1 (wrs_of w2 (wrs_of w3 (wrs_of w4 hrest))))
        · -- the set bit under the borrow: rewritten clear over its tail
          rw [hb1, show decide ((1 : F) = 1) = true by decide]
          show wrs (memOf Mm) _ (if bs' = [] then [] else _) = true
          rw [if_neg hne]
          have hptr : (D.main q Dec.PTR).val = 2 := by rw [hf.ptr, hkc, hb1, ← e4, hb]; decide
          rw [hptr] at w4
          have hwl : D.main q Dec.CWL = 1 := by rw [hf.cwl, hkc, hf.wl, ← e4, hb, hb1, hl]; decide
          have w5 := wcwl hwl
          exact wrs_of w0 (wrs_of w1 (wrs_of w2 (wrs_of w3 (wrs_of w4 (wrs_of w5 rfl)))))
    · -- the last: its bit is set, the top, dropped under the borrow
      have hbit : D.main q Dec.BIT = 1 := by
        have := hf.canon
        rw [hkc, hl] at this
        rcases hf.bit with z | z
        · rw [z] at this; exact absurd this (by decide)
        · exact z
      rw [hl, show (0 : F) + ofN 2 * 1 = 0 + ofN 2 * 1 from rfl] at hsent
      have hnil : bs' = [] := h.chain_term _ _ _ _ _ _ _ _ _ hsent (.inl rfl) hrb'
      subst hnil
      rw [hbit, show decide ((1 : F) = 1) = true by decide]
      refine ⟨fun _ => by simp only [List.length_cons, List.length_nil]; omega, fun hb _ => ?_, fun _ he => nomatch he⟩
      have hclk : D.main q Dec.CLK = 1 := by rw [hf.clk, hkc, ← e4, hb]; decide
      have hdr1 : D.main q Dec.DROPPED = 1 := by rw [hf.dropped, ← e4, hb, hbit, hl]; decide
      have hw1 := wclk hclk
      rw [(hnextl 1 hdr1).2 rfl] at hw1
      have hroot : bitsRoot ((C.main r0 CTR).val + 12 + 6 * L.val) [true] = 0 := rfl
      rw [hroot]
      exact wrs_of hw1 rfl
  · -- a thunk: its row passes the step on to the target
    have hkb : D.main q Dec.INB = 1 := by
      rcases hkn with hkc | hkn | hkb
      · rw [e0, e1, h.cn_noind hq (.inl hkc)] at hi; cases hi
      · rw [e0, e1, h.cn_noind hq (.inr hkn)] at hi; cases hi
      · exact hkb
    obtain ⟨hi', _⟩ := h.indRead hq (kind_of_inb hf hkb)
    rw [← e0, ← e1, hi] at hi'
    cases hi'
    have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3),
        D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM, D.main q Dec.LVL, D.main q Dec.BW,
        D.main q Dec.WC] := .inr (.inr ⟨q, hq, hkb, rfl⟩)
    rw [← e0, ← e2, ← e3, ← e4, ← e5] at hsent
    exact ih nf' (by omega) _ _ _ _ _ _ hsent hrb' hcan hbw

end

end Circuit
