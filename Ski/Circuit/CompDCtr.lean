import Ski.Circuit.CompDBack

/-!
# The circuit with the `dec` jet: the counter

The head's chain counts its writes in steps of six, at most one per level,
and its levels stay below `32` (`CompDOK.chain_wc`); so every verdict's
count is at most `192` (`verd_wc`) and the result's counter is the key plus
between `3` and `207` (`res_ctr`).  A jet row moves the counter that far
forward (`jet_next_ctr`), every other row as its kind does, so no two jet
rows share a counter (`CompDOK.jet_key_unique`) and each call's messages,
keyed by its counter, are its own.
-/

namespace Circuit

open B Air

/-- What a kind other than the jet's adds to the counter. -/
def incD (k : Nat) : Nat := if k = 0 then 1 else if k = 3 then 3 else 0

theorem cons_of_csend {D : Table} {q : Nat} (hf : DecRowF D q) (h : D.main q Dec.CSEND = 1) :
    D.main q Dec.KCONS = 1 := by
  rw [hf.csend] at h; exact h

/-- Two bits under `a + 2 b` are read back. -/
theorem bits2 {a b c d : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1)
    (h : a + ofN 2 * b = c + ofN 2 * d) : a = c ∧ b = d := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem bits2_zero {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : a + ofN 2 * b = 0) : a = 0 ∧ b = 0 :=
  bits2 ha hb (.inl rfl) (.inl rfl) (by rw [h]; decide)

theorem val_succ_lt {x : F} (h : x.val < 32) : (x + 1).val = x.val + 1 := val_add_of_lt (by have := P_big; show _ + 1 < P; omega)

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

/-- A `Cons` or nil row's pointer is not a thunk. -/
theorem CompDOK.cn_noind {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCONS = 1 ∨ D.main q Dec.KNIL = 1) :
    DecJet.readInd ((memOf Mm).take (D.main q Dec.KEY).val) (D.main q Dec.PC).val = none := by
  rcases h.kind_of_cn hq hk with hd | hd
  · obtain ⟨_, hrc⟩ := h.consRead hq hd
    cases hi : DecJet.readInd ((memOf Mm).take (D.main q Dec.KEY).val) (D.main q Dec.PC).val with
    | none => rfl
    | some R => rw [DecJet.readInd_cons hi] at hrc; cases hrc
  · have hK := h.nilRead hq hd
    cases hi : DecJet.readInd ((memOf Mm).take (D.main q Dec.KEY).val) (D.main q Dec.PC).val with
    | none => rfl
    | some R => rw [DecJet.readInd_isK hi] at hK; cases hK

/-- **The head's chain counts its writes**: a `Cons` or nil row in mode `0`,
    not a list's end, at level `m` has `m ≤ 32` and at most `6 m` written
    cells, back along its chain through any thunks. -/
theorem CompDOK.chain_wc : ∀ (m q : Nat), q < D.h → (D.main q Dec.KCONS = 1 ∨ D.main q Dec.KNIL = 1) →
    D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM = 0 → (D.main q Dec.LVL).val = m →
    m ≤ 32 ∧ (D.main q Dec.WC).val ≤ 6 * m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q0 hq0 hkn hmf hl
    have hrec := h.chain_sent ⟨q0, hq0, by rcases hkn with a | a; exact .inl a; exact .inr (.inl a), rfl⟩
    rw [hmf] at hrec
    obtain ⟨_, p, h0, _⟩ := h.chain_back' hrec (h.cn_noind hq0 hkn)
    rcases h0 with ⟨q, hq, hk, e⟩ | ⟨q, hq, hk, e⟩
    · simp only [List.cons.injEq, and_true] at e
      obtain ⟨_, _, _, e3, _, e5⟩ := e
      rw [e3] at hl; rw [e5]
      simp only [show (0 : F).val = 0 from rfl] at hl ⊢
      exact ⟨by omega, by omega⟩
    · simp only [List.cons.injEq, and_true] at e
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
      have hf := decRowF_of h.dec hq
      have hkc := cons_of_csend hf hk
      have hm0 := (bits2_zero hf.mode hf.last e2.symm).1
      have hlv := dec_level h.dec hq hkc hm0
      have hl' : (D.main q0 Dec.LVL).val = (D.main q Dec.LVL).val + 1 := by rw [e3]; exact val_succ_lt hlv
      have hmf' : D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM = 0 := by rw [← h.cons_mf hq hkc, hm0]
      obtain ⟨_, hw⟩ := ih (D.main q Dec.LVL).val (by unfold DecJet.W at hlv; omega) q hq (.inl hkc) hmf' rfl
      have hwr : D.main q Dec.WRITES = 0 ∨ D.main q Dec.WRITES = 1 := by
        rw [hf.writes, hf.dropped]
        rcases hf.bw with a | a <;> rcases hf.bit with b | b <;> rcases hf.last with c' | c' <;> rw [a, b, c'] <;> decide
      have hwcn := hf.wcn
      rw [e5, hwcn]
      unfold DecJet.W at hlv
      have hPP : P = 2013265921 := rfl
      refine ⟨by omega, ?_⟩
      rw [← hl, hl']
      rcases hwr with z | z <;> rw [z]
      · rw [show ofN 6 * (0 : F) = 0 by decide, add_zero']; omega
      · rw [show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]; omega

/-- **Every verdict's count is small.** -/
theorem CompDOK.verd_wc {k e w : F} (hs : VerdSent D [k, e, w]) : (e = 0 ∨ e = 1) ∧ w.val ≤ 192 := by
  obtain ⟨q, hq, ⟨hd, ev⟩ | ⟨hd, ev⟩ | ⟨hd, ev⟩⟩ := hs <;> simp only [List.cons.injEq, and_true] at ev <;>
    obtain ⟨_, e1, e2⟩ := ev <;> have hf := decRowF_of h.dec hq
  · -- the head's last `Cons`, in mode `0`
    rw [hf.done0] at hd
    have hkc : D.main q Dec.KCONS = 1 ∧ D.main q Dec.MODE = 0 := by
      rcases hf.kcons with a | a <;> rcases hf.last with b | b <;> rcases hf.mode with c' | c' <;> rw [a, b, c'] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, c'⟩
    have hlv := dec_level h.dec hq hkc.1 hkc.2
    obtain ⟨_, hw⟩ := h.chain_wc _ q hq (.inl hkc.1) (by rw [← h.cons_mf hq hkc.1, hkc.2]) rfl
    have hwr : D.main q Dec.WRITES = 0 ∨ D.main q Dec.WRITES = 1 := by
      rw [hf.writes, hf.dropped]
      rcases hf.bw with a | a <;> rcases hf.bit with b | b <;> rcases hf.last with c' | c' <;> rw [a, b, c'] <;> decide
    refine ⟨.inl e1, ?_⟩
    rw [e2, hf.wcn]
    unfold DecJet.W at hlv
    have hPP : P = 2013265921 := rfl
    rcases hwr with z | z <;> rw [z]
    · rw [show ofN 6 * (0 : F) = 0 by decide, add_zero']; omega
    · rw [show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]; omega
  · -- the head's nil, in mode `0`
    rw [hf.done1] at hd
    have hkn : D.main q Dec.KNIL = 1 ∧ D.main q Dec.MODE = 0 ∧ D.main q Dec.TERM = 0 := by
      rcases hf.knil with a | a <;> rcases hf.mode with c' | c' <;> rcases hf.term with t | t <;> rw [a, c', t] at hd
      all_goals first | exact absurd hd (by decide) | exact ⟨a, c', t⟩
    obtain ⟨hl, hw⟩ := h.chain_wc _ q hq (.inr hkn.1) (by rw [hkn.2.1, hkn.2.2]; decide) rfl
    exact ⟨.inr e1, by rw [e2]; omega⟩
  · exact ⟨.inr e1, by rw [e2]; decide⟩

/-- **The result's counter** is its key plus between `3` and `207`. -/
theorem CompDOK.res_ctr {k a b : F} (hs : ResSent D [k, a, b]) : ∃ x, 3 ≤ x ∧ x ≤ 207 ∧ b = k + ofN x := by
  obtain ⟨q, hq, ⟨hd, ev⟩ | ⟨hd, ev⟩⟩ := hs <;> simp only [List.cons.injEq, and_true] at ev <;>
    obtain ⟨e0, _, e2⟩ := ev
  · have hv := h.verd_sent ⟨q, hq, hd, rfl⟩
    obtain ⟨he, hw⟩ := h.verd_wc hv
    have hPP : P = 2013265921 := rfl
    refine ⟨12 + (D.main q Dec.WC).val + 3 * (D.main q Dec.ERR).val, ?_, ?_, ?_⟩
    · omega
    · rcases he with z | z <;> rw [z] <;> simp only [show (0 : F).val = 0 from rfl, show (1 : F).val = 1 from rfl] <;>
        omega
    · rw [e2, e0]
      rcases he with z | z <;> rw [z]
      · rw [show ofN 3 * (0 : F) = 0 by decide, add_zero', show (0 : F).val = 0 from rfl, Nat.mul_zero, Nat.add_zero,
          ofN_add, ofN_val, add_assoc']
      · rw [show ofN 3 * (1 : F) = ofN 3 by decide, show (1 : F).val = 1 from rfl, Nat.mul_one, ofN_add, ofN_add,
          ofN_val, add_assoc', add_assoc', add_assoc']
  · exact ⟨3, by decide, by decide, by rw [e2, e0]⟩

/-- **A jet row moves the counter** forward by between `3` and `207`. -/
theorem CompDOK.jet_next_ctr {r : Nat} (hn : r + 1 < C.h) (hp : C.main r DECSEL = 1) :
    ∃ x, 3 ≤ x ∧ x ≤ 207 ∧ (C.main (r + 1) CTR).val = (C.main r CTR).val + x := by
  have hr : r < C.h := Nat.lt_of_succ_lt hn
  obtain ⟨_, _, e3⟩ := h.jetNext hn hp
  obtain ⟨x, h3, h207, e⟩ := h.res_ctr (h.res_sent ⟨r, hr, hp, rfl⟩)
  have hb := h.ctr_lt hr
  have hPP : P = 2013265921 := rfl
  refine ⟨x, h3, h207, ?_⟩
  rw [e3, e, val_add_nat (by omega)]

/-- **The counter grows by the row's kind**, off the jet. -/
theorem CompDOK.next_ctr {r k : Nat} (hn : r + 1 < C.h) (hk : IsKindD C r k) (hk12 : k ≠ 12) :
    (C.main (r + 1) CTR).val = (C.main r CTR).val + incD k := by
  have hr : r < C.h := Nat.lt_of_succ_lt hn
  obtain ⟨_, _, _, _, _, _, hDec, _, _, hnc⟩ := kind_factsD hr hk
  obtain ⟨_, _, e⟩ := next_regsD h.cpu hr hn
  have hsel : C.main r DECSEL = 0 := by
    rw [← col_eval hr DECSEL]
    show sDec.eval _ = 0
    rw [hDec, if_neg hk12]; rfl
  rw [hnc, hsel, zero_mul', add_zero'] at e
  have cv := col_eval hr
  have hb := h.ctr_lt hr
  have hP := P_big
  have fe : C.main (r + 1) CTR = C.main r CTR + ofN (incD k) := by
    rw [e]
    by_cases k0 : k = 0
    · subst k0
      show (E.add (col CTR) one).eval _ = _
      simp only [E.eval, cv, B.one, B.c, ofN_one]; rfl
    by_cases k3 : k = 3
    · subst k3
      show (E.add (col CTR) (c 3)).eval _ = _
      simp only [E.eval, cv, B.c]; rfl
    have hc : nextCtrOfD k = col CTR := by
      unfold nextCtrOfD nextCtrOfC nextCtrOf
      rw [if_neg hk12]
      by_cases k11 : k = 11
      · rw [if_pos k11]
      · rw [if_neg k11, if_neg k0, if_neg k3]
    have hi : incD k = 0 := by unfold incD; rw [if_neg k0, if_neg k3]
    rw [hc, cv, hi, ofN_zero, add_zero']
  have hinc : incD k ≤ 3 := by unfold incD; split <;> (try split) <;> decide
  have hP' : 2 ^ 27 + 2 ^ 24 + 1 + 3 < P := by decide
  rw [fe, val_add_nat (by omega)]

/-- The counter never decreases. -/
theorem CompDOK.ctr_le {r : Nat} (d : Nat) : r + d < C.h → (C.main r CTR).val ≤ (C.main (r + d) CTR).val := by
  induction d with
  | zero => intro _; exact Nat.le_refl _
  | succ d ih =>
    intro hd
    have hd1 : r + d + 1 < C.h := hd
    have ih := ih (Nat.lt_of_succ_lt hd1)
    obtain ⟨k, hk⟩ := kind_ofD h.cpu (Nat.lt_of_succ_lt hd1)
    rw [show r + (d + 1) = r + d + 1 from rfl]
    by_cases hk12 : k = 12
    · have hp : C.main (r + d) DECSEL = 1 := by rw [hk.2.2.2, if_pos hk12]
      obtain ⟨x, _, _, e⟩ := h.jet_next_ctr hd1 hp
      omega
    · rw [h.next_ctr hd1 hk hk12]; omega

/-- **Past a jet row the counter is higher.** -/
theorem CompDOK.jet_lt {r : Nat} (hp : C.main r DECSEL = 1) {d : Nat} (hd : r + 1 + d < C.h) :
    (C.main r CTR).val + 3 ≤ (C.main (r + 1 + d) CTR).val := by
  have hr1 : r + 1 < C.h := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hd
  obtain ⟨x, hx, _, e⟩ := h.jet_next_ctr hr1 hp
  have hm := h.ctr_le (r := r + 1) d hd
  omega

/-- **No two jet rows share a counter.** -/
theorem CompDOK.jet_key_unique {r r' : Nat} (hr : r < C.h) (hr' : r' < C.h) (hp : C.main r DECSEL = 1)
    (hp' : C.main r' DECSEL = 1) (e : C.main r CTR = C.main r' CTR) : r = r' := by
  rcases Nat.lt_trichotomy r r' with hlt | heq | hgt
  · have := h.jet_lt hp (d := r' - r - 1) (by rw [show r + 1 + (r' - r - 1) = r' by omega]; exact hr')
    rw [show r + 1 + (r' - r - 1) = r' by omega, ← e] at this
    omega
  · exact heq
  · have := h.jet_lt hp' (d := r - r' - 1) (by rw [show r' + 1 + (r - r' - 1) = r by omega]; exact hr)
    rw [show r' + 1 + (r - r' - 1) = r by omega, e] at this
    omega

end

end Circuit
