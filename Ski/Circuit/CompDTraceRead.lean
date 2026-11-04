import Ski.Circuit.CompDTrace
set_option linter.unusedSimpArgs false

/-!
# What an honest DEC row reads

A DEC row over the memory `A`, at a pointer where `Ski/DecJet.lean`'s
reader succeeds below the key, reads its pattern: every active slot's
address is below the key and the memory cell there has the slot's tag
(`DecT.ReadsOK`), and its fields are the reader's (`cellReads`,
`atomReads`, `consReads`, `nilReads`) — the converse of
`Circuit.CompDOK.cellRead` and its kin.
-/

namespace Circuit

open B Air

namespace DecT

/-- **A row reads memory cells**: each active slot below the key, with its tag. -/
def ReadsOK (A : List Cell) (d : DR) : Prop :=
  ∀ j, act d j = true → (sl A d j).1 < d.key ∧ cellTag (A.getD (sl A d j).1 .nil) = (sl A d j).2.1

theorem act_lt {d : DR} {j : Nat} (h : act d j = true) : j < (patOf d.kind).length := by
  unfold act at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem tk {A : List Cell} {key x : Nat} {c : Cell} (h : (A.take key)[x]? = some c) :
    x < key ∧ A.getD x .nil = c := by
  rw [List.getElem?_take] at h
  split at h
  · next hx => exact ⟨hx, by rw [List.getD_eq_getElem?_getD, h]; rfl⟩
  · cases h

theorem skk_dec {H : List Cell} {a : Nat} (h : DecJet.isSKK H a = true) :
    ∃ s kk k1 k2, H[a]? = some (.app s kk) ∧ H[s]? = some .S ∧ H[kk]? = some (.app k1 k2) ∧
      H[k1]? = some .K ∧ H[k2]? = some .K := by
  unfold DecJet.isSKK at h
  repeat' (split at h <;> try contradiction)
  all_goals (try simp only [Bool.and_false, Bool.false_eq_true] at h)
  rename_i _ s kk ha _ k1 k2 hkk
  simp only [Bool.and_eq_true] at h
  exact ⟨s, kk, k1, k2, ha, DecJet.isS_eq h.1, hkk, DecJet.isK_eq h.2.1, DecJet.isK_eq h.2.2⟩

theorem si_dec {H : List Cell} {a : Nat} (h : DecJet.isSI H a = true) :
    ∃ s i, H[a]? = some (.app s i) ∧ H[s]? = some .S ∧ H[i]? = some .I := by
  unfold DecJet.isSI at h
  repeat' (split at h <;> try contradiction)
  rename_i _ s i ha
  simp only [Bool.and_eq_true] at h
  exact ⟨s, i, ha, DecJet.isS_eq h.1, DecJet.isI_eq h.2⟩

theorem boolAt_dec {H : List Cell} {a : Nat} {b : Bool} (h : DecJet.boolAt H a = some b) :
    (b = true ∧ H[a]? = some .K) ∨
      (b = false ∧ ∃ f x, H[a]? = some (.app f x) ∧ H[f]? = some .K ∧ H[x]? = some .I) := by
  unfold DecJet.boolAt at h
  split at h
  · next hk => exact .inl ⟨(Option.some.inj h).symm, hk⟩
  · next f x hk =>
    split at h
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      exact .inr ⟨(Option.some.inj h).symm, f, x, hk, DecJet.isK_eq hc.1, DecJet.isI_eq hc.2⟩
    · cases h
  · cases h

/-- A slot's value from its source and its memory cell. -/
theorem sl_eq (A : List Cell) (d : DR) {j : Nat} {s : Dec.Src} {t : Dec.Tg}
    (hp : (patOf d.kind)[j]? = some (s, t)) {a : Nat} (ha : srcN (slots A d) d.p s = a) {cell : Cell}
    (hc : A.getD a .nil = cell) : sl A d j = (a, tgN d.bit d.last t, cellFields cell) := by
  obtain ⟨hjl, hget⟩ := List.getElem?_eq_some_iff.1 hp
  obtain ⟨e1, e2, e3⟩ := sl_spec A d hjl
  rw [hget] at e1 e2
  rw [e1, ha] at e3
  rw [hc] at e3
  ext
  · exact e1.trans ha
  · exact e2
  · exact congrArg Prod.fst e3
  · exact congrArg Prod.snd e3

/-- **A nil row reads `K`.** -/
theorem nilReads {A : List Cell} {d : DR} (hk : d.kind = 4) (h : DecJet.isK (A.take d.key) d.p = true) :
    ReadsOK A d := by
  obtain ⟨l_p, g_p⟩ := tk (DecJet.isK_eq h)
  have e0 : sl A d 0 = (d.p, 1, 0, 0) := by
    rw [sl_eq A d (j := 0) (s := .rowP) (t := .C 1) (a := d.p) (by rw [hk]; rfl) rfl g_p]; rfl
  intro j hj
  have hjl := act_lt hj
  rw [hk] at hjl
  simp only [patOf] at hjl
  simp at hjl
  subst hjl
  rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩

/-- **A `Cell` row reads its pattern**: its slots are memory cells below
    the key, and its fields the wrapper's. -/
theorem cellReads {A : List Cell} {d : DR} (hk : d.kind = 1) {sk : DecJet.CellSk}
    (h : DecJet.readCell (A.take d.key) d.p = some sk) :
    ReadsOK A d ∧ (sl A d 2).2.2.1 = sk.a1 ∧ (sl A d 8).2.2.1 = sk.a2 ∧ (sl A d 14).2.2.2 = sk.kt ∧
      (sl A d 15).2.2.1 = sk.s3 ∧ (sl A d 17).2.2.1 = sk.si ∧ (sl A d 21).2.2.2 = sk.h ∧ (sl A d 23).2.2.2 = sk.t := by
  unfold DecJet.readCell at h
  repeat' (split at h <;> try contradiction)
  rename_i _ k0 y1 h_p _ a1 y2 h_y1 _ a2 y3 h_y2 _ p1 kt h_y3 _ _ s3 p2 k6 t h_p1 h_kt _ si kh h_p2 _ k5 hh h_kh hc
  simp only [Option.some.injEq] at h; subst h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := hc
  have h_k0 := DecJet.isK_eq c1
  obtain ⟨sa, kka, k1a, k2a, h_a1, h_sa, h_kka, h_k1a, h_k2a⟩ := skk_dec c2
  obtain ⟨sb, kkb, k1b, k2b, h_a2, h_sb, h_kkb, h_k1b, h_k2b⟩ := skk_dec c3
  have h_s3 := DecJet.isS_eq c4
  obtain ⟨sc, ic, h_si, h_sc, h_ic⟩ := si_dec c5
  have h_k5 := DecJet.isK_eq c6
  have h_k6 := DecJet.isK_eq c7
  obtain ⟨l_p, g_p⟩ := tk h_p
  obtain ⟨l_k0, g_k0⟩ := tk h_k0
  obtain ⟨l_y1, g_y1⟩ := tk h_y1
  obtain ⟨l_a1, g_a1⟩ := tk h_a1
  obtain ⟨l_sa, g_sa⟩ := tk h_sa
  obtain ⟨l_kka, g_kka⟩ := tk h_kka
  obtain ⟨l_k1a, g_k1a⟩ := tk h_k1a
  obtain ⟨l_k2a, g_k2a⟩ := tk h_k2a
  obtain ⟨l_y2, g_y2⟩ := tk h_y2
  obtain ⟨l_a2, g_a2⟩ := tk h_a2
  obtain ⟨l_sb, g_sb⟩ := tk h_sb
  obtain ⟨l_kkb, g_kkb⟩ := tk h_kkb
  obtain ⟨l_k1b, g_k1b⟩ := tk h_k1b
  obtain ⟨l_k2b, g_k2b⟩ := tk h_k2b
  obtain ⟨l_y3, g_y3⟩ := tk h_y3
  obtain ⟨l_p1, g_p1⟩ := tk h_p1
  obtain ⟨l_s3, g_s3⟩ := tk h_s3
  obtain ⟨l_p2, g_p2⟩ := tk h_p2
  obtain ⟨l_si, g_si⟩ := tk h_si
  obtain ⟨l_sc, g_sc⟩ := tk h_sc
  obtain ⟨l_ic, g_ic⟩ := tk h_ic
  obtain ⟨l_kh, g_kh⟩ := tk h_kh
  obtain ⟨l_k5, g_k5⟩ := tk h_k5
  obtain ⟨l_kt, g_kt⟩ := tk h_kt
  obtain ⟨l_k6, g_k6⟩ := tk h_k6
  have e0 : sl A d 0 = (d.p, 3, k0, y1) := by
    rw [sl_eq A d (j := 0) (s := .rowP) (t := (.C 3)) (a := d.p) (by rw [hk]; rfl) rfl g_p]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e1 : sl A d 1 = (k0, 1, 0, 0) := by
    rw [sl_eq A d (j := 1) (s := (.F1 0)) (t := (.C 1)) (a := k0) (by rw [hk]; rfl) (by show (sl A d 0).2.2.1 = k0; rw [e0]) g_k0]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e2 : sl A d 2 = (y1, 3, a1, y2) := by
    rw [sl_eq A d (j := 2) (s := (.F2 0)) (t := (.C 3)) (a := y1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.2 = y1; rw [e0]) g_y1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e3 : sl A d 3 = (a1, 3, sa, kka) := by
    rw [sl_eq A d (j := 3) (s := (.F1 2)) (t := (.C 3)) (a := a1) (by rw [hk]; rfl) (by show (sl A d 2).2.2.1 = a1; rw [e2]) g_a1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e4 : sl A d 4 = (sa, 0, 0, 0) := by
    rw [sl_eq A d (j := 4) (s := (.F1 3)) (t := (.C 0)) (a := sa) (by rw [hk]; rfl) (by show (sl A d 3).2.2.1 = sa; rw [e3]) g_sa]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e5 : sl A d 5 = (kka, 3, k1a, k2a) := by
    rw [sl_eq A d (j := 5) (s := (.F2 3)) (t := (.C 3)) (a := kka) (by rw [hk]; rfl) (by show (sl A d 3).2.2.2 = kka; rw [e3]) g_kka]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e6 : sl A d 6 = (k1a, 1, 0, 0) := by
    rw [sl_eq A d (j := 6) (s := (.F1 5)) (t := (.C 1)) (a := k1a) (by rw [hk]; rfl) (by show (sl A d 5).2.2.1 = k1a; rw [e5]) g_k1a]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e7 : sl A d 7 = (k2a, 1, 0, 0) := by
    rw [sl_eq A d (j := 7) (s := (.F2 5)) (t := (.C 1)) (a := k2a) (by rw [hk]; rfl) (by show (sl A d 5).2.2.2 = k2a; rw [e5]) g_k2a]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e8 : sl A d 8 = (y2, 3, a2, y3) := by
    rw [sl_eq A d (j := 8) (s := (.F2 2)) (t := (.C 3)) (a := y2) (by rw [hk]; rfl) (by show (sl A d 2).2.2.2 = y2; rw [e2]) g_y2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e9 : sl A d 9 = (a2, 3, sb, kkb) := by
    rw [sl_eq A d (j := 9) (s := (.F1 8)) (t := (.C 3)) (a := a2) (by rw [hk]; rfl) (by show (sl A d 8).2.2.1 = a2; rw [e8]) g_a2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e10 : sl A d 10 = (sb, 0, 0, 0) := by
    rw [sl_eq A d (j := 10) (s := (.F1 9)) (t := (.C 0)) (a := sb) (by rw [hk]; rfl) (by show (sl A d 9).2.2.1 = sb; rw [e9]) g_sb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e11 : sl A d 11 = (kkb, 3, k1b, k2b) := by
    rw [sl_eq A d (j := 11) (s := (.F2 9)) (t := (.C 3)) (a := kkb) (by rw [hk]; rfl) (by show (sl A d 9).2.2.2 = kkb; rw [e9]) g_kkb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e12 : sl A d 12 = (k1b, 1, 0, 0) := by
    rw [sl_eq A d (j := 12) (s := (.F1 11)) (t := (.C 1)) (a := k1b) (by rw [hk]; rfl) (by show (sl A d 11).2.2.1 = k1b; rw [e11]) g_k1b]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e13 : sl A d 13 = (k2b, 1, 0, 0) := by
    rw [sl_eq A d (j := 13) (s := (.F2 11)) (t := (.C 1)) (a := k2b) (by rw [hk]; rfl) (by show (sl A d 11).2.2.2 = k2b; rw [e11]) g_k2b]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e14 : sl A d 14 = (y3, 3, p1, kt) := by
    rw [sl_eq A d (j := 14) (s := (.F2 8)) (t := (.C 3)) (a := y3) (by rw [hk]; rfl) (by show (sl A d 8).2.2.2 = y3; rw [e8]) g_y3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e15 : sl A d 15 = (p1, 3, s3, p2) := by
    rw [sl_eq A d (j := 15) (s := (.F1 14)) (t := (.C 3)) (a := p1) (by rw [hk]; rfl) (by show (sl A d 14).2.2.1 = p1; rw [e14]) g_p1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e16 : sl A d 16 = (s3, 0, 0, 0) := by
    rw [sl_eq A d (j := 16) (s := (.F1 15)) (t := (.C 0)) (a := s3) (by rw [hk]; rfl) (by show (sl A d 15).2.2.1 = s3; rw [e15]) g_s3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e17 : sl A d 17 = (p2, 3, si, kh) := by
    rw [sl_eq A d (j := 17) (s := (.F2 15)) (t := (.C 3)) (a := p2) (by rw [hk]; rfl) (by show (sl A d 15).2.2.2 = p2; rw [e15]) g_p2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e18 : sl A d 18 = (si, 3, sc, ic) := by
    rw [sl_eq A d (j := 18) (s := (.F1 17)) (t := (.C 3)) (a := si) (by rw [hk]; rfl) (by show (sl A d 17).2.2.1 = si; rw [e17]) g_si]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e19 : sl A d 19 = (sc, 0, 0, 0) := by
    rw [sl_eq A d (j := 19) (s := (.F1 18)) (t := (.C 0)) (a := sc) (by rw [hk]; rfl) (by show (sl A d 18).2.2.1 = sc; rw [e18]) g_sc]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e20 : sl A d 20 = (ic, 2, 0, 0) := by
    rw [sl_eq A d (j := 20) (s := (.F2 18)) (t := (.C 2)) (a := ic) (by rw [hk]; rfl) (by show (sl A d 18).2.2.2 = ic; rw [e18]) g_ic]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e21 : sl A d 21 = (kh, 3, k5, hh) := by
    rw [sl_eq A d (j := 21) (s := (.F2 17)) (t := (.C 3)) (a := kh) (by rw [hk]; rfl) (by show (sl A d 17).2.2.2 = kh; rw [e17]) g_kh]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e22 : sl A d 22 = (k5, 1, 0, 0) := by
    rw [sl_eq A d (j := 22) (s := (.F1 21)) (t := (.C 1)) (a := k5) (by rw [hk]; rfl) (by show (sl A d 21).2.2.1 = k5; rw [e21]) g_k5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e23 : sl A d 23 = (kt, 3, k6, t) := by
    rw [sl_eq A d (j := 23) (s := (.F2 14)) (t := (.C 3)) (a := kt) (by rw [hk]; rfl) (by show (sl A d 14).2.2.2 = kt; rw [e14]) g_kt]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e24 : sl A d 24 = (k6, 1, 0, 0) := by
    rw [sl_eq A d (j := 24) (s := (.F1 23)) (t := (.C 1)) (a := k6) (by rw [hk]; rfl) (by show (sl A d 23).2.2.1 = k6; rw [e23]) g_k6]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  refine ⟨fun j hj => ?_, ?_⟩
  · have hjl := act_lt hj
    rw [hk] at hjl; simp only [patOf, Dec.cellSlots, Dec.atomSlots, Dec.consSlots] at hjl
    simp at hjl
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩
    · rw [e1]; exact ⟨l_k0, by rw [g_k0]; rfl⟩
    · rw [e2]; exact ⟨l_y1, by rw [g_y1]; rfl⟩
    · rw [e3]; exact ⟨l_a1, by rw [g_a1]; rfl⟩
    · rw [e4]; exact ⟨l_sa, by rw [g_sa]; rfl⟩
    · rw [e5]; exact ⟨l_kka, by rw [g_kka]; rfl⟩
    · rw [e6]; exact ⟨l_k1a, by rw [g_k1a]; rfl⟩
    · rw [e7]; exact ⟨l_k2a, by rw [g_k2a]; rfl⟩
    · rw [e8]; exact ⟨l_y2, by rw [g_y2]; rfl⟩
    · rw [e9]; exact ⟨l_a2, by rw [g_a2]; rfl⟩
    · rw [e10]; exact ⟨l_sb, by rw [g_sb]; rfl⟩
    · rw [e11]; exact ⟨l_kkb, by rw [g_kkb]; rfl⟩
    · rw [e12]; exact ⟨l_k1b, by rw [g_k1b]; rfl⟩
    · rw [e13]; exact ⟨l_k2b, by rw [g_k2b]; rfl⟩
    · rw [e14]; exact ⟨l_y3, by rw [g_y3]; rfl⟩
    · rw [e15]; exact ⟨l_p1, by rw [g_p1]; rfl⟩
    · rw [e16]; exact ⟨l_s3, by rw [g_s3]; rfl⟩
    · rw [e17]; exact ⟨l_p2, by rw [g_p2]; rfl⟩
    · rw [e18]; exact ⟨l_si, by rw [g_si]; rfl⟩
    · rw [e19]; exact ⟨l_sc, by rw [g_sc]; rfl⟩
    · rw [e20]; exact ⟨l_ic, by rw [g_ic]; rfl⟩
    · rw [e21]; exact ⟨l_kh, by rw [g_kh]; rfl⟩
    · rw [e22]; exact ⟨l_k5, by rw [g_k5]; rfl⟩
    · rw [e23]; exact ⟨l_kt, by rw [g_kt]; rfl⟩
    · rw [e24]; exact ⟨l_k6, by rw [g_k6]; rfl⟩
  · exact ⟨by rw [e2], by rw [e8], by rw [e14], by rw [e15], by rw [e17], by rw [e21], by rw [e23]⟩

/-- **An `Atom` row reads its pattern.** -/
theorem atomReads {A : List Cell} {d : DR} (hk : d.kind = 2) {sk : DecJet.AtomSk}
    (h : DecJet.readAtom (A.take d.key) d.p = some sk) :
    ReadsOK A d ∧ (sl A d 0).2.2.1 = sk.a1 ∧ (sl A d 6).2.2.1 = sk.a2 ∧ (sl A d 12).2.2.1 = sk.a3 ∧
      (sl A d 18).2.2.1 = sk.si ∧ (sl A d 22).2.2.2 = sk.b := by
  unfold DecJet.readAtom at h
  repeat' (split at h <;> try contradiction)
  rename_i _ a1 x1 h_p _ a2 x2 h_x1 _ a3 x3 h_x2 _ si kb h_x3 _ k b h_kb hc
  simp only [Option.some.injEq] at h; subst h
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
  obtain ⟨sa, kka, k1a, k2a, h_a1, h_sa, h_kka, h_k1a, h_k2a⟩ := skk_dec c1
  obtain ⟨sb, kkb, k1b, k2b, h_a2, h_sb, h_kkb, h_k1b, h_k2b⟩ := skk_dec c2
  obtain ⟨sc, kkc, k1c, k2c, h_a3, h_sc, h_kkc, h_k1c, h_k2c⟩ := skk_dec c3
  obtain ⟨sd, id, h_si, h_sd, h_id⟩ := si_dec c4
  have h_k := DecJet.isK_eq c5
  obtain ⟨l_p, g_p⟩ := tk h_p
  obtain ⟨l_a1, g_a1⟩ := tk h_a1
  obtain ⟨l_sa, g_sa⟩ := tk h_sa
  obtain ⟨l_kka, g_kka⟩ := tk h_kka
  obtain ⟨l_k1a, g_k1a⟩ := tk h_k1a
  obtain ⟨l_k2a, g_k2a⟩ := tk h_k2a
  obtain ⟨l_x1, g_x1⟩ := tk h_x1
  obtain ⟨l_a2, g_a2⟩ := tk h_a2
  obtain ⟨l_sb, g_sb⟩ := tk h_sb
  obtain ⟨l_kkb, g_kkb⟩ := tk h_kkb
  obtain ⟨l_k1b, g_k1b⟩ := tk h_k1b
  obtain ⟨l_k2b, g_k2b⟩ := tk h_k2b
  obtain ⟨l_x2, g_x2⟩ := tk h_x2
  obtain ⟨l_a3, g_a3⟩ := tk h_a3
  obtain ⟨l_sc, g_sc⟩ := tk h_sc
  obtain ⟨l_kkc, g_kkc⟩ := tk h_kkc
  obtain ⟨l_k1c, g_k1c⟩ := tk h_k1c
  obtain ⟨l_k2c, g_k2c⟩ := tk h_k2c
  obtain ⟨l_x3, g_x3⟩ := tk h_x3
  obtain ⟨l_si, g_si⟩ := tk h_si
  obtain ⟨l_sd, g_sd⟩ := tk h_sd
  obtain ⟨l_id, g_id⟩ := tk h_id
  obtain ⟨l_kb, g_kb⟩ := tk h_kb
  obtain ⟨l_k, g_k⟩ := tk h_k
  have e0 : sl A d 0 = (d.p, 3, a1, x1) := by
    rw [sl_eq A d (j := 0) (s := .rowP) (t := (.C 3)) (a := d.p) (by rw [hk]; rfl) rfl g_p]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e1 : sl A d 1 = (a1, 3, sa, kka) := by
    rw [sl_eq A d (j := 1) (s := (.F1 0)) (t := (.C 3)) (a := a1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.1 = a1; rw [e0]) g_a1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e2 : sl A d 2 = (sa, 0, 0, 0) := by
    rw [sl_eq A d (j := 2) (s := (.F1 1)) (t := (.C 0)) (a := sa) (by rw [hk]; rfl) (by show (sl A d 1).2.2.1 = sa; rw [e1]) g_sa]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e3 : sl A d 3 = (kka, 3, k1a, k2a) := by
    rw [sl_eq A d (j := 3) (s := (.F2 1)) (t := (.C 3)) (a := kka) (by rw [hk]; rfl) (by show (sl A d 1).2.2.2 = kka; rw [e1]) g_kka]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e4 : sl A d 4 = (k1a, 1, 0, 0) := by
    rw [sl_eq A d (j := 4) (s := (.F1 3)) (t := (.C 1)) (a := k1a) (by rw [hk]; rfl) (by show (sl A d 3).2.2.1 = k1a; rw [e3]) g_k1a]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e5 : sl A d 5 = (k2a, 1, 0, 0) := by
    rw [sl_eq A d (j := 5) (s := (.F2 3)) (t := (.C 1)) (a := k2a) (by rw [hk]; rfl) (by show (sl A d 3).2.2.2 = k2a; rw [e3]) g_k2a]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e6 : sl A d 6 = (x1, 3, a2, x2) := by
    rw [sl_eq A d (j := 6) (s := (.F2 0)) (t := (.C 3)) (a := x1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.2 = x1; rw [e0]) g_x1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e7 : sl A d 7 = (a2, 3, sb, kkb) := by
    rw [sl_eq A d (j := 7) (s := (.F1 6)) (t := (.C 3)) (a := a2) (by rw [hk]; rfl) (by show (sl A d 6).2.2.1 = a2; rw [e6]) g_a2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e8 : sl A d 8 = (sb, 0, 0, 0) := by
    rw [sl_eq A d (j := 8) (s := (.F1 7)) (t := (.C 0)) (a := sb) (by rw [hk]; rfl) (by show (sl A d 7).2.2.1 = sb; rw [e7]) g_sb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e9 : sl A d 9 = (kkb, 3, k1b, k2b) := by
    rw [sl_eq A d (j := 9) (s := (.F2 7)) (t := (.C 3)) (a := kkb) (by rw [hk]; rfl) (by show (sl A d 7).2.2.2 = kkb; rw [e7]) g_kkb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e10 : sl A d 10 = (k1b, 1, 0, 0) := by
    rw [sl_eq A d (j := 10) (s := (.F1 9)) (t := (.C 1)) (a := k1b) (by rw [hk]; rfl) (by show (sl A d 9).2.2.1 = k1b; rw [e9]) g_k1b]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e11 : sl A d 11 = (k2b, 1, 0, 0) := by
    rw [sl_eq A d (j := 11) (s := (.F2 9)) (t := (.C 1)) (a := k2b) (by rw [hk]; rfl) (by show (sl A d 9).2.2.2 = k2b; rw [e9]) g_k2b]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e12 : sl A d 12 = (x2, 3, a3, x3) := by
    rw [sl_eq A d (j := 12) (s := (.F2 6)) (t := (.C 3)) (a := x2) (by rw [hk]; rfl) (by show (sl A d 6).2.2.2 = x2; rw [e6]) g_x2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e13 : sl A d 13 = (a3, 3, sc, kkc) := by
    rw [sl_eq A d (j := 13) (s := (.F1 12)) (t := (.C 3)) (a := a3) (by rw [hk]; rfl) (by show (sl A d 12).2.2.1 = a3; rw [e12]) g_a3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e14 : sl A d 14 = (sc, 0, 0, 0) := by
    rw [sl_eq A d (j := 14) (s := (.F1 13)) (t := (.C 0)) (a := sc) (by rw [hk]; rfl) (by show (sl A d 13).2.2.1 = sc; rw [e13]) g_sc]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e15 : sl A d 15 = (kkc, 3, k1c, k2c) := by
    rw [sl_eq A d (j := 15) (s := (.F2 13)) (t := (.C 3)) (a := kkc) (by rw [hk]; rfl) (by show (sl A d 13).2.2.2 = kkc; rw [e13]) g_kkc]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e16 : sl A d 16 = (k1c, 1, 0, 0) := by
    rw [sl_eq A d (j := 16) (s := (.F1 15)) (t := (.C 1)) (a := k1c) (by rw [hk]; rfl) (by show (sl A d 15).2.2.1 = k1c; rw [e15]) g_k1c]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e17 : sl A d 17 = (k2c, 1, 0, 0) := by
    rw [sl_eq A d (j := 17) (s := (.F2 15)) (t := (.C 1)) (a := k2c) (by rw [hk]; rfl) (by show (sl A d 15).2.2.2 = k2c; rw [e15]) g_k2c]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e18 : sl A d 18 = (x3, 3, si, kb) := by
    rw [sl_eq A d (j := 18) (s := (.F2 12)) (t := (.C 3)) (a := x3) (by rw [hk]; rfl) (by show (sl A d 12).2.2.2 = x3; rw [e12]) g_x3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e19 : sl A d 19 = (si, 3, sd, id) := by
    rw [sl_eq A d (j := 19) (s := (.F1 18)) (t := (.C 3)) (a := si) (by rw [hk]; rfl) (by show (sl A d 18).2.2.1 = si; rw [e18]) g_si]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e20 : sl A d 20 = (sd, 0, 0, 0) := by
    rw [sl_eq A d (j := 20) (s := (.F1 19)) (t := (.C 0)) (a := sd) (by rw [hk]; rfl) (by show (sl A d 19).2.2.1 = sd; rw [e19]) g_sd]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e21 : sl A d 21 = (id, 2, 0, 0) := by
    rw [sl_eq A d (j := 21) (s := (.F2 19)) (t := (.C 2)) (a := id) (by rw [hk]; rfl) (by show (sl A d 19).2.2.2 = id; rw [e19]) g_id]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e22 : sl A d 22 = (kb, 3, k, b) := by
    rw [sl_eq A d (j := 22) (s := (.F2 18)) (t := (.C 3)) (a := kb) (by rw [hk]; rfl) (by show (sl A d 18).2.2.2 = kb; rw [e18]) g_kb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  have e23 : sl A d 23 = (k, 1, 0, 0) := by
    rw [sl_eq A d (j := 23) (s := (.F1 22)) (t := (.C 1)) (a := k) (by rw [hk]; rfl) (by show (sl A d 22).2.2.1 = k; rw [e22]) g_k]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
  refine ⟨fun j hj => ?_, ?_⟩
  · have hjl := act_lt hj
    rw [hk] at hjl; simp only [patOf, Dec.cellSlots, Dec.atomSlots, Dec.consSlots] at hjl
    simp at hjl
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩
    · rw [e1]; exact ⟨l_a1, by rw [g_a1]; rfl⟩
    · rw [e2]; exact ⟨l_sa, by rw [g_sa]; rfl⟩
    · rw [e3]; exact ⟨l_kka, by rw [g_kka]; rfl⟩
    · rw [e4]; exact ⟨l_k1a, by rw [g_k1a]; rfl⟩
    · rw [e5]; exact ⟨l_k2a, by rw [g_k2a]; rfl⟩
    · rw [e6]; exact ⟨l_x1, by rw [g_x1]; rfl⟩
    · rw [e7]; exact ⟨l_a2, by rw [g_a2]; rfl⟩
    · rw [e8]; exact ⟨l_sb, by rw [g_sb]; rfl⟩
    · rw [e9]; exact ⟨l_kkb, by rw [g_kkb]; rfl⟩
    · rw [e10]; exact ⟨l_k1b, by rw [g_k1b]; rfl⟩
    · rw [e11]; exact ⟨l_k2b, by rw [g_k2b]; rfl⟩
    · rw [e12]; exact ⟨l_x2, by rw [g_x2]; rfl⟩
    · rw [e13]; exact ⟨l_a3, by rw [g_a3]; rfl⟩
    · rw [e14]; exact ⟨l_sc, by rw [g_sc]; rfl⟩
    · rw [e15]; exact ⟨l_kkc, by rw [g_kkc]; rfl⟩
    · rw [e16]; exact ⟨l_k1c, by rw [g_k1c]; rfl⟩
    · rw [e17]; exact ⟨l_k2c, by rw [g_k2c]; rfl⟩
    · rw [e18]; exact ⟨l_x3, by rw [g_x3]; rfl⟩
    · rw [e19]; exact ⟨l_si, by rw [g_si]; rfl⟩
    · rw [e20]; exact ⟨l_sd, by rw [g_sd]; rfl⟩
    · rw [e21]; exact ⟨l_id, by rw [g_id]; rfl⟩
    · rw [e22]; exact ⟨l_kb, by rw [g_kb]; rfl⟩
    · rw [e23]; exact ⟨l_k, by rw [g_k]; rfl⟩
  · exact ⟨by rw [e0], by rw [e6], by rw [e12], by rw [e18], by rw [e22]⟩

/-- **A `Cons` row reads its pattern**: its bit's cell, and its tail's
    when it is not the last. -/
theorem consReads {A : List Cell} {d : DR} (hk : d.kind = 3) {b : Bool} {sk : DecJet.ConsSk}
    (h : DecJet.readCons (A.take d.key) d.p = some (b, sk)) (hbit : d.bit = b)
    (hlast : d.last = DecJet.isK (A.take d.key) sk.t)
    (htail : DecJet.isK (A.take d.key) sk.t = false → ∃ x y, (A.take d.key)[sk.t]? = some (.app x y)) :
    ReadsOK A d ∧ (sl A d 3).2.2.1 = sk.s ∧ (sl A d 5).2.2.1 = sk.c5 ∧ (sl A d 14).2.2.2 = sk.t := by
  unfold DecJet.readCons at h
  repeat' (split at h <;> try contradiction)
  rename_i _ k c1 h_p ck _ c2 c3 h_c1 _ _ s c4 k3 t h_c2 h_c3 csk3 _ c5 c6 h_c4 cc5 _ k2 hb h_c6 ck2 _ b' hbool
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  simp only [Bool.and_eq_true] at csk3
  have h_k := DecJet.isK_eq ck
  have h_s := DecJet.isS_eq csk3.1
  have h_k3 := DecJet.isK_eq csk3.2
  obtain ⟨s5, i5, h_c5, h_s5, h_i5⟩ := si_dec cc5
  have h_k2 := DecJet.isK_eq ck2
  obtain ⟨l_p, g_p⟩ := tk h_p
  obtain ⟨l_k, g_k⟩ := tk h_k
  obtain ⟨l_c1, g_c1⟩ := tk h_c1
  obtain ⟨l_c2, g_c2⟩ := tk h_c2
  obtain ⟨l_s, g_s⟩ := tk h_s
  obtain ⟨l_c4, g_c4⟩ := tk h_c4
  obtain ⟨l_c5, g_c5⟩ := tk h_c5
  obtain ⟨l_s5, g_s5⟩ := tk h_s5
  obtain ⟨l_i5, g_i5⟩ := tk h_i5
  obtain ⟨l_c6, g_c6⟩ := tk h_c6
  obtain ⟨l_k2, g_k2⟩ := tk h_k2
  obtain ⟨l_c3, g_c3⟩ := tk h_c3
  obtain ⟨l_k3, g_k3⟩ := tk h_k3
  rcases boolAt_dec hbool with ⟨rfl, h_hb⟩ | ⟨rfl, f, x, h_hb, h_f, h_x⟩ <;>
    cases hl : DecJet.isK (A.take d.key) t
  · obtain ⟨tx, ty, h_t⟩ := htail hl
    obtain ⟨l_hb, g_hb⟩ := tk h_hb
    obtain ⟨l_t, g_t⟩ := tk h_t
    have e0 : sl A d 0 = (d.p, 3, k, c1) := by
      rw [sl_eq A d (j := 0) (s := .rowP) (t := (.C 3)) (a := d.p) (by rw [hk]; rfl) rfl g_p]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e1 : sl A d 1 = (k, 1, 0, 0) := by
      rw [sl_eq A d (j := 1) (s := (.F1 0)) (t := (.C 1)) (a := k) (by rw [hk]; rfl) (by show (sl A d 0).2.2.1 = k; rw [e0]) g_k]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e2 : sl A d 2 = (c1, 3, c2, c3) := by
      rw [sl_eq A d (j := 2) (s := (.F2 0)) (t := (.C 3)) (a := c1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.2 = c1; rw [e0]) g_c1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e3 : sl A d 3 = (c2, 3, s, c4) := by
      rw [sl_eq A d (j := 3) (s := (.F1 2)) (t := (.C 3)) (a := c2) (by rw [hk]; rfl) (by show (sl A d 2).2.2.1 = c2; rw [e2]) g_c2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e4 : sl A d 4 = (s, 0, 0, 0) := by
      rw [sl_eq A d (j := 4) (s := (.F1 3)) (t := (.C 0)) (a := s) (by rw [hk]; rfl) (by show (sl A d 3).2.2.1 = s; rw [e3]) g_s]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e5 : sl A d 5 = (c4, 3, c5, c6) := by
      rw [sl_eq A d (j := 5) (s := (.F2 3)) (t := (.C 3)) (a := c4) (by rw [hk]; rfl) (by show (sl A d 3).2.2.2 = c4; rw [e3]) g_c4]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e6 : sl A d 6 = (c5, 3, s5, i5) := by
      rw [sl_eq A d (j := 6) (s := (.F1 5)) (t := (.C 3)) (a := c5) (by rw [hk]; rfl) (by show (sl A d 5).2.2.1 = c5; rw [e5]) g_c5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e7 : sl A d 7 = (s5, 0, 0, 0) := by
      rw [sl_eq A d (j := 7) (s := (.F1 6)) (t := (.C 0)) (a := s5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.1 = s5; rw [e6]) g_s5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e8 : sl A d 8 = (i5, 2, 0, 0) := by
      rw [sl_eq A d (j := 8) (s := (.F2 6)) (t := (.C 2)) (a := i5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.2 = i5; rw [e6]) g_i5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e9 : sl A d 9 = (c6, 3, k2, hb) := by
      rw [sl_eq A d (j := 9) (s := (.F2 5)) (t := (.C 3)) (a := c6) (by rw [hk]; rfl) (by show (sl A d 5).2.2.2 = c6; rw [e5]) g_c6]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e10 : sl A d 10 = (k2, 1, 0, 0) := by
      rw [sl_eq A d (j := 10) (s := (.F1 9)) (t := (.C 1)) (a := k2) (by rw [hk]; rfl) (by show (sl A d 9).2.2.1 = k2; rw [e9]) g_k2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e11 : sl A d 11 = (hb, 1, 0, 0) := by
      rw [sl_eq A d (j := 11) (s := (.F2 9)) (t := .BitTag) (a := hb) (by rw [hk]; rfl) (by show (sl A d 9).2.2.2 = hb; rw [e9]) g_hb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e14 : sl A d 14 = (c3, 3, k3, t) := by
      rw [sl_eq A d (j := 14) (s := (.F2 2)) (t := (.C 3)) (a := c3) (by rw [hk]; rfl) (by show (sl A d 2).2.2.2 = c3; rw [e2]) g_c3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e15 : sl A d 15 = (k3, 1, 0, 0) := by
      rw [sl_eq A d (j := 15) (s := (.F1 14)) (t := (.C 1)) (a := k3) (by rw [hk]; rfl) (by show (sl A d 14).2.2.1 = k3; rw [e14]) g_k3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e16 : sl A d 16 = (t, 3, tx, ty) := by
      rw [sl_eq A d (j := 16) (s := (.F2 14)) (t := .LastTag) (a := t) (by rw [hk]; rfl) (by show (sl A d 14).2.2.2 = t; rw [e14]) g_t]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    refine ⟨fun j hj => ?_, ?_⟩
    · have hjl := act_lt hj
      rw [hk] at hjl; simp only [patOf, Dec.cellSlots, Dec.atomSlots, Dec.consSlots] at hjl
      simp at hjl
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩
      · rw [e1]; exact ⟨l_k, by rw [g_k]; rfl⟩
      · rw [e2]; exact ⟨l_c1, by rw [g_c1]; rfl⟩
      · rw [e3]; exact ⟨l_c2, by rw [g_c2]; rfl⟩
      · rw [e4]; exact ⟨l_s, by rw [g_s]; rfl⟩
      · rw [e5]; exact ⟨l_c4, by rw [g_c4]; rfl⟩
      · rw [e6]; exact ⟨l_c5, by rw [g_c5]; rfl⟩
      · rw [e7]; exact ⟨l_s5, by rw [g_s5]; rfl⟩
      · rw [e8]; exact ⟨l_i5, by rw [g_i5]; rfl⟩
      · rw [e9]; exact ⟨l_c6, by rw [g_c6]; rfl⟩
      · rw [e10]; exact ⟨l_k2, by rw [g_k2]; rfl⟩
      · rw [e11]; exact ⟨l_hb, by rw [g_hb]; rfl⟩
      · exact absurd hj (by unfold act; rw [hk, hbit]; decide)
      · exact absurd hj (by unfold act; rw [hk, hbit]; decide)
      · rw [e14]; exact ⟨l_c3, by rw [g_c3]; rfl⟩
      · rw [e15]; exact ⟨l_k3, by rw [g_k3]; rfl⟩
      · rw [e16]; exact ⟨l_t, by rw [g_t]; rfl⟩
    · exact ⟨by rw [e3], by rw [e5], by rw [e14]⟩
  · have h_t := DecJet.isK_eq hl
    obtain ⟨l_hb, g_hb⟩ := tk h_hb
    obtain ⟨l_t, g_t⟩ := tk h_t
    have e0 : sl A d 0 = (d.p, 3, k, c1) := by
      rw [sl_eq A d (j := 0) (s := .rowP) (t := (.C 3)) (a := d.p) (by rw [hk]; rfl) rfl g_p]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e1 : sl A d 1 = (k, 1, 0, 0) := by
      rw [sl_eq A d (j := 1) (s := (.F1 0)) (t := (.C 1)) (a := k) (by rw [hk]; rfl) (by show (sl A d 0).2.2.1 = k; rw [e0]) g_k]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e2 : sl A d 2 = (c1, 3, c2, c3) := by
      rw [sl_eq A d (j := 2) (s := (.F2 0)) (t := (.C 3)) (a := c1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.2 = c1; rw [e0]) g_c1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e3 : sl A d 3 = (c2, 3, s, c4) := by
      rw [sl_eq A d (j := 3) (s := (.F1 2)) (t := (.C 3)) (a := c2) (by rw [hk]; rfl) (by show (sl A d 2).2.2.1 = c2; rw [e2]) g_c2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e4 : sl A d 4 = (s, 0, 0, 0) := by
      rw [sl_eq A d (j := 4) (s := (.F1 3)) (t := (.C 0)) (a := s) (by rw [hk]; rfl) (by show (sl A d 3).2.2.1 = s; rw [e3]) g_s]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e5 : sl A d 5 = (c4, 3, c5, c6) := by
      rw [sl_eq A d (j := 5) (s := (.F2 3)) (t := (.C 3)) (a := c4) (by rw [hk]; rfl) (by show (sl A d 3).2.2.2 = c4; rw [e3]) g_c4]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e6 : sl A d 6 = (c5, 3, s5, i5) := by
      rw [sl_eq A d (j := 6) (s := (.F1 5)) (t := (.C 3)) (a := c5) (by rw [hk]; rfl) (by show (sl A d 5).2.2.1 = c5; rw [e5]) g_c5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e7 : sl A d 7 = (s5, 0, 0, 0) := by
      rw [sl_eq A d (j := 7) (s := (.F1 6)) (t := (.C 0)) (a := s5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.1 = s5; rw [e6]) g_s5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e8 : sl A d 8 = (i5, 2, 0, 0) := by
      rw [sl_eq A d (j := 8) (s := (.F2 6)) (t := (.C 2)) (a := i5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.2 = i5; rw [e6]) g_i5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e9 : sl A d 9 = (c6, 3, k2, hb) := by
      rw [sl_eq A d (j := 9) (s := (.F2 5)) (t := (.C 3)) (a := c6) (by rw [hk]; rfl) (by show (sl A d 5).2.2.2 = c6; rw [e5]) g_c6]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e10 : sl A d 10 = (k2, 1, 0, 0) := by
      rw [sl_eq A d (j := 10) (s := (.F1 9)) (t := (.C 1)) (a := k2) (by rw [hk]; rfl) (by show (sl A d 9).2.2.1 = k2; rw [e9]) g_k2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e11 : sl A d 11 = (hb, 1, 0, 0) := by
      rw [sl_eq A d (j := 11) (s := (.F2 9)) (t := .BitTag) (a := hb) (by rw [hk]; rfl) (by show (sl A d 9).2.2.2 = hb; rw [e9]) g_hb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e14 : sl A d 14 = (c3, 3, k3, t) := by
      rw [sl_eq A d (j := 14) (s := (.F2 2)) (t := (.C 3)) (a := c3) (by rw [hk]; rfl) (by show (sl A d 2).2.2.2 = c3; rw [e2]) g_c3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e15 : sl A d 15 = (k3, 1, 0, 0) := by
      rw [sl_eq A d (j := 15) (s := (.F1 14)) (t := (.C 1)) (a := k3) (by rw [hk]; rfl) (by show (sl A d 14).2.2.1 = k3; rw [e14]) g_k3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e16 : sl A d 16 = (t, 1, 0, 0) := by
      rw [sl_eq A d (j := 16) (s := (.F2 14)) (t := .LastTag) (a := t) (by rw [hk]; rfl) (by show (sl A d 14).2.2.2 = t; rw [e14]) g_t]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    refine ⟨fun j hj => ?_, ?_⟩
    · have hjl := act_lt hj
      rw [hk] at hjl; simp only [patOf, Dec.cellSlots, Dec.atomSlots, Dec.consSlots] at hjl
      simp at hjl
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩
      · rw [e1]; exact ⟨l_k, by rw [g_k]; rfl⟩
      · rw [e2]; exact ⟨l_c1, by rw [g_c1]; rfl⟩
      · rw [e3]; exact ⟨l_c2, by rw [g_c2]; rfl⟩
      · rw [e4]; exact ⟨l_s, by rw [g_s]; rfl⟩
      · rw [e5]; exact ⟨l_c4, by rw [g_c4]; rfl⟩
      · rw [e6]; exact ⟨l_c5, by rw [g_c5]; rfl⟩
      · rw [e7]; exact ⟨l_s5, by rw [g_s5]; rfl⟩
      · rw [e8]; exact ⟨l_i5, by rw [g_i5]; rfl⟩
      · rw [e9]; exact ⟨l_c6, by rw [g_c6]; rfl⟩
      · rw [e10]; exact ⟨l_k2, by rw [g_k2]; rfl⟩
      · rw [e11]; exact ⟨l_hb, by rw [g_hb]; rfl⟩
      · exact absurd hj (by unfold act; rw [hk, hbit]; decide)
      · exact absurd hj (by unfold act; rw [hk, hbit]; decide)
      · rw [e14]; exact ⟨l_c3, by rw [g_c3]; rfl⟩
      · rw [e15]; exact ⟨l_k3, by rw [g_k3]; rfl⟩
      · rw [e16]; exact ⟨l_t, by rw [g_t]; rfl⟩
    · exact ⟨by rw [e3], by rw [e5], by rw [e14]⟩
  · obtain ⟨tx, ty, h_t⟩ := htail hl
    obtain ⟨l_hb, g_hb⟩ := tk h_hb
    obtain ⟨l_t, g_t⟩ := tk h_t
    obtain ⟨l_f, g_f⟩ := tk h_f
    obtain ⟨l_x, g_x⟩ := tk h_x
    have e0 : sl A d 0 = (d.p, 3, k, c1) := by
      rw [sl_eq A d (j := 0) (s := .rowP) (t := (.C 3)) (a := d.p) (by rw [hk]; rfl) rfl g_p]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e1 : sl A d 1 = (k, 1, 0, 0) := by
      rw [sl_eq A d (j := 1) (s := (.F1 0)) (t := (.C 1)) (a := k) (by rw [hk]; rfl) (by show (sl A d 0).2.2.1 = k; rw [e0]) g_k]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e2 : sl A d 2 = (c1, 3, c2, c3) := by
      rw [sl_eq A d (j := 2) (s := (.F2 0)) (t := (.C 3)) (a := c1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.2 = c1; rw [e0]) g_c1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e3 : sl A d 3 = (c2, 3, s, c4) := by
      rw [sl_eq A d (j := 3) (s := (.F1 2)) (t := (.C 3)) (a := c2) (by rw [hk]; rfl) (by show (sl A d 2).2.2.1 = c2; rw [e2]) g_c2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e4 : sl A d 4 = (s, 0, 0, 0) := by
      rw [sl_eq A d (j := 4) (s := (.F1 3)) (t := (.C 0)) (a := s) (by rw [hk]; rfl) (by show (sl A d 3).2.2.1 = s; rw [e3]) g_s]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e5 : sl A d 5 = (c4, 3, c5, c6) := by
      rw [sl_eq A d (j := 5) (s := (.F2 3)) (t := (.C 3)) (a := c4) (by rw [hk]; rfl) (by show (sl A d 3).2.2.2 = c4; rw [e3]) g_c4]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e6 : sl A d 6 = (c5, 3, s5, i5) := by
      rw [sl_eq A d (j := 6) (s := (.F1 5)) (t := (.C 3)) (a := c5) (by rw [hk]; rfl) (by show (sl A d 5).2.2.1 = c5; rw [e5]) g_c5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e7 : sl A d 7 = (s5, 0, 0, 0) := by
      rw [sl_eq A d (j := 7) (s := (.F1 6)) (t := (.C 0)) (a := s5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.1 = s5; rw [e6]) g_s5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e8 : sl A d 8 = (i5, 2, 0, 0) := by
      rw [sl_eq A d (j := 8) (s := (.F2 6)) (t := (.C 2)) (a := i5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.2 = i5; rw [e6]) g_i5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e9 : sl A d 9 = (c6, 3, k2, hb) := by
      rw [sl_eq A d (j := 9) (s := (.F2 5)) (t := (.C 3)) (a := c6) (by rw [hk]; rfl) (by show (sl A d 5).2.2.2 = c6; rw [e5]) g_c6]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e10 : sl A d 10 = (k2, 1, 0, 0) := by
      rw [sl_eq A d (j := 10) (s := (.F1 9)) (t := (.C 1)) (a := k2) (by rw [hk]; rfl) (by show (sl A d 9).2.2.1 = k2; rw [e9]) g_k2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e11 : sl A d 11 = (hb, 3, f, x) := by
      rw [sl_eq A d (j := 11) (s := (.F2 9)) (t := .BitTag) (a := hb) (by rw [hk]; rfl) (by show (sl A d 9).2.2.2 = hb; rw [e9]) g_hb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e12 : sl A d 12 = (f, 1, 0, 0) := by
      rw [sl_eq A d (j := 12) (s := (.F1 11)) (t := (.C 1)) (a := f) (by rw [hk]; rfl) (by show (sl A d 11).2.2.1 = f; rw [e11]) g_f]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e13 : sl A d 13 = (x, 2, 0, 0) := by
      rw [sl_eq A d (j := 13) (s := (.F2 11)) (t := (.C 2)) (a := x) (by rw [hk]; rfl) (by show (sl A d 11).2.2.2 = x; rw [e11]) g_x]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e14 : sl A d 14 = (c3, 3, k3, t) := by
      rw [sl_eq A d (j := 14) (s := (.F2 2)) (t := (.C 3)) (a := c3) (by rw [hk]; rfl) (by show (sl A d 2).2.2.2 = c3; rw [e2]) g_c3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e15 : sl A d 15 = (k3, 1, 0, 0) := by
      rw [sl_eq A d (j := 15) (s := (.F1 14)) (t := (.C 1)) (a := k3) (by rw [hk]; rfl) (by show (sl A d 14).2.2.1 = k3; rw [e14]) g_k3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e16 : sl A d 16 = (t, 3, tx, ty) := by
      rw [sl_eq A d (j := 16) (s := (.F2 14)) (t := .LastTag) (a := t) (by rw [hk]; rfl) (by show (sl A d 14).2.2.2 = t; rw [e14]) g_t]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    refine ⟨fun j hj => ?_, ?_⟩
    · have hjl := act_lt hj
      rw [hk] at hjl; simp only [patOf, Dec.cellSlots, Dec.atomSlots, Dec.consSlots] at hjl
      simp at hjl
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩
      · rw [e1]; exact ⟨l_k, by rw [g_k]; rfl⟩
      · rw [e2]; exact ⟨l_c1, by rw [g_c1]; rfl⟩
      · rw [e3]; exact ⟨l_c2, by rw [g_c2]; rfl⟩
      · rw [e4]; exact ⟨l_s, by rw [g_s]; rfl⟩
      · rw [e5]; exact ⟨l_c4, by rw [g_c4]; rfl⟩
      · rw [e6]; exact ⟨l_c5, by rw [g_c5]; rfl⟩
      · rw [e7]; exact ⟨l_s5, by rw [g_s5]; rfl⟩
      · rw [e8]; exact ⟨l_i5, by rw [g_i5]; rfl⟩
      · rw [e9]; exact ⟨l_c6, by rw [g_c6]; rfl⟩
      · rw [e10]; exact ⟨l_k2, by rw [g_k2]; rfl⟩
      · rw [e11]; exact ⟨l_hb, by rw [g_hb]; rfl⟩
      · rw [e12]; exact ⟨l_f, by rw [g_f]; rfl⟩
      · rw [e13]; exact ⟨l_x, by rw [g_x]; rfl⟩
      · rw [e14]; exact ⟨l_c3, by rw [g_c3]; rfl⟩
      · rw [e15]; exact ⟨l_k3, by rw [g_k3]; rfl⟩
      · rw [e16]; exact ⟨l_t, by rw [g_t]; rfl⟩
    · exact ⟨by rw [e3], by rw [e5], by rw [e14]⟩
  · have h_t := DecJet.isK_eq hl
    obtain ⟨l_hb, g_hb⟩ := tk h_hb
    obtain ⟨l_t, g_t⟩ := tk h_t
    obtain ⟨l_f, g_f⟩ := tk h_f
    obtain ⟨l_x, g_x⟩ := tk h_x
    have e0 : sl A d 0 = (d.p, 3, k, c1) := by
      rw [sl_eq A d (j := 0) (s := .rowP) (t := (.C 3)) (a := d.p) (by rw [hk]; rfl) rfl g_p]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e1 : sl A d 1 = (k, 1, 0, 0) := by
      rw [sl_eq A d (j := 1) (s := (.F1 0)) (t := (.C 1)) (a := k) (by rw [hk]; rfl) (by show (sl A d 0).2.2.1 = k; rw [e0]) g_k]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e2 : sl A d 2 = (c1, 3, c2, c3) := by
      rw [sl_eq A d (j := 2) (s := (.F2 0)) (t := (.C 3)) (a := c1) (by rw [hk]; rfl) (by show (sl A d 0).2.2.2 = c1; rw [e0]) g_c1]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e3 : sl A d 3 = (c2, 3, s, c4) := by
      rw [sl_eq A d (j := 3) (s := (.F1 2)) (t := (.C 3)) (a := c2) (by rw [hk]; rfl) (by show (sl A d 2).2.2.1 = c2; rw [e2]) g_c2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e4 : sl A d 4 = (s, 0, 0, 0) := by
      rw [sl_eq A d (j := 4) (s := (.F1 3)) (t := (.C 0)) (a := s) (by rw [hk]; rfl) (by show (sl A d 3).2.2.1 = s; rw [e3]) g_s]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e5 : sl A d 5 = (c4, 3, c5, c6) := by
      rw [sl_eq A d (j := 5) (s := (.F2 3)) (t := (.C 3)) (a := c4) (by rw [hk]; rfl) (by show (sl A d 3).2.2.2 = c4; rw [e3]) g_c4]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e6 : sl A d 6 = (c5, 3, s5, i5) := by
      rw [sl_eq A d (j := 6) (s := (.F1 5)) (t := (.C 3)) (a := c5) (by rw [hk]; rfl) (by show (sl A d 5).2.2.1 = c5; rw [e5]) g_c5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e7 : sl A d 7 = (s5, 0, 0, 0) := by
      rw [sl_eq A d (j := 7) (s := (.F1 6)) (t := (.C 0)) (a := s5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.1 = s5; rw [e6]) g_s5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e8 : sl A d 8 = (i5, 2, 0, 0) := by
      rw [sl_eq A d (j := 8) (s := (.F2 6)) (t := (.C 2)) (a := i5) (by rw [hk]; rfl) (by show (sl A d 6).2.2.2 = i5; rw [e6]) g_i5]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e9 : sl A d 9 = (c6, 3, k2, hb) := by
      rw [sl_eq A d (j := 9) (s := (.F2 5)) (t := (.C 3)) (a := c6) (by rw [hk]; rfl) (by show (sl A d 5).2.2.2 = c6; rw [e5]) g_c6]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e10 : sl A d 10 = (k2, 1, 0, 0) := by
      rw [sl_eq A d (j := 10) (s := (.F1 9)) (t := (.C 1)) (a := k2) (by rw [hk]; rfl) (by show (sl A d 9).2.2.1 = k2; rw [e9]) g_k2]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e11 : sl A d 11 = (hb, 3, f, x) := by
      rw [sl_eq A d (j := 11) (s := (.F2 9)) (t := .BitTag) (a := hb) (by rw [hk]; rfl) (by show (sl A d 9).2.2.2 = hb; rw [e9]) g_hb]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e12 : sl A d 12 = (f, 1, 0, 0) := by
      rw [sl_eq A d (j := 12) (s := (.F1 11)) (t := (.C 1)) (a := f) (by rw [hk]; rfl) (by show (sl A d 11).2.2.1 = f; rw [e11]) g_f]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e13 : sl A d 13 = (x, 2, 0, 0) := by
      rw [sl_eq A d (j := 13) (s := (.F2 11)) (t := (.C 2)) (a := x) (by rw [hk]; rfl) (by show (sl A d 11).2.2.2 = x; rw [e11]) g_x]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e14 : sl A d 14 = (c3, 3, k3, t) := by
      rw [sl_eq A d (j := 14) (s := (.F2 2)) (t := (.C 3)) (a := c3) (by rw [hk]; rfl) (by show (sl A d 2).2.2.2 = c3; rw [e2]) g_c3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e15 : sl A d 15 = (k3, 1, 0, 0) := by
      rw [sl_eq A d (j := 15) (s := (.F1 14)) (t := (.C 1)) (a := k3) (by rw [hk]; rfl) (by show (sl A d 14).2.2.1 = k3; rw [e14]) g_k3]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    have e16 : sl A d 16 = (t, 1, 0, 0) := by
      rw [sl_eq A d (j := 16) (s := (.F2 14)) (t := .LastTag) (a := t) (by rw [hk]; rfl) (by show (sl A d 14).2.2.2 = t; rw [e14]) g_t]; first | rfl | (simp only [tgN, hbit, hlast, hl]; rfl)
    refine ⟨fun j hj => ?_, ?_⟩
    · have hjl := act_lt hj
      rw [hk] at hjl; simp only [patOf, Dec.cellSlots, Dec.atomSlots, Dec.consSlots] at hjl
      simp at hjl
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [e0]; exact ⟨l_p, by rw [g_p]; rfl⟩
      · rw [e1]; exact ⟨l_k, by rw [g_k]; rfl⟩
      · rw [e2]; exact ⟨l_c1, by rw [g_c1]; rfl⟩
      · rw [e3]; exact ⟨l_c2, by rw [g_c2]; rfl⟩
      · rw [e4]; exact ⟨l_s, by rw [g_s]; rfl⟩
      · rw [e5]; exact ⟨l_c4, by rw [g_c4]; rfl⟩
      · rw [e6]; exact ⟨l_c5, by rw [g_c5]; rfl⟩
      · rw [e7]; exact ⟨l_s5, by rw [g_s5]; rfl⟩
      · rw [e8]; exact ⟨l_i5, by rw [g_i5]; rfl⟩
      · rw [e9]; exact ⟨l_c6, by rw [g_c6]; rfl⟩
      · rw [e10]; exact ⟨l_k2, by rw [g_k2]; rfl⟩
      · rw [e11]; exact ⟨l_hb, by rw [g_hb]; rfl⟩
      · rw [e12]; exact ⟨l_f, by rw [g_f]; rfl⟩
      · rw [e13]; exact ⟨l_x, by rw [g_x]; rfl⟩
      · rw [e14]; exact ⟨l_c3, by rw [g_c3]; rfl⟩
      · rw [e15]; exact ⟨l_k3, by rw [g_k3]; rfl⟩
      · rw [e16]; exact ⟨l_t, by rw [g_t]; rfl⟩
    · exact ⟨by rw [e3], by rw [e5], by rw [e14]⟩

end DecT

end Circuit
