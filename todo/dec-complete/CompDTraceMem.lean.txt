import Ski.Circuit.CompDTraceCall

/-!
# An honest DEC row's memory messages are memory cells

A row's 25 reads are memory cells when it reads its pattern (`ReadsOK`);
its 30 writes are when the memory holds, at the call's key, the cells the
row writes (`DecT.WritesOK`): the subject's `Cell` wrapper and `errT`,
the head's `Atom` wrapper or a cell head's filler, a rewritten bit's
`Cons` and its link.  **`DecT.row_mem`**.
-/

namespace Circuit

open B Air

namespace DecT

/-- The memory holds `c` at `a`. -/
def At (A : List Cell) (a : Nat) (c : Cell) : Prop := a < A.length ∧ A.getD a .nil = c

/-- The memory holds the cells `L` from `c`. -/
def Cells (A : List Cell) (c : Nat) (L : List Cell) : Prop := ∀ i (h : i < L.length), At A (c + i) L[i]

/-- **The cells a row writes are in memory.** -/
structure WritesOK (A : List Cell) (d : DR) : Prop where
  sub : d.kind = 1 → d.ro = 0 → Cells A d.key
    [.app 0 (d.key + 1), .app (sl A d 2).2.2.1 (d.key + 2), .app (sl A d 8).2.2.1 (d.key + 3),
     .app (d.key + 4) (sl A d 14).2.2.2, .app (sl A d 15).2.2.1 (d.key + 5), .app (sl A d 17).2.2.1 (d.key + 6),
     .app 0 (d.key + 7)]
  suberr : d.kind = 1 → d.ro = 0 → d.err = true → Cells A (d.key + 12)
    [.app 0 (d.key + 13), .app 0 (d.key + 14), .app 0 1]
  hc : d.kind = 1 → d.ro = 1 → Cells A (d.key + 7) (List.replicate 5 (.app 0 0))
  hat : d.kind = 2 → d.ro = 1 → Cells A (d.key + 7)
    [.app (sl A d 0).2.2.1 (d.key + 8), .app (sl A d 6).2.2.1 (d.key + 9), .app (sl A d 12).2.2.1 (d.key + 10),
     .app (sl A d 18).2.2.1 (d.key + 11)]
  asub : d.kind = 2 → d.ro = 0 → Cells A d.key [.app 0 (d.key + 1), .app 0 (d.key + 2), .app 0 1]
  cw : d.kind = 3 → d.bw = true → ¬(d.bit = true ∧ d.last = true) → Cells A (d.key + 12 + 6 * d.lvl)
    [.app 0 (d.key + 12 + 6 * d.lvl + 1), .app (d.key + 12 + 6 * d.lvl + 2) (d.key + 12 + 6 * d.lvl + 5),
     .app (sl A d 3).2.2.1 (d.key + 12 + 6 * d.lvl + 3), .app (sl A d 5).2.2.1 (d.key + 12 + 6 * d.lvl + 4),
     .app 0 (if d.bit then 2 else 0)]
  cwl : d.kind = 3 → d.bw = true → d.bit = true → d.last = false →
    At A (d.key + 12 + 6 * d.lvl + 5) (.app 0 (sl A d 14).2.2.2)
  clk : d.kind = 3 → d.bw = true →
    At A (d.key + 11 + 6 * d.lvl) (.app 0 (if d.bit && d.last then 0 else d.key + 12 + 6 * d.lvl))
  nlk : d.kind = 4 → d.bw = true → At A (d.key + 11) (.app 0 0)

section
variable {A : List Cell} {d : DR}

theorem wr_case {ρ : Atom → F} {addr x y : E} {a a' X Y : Nat} (hA : At A a (.app X Y)) (ha : addr.eval ρ = ofN a')
    (hx : x.eval ρ = ofN X) (hy : y.eval ρ = ofN Y) (he : a' = a := by omega) :
    ∃ m, m < A.length ∧ [addr, c 3, x, y].map (fun e => e.eval ρ) = tupleOf A m := by
  subst he
  refine ⟨a', hA.1, ?_⟩
  simp only [List.map_cons, List.map_nil, tupleOf, hA.2, ha, hx, hy, cellTag, cellFields]
  rfl

theorem evK (n : Nat) : (Dec.kE n).eval ((rowT A d).env 0) = ofN (d.key + n) := by
  rw [ofN_add]; rfl

theorem evA (n : Nat) : (Dec.apE n).eval ((rowT A d).env 0) = ofN (d.key + 12 + 6 * d.lvl + n) := by
  rw [ofN_add, ofN_add, ofN_add, ofN_mul]; rfl

theorem evLK : (E.add (E.add (col Dec.KEY) (c 11)) (E.mul (c 6) (col Dec.LVL))).eval ((rowT A d).env 0) =
    ofN (d.key + 11 + 6 * d.lvl) := by
  rw [ofN_add, ofN_add, ofN_mul]; rfl

theorem evF1 {j : Nat} (hj : j < Dec.NSLOT) : (Dec.f1 j).eval ((rowT A d).env 0) = ofN (sl A d j).2.2.1 :=
  col_f1 A d hj

theorem evF2 {j : Nat} (hj : j < Dec.NSLOT) : (Dec.f2 j).eval ((rowT A d).env 0) = ofN (sl A d j).2.2.2 :=
  col_f2 A d hj

theorem evPTR (hk : d.kind = 3) (hb : d.bw = true) :
    (col Dec.PTR).eval ((rowT A d).env 0) = ofN (if d.bit then 2 else 0) := by
  show ks d * (ofN 2 - ofN 2 * (vBIT d + vBW d - ofN 2 * vBIT d * vBW d)) = _
  simp only [ks, bF_t hk, vBW, vBIT, hb]
  cases d.bit <;> decide

theorem evNEXTL (hk : d.kind = 3) (hb : d.bw = true) :
    (col Dec.NEXTL).eval ((rowT A d).env 0) = ofN (if d.bit && d.last then 0 else d.key + 12 + 6 * d.lvl) := by
  show ks d * (1 - vDROP d) * (ofN d.key + ofN 12 + ofN 6 * ofN d.lvl) = _
  simp only [ks, bF_t hk, vDROP, vBW, vBIT, vL, hb]
  have e : ofN (d.key + 12 + 6 * d.lvl) = ofN d.key + ofN 12 + ofN 6 * ofN d.lvl := by
    rw [ofN_add, ofN_add, ofN_mul]
  cases d.bit <;> cases d.last
  · show 1 * (1 - 1 * 0 * 0) * _ = ofN (d.key + 12 + 6 * d.lvl)
    rw [e, show (1 * (1 - 1 * 0 * 0) : F) = 1 by decide, one_mul']
  · show 1 * (1 - 1 * 0 * 1) * _ = ofN (d.key + 12 + 6 * d.lvl)
    rw [e, show (1 * (1 - 1 * 0 * 1) : F) = 1 by decide, one_mul']
  · show 1 * (1 - 1 * 1 * 0) * _ = ofN (d.key + 12 + 6 * d.lvl)
    rw [e, show (1 * (1 - 1 * 1 * 0) : F) = 1 by decide, one_mul']
  · show 1 * (1 - 1 * 1 * 1) * _ = (0 : F)
    rw [show (1 * (1 - 1 * 1 * 1) : F) = 0 by decide, zero_mul']

theorem nz {P : Prop} [Decidable P] {x : F} (h : bF (decide P) * x ≠ 0) : P := by
  by_cases hp : P
  · exact hp
  · rw [bF_f hp, zero_mul'] at h; exact absurd rfl h

theorem nz' {P : Prop} [Decidable P] {x : F} (h : x * bF (decide P) ≠ 0) : P := by
  by_cases hp : P
  · exact hp
  · rw [bF_f hp, mul_zero'] at h; exact absurd rfl h

theorem sub_nz (h : vSUB d ≠ 0) : d.kind = 1 ∧ d.ro = 0 := by
  unfold vSUB kc h0 at h
  exact ⟨nz h, (nz' h).2⟩

theorem suberr_nz (h : vSUB d * bF d.err ≠ 0) : d.kind = 1 ∧ d.ro = 0 ∧ d.err = true := by
  have h1 : vSUB d ≠ 0 := fun e => h (by rw [e, zero_mul'])
  refine ⟨(sub_nz h1).1, (sub_nz h1).2, ?_⟩
  cases he : d.err
  · rw [he] at h; exact absurd (mul_zero' _) h
  · rfl

theorem hc_nz (h : kc d * h1 d ≠ 0) : d.kind = 1 ∧ d.ro = 1 := by
  unfold kc h1 at h; exact ⟨nz h, (nz' h).2⟩

theorem hat_nz (h : ka d * h1 d ≠ 0) : d.kind = 2 ∧ d.ro = 1 := by
  unfold ka h1 at h; exact ⟨nz h, (nz' h).2⟩

theorem asub_nz (h : ka d * h0 d ≠ 0) : d.kind = 2 ∧ d.ro = 0 := by
  unfold ka h0 at h; exact ⟨nz h, (nz' h).2⟩

theorem cw_nz (h : ks d * vWR d ≠ 0) : d.kind = 3 ∧ d.bw = true ∧ ¬(d.bit = true ∧ d.last = true) := by
  unfold ks at h
  have hk := nz h
  rw [bF_t hk, one_mul'] at h
  refine ⟨hk, ?_⟩
  simp only [vWR, vDROP, vBW, vBIT, vL] at h
  cases hb : d.bw <;> cases hi : d.bit <;> cases hl : d.last <;> simp only [hb, hi, hl, bF_true, bF_false] at h <;>
    first | exact absurd h (by decide) | simp

theorem cwl_nz (h : ks d * vWL d ≠ 0) : d.kind = 3 ∧ d.bw = true ∧ d.bit = true ∧ d.last = false := by
  unfold ks at h
  have hk := nz h
  rw [bF_t hk, one_mul'] at h
  refine ⟨hk, ?_⟩
  simp only [vWL, vBW, vBIT, vL] at h
  cases hb : d.bw <;> cases hi : d.bit <;> cases hl : d.last <;> simp only [hb, hi, hl, bF_true, bF_false] at h <;>
    first | exact absurd h (by decide) | simp

theorem clk_nz (h : ks d * vBW d ≠ 0) : d.kind = 3 ∧ d.bw = true := by
  unfold ks at h
  have hk := nz h
  rw [bF_t hk, one_mul'] at h
  refine ⟨hk, ?_⟩
  simp only [vBW] at h
  cases hb : d.bw <;> simp only [hb, bF_true, bF_false] at h <;> first | exact absurd h (by decide) | rfl

theorem nlk_nz (h : kn d * vBW d ≠ 0) : d.kind = 4 ∧ d.bw = true := by
  unfold kn at h
  have hk := nz h
  rw [bF_t hk, one_mul'] at h
  refine ⟨hk, ?_⟩
  simp only [vBW] at h
  cases hb : d.bw <;> simp only [hb, bF_true, bF_false] at h <;> first | exact absurd h (by decide) | rfl

theorem decInters_split : Dec.decInters = (List.range Dec.NSLOT).map Dec.slotInter ++ Dec.decInters.drop 25 := by
  rfl

theorem decInters_tail : Dec.decInters.drop 25 =
  [⟨"decn", 1, .neg (.add (col Dec.KCELL) (col Dec.KATOM)), [col Dec.KEY, col Dec.PC, col Dec.RO]⟩,
     ⟨"decn", 1, col Dec.KCELL, [col Dec.KEY, Dec.f2 21, .sub (c 2) (col Dec.H0)]⟩,
     ⟨"decn", 1, col Dec.KCELL, [col Dec.KEY, Dec.f2 23, c 2]⟩,
     ⟨"decb", 1, col Dec.KATOM, [col Dec.KEY, Dec.f2 22, .sub one (col Dec.H1), c 0, col Dec.H1, c 0]⟩,
     ⟨"decb", 1, .neg (col Dec.KCONS), [col Dec.KEY, col Dec.PC, col Dec.MODE, col Dec.LVL, col Dec.BW, col Dec.WC]⟩,
     ⟨"decb", 1, col Dec.CSEND, [col Dec.KEY, Dec.f2 14, col Dec.MODE, .add (col Dec.LVL) one, col Dec.NBW, col Dec.WCN]⟩,
     ⟨"decb", 1, .neg (col Dec.KNIL), [col Dec.KEY, col Dec.PC, col Dec.MODE, col Dec.LVL, col Dec.BW, col Dec.WC]⟩,
     ⟨"decd", 1, .neg (col Dec.SUB), [col Dec.KEY, col Dec.ERR, col Dec.WC]⟩,
     ⟨"decd", 1, col Dec.DONE0, [col Dec.KEY, c 0, col Dec.WCN]⟩,
     ⟨"decd", 1, col Dec.DONE1, [col Dec.KEY, c 1, col Dec.WC]⟩,
     ⟨"decd", 1, col Dec.HC, [col Dec.KEY, c 1, c 0]⟩,
     ⟨"decx", 1, col Dec.SUB, [col Dec.KEY, .add (col Dec.KEY) (.mul (c 12) (col Dec.ERR)),
       .add (.add (.add (col Dec.KEY) (c 12)) (col Dec.WC)) (.mul (c 3) (col Dec.ERR))]⟩,
     ⟨"decx", 1, col Dec.ASUB, [col Dec.KEY, col Dec.KEY, .add (col Dec.KEY) (c 3)]⟩,
     -- The subject's `Cell` wrapper at `key`.
     Dec.wr (Dec.kE 0) (c 0) (Dec.kE 1) (col Dec.SUB), Dec.wr (Dec.kE 1) (Dec.f1 2) (Dec.kE 2) (col Dec.SUB), Dec.wr (Dec.kE 2) (Dec.f1 8) (Dec.kE 3) (col Dec.SUB),
     Dec.wr (Dec.kE 3) (Dec.kE 4) (Dec.f2 14) (col Dec.SUB), Dec.wr (Dec.kE 4) (Dec.f1 15) (Dec.kE 5) (col Dec.SUB), Dec.wr (Dec.kE 5) (Dec.f1 17) (Dec.kE 6) (col Dec.SUB),
     Dec.wr (Dec.kE 6) (c 0) (Dec.kE 7) (col Dec.SUB),
     -- `errT` at `key + 12` on a crash.
     Dec.wr (Dec.kE 12) (c 0) (Dec.kE 13) (col Dec.SUBERR), Dec.wr (Dec.kE 13) (c 0) (Dec.kE 14) (col Dec.SUBERR), Dec.wr (Dec.kE 14) (c 0) (c 1) (col Dec.SUBERR),
     -- A cell head: the `Atom` wrapper's slots filled.
     Dec.wr (Dec.kE 7) (c 0) (c 0) (col Dec.HC), Dec.wr (Dec.kE 8) (c 0) (c 0) (col Dec.HC), Dec.wr (Dec.kE 9) (c 0) (c 0) (col Dec.HC),
     Dec.wr (Dec.kE 10) (c 0) (c 0) (col Dec.HC), Dec.wr (Dec.kE 11) (c 0) (c 0) (col Dec.HC),
     -- The head's `Atom` wrapper at `key + 7`.
     Dec.wr (Dec.kE 7) (Dec.f1 0) (Dec.kE 8) (col Dec.HAT), Dec.wr (Dec.kE 8) (Dec.f1 6) (Dec.kE 9) (col Dec.HAT), Dec.wr (Dec.kE 9) (Dec.f1 12) (Dec.kE 10) (col Dec.HAT),
     Dec.wr (Dec.kE 10) (Dec.f1 18) (Dec.kE 11) (col Dec.HAT),
     -- An atom subject: `errT` at `key`.
     Dec.wr (Dec.kE 0) (c 0) (Dec.kE 1) (col Dec.ASUB), Dec.wr (Dec.kE 1) (c 0) (Dec.kE 2) (col Dec.ASUB), Dec.wr (Dec.kE 2) (c 0) (c 1) (col Dec.ASUB),
     -- A rewritten bit's `Cons`.
     Dec.wr (Dec.apE 0) (c 0) (Dec.apE 1) (col Dec.CW), Dec.wr (Dec.apE 1) (Dec.apE 2) (Dec.apE 5) (col Dec.CW), Dec.wr (Dec.apE 2) (Dec.f1 3) (Dec.apE 3) (col Dec.CW),
     Dec.wr (Dec.apE 3) (Dec.f1 5) (Dec.apE 4) (col Dec.CW), Dec.wr (Dec.apE 4) (c 0) (col Dec.PTR) (col Dec.CW),
     Dec.wr (Dec.apE 5) (c 0) (Dec.f2 14) (col Dec.CWL),
     -- The link to this bit, from the bit below or the `Atom` wrapper.
     Dec.wr (.add (.add (col Dec.KEY) (c 11)) (.mul (c 6) (col Dec.LVL))) (c 0) (col Dec.NEXTL) (col Dec.CLK),
     Dec.wr (Dec.kE 11) (c 0) (c 0) (col Dec.NLK)]
 := rfl

set_option maxRecDepth 10000 in
/-- **A well-formed row whose writes are in memory is honest on `mem`.** -/
theorem row_mem (hok : OK A d) (hw : WritesOK A d) (hkl : d.key ≤ A.length) :
    ∀ I ∈ Dec.decAir.inters, I.bus = "mem" → I.count.eval (envOf (vec A d)) ≠ 0 →
      ∃ m, m < A.length ∧ I.fields.map (fun e => e.eval (envOf (vec A d))) = tupleOf A m := by
  intro I hI hbus hc0
  have cong := E.eval_congr (vec_env A d)
  obtain ⟨hcA, hfA⟩ := dec_nowOnly I hI
  rw [cong _ hcA] at hc0
  rw [List.map_congr_left (fun e he => cong e (hfA e he))]
  generalize hρ : (rowT A d).env 0 = ρ at hc0
  have hc := hc0
  change I ∈ Dec.decInters at hI
  rw [decInters_split] at hI
  rcases List.mem_append.1 hI with hI | hI
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hI
    have hj : j < Dec.NSLOT := List.mem_range.1 hj
    subst hρ
    have hsk := slot_kind (D := rowT A d) (q := 0) Nat.zero_lt_one (rowF hok.1) (rowK hok.1) hj
    change (Dec.actE j).eval _ ≠ 0 at hc
    rw [hsk.2.2, expAct_val] at hc
    have ha : act d j = true := by cases h : act d j; rw [h] at hc; exact absurd rfl hc; rfl
    obtain ⟨hlt, htag⟩ := hok.2 j ha
    have hsp := (sl_spec A d (act_lt ha)).2.2
    refine ⟨(sl A d j).1, by omega, ?_⟩
    show [d.col A (Dec.ADDR + j), d.col A (Dec.TAG + j), d.col A (Dec.DFLD + 2 * j), d.col A (Dec.DFLD + 2 * j + 1)] = _
    rw [col_addr A d hj, col_tag A d hj, col_f1 A d hj, col_f2 A d hj]
    unfold tupleOf
    rw [htag, ← hsp]
  · subst hρ
    rw [decInters_tail] at hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | (exact absurd hbus (by decide)) | skip
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 0 (by simp)) (evK 0) rfl (evK 1)
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 1 (by simp)) (evK 1) (evF1 (j := 2) (by decide)) (evK 2)
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 2 (by simp)) (evK 2) (evF1 (j := 8) (by decide)) (evK 3)
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 3 (by simp)) (evK 3) (evK 4) (evF2 (j := 14) (by decide))
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 4 (by simp)) (evK 4) (evF1 (j := 15) (by decide)) (evK 5)
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 5 (by simp)) (evK 5) (evF1 (j := 17) (by decide)) (evK 6)
    · obtain ⟨hk, hr⟩ := sub_nz hc
      exact wr_case (hw.sub hk hr 6 (by simp)) (evK 6) rfl (evK 7)
    · obtain ⟨hk, hr, he⟩ := suberr_nz hc
      exact wr_case (hw.suberr hk hr he 0 (by simp)) (evK 12) rfl (evK 13)
    · obtain ⟨hk, hr, he⟩ := suberr_nz hc
      exact wr_case (hw.suberr hk hr he 1 (by simp)) (evK 13) rfl (evK 14)
    · obtain ⟨hk, hr, he⟩ := suberr_nz hc
      exact wr_case (hw.suberr hk hr he 2 (by simp)) (evK 14) rfl rfl
    · obtain ⟨hk, hr⟩ := hc_nz hc
      exact wr_case (hw.hc hk hr 0 (by simp)) (evK 7) rfl rfl
    · obtain ⟨hk, hr⟩ := hc_nz hc
      exact wr_case (hw.hc hk hr 1 (by simp)) (evK 8) rfl rfl
    · obtain ⟨hk, hr⟩ := hc_nz hc
      exact wr_case (hw.hc hk hr 2 (by simp)) (evK 9) rfl rfl
    · obtain ⟨hk, hr⟩ := hc_nz hc
      exact wr_case (hw.hc hk hr 3 (by simp)) (evK 10) rfl rfl
    · obtain ⟨hk, hr⟩ := hc_nz hc
      exact wr_case (hw.hc hk hr 4 (by simp)) (evK 11) rfl rfl
    · obtain ⟨hk, hr⟩ := hat_nz hc
      exact wr_case (hw.hat hk hr 0 (by simp)) (evK 7) (evF1 (j := 0) (by decide)) (evK 8)
    · obtain ⟨hk, hr⟩ := hat_nz hc
      exact wr_case (hw.hat hk hr 1 (by simp)) (evK 8) (evF1 (j := 6) (by decide)) (evK 9)
    · obtain ⟨hk, hr⟩ := hat_nz hc
      exact wr_case (hw.hat hk hr 2 (by simp)) (evK 9) (evF1 (j := 12) (by decide)) (evK 10)
    · obtain ⟨hk, hr⟩ := hat_nz hc
      exact wr_case (hw.hat hk hr 3 (by simp)) (evK 10) (evF1 (j := 18) (by decide)) (evK 11)
    · obtain ⟨hk, hr⟩ := asub_nz hc
      exact wr_case (hw.asub hk hr 0 (by simp)) (evK 0) rfl (evK 1)
    · obtain ⟨hk, hr⟩ := asub_nz hc
      exact wr_case (hw.asub hk hr 1 (by simp)) (evK 1) rfl (evK 2)
    · obtain ⟨hk, hr⟩ := asub_nz hc
      exact wr_case (hw.asub hk hr 2 (by simp)) (evK 2) rfl rfl
    · obtain ⟨hk, hb, hnl⟩ := cw_nz hc
      exact wr_case (hw.cw hk hb hnl 0 (by simp)) (evA 0) rfl (evA 1)
    · obtain ⟨hk, hb, hnl⟩ := cw_nz hc
      exact wr_case (hw.cw hk hb hnl 1 (by simp)) (evA 1) (evA 2) (evA 5)
    · obtain ⟨hk, hb, hnl⟩ := cw_nz hc
      exact wr_case (hw.cw hk hb hnl 2 (by simp)) (evA 2) (evF1 (j := 3) (by decide)) (evA 3)
    · obtain ⟨hk, hb, hnl⟩ := cw_nz hc
      exact wr_case (hw.cw hk hb hnl 3 (by simp)) (evA 3) (evF1 (j := 5) (by decide)) (evA 4)
    · obtain ⟨hk, hb, hnl⟩ := cw_nz hc
      exact wr_case (hw.cw hk hb hnl 4 (by simp)) (evA 4) rfl (evPTR hk hb)
    · obtain ⟨hk, hb, hbit, hl⟩ := cwl_nz hc
      exact wr_case (hw.cwl hk hb hbit hl) (evA 5) rfl (evF2 (j := 14) (by decide))
    · obtain ⟨hk, hb⟩ := clk_nz hc
      exact wr_case (hw.clk hk hb) (evLK) rfl (evNEXTL hk hb)
    · obtain ⟨hk, hb⟩ := nlk_nz hc
      exact wr_case (hw.nlk hk hb) (evK 11) rfl rfl
end

end DecT

end Circuit
