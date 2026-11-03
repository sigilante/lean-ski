import Ski.Circuit.CompDStep

/-!
# The circuit with the `dec` jet: what a DEC row reads

A DEC row of each kind reads, through its slots, the cells of its pattern
in the memory below its key (`CompDOK.slotS`), so the Lean readers of
`Ski/DecJet.lean` succeed there: a `Cell` row is `DecJet.readCell` at its
pointer and no `Atom` (`CompDOK.cellRead`), an `Atom` row is
`DecJet.readAtom` (`atomRead`), a `Cons` row is `DecJet.readCons`, its tail
`K` exactly when it is the last (`consRead`), and a nil row reads `K`
(`nilRead`).
-/

namespace Circuit

open B Air DecJet

/-- A slot's source and tag, as the row's values. -/
def srcV (D : Table) (q : Nat) : Dec.Src → F
  | .rowP => D.main q Dec.PC
  | .F1 i => D.main q (Dec.DFLD + 2 * i)
  | .F2 i => D.main q (Dec.DFLD + 2 * i + 1)

def tgV (D : Table) (q : Nat) : Dec.Tg → F
  | .C n => ofN n
  | .BitTag => ofN 3 - ofN 2 * D.main q Dec.BIT
  | .LastTag => ofN 3 - ofN 2 * D.main q Dec.ISLAST

theorem src_eval {D : Table} {q : Nat} (hq : q < D.h) (s : Dec.Src) : (Dec.src s).eval (D.env q) = srcV D q s := by
  cases s <;> simp [Dec.src, Dec.f1, Dec.f2, srcV, col_eval hq]

theorem tg_eval {D : Table} {q : Nat} (hq : q < D.h) (t : Dec.Tg) : (Dec.tg t).eval (D.env q) = tgV D q t := by
  cases t <;> simp [Dec.tg, tgV, E.eval, B.c, col_eval hq]

theorem slotsOf_len {dk : Nat} : (slotsOf dk).length ≤ Dec.NSLOT := by
  unfold slotsOf
  split
  · decide
  · split
    · decide
    · split
      · decide
      · decide

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

/-- **A slot of the row's pattern reads its cell** below the key. -/
theorem CompDOK.slotS {q dk : Nat} (hq : q < D.h) (hk : DKind D q dk) (hdk : dk = 1 ∨ dk = 2 ∨ dk = 3)
    {j : Nat} {s : Dec.Src} {t : Dec.Tg} (hs : (slotsOf dk)[j]? = some (s, t))
    (hact : dk = 3 → j ∈ Dec.consGated → D.main q Dec.CG = 1) :
    (srcV D q s).val < (D.main q Dec.KEY).val ∧
      ((memOf Mm).take (D.main q Dec.KEY).val)[(srcV D q s).val]? =
        some (cellOf (tgV D q t) (D.main q (Dec.DFLD + 2 * j)) (D.main q (Dec.DFLD + 2 * j + 1))) := by
  have hf := decRowF_of h.dec hq
  have hj : j < Dec.NSLOT := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hs).1 slotsOf_len
  have h4 : dk ≠ 4 := by rcases hdk with rfl | rfl | rfl <;> decide
  obtain ⟨ka, kt, kc⟩ := slot_kind hq hf hk hj
  obtain ⟨ca, ct, _, _⟩ := slot_cols h.dec hq hj
  have ea : expAddr dk j = Dec.src s := by unfold expAddr; rw [if_neg h4, hs]
  have et : expTag dk j = Dec.tg t := by unfold expTag; rw [if_neg h4, hs]
  have hact' : (Dec.actE j).eval (D.env q) = 1 := by
    rw [kc]
    unfold expAct
    rw [if_neg h4, hs]
    dsimp only
    split
    · next hg => show D.env q (.main 0 Dec.CG) = 1; rw [env_main0 hq]; exact hact hg.1 hg.2
    · rfl
  obtain ⟨hlt, hget⟩ := h.slotRead hq hj hact'
  rw [ca, ka, ea, src_eval hq] at hlt hget
  rw [ct, kt, et, tg_eval hq] at hget
  refine ⟨hlt, ?_⟩
  rw [List.getElem?_take, if_pos hlt, hget]

/-- **A `Cell` row reads a `Cell` wrapper** at its pointer, and no `Atom`. -/
theorem CompDOK.cellRead {q : Nat} (hq : q < D.h) (hk : DKind D q 1) :
    let H := (memOf Mm).take (D.main q Dec.KEY).val
    readCell H (D.main q Dec.PC).val = some ⟨(D.main q (Dec.DFLD + 4)).val, (D.main q (Dec.DFLD + 16)).val,
      (D.main q (Dec.DFLD + 30)).val, (D.main q (Dec.DFLD + 34)).val, (D.main q (Dec.DFLD + 29)).val,
      (D.main q (Dec.DFLD + 43)).val, (D.main q (Dec.DFLD + 47)).val⟩ ∧
    readAtom H (D.main q Dec.PC).val = none ∧ isK H (D.main q Dec.PC).val = false := by
  intro H
  have s0 : H[(D.main q Dec.PC).val]? = some (.app (D.main q Dec.DFLD).val (D.main q (Dec.DFLD + 1)).val) :=
    (h.slotS hq hk (by decide) (j := 0) (s := .rowP) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s1 : H[(D.main q Dec.DFLD).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 1) (s := (.F1 0)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s2 : H[(D.main q (Dec.DFLD + 1)).val]? = some (.app (D.main q (Dec.DFLD + 4)).val (D.main q (Dec.DFLD + 5)).val) :=
    (h.slotS hq hk (by decide) (j := 2) (s := (.F2 0)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s3 : H[(D.main q (Dec.DFLD + 4)).val]? = some (.app (D.main q (Dec.DFLD + 6)).val (D.main q (Dec.DFLD + 7)).val) :=
    (h.slotS hq hk (by decide) (j := 3) (s := (.F1 2)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s4 : H[(D.main q (Dec.DFLD + 6)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 4) (s := (.F1 3)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s5 : H[(D.main q (Dec.DFLD + 7)).val]? = some (.app (D.main q (Dec.DFLD + 10)).val (D.main q (Dec.DFLD + 11)).val) :=
    (h.slotS hq hk (by decide) (j := 5) (s := (.F2 3)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s6 : H[(D.main q (Dec.DFLD + 10)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 6) (s := (.F1 5)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s7 : H[(D.main q (Dec.DFLD + 11)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 7) (s := (.F2 5)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s8 : H[(D.main q (Dec.DFLD + 5)).val]? = some (.app (D.main q (Dec.DFLD + 16)).val (D.main q (Dec.DFLD + 17)).val) :=
    (h.slotS hq hk (by decide) (j := 8) (s := (.F2 2)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s9 : H[(D.main q (Dec.DFLD + 16)).val]? = some (.app (D.main q (Dec.DFLD + 18)).val (D.main q (Dec.DFLD + 19)).val) :=
    (h.slotS hq hk (by decide) (j := 9) (s := (.F1 8)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s10 : H[(D.main q (Dec.DFLD + 18)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 10) (s := (.F1 9)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s11 : H[(D.main q (Dec.DFLD + 19)).val]? = some (.app (D.main q (Dec.DFLD + 22)).val (D.main q (Dec.DFLD + 23)).val) :=
    (h.slotS hq hk (by decide) (j := 11) (s := (.F2 9)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s12 : H[(D.main q (Dec.DFLD + 22)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 12) (s := (.F1 11)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s13 : H[(D.main q (Dec.DFLD + 23)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 13) (s := (.F2 11)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s14 : H[(D.main q (Dec.DFLD + 17)).val]? = some (.app (D.main q (Dec.DFLD + 28)).val (D.main q (Dec.DFLD + 29)).val) :=
    (h.slotS hq hk (by decide) (j := 14) (s := (.F2 8)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s15 : H[(D.main q (Dec.DFLD + 28)).val]? = some (.app (D.main q (Dec.DFLD + 30)).val (D.main q (Dec.DFLD + 31)).val) :=
    (h.slotS hq hk (by decide) (j := 15) (s := (.F1 14)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s16 : H[(D.main q (Dec.DFLD + 30)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 16) (s := (.F1 15)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s17 : H[(D.main q (Dec.DFLD + 31)).val]? = some (.app (D.main q (Dec.DFLD + 34)).val (D.main q (Dec.DFLD + 35)).val) :=
    (h.slotS hq hk (by decide) (j := 17) (s := (.F2 15)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s18 : H[(D.main q (Dec.DFLD + 34)).val]? = some (.app (D.main q (Dec.DFLD + 36)).val (D.main q (Dec.DFLD + 37)).val) :=
    (h.slotS hq hk (by decide) (j := 18) (s := (.F1 17)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s19 : H[(D.main q (Dec.DFLD + 36)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 19) (s := (.F1 18)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s20 : H[(D.main q (Dec.DFLD + 37)).val]? = some (.I) :=
    (h.slotS hq hk (by decide) (j := 20) (s := (.F2 18)) (t := .C 2) rfl (fun h3 => absurd h3 (by decide))).2
  have s21 : H[(D.main q (Dec.DFLD + 35)).val]? = some (.app (D.main q (Dec.DFLD + 42)).val (D.main q (Dec.DFLD + 43)).val) :=
    (h.slotS hq hk (by decide) (j := 21) (s := (.F2 17)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s22 : H[(D.main q (Dec.DFLD + 42)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 22) (s := (.F1 21)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s23 : H[(D.main q (Dec.DFLD + 29)).val]? = some (.app (D.main q (Dec.DFLD + 46)).val (D.main q (Dec.DFLD + 47)).val) :=
    (h.slotS hq hk (by decide) (j := 23) (s := (.F2 14)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s24 : H[(D.main q (Dec.DFLD + 46)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 24) (s := (.F1 23)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  refine ⟨?_, ?_, ?_⟩
  · simp only [readCell, s0, s2, s8, s14, s15, s23, s17, s21, isK, isS, isI, isSI, isSKK, s1, s3, s4, s5, s6, s7, s9,
      s10, s11, s12, s13, s16, s18, s19, s20, s22, s24, beq_self_eq_true, Bool.and_self, if_true]
  · have hS : isSKK H (D.main q Dec.DFLD).val = false := by simp [isSKK, s1]
    simp only [readAtom, s0, s2, s8, s14, s23, hS, Bool.false_and, Bool.false_eq_true, if_false]
  · simp [isK, s0]

/-- **An `Atom` row reads an `Atom` wrapper** at its pointer. -/
theorem CompDOK.atomRead {q : Nat} (hq : q < D.h) (hk : DKind D q 2) :
    let H := (memOf Mm).take (D.main q Dec.KEY).val
    readAtom H (D.main q Dec.PC).val = some ⟨(D.main q Dec.DFLD).val, (D.main q (Dec.DFLD + 12)).val,
      (D.main q (Dec.DFLD + 24)).val, (D.main q (Dec.DFLD + 36)).val, (D.main q (Dec.DFLD + 45)).val⟩ ∧
    isK H (D.main q Dec.PC).val = false := by
  intro H
  have s0 : H[(D.main q Dec.PC).val]? = some (.app (D.main q Dec.DFLD).val (D.main q (Dec.DFLD + 1)).val) :=
    (h.slotS hq hk (by decide) (j := 0) (s := .rowP) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s1 : H[(D.main q Dec.DFLD).val]? = some (.app (D.main q (Dec.DFLD + 2)).val (D.main q (Dec.DFLD + 3)).val) :=
    (h.slotS hq hk (by decide) (j := 1) (s := (.F1 0)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s2 : H[(D.main q (Dec.DFLD + 2)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 2) (s := (.F1 1)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s3 : H[(D.main q (Dec.DFLD + 3)).val]? = some (.app (D.main q (Dec.DFLD + 6)).val (D.main q (Dec.DFLD + 7)).val) :=
    (h.slotS hq hk (by decide) (j := 3) (s := (.F2 1)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s4 : H[(D.main q (Dec.DFLD + 6)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 4) (s := (.F1 3)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s5 : H[(D.main q (Dec.DFLD + 7)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 5) (s := (.F2 3)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s6 : H[(D.main q (Dec.DFLD + 1)).val]? = some (.app (D.main q (Dec.DFLD + 12)).val (D.main q (Dec.DFLD + 13)).val) :=
    (h.slotS hq hk (by decide) (j := 6) (s := (.F2 0)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s7 : H[(D.main q (Dec.DFLD + 12)).val]? = some (.app (D.main q (Dec.DFLD + 14)).val (D.main q (Dec.DFLD + 15)).val) :=
    (h.slotS hq hk (by decide) (j := 7) (s := (.F1 6)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s8 : H[(D.main q (Dec.DFLD + 14)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 8) (s := (.F1 7)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s9 : H[(D.main q (Dec.DFLD + 15)).val]? = some (.app (D.main q (Dec.DFLD + 18)).val (D.main q (Dec.DFLD + 19)).val) :=
    (h.slotS hq hk (by decide) (j := 9) (s := (.F2 7)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s10 : H[(D.main q (Dec.DFLD + 18)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 10) (s := (.F1 9)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s11 : H[(D.main q (Dec.DFLD + 19)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 11) (s := (.F2 9)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s12 : H[(D.main q (Dec.DFLD + 13)).val]? = some (.app (D.main q (Dec.DFLD + 24)).val (D.main q (Dec.DFLD + 25)).val) :=
    (h.slotS hq hk (by decide) (j := 12) (s := (.F2 6)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s13 : H[(D.main q (Dec.DFLD + 24)).val]? = some (.app (D.main q (Dec.DFLD + 26)).val (D.main q (Dec.DFLD + 27)).val) :=
    (h.slotS hq hk (by decide) (j := 13) (s := (.F1 12)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s14 : H[(D.main q (Dec.DFLD + 26)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 14) (s := (.F1 13)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s15 : H[(D.main q (Dec.DFLD + 27)).val]? = some (.app (D.main q (Dec.DFLD + 30)).val (D.main q (Dec.DFLD + 31)).val) :=
    (h.slotS hq hk (by decide) (j := 15) (s := (.F2 13)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s16 : H[(D.main q (Dec.DFLD + 30)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 16) (s := (.F1 15)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s17 : H[(D.main q (Dec.DFLD + 31)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 17) (s := (.F2 15)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  have s18 : H[(D.main q (Dec.DFLD + 25)).val]? = some (.app (D.main q (Dec.DFLD + 36)).val (D.main q (Dec.DFLD + 37)).val) :=
    (h.slotS hq hk (by decide) (j := 18) (s := (.F2 12)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s19 : H[(D.main q (Dec.DFLD + 36)).val]? = some (.app (D.main q (Dec.DFLD + 38)).val (D.main q (Dec.DFLD + 39)).val) :=
    (h.slotS hq hk (by decide) (j := 19) (s := (.F1 18)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s20 : H[(D.main q (Dec.DFLD + 38)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 20) (s := (.F1 19)) (t := .C 0) rfl (fun h3 => absurd h3 (by decide))).2
  have s21 : H[(D.main q (Dec.DFLD + 39)).val]? = some (.I) :=
    (h.slotS hq hk (by decide) (j := 21) (s := (.F2 19)) (t := .C 2) rfl (fun h3 => absurd h3 (by decide))).2
  have s22 : H[(D.main q (Dec.DFLD + 37)).val]? = some (.app (D.main q (Dec.DFLD + 44)).val (D.main q (Dec.DFLD + 45)).val) :=
    (h.slotS hq hk (by decide) (j := 22) (s := (.F2 18)) (t := .C 3) rfl (fun h3 => absurd h3 (by decide))).2
  have s23 : H[(D.main q (Dec.DFLD + 44)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 23) (s := (.F1 22)) (t := .C 1) rfl (fun h3 => absurd h3 (by decide))).2
  refine ⟨?_, ?_⟩
  · simp only [readAtom, s0, s6, s12, s18, s22, isK, isS, isI, isSI, isSKK, s1, s2, s3, s4, s5, s7, s8, s9, s10, s11,
      s13, s14, s15, s16, s17, s19, s20, s21, s23, beq_self_eq_true, Bool.and_self, if_true]
  · simp [isK, s0]


/-- **A `Cons` row reads a `Cons` cell** at its pointer, its bit the row's,
    its tail `K` when it is the last and an application when not. -/
theorem CompDOK.consRead {q : Nat} (hq : q < D.h) (hk : DKind D q 3) :
    let H := (memOf Mm).take (D.main q Dec.KEY).val
    isK H (D.main q Dec.PC).val = false ∧
    DecJet.readCons H (D.main q Dec.PC).val = some (decide (D.main q Dec.BIT = 1),
      ⟨(D.main q (Dec.DFLD + 6)).val, (D.main q (Dec.DFLD + 10)).val, (D.main q (Dec.DFLD + 29)).val⟩) ∧
    (D.main q Dec.ISLAST = 1 → isK H (D.main q (Dec.DFLD + 29)).val = true) ∧
    (D.main q Dec.ISLAST = 0 → H[(D.main q (Dec.DFLD + 29)).val]? =
      some (.app (D.main q (Dec.DFLD + 32)).val (D.main q (Dec.DFLD + 33)).val)) := by
  intro H
  have hf := decRowF_of h.dec hq
  have s0 : H[(D.main q Dec.PC).val]? = some (.app (D.main q Dec.DFLD).val (D.main q (Dec.DFLD + 1)).val) :=
    (h.slotS hq hk (by decide) (j := 0) (s := .rowP) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s1 : H[(D.main q Dec.DFLD).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 1) (s := (.F1 0)) (t := .C 1) rfl (fun _ hj => absurd hj (by decide))).2
  have s2 : H[(D.main q (Dec.DFLD + 1)).val]? = some (.app (D.main q (Dec.DFLD + 4)).val (D.main q (Dec.DFLD + 5)).val) :=
    (h.slotS hq hk (by decide) (j := 2) (s := (.F2 0)) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s3 : H[(D.main q (Dec.DFLD + 4)).val]? = some (.app (D.main q (Dec.DFLD + 6)).val (D.main q (Dec.DFLD + 7)).val) :=
    (h.slotS hq hk (by decide) (j := 3) (s := (.F1 2)) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s4 : H[(D.main q (Dec.DFLD + 6)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 4) (s := (.F1 3)) (t := .C 0) rfl (fun _ hj => absurd hj (by decide))).2
  have s5 : H[(D.main q (Dec.DFLD + 7)).val]? = some (.app (D.main q (Dec.DFLD + 10)).val (D.main q (Dec.DFLD + 11)).val) :=
    (h.slotS hq hk (by decide) (j := 5) (s := (.F2 3)) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s6 : H[(D.main q (Dec.DFLD + 10)).val]? = some (.app (D.main q (Dec.DFLD + 12)).val (D.main q (Dec.DFLD + 13)).val) :=
    (h.slotS hq hk (by decide) (j := 6) (s := (.F1 5)) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s7 : H[(D.main q (Dec.DFLD + 12)).val]? = some (.S) :=
    (h.slotS hq hk (by decide) (j := 7) (s := (.F1 6)) (t := .C 0) rfl (fun _ hj => absurd hj (by decide))).2
  have s8 : H[(D.main q (Dec.DFLD + 13)).val]? = some (.I) :=
    (h.slotS hq hk (by decide) (j := 8) (s := (.F2 6)) (t := .C 2) rfl (fun _ hj => absurd hj (by decide))).2
  have s9 : H[(D.main q (Dec.DFLD + 11)).val]? = some (.app (D.main q (Dec.DFLD + 18)).val (D.main q (Dec.DFLD + 19)).val) :=
    (h.slotS hq hk (by decide) (j := 9) (s := (.F2 5)) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s10 : H[(D.main q (Dec.DFLD + 18)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 10) (s := (.F1 9)) (t := .C 1) rfl (fun _ hj => absurd hj (by decide))).2
  have s12 : D.main q Dec.BIT = 0 → H[(D.main q (Dec.DFLD + 22)).val]? = some (.K) := fun hb =>
    (h.slotS hq hk (by decide) (j := 12) (s := (.F1 11)) (t := .C 1) rfl
      (fun _ _ => by rw [hf.cg, hk.2.2.2.1, hb]; decide)).2
  have s13 : D.main q Dec.BIT = 0 → H[(D.main q (Dec.DFLD + 23)).val]? = some (.I) := fun hb =>
    (h.slotS hq hk (by decide) (j := 13) (s := (.F2 11)) (t := .C 2) rfl
      (fun _ _ => by rw [hf.cg, hk.2.2.2.1, hb]; decide)).2
  have s14 : H[(D.main q (Dec.DFLD + 5)).val]? = some (.app (D.main q (Dec.DFLD + 28)).val (D.main q (Dec.DFLD + 29)).val) :=
    (h.slotS hq hk (by decide) (j := 14) (s := (.F2 2)) (t := .C 3) rfl (fun _ hj => absurd hj (by decide))).2
  have s15 : H[(D.main q (Dec.DFLD + 28)).val]? = some (.K) :=
    (h.slotS hq hk (by decide) (j := 15) (s := (.F1 14)) (t := .C 1) rfl (fun _ hj => absurd hj (by decide))).2
  have s11 : H[(D.main q (Dec.DFLD + 19)).val]? = some (cellOf (ofN 3 - ofN 2 * D.main q Dec.BIT)
      (D.main q (Dec.DFLD + 22)) (D.main q (Dec.DFLD + 23))) :=
    (h.slotS hq hk (by decide) (j := 11) (s := .F2 9) (t := .BitTag) rfl (fun _ hj => absurd hj (by decide))).2
  have s16 : H[(D.main q (Dec.DFLD + 29)).val]? = some (cellOf (ofN 3 - ofN 2 * D.main q Dec.ISLAST)
      (D.main q (Dec.DFLD + 32)) (D.main q (Dec.DFLD + 33))) :=
    (h.slotS hq hk (by decide) (j := 16) (s := .F2 14) (t := .LastTag) rfl (fun _ hj => absurd hj (by decide))).2
  have hbool : boolAt H (D.main q (Dec.DFLD + 19)).val = some (decide (D.main q Dec.BIT = 1)) := by
    rcases hf.bit with hb | hb
    · rw [hb, show ofN 3 - ofN 2 * (0 : F) = ofN 3 by decide] at s11
      rw [hb, show decide ((0 : F) = 1) = false by decide]
      have e12 := s12 hb
      have e13 := s13 hb
      simp only [boolAt, s11, cellOf_app, isK, isI, e12, e13, beq_self_eq_true, Bool.and_self, if_true]
    · rw [hb, show ofN 3 - ofN 2 * (1 : F) = ofN 1 by decide] at s11
      rw [hb, show decide ((1 : F) = 1) = true by decide]
      simp only [boolAt, s11]; rfl
  refine ⟨by simp [isK, s0], ?_, fun hl => ?_, fun hl => ?_⟩
  · simp only [DecJet.readCons, s0, s2, s3, s14, s5, s9, isK, isS, isSI, isI, s1, s4, s15, s6, s7, s8, s10, hbool,
      beq_self_eq_true, Bool.and_self, if_true]
  · rw [hl, show ofN 3 - ofN 2 * (1 : F) = ofN 1 by decide] at s16
    simp only [isK, s16]; rfl
  · rw [hl, show ofN 3 - ofN 2 * (0 : F) = ofN 3 by decide] at s16
    rw [s16]; rfl

/-- **A nil row reads `K`** at its pointer. -/
theorem CompDOK.nilRead {q : Nat} (hq : q < D.h) (hk : DKind D q 4) :
    isK ((memOf Mm).take (D.main q Dec.KEY).val) (D.main q Dec.PC).val = true := by
  have hf := decRowF_of h.dec hq
  obtain ⟨ka, kt, kc⟩ := slot_kind hq hf hk (j := 0) (by decide)
  obtain ⟨ca, ct, _, _⟩ := slot_cols h.dec hq (j := 0) (by decide)
  obtain ⟨hlt, hget⟩ := h.slotRead hq (j := 0) (by decide) (by rw [kc]; rfl)
  have e1 : D.main q (Dec.ADDR + 0) = D.main q Dec.PC := by
    rw [ca, ka]; exact col_eval hq _
  have e2 : D.main q (Dec.TAG + 0) = ofN 1 := by rw [ct, kt]; rfl
  rw [e1] at hlt hget
  rw [e2] at hget
  simp only [isK, List.getElem?_take, if_pos hlt, hget]; rfl

end

end Circuit
