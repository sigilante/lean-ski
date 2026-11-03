import Ski.Circuit.CompDHead

/-!
# The circuit with the `dec` jet: what a DEC row writes

Each DEC row's writes, with count `1`, are memory cells at addresses its
key (and on a `Cons` row, its level) fixes: the subject's `Cell` wrapper
(`CompDOK.subWrites`), the crash (`errWrites`), a cell head's blank `Atom`
(`hcWrites`), the head's `Atom` wrapper (`hatWrites`), an atom subject's
crash (`asubWrites`), a nil head's link (`nlkWrite`), and a `Cons` row's
rewritten bit and link (`consWrites`).
-/

namespace Circuit

open B Air DecJet

theorem val_key_add {x : F} {n : Nat} (hx : x.val < 2 ^ 28) (hn : n ≤ 300) : (x + ofN n).val = x.val + n :=
  val_add_nat (by have : P = 2013265921 := rfl; omega)

theorem val_mul6 {l : F} (hl : l.val < 64) : (ofN 6 * l).val = 6 * l.val := by
  rw [Fin.val_mul, val_ofN (by decide), Nat.mod_eq_of_lt (by have : P = 2013265921 := rfl; omega)]

theorem val_aE {x l : F} (hx : x.val < 2 ^ 28) (hl : l.val < 64) :
    (x + ofN 12 + ofN 6 * l).val = x.val + 12 + 6 * l.val := by
  rw [val_add_of_lt, val_key_add hx (by decide), val_mul6 hl] <;>
  rw [val_key_add hx (by decide), val_mul6 hl] <;> have : P = 2013265921 := rfl <;> omega

theorem val_link {x l : F} (hx : x.val < 2 ^ 28) (hl : l.val < 64) :
    (x + ofN 11 + ofN 6 * l).val = x.val + 11 + 6 * l.val := by
  rw [val_add_of_lt, val_key_add hx (by decide), val_mul6 hl] <;>
  rw [val_key_add hx (by decide), val_mul6 hl] <;> have : P = 2013265921 := rfl <;> omega

theorem val_aE_add {x l : F} (hx : x.val < 2 ^ 28) (hl : l.val < 64) {n : Nat} (hn : n ≤ 6) :
    (x + ofN 12 + ofN 6 * l + ofN n).val = x.val + 12 + 6 * l.val + n := by
  rw [val_add_nat (by rw [val_aE hx hl]; have : P = 2013265921 := rfl; omega), val_aE hx hl]

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

/-- A write of `writesI` with count `1` is an application cell in the memory. -/
theorem CompDOK.wrAt {q : Nat} (hq : q < D.h) {ae xe ye ce : E} (hI : Dec.wr ae xe ye ce ∈ Dec.writesI)
    (hc : ce.eval (D.env q) = 1) :
    (memOf Mm)[(ae.eval (D.env q)).val]? = some (.app (xe.eval (D.env q)).val (ye.eval (D.env q)).val) := by
  have := (h.decWrite hq hI (a := ae.eval (D.env q)) (t := ofN 3) (x := xe.eval (D.env q)) (y := ye.eval (D.env q))
    (by simp only [Dec.wr, List.map_cons, List.map_nil, E.eval, c]) hc).2
  rw [this]; rfl

theorem CompDOK.wrK {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28) {i : Nat} (hi : i ≤ 14)
    {xe ye ce : E} (hI : Dec.wr (Dec.kE i) xe ye ce ∈ Dec.writesI) (hc : ce.eval (D.env q) = 1) :
    (memOf Mm)[(D.main q Dec.KEY).val + i]? = some (.app (xe.eval (D.env q)).val (ye.eval (D.env q)).val) := by
  have := h.wrAt hq hI hc
  simp only [Dec.kE, E.eval, col_eval hq, c] at this
  rw [val_key_add hk (by omega)] at this
  exact this

/-- **The subject's `Cell` wrapper**, written at the key. -/
theorem CompDOK.subWrites {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28) (hs : D.main q Dec.SUB = 1) :
    let k := (D.main q Dec.KEY).val
    (memOf Mm)[k]? = some (.app 0 (k + 1)) ∧
    (memOf Mm)[k + 1]? = some (.app (D.main q (Dec.DFLD + 4)).val (k + 2)) ∧
    (memOf Mm)[k + 2]? = some (.app (D.main q (Dec.DFLD + 16)).val (k + 3)) ∧
    (memOf Mm)[k + 3]? = some (.app (k + 4) (D.main q (Dec.DFLD + 29)).val) ∧
    (memOf Mm)[k + 4]? = some (.app (D.main q (Dec.DFLD + 30)).val (k + 5)) ∧
    (memOf Mm)[k + 5]? = some (.app (D.main q (Dec.DFLD + 34)).val (k + 6)) ∧
    (memOf Mm)[k + 6]? = some (.app 0 (k + 7)) := by
  intro k
  have cv := col_eval hq
  have hc : (col Dec.SUB).eval (D.env q) = 1 := by rw [cv, hs]
  have w := fun {i : Nat} (hi : i ≤ 14) {xe ye : E} (hI : Dec.wr (Dec.kE i) xe ye (col Dec.SUB) ∈ Dec.writesI) =>
    h.wrK hq hk hi hI hc
  have k1 : ∀ i, i ≤ 14 → ((Dec.kE i).eval (D.env q)).val = k + i := fun i hi => by
    simp only [Dec.kE, E.eval, cv, c]; exact val_key_add hk (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := w (i := 0) (by decide) (xe := c 0) (ye := Dec.kE 1) (by simp [Dec.writesI])
    rw [Nat.add_zero, k1 1 (by decide)] at this; exact this
  · have := w (i := 1) (by decide) (xe := Dec.f1 2) (ye := Dec.kE 2) (by simp [Dec.writesI])
    rw [k1 2 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := w (i := 2) (by decide) (xe := Dec.f1 8) (ye := Dec.kE 3) (by simp [Dec.writesI])
    rw [k1 3 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := w (i := 3) (by decide) (xe := Dec.kE 4) (ye := Dec.f2 14) (by simp [Dec.writesI])
    rw [k1 4 (by decide)] at this; simpa [Dec.f2, cv] using this
  · have := w (i := 4) (by decide) (xe := Dec.f1 15) (ye := Dec.kE 5) (by simp [Dec.writesI])
    rw [k1 5 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := w (i := 5) (by decide) (xe := Dec.f1 17) (ye := Dec.kE 6) (by simp [Dec.writesI])
    rw [k1 6 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := w (i := 6) (by decide) (xe := c 0) (ye := Dec.kE 7) (by simp [Dec.writesI])
    rw [k1 7 (by decide)] at this; exact this


/-- **The crash**, written at the key plus `12` when the subject's row errs. -/
theorem CompDOK.errWrites {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28)
    (hs : D.main q Dec.SUBERR = 1) :
    let k := (D.main q Dec.KEY).val
    (memOf Mm)[k + 12]? = some (.app 0 (k + 13)) ∧ (memOf Mm)[k + 13]? = some (.app 0 (k + 14)) ∧
    (memOf Mm)[k + 14]? = some (.app 0 1) := by
  intro k
  have cv := col_eval hq
  have hc : (col Dec.SUBERR).eval (D.env q) = 1 := by rw [cv, hs]
  have k1 : ∀ i, i ≤ 14 → ((Dec.kE i).eval (D.env q)).val = k + i := fun i hi => by
    simp only [Dec.kE, E.eval, cv, c]; exact val_key_add hk (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have := h.wrK hq hk (i := 12) (by decide) (xe := c 0) (ye := Dec.kE 13) (by simp [Dec.writesI]) hc
    rw [k1 13 (by decide)] at this; exact this
  · have := h.wrK hq hk (i := 13) (by decide) (xe := c 0) (ye := Dec.kE 14) (by simp [Dec.writesI]) hc
    rw [k1 14 (by decide)] at this; exact this
  · exact h.wrK hq hk (i := 14) (by decide) (xe := c 0) (ye := c 1) (by simp [Dec.writesI]) hc

/-- **A cell head's blank `Atom`**: five `app 0 0` cells after the wrapper. -/
theorem CompDOK.hcWrites {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28) (hs : D.main q Dec.HC = 1) :
    ∀ i, i < 5 → (memOf Mm)[(D.main q Dec.KEY).val + 7 + i]? = some (.app 0 0) := by
  have hc : (col Dec.HC).eval (D.env q) = 1 := by rw [col_eval hq, hs]
  intro i hi
  rw [Nat.add_assoc]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · exact h.wrK hq hk (i := 7) (by decide) (xe := c 0) (ye := c 0) (by simp [Dec.writesI]) hc
  · exact h.wrK hq hk (i := 8) (by decide) (xe := c 0) (ye := c 0) (by simp [Dec.writesI]) hc
  · exact h.wrK hq hk (i := 9) (by decide) (xe := c 0) (ye := c 0) (by simp [Dec.writesI]) hc
  · exact h.wrK hq hk (i := 10) (by decide) (xe := c 0) (ye := c 0) (by simp [Dec.writesI]) hc
  · exact h.wrK hq hk (i := 11) (by decide) (xe := c 0) (ye := c 0) (by simp [Dec.writesI]) hc

/-- **The head's `Atom` wrapper**, its first four cells. -/
theorem CompDOK.hatWrites {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28) (hs : D.main q Dec.HAT = 1) :
    let k := (D.main q Dec.KEY).val
    (memOf Mm)[k + 7]? = some (.app (D.main q Dec.DFLD).val (k + 8)) ∧
    (memOf Mm)[k + 8]? = some (.app (D.main q (Dec.DFLD + 12)).val (k + 9)) ∧
    (memOf Mm)[k + 9]? = some (.app (D.main q (Dec.DFLD + 24)).val (k + 10)) ∧
    (memOf Mm)[k + 10]? = some (.app (D.main q (Dec.DFLD + 36)).val (k + 11)) := by
  intro k
  have cv := col_eval hq
  have hc : (col Dec.HAT).eval (D.env q) = 1 := by rw [cv, hs]
  have k1 : ∀ i, i ≤ 14 → ((Dec.kE i).eval (D.env q)).val = k + i := fun i hi => by
    simp only [Dec.kE, E.eval, cv, c]; exact val_key_add hk (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h.wrK hq hk (i := 7) (by decide) (xe := Dec.f1 0) (ye := Dec.kE 8) (by simp [Dec.writesI]) hc
    rw [k1 8 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := h.wrK hq hk (i := 8) (by decide) (xe := Dec.f1 6) (ye := Dec.kE 9) (by simp [Dec.writesI]) hc
    rw [k1 9 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := h.wrK hq hk (i := 9) (by decide) (xe := Dec.f1 12) (ye := Dec.kE 10) (by simp [Dec.writesI]) hc
    rw [k1 10 (by decide)] at this; simpa [Dec.f1, cv] using this
  · have := h.wrK hq hk (i := 10) (by decide) (xe := Dec.f1 18) (ye := Dec.kE 11) (by simp [Dec.writesI]) hc
    rw [k1 11 (by decide)] at this; simpa [Dec.f1, cv] using this

/-- **An atom subject's crash**, written at the key. -/
theorem CompDOK.asubWrites {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28)
    (hs : D.main q Dec.ASUB = 1) :
    let k := (D.main q Dec.KEY).val
    (memOf Mm)[k]? = some (.app 0 (k + 1)) ∧ (memOf Mm)[k + 1]? = some (.app 0 (k + 2)) ∧
    (memOf Mm)[k + 2]? = some (.app 0 1) := by
  intro k
  have cv := col_eval hq
  have hc : (col Dec.ASUB).eval (D.env q) = 1 := by rw [cv, hs]
  have k1 : ∀ i, i ≤ 14 → ((Dec.kE i).eval (D.env q)).val = k + i := fun i hi => by
    simp only [Dec.kE, E.eval, cv, c]; exact val_key_add hk (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have := h.wrK hq hk (i := 0) (by decide) (xe := c 0) (ye := Dec.kE 1) (by simp [Dec.writesI]) hc
    rw [Nat.add_zero, k1 1 (by decide)] at this; exact this
  · have := h.wrK hq hk (i := 1) (by decide) (xe := c 0) (ye := Dec.kE 2) (by simp [Dec.writesI]) hc
    rw [k1 2 (by decide)] at this; exact this
  · exact h.wrK hq hk (i := 2) (by decide) (xe := c 0) (ye := c 1) (by simp [Dec.writesI]) hc

/-- **An empty head's link**: `app 0 0` at the key plus `11`. -/
theorem CompDOK.nlkWrite {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28) (hs : D.main q Dec.NLK = 1) :
    (memOf Mm)[(D.main q Dec.KEY).val + 11]? = some (.app 0 0) :=
  h.wrK hq hk (i := 11) (by decide) (xe := c 0) (ye := c 0) (ce := col Dec.NLK) (by simp [Dec.writesI])
    (by rw [col_eval hq, hs])

/-- **A `Cons` row's writes**, at `c = key + 12 + 6 · level`: under the
    borrow its link at `c - 1`; when it rewrites, five cells of the
    rewritten `Cons` at `c`, and the sixth, its tail, when it is the set bit. -/
theorem CompDOK.consWrites {q : Nat} (hq : q < D.h) (hk : (D.main q Dec.KEY).val < 2 ^ 28)
    (hl : (D.main q Dec.LVL).val < 32) :
    let a0 := (D.main q Dec.KEY).val + 12 + 6 * (D.main q Dec.LVL).val
    (D.main q Dec.CLK = 1 → (memOf Mm)[(D.main q Dec.KEY).val + 11 + 6 * (D.main q Dec.LVL).val]? =
      some (.app 0 (D.main q Dec.NEXTL).val)) ∧
    (D.main q Dec.CW = 1 →
      (memOf Mm)[a0]? = some (.app 0 (a0 + 1)) ∧ (memOf Mm)[a0 + 1]? = some (.app (a0 + 2) (a0 + 5)) ∧
      (memOf Mm)[a0 + 2]? = some (.app (D.main q (Dec.DFLD + 6)).val (a0 + 3)) ∧
      (memOf Mm)[a0 + 3]? = some (.app (D.main q (Dec.DFLD + 10)).val (a0 + 4)) ∧
      (memOf Mm)[a0 + 4]? = some (.app 0 (D.main q Dec.PTR).val)) ∧
    (D.main q Dec.CWL = 1 → (memOf Mm)[a0 + 5]? = some (.app 0 (D.main q (Dec.DFLD + 29)).val)) := by
  intro a0
  have cv := col_eval hq
  have hl' : (D.main q Dec.LVL).val < 64 := by omega
  have ap : ∀ i, i ≤ 6 → ((Dec.apE i).eval (D.env q)).val = a0 + i := fun i hi => by
    simp only [Dec.apE, Dec.aE, E.eval, cv, c]; exact val_aE_add hk hl' hi
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · have := h.wrAt hq (ae := .add (.add (col Dec.KEY) (c 11)) (.mul (c 6) (col Dec.LVL))) (xe := c 0)
      (ye := col Dec.NEXTL) (ce := col Dec.CLK) (by simp [Dec.writesI]) (by rw [cv, hs])
    simp only [E.eval, cv, c] at this
    rw [val_link hk hl'] at this
    exact this
  · have hc : (col Dec.CW).eval (D.env q) = 1 := by rw [cv, hs]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have := h.wrAt hq (ae := Dec.apE 0) (xe := c 0) (ye := Dec.apE 1) (by simp [Dec.writesI]) hc
      rw [ap 0 (by decide), ap 1 (by decide)] at this; exact this
    · have := h.wrAt hq (ae := Dec.apE 1) (xe := Dec.apE 2) (ye := Dec.apE 5) (by simp [Dec.writesI]) hc
      rw [ap 1 (by decide), ap 2 (by decide), ap 5 (by decide)] at this; exact this
    · have := h.wrAt hq (ae := Dec.apE 2) (xe := Dec.f1 3) (ye := Dec.apE 3) (by simp [Dec.writesI]) hc
      rw [ap 2 (by decide), ap 3 (by decide)] at this; simpa [Dec.f1, cv] using this
    · have := h.wrAt hq (ae := Dec.apE 3) (xe := Dec.f1 5) (ye := Dec.apE 4) (by simp [Dec.writesI]) hc
      rw [ap 3 (by decide), ap 4 (by decide)] at this; simpa [Dec.f1, cv] using this
    · have := h.wrAt hq (ae := Dec.apE 4) (xe := c 0) (ye := col Dec.PTR) (by simp [Dec.writesI]) hc
      rw [ap 4 (by decide)] at this; simp only [cv] at this; exact this
  · have := h.wrAt hq (ae := Dec.apE 5) (xe := c 0) (ye := Dec.f2 14) (ce := col Dec.CWL) (by simp [Dec.writesI])
      (by rw [cv, hs])
    rw [ap 5 (by decide)] at this; simp only [Dec.f2, cv] at this; exact this

end

end Circuit
