import Ski.DecJet

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Term

/-!
# The `dec` jet's row reading through `K`-thunks

`Ski/NoLayout.lean` proves that on the write-once machine no closed term
lays out a computed `encNn` cell by cell: a computed cell reaches a
dynamic continuation only folded, as the thunk `K R w` (an application
cell whose function is `K` applied to `R`).  This module generalises the
row's reader so that it reads through such thunks, and re-establishes the
row's read-back.

**The reader.**  `readInd H p` is the indirection at `p`: `p` holds `f w`,
`f` holds `k R` and `k` holds `K`; the read follows to `R`.  The reader
follows indirections

- at every pointer the need tree passes through: the subject's root and
  head (`readSubjI`, `headAtom`), a cell's halves (`readNnI`), an atom's
  bit list and every tail in it (`readBitsI`);
- at one slot inside a `Cell` wrapper, the cell `K t` that holds the tail
  (`ktAt`).  A continuation-passing normaliser cannot write both
  `S (S I (K h))` and `K t` bare when `h` and `t` are both computed
  (`NoLayout`), so one of them arrives folded; the reader takes `K t`
  through one thunk.

No pattern the row reads has the shape `K R w` at those pointers, so the
reader is deterministic.  The fuel bounds the chains; in a state whose
read-back is finite every chain is.

**Read-back.**  An indirection is invisible to the term: `K R w ⟶ R`.  The
read-back of a subject the reader reads is not `encNn s` but a term that
reduces to it (`ORed`, contraction of `K`-redexes anywhere in the term):
`readNnI_ot`, `readSubjI_ot`.  The row writes the same cells as
`DecJet.decRow` (`outCells`), over the input's cells, so the output's
read-back reduces to `encO (decSpec s)` (`out_otI`).

**`decRowI_step`**: a row reads back as `J ⬝ u ⬝ R` with `u ↠ encNn s`, the
next state as `v ⬝ R` with `v ↠ encO (decSpec s)`.  **`decRowI_jstep`**: one
step of `JStepI`, the head reduction with the jet up to `ORed` on both
sides, and **`JStepsI.close_K`**: a run of `JStepI` to `K` closes, the jet
closed to any implementation of the contract, to a weak reduction to `K`
(Church–Rosser, `wsteps_K_iff`).  The contract (`decContract`) is
unchanged.

**`decRow_decRowI`**: the reader extends `decRow`'s; on a subject laid out
without thunks the two rows agree.

The circuit's DEC table still reads `decRow`'s patterns; carrying this
reader into it (an indirection row kind in the need tree and the bit
chains, and the tail slot's thunk in the `Cell` row) is the open part of
the route (`todo/dec-norm.md`).
-/

namespace DecJet

open Compose BitArith Mach Air

-- ---------------------------------------------------------------------------
-- `K`-contraction anywhere in an open term
-- ---------------------------------------------------------------------------

/-- **Contraction of `K`-redexes anywhere**: `K x y ⟶ x`, under both sides
    of an application. -/
inductive ORed : OTerm → OTerm → Prop
  | refl (t : OTerm) : ORed t t
  | trans {t u v : OTerm} : ORed t u → ORed u v → ORed t v
  | K (x y : OTerm) : ORed (.K ⬝ₒ x ⬝ₒ y) x
  | app {f f' x x' : OTerm} : ORed f f' → ORed x x' → ORed (f ⬝ₒ x) (f' ⬝ₒ x')

theorem ORed.close (σ : Nat → Term) {u v : OTerm} (h : ORed u v) : WSteps (u.close σ) (v.close σ) := by
  induction h with
  | refl _ => exact .refl _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | K x y => exact .single (.K _ _)
  | app _ _ ihf ihx => exact (WSteps.left _ ihf).trans (WSteps.right _ ihx)

theorem ORed.appR (f : OTerm) {x x' : OTerm} (h : ORed x x') : ORed (f ⬝ₒ x) (f ⬝ₒ x') := .app (.refl f) h

theorem ORed.appL' {f f' : OTerm} (x : OTerm) (h : ORed f f') : ORed (f ⬝ₒ x) (f' ⬝ₒ x) := .app h (.refl x)

theorem ORed.atomO {b b' : OTerm} (h : ORed b b') : ORed (atomO b) (atomO b') :=
  .appR _ (.appR _ (.appR _ (.appR _ (.appR _ h))))

theorem ORed.pairO {h h' t t' : OTerm} (hh : ORed h h') (ht : ORed t t') :
    ORed (BitArith.pairO h t) (BitArith.pairO h' t') :=
  .app (.appR _ (.appR _ (.appR _ hh))) (.appR _ ht)

theorem ORed.cellO {h h' t t' : OTerm} (hh : ORed h h') (ht : ORed t t') : ORed (cellO h t) (cellO h' t') :=
  .appR _ (.appR _ (.appR _ (ORed.pairO hh ht)))

theorem ORed.consO {h t t' : OTerm} (ht : ORed t t') : ORed (consO h t) (consO h t') :=
  .appR _ (ORed.pairO (.refl h) ht)

-- ---------------------------------------------------------------------------
-- The indirection
-- ---------------------------------------------------------------------------

/-- **A `K`-thunk at `p`**: `p` holds `f w`, `f` holds `k R`, `k` holds
    `K`; its target `R`. -/
def readInd (H : List Cell) (p : Nat) : Option Nat :=
  match H[p]? with
  | some (.app f _) =>
    match H[f]? with
    | some (.app k R) => if isK H k then some R else none
    | _ => none
  | _ => none

theorem readInd_eq {H : List Cell} {p R : Nat} (h : readInd H p = some R) :
    ∃ f w k, H[p]? = some (.app f w) ∧ H[f]? = some (.app k R) ∧ isK H k = true := by
  unfold readInd at h
  split at h
  · rename_i f w hp
    split at h
    · rename_i k R' hf
      split at h
      · rename_i hk; cases h; exact ⟨f, w, k, hp, hf, hk⟩
      · cases h
    · cases h
  · cases h

/-- **An indirection peeled**: its read-back reduces to its target's, two
    fuels below. -/
theorem readInd_peel {H : List Cell} {p R : Nat} (h : readInd H p = some R) {F : Nat} {u : OTerm}
    (hu : otermAt H F p = some u) : ∃ f tr, F = f + 2 ∧ otermAt H f R = some tr ∧ ORed u tr := by
  obtain ⟨f, w, k, hp, hf, hk⟩ := readInd_eq h
  obtain ⟨F1, t1, t2, rfl, g1, _, rfl⟩ := app_peel hp hu
  obtain ⟨F2, t3, t4, rfl, g3, g4, rfl⟩ := app_peel hf g1
  have e := K_peel (isK_eq hk) g3
  subst e
  exact ⟨F2, t4, rfl, g4, .K _ _⟩

/-- No `K`-thunk is a `K`. -/
theorem readInd_isK {H : List Cell} {p R : Nat} (h : readInd H p = some R) : isK H p = false := by
  obtain ⟨f, w, k, hp, _, _⟩ := readInd_eq h
  unfold isK; rw [hp]; rfl

/-- No `K`-thunk is a `Cons` cell (its function is a cell, not `K`). -/
theorem readInd_cons {H : List Cell} {p R : Nat} (h : readInd H p = some R) : readCons H p = none := by
  obtain ⟨f, w, k, hp, hf, _⟩ := readInd_eq h
  unfold readCons; rw [hp]; dsimp only
  have : isK H f = false := by unfold isK; rw [hf]; rfl
  rw [if_neg (by rw [this]; decide)]

-- ---------------------------------------------------------------------------
-- Bit lists through thunks
-- ---------------------------------------------------------------------------

/-- **A bit list at `p`**, its `Cons` cells and their tails possibly behind
    `K`-thunks. -/
def readBitsI (H : List Cell) : Nat → Nat → Option (List Bool × List ConsSk)
  | 0, _ => none
  | n + 1, p =>
    if isK H p then some ([], [])
    else match readCons H p with
      | some (b, sk) =>
        match readBitsI H n sk.t with
        | some (bs, sks) => some (b :: bs, sk :: sks)
        | none => none
      | none =>
        match readInd H p with
        | some R => readBitsI H n R
        | none => none

theorem readBitsI_ot {H : List Cell} : ∀ {n p : Nat} {bs : List Bool} {sks : List ConsSk},
    readBitsI H n p = some (bs, sks) → ∀ {F : Nat} {u : OTerm}, otermAt H F p = some u → ORed u (bl bs).toO
  | 0, _, _, _, h, _, _, _ => nomatch h
  | n + 1, p, bs, sks, h, F, u, hu => by
    unfold readBitsI at h
    split at h
    · rename_i hk
      cases h
      rw [K_peel (isK_eq hk) hu]; exact .refl _
    · cases hc : readCons H p with
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h
        dsimp only at h
        cases hr : readBitsI H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          obtain ⟨bs', sks'⟩ := q'
          rw [hr] at h
          cases h
          obtain ⟨f, tt, rfl, _, rfl, ht, _, _⟩ := readCons_peel hc hu
          exact ORed.consO (readBitsI_ot hr ht)
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R =>
          rw [hi] at h
          dsimp only at h
          obtain ⟨f, tr, rfl, hR, hred⟩ := readInd_peel hi hu
          exact hred.trans (readBitsI_ot h hR)

theorem readBitsI_length {H : List Cell} : ∀ {n p : Nat} {bs : List Bool} {sks : List ConsSk},
    readBitsI H n p = some (bs, sks) → sks.length = bs.length
  | 0, _, _, _, h => by cases h
  | n + 1, p, bs, sks, h => by
    unfold readBitsI at h
    split at h
    · cases h; rfl
    · cases hc : readCons H p with
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h
        dsimp only at h
        cases hr : readBitsI H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          obtain ⟨bs', sks'⟩ := q'
          rw [hr] at h
          cases h
          exact congrArg (· + 1) (readBitsI_length hr)
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h; exact readBitsI_length h

-- ---------------------------------------------------------------------------
-- A `Cell` wrapper whose tail slot may be a thunk
-- ---------------------------------------------------------------------------

/-- **The tail slot at `kt`**: `K t`, or a `K`-thunk of `K t`; the tail `t`. -/
def ktAt (H : List Cell) (kt : Nat) : Option Nat :=
  match H[kt]? with
  | some (.app k6 t) =>
    if isK H k6 then some t
    else
      match readInd H kt with
      | some kt' =>
        match H[kt']? with
        | some (.app k6' t') => if isK H k6' then some t' else none
        | _ => none
      | none => none
  | _ => none

/-- The tail slot read back: it reduces to `K` of the tail's read-back, the
    tail at least two fuels below. -/
theorem ktAt_peel {H : List Cell} {kt t : Nat} (h : ktAt H kt = some t) {F : Nat} {u : OTerm}
    (hu : otermAt H F kt = some u) : ∃ f tt, f + 1 ≤ F ∧ otermAt H f t = some tt ∧ ORed u (.K ⬝ₒ tt) := by
  unfold ktAt at h
  split at h
  · rename_i k6 t0 hkt
    split at h
    · rename_i hk
      cases h
      obtain ⟨f, t1, t2, rfl, g1, g2, rfl⟩ := app_peel hkt hu
      rw [K_peel (isK_eq hk) g1]
      have := otermAt_pos g2
      exact ⟨f, t2, by omega, g2, .refl _⟩
    · cases hi : readInd H kt with
      | none => rw [hi] at h; cases h
      | some kt' =>
        rw [hi] at h
        dsimp only at h
        split at h
        · rename_i k6' t' hkt'
          split at h
          · rename_i hk'
            cases h
            obtain ⟨f, tr, rfl, hR, hred⟩ := readInd_peel hi hu
            obtain ⟨f2, t1, t2, rfl, g1, g2, rfl⟩ := app_peel hkt' hR
            rw [K_peel (isK_eq hk') g1] at hred
            exact ⟨f2, t2, by omega, g2, hred⟩
          · cases h
        · cases h
  · cases h

/-- **`Cell h t` at `p`**, the tail slot through `ktAt`: `K (S (K K) (S (K K)
    (S (S I (K h)) kt)))`, `kt` holding `K t` or a thunk of it.  The
    sketch's `kt` is the slot as the wrapper holds it. -/
def readCellI (H : List Cell) (p : Nat) : Option CellSk :=
  match H[p]? with
  | some (.app k0 y1) =>
    match H[y1]? with
    | some (.app a1 y2) =>
      match H[y2]? with
      | some (.app a2 y3) =>
        match H[y3]? with
        | some (.app p1 kt) =>
          match H[p1]? with
          | some (.app s3 p2) =>
            match H[p2]? with
            | some (.app si kh) =>
              match H[kh]? with
              | some (.app k5 h) =>
                if isK H k0 && isSKK H a1 && isSKK H a2 && isS H s3 && isSI H si && isK H k5 then
                  match ktAt H kt with
                  | some t => some ⟨a1, a2, s3, si, kt, h, t⟩
                  | none => none
                else none
              | _ => none
            | _ => none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- **A `Cell` wrapper peeled**: its read-back reduces to `cellO` of its
    halves' read-backs. -/
theorem readCellI_peel {H : List Cell} {p : Nat} {sk : CellSk} (h : readCellI H p = some sk) {F : Nat} {u : OTerm}
    (hu : otermAt H F p = some u) :
    ∃ f th tt tk, F = f + 7 ∧ u = .K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ
        (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ th)) ⬝ₒ tk))) ∧
      otermAt H f sk.h = some th ∧ otermAt H (f + 3) sk.kt = some tk ∧ ORed tk (.K ⬝ₒ tt) ∧
      (∃ g, otermAt H g sk.t = some tt) ∧
      isSKK H sk.a1 = true ∧ isSKK H sk.a2 = true ∧ isS H sk.s3 = true ∧ isSI H sk.si = true := by
  unfold readCellI at h
  split at h <;> try cases h
  rename_i k0 y1 hp
  split at h <;> try cases h
  rename_i a1 y2 h1
  split at h <;> try cases h
  rename_i a2 y3 h2
  split at h <;> try cases h
  rename_i p1 kt h3
  split at h <;> try cases h
  rename_i s3 p2 h4
  split at h <;> try cases h
  rename_i si kh h6
  split at h <;> try cases h
  rename_i k5 hh h7
  split at h
  · rename_i hall
    cases hkt : ktAt H kt with
    | none => rw [hkt] at h; cases h
    | some t =>
      rw [hkt] at h
      cases h
      simp only [Bool.and_eq_true] at hall
      obtain ⟨⟨⟨⟨⟨hk0, ha1⟩, ha2⟩, hs3⟩, hsi⟩, hk5⟩ := hall
      obtain ⟨f1, t1, t2, rfl, g1, g2, rfl⟩ := app_peel hp hu
      have e1 := K_peel (isK_eq hk0) g1
      obtain ⟨f2, t3, t4, rfl, g3, g4, rfl⟩ := app_peel h1 g2
      have e3 := otermAt_det g3 (isSKK_ot ha1 (F := 3) (Nat.le_refl _))
      obtain ⟨f3, t5, t6, rfl, g5, g6, rfl⟩ := app_peel h2 g4
      have e5 := otermAt_det g5 (isSKK_ot ha2 (F := 3) (Nat.le_refl _))
      obtain ⟨f4, t7, t8, rfl, g7, g8, rfl⟩ := app_peel h3 g6
      obtain ⟨f5, t9, t10, rfl, g9, g10, rfl⟩ := app_peel h4 g7
      have e9 := S_peel (isS_eq hs3) g9
      obtain ⟨f6, t13, t14, rfl, g13, g14, rfl⟩ := app_peel h6 g10
      have e13 := otermAt_det g13 (isSI_ot hsi (F := 2) (Nat.le_refl _))
      obtain ⟨f7, t15, t16, rfl, g15, g16, rfl⟩ := app_peel h7 g14
      have e15 := K_peel (isK_eq hk5) g15
      obtain ⟨g, tt, _, gt, hred⟩ := ktAt_peel hkt g8
      subst e1 e3 e5 e9 e13 e15
      exact ⟨f7, t16, tt, t8, by omega, rfl, g16, g8, hred, ⟨g, gt⟩, ha1, ha2, hs3, hsi⟩
  · cases h

-- ---------------------------------------------------------------------------
-- Nouns through thunks
-- ---------------------------------------------------------------------------

/-- **A well-formed noun at `p`**, through `K`-thunks at its root, its
    halves, its bit list and every tail in it, and its tail slots. -/
def readNnI (H : List Cell) : Nat → Nat → Option Nn
  | 0, _ => none
  | n + 1, p =>
    match readAtom H p with
    | some sk =>
      match readBitsI H (n + 1) sk.b with
      | some (bs, _) => if canonB bs then some (.atom bs) else none
      | none => none
    | none =>
      match readCellI H p with
      | some sk =>
        match readNnI H n sk.h, readNnI H n sk.t with
        | some h, some t => some (.cell h t)
        | _, _ => none
      | none =>
        match readInd H p with
        | some R => readNnI H n R
        | none => none

/-- **A noun read back** reduces to its encoding. -/
theorem readNnI_ot {H : List Cell} : ∀ {n p : Nat} {s : Nn}, readNnI H n p = some s →
    ∀ {F : Nat} {u : OTerm}, otermAt H F p = some u → ORed u (encNn s).toO
  | 0, _, _, h, _, _, _ => nomatch h
  | n + 1, p, s, h, F, u, hu => by
    unfold readNnI at h
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h
      dsimp only at h
      cases hb : readBitsI H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks⟩ := q
        rw [hb] at h
        dsimp only at h
        split at h
        · cases h
          obtain ⟨f, tb, rfl, rfl, htb, _⟩ := readAtom_peel ha hu
          exact ORed.atomO (readBitsI_ot hb htb)
        · cases h
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hc : readCellI H p with
      | some sk =>
        rw [hc] at h
        dsimp only at h
        cases hh : readNnI H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNnI H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st =>
            rw [hh, ht] at h
            cases h
            obtain ⟨f, th, tt, tk, rfl, rfl, hth, _, hred, ⟨g, htt⟩, _⟩ := readCellI_peel hc hu
            have e1 := readNnI_ot hh hth
            have e2 := readNnI_ot ht htt
            show ORed _ (cellO (encNn sh).toO (encNn st).toO)
            refine .appR _ (.appR _ (.appR _ (.app (.appR _ (.appR _ (.appR _ e1))) ?_)))
            exact hred.trans (.appR _ e2)
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R =>
          rw [hi] at h
          dsimp only at h
          obtain ⟨f, tr, rfl, hR, hred⟩ := readInd_peel hi hu
          exact hred.trans (readNnI_ot h hR)

/-- A read noun is well formed. -/
theorem readNnI_wf {H : List Cell} : ∀ {n p : Nat} {s : Nn}, readNnI H n p = some s → s.wf = true
  | 0, _, _, h => nomatch h
  | n + 1, p, s, h => by
    unfold readNnI at h
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h
      dsimp only at h
      cases hb : readBitsI H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks⟩ := q
        rw [hb] at h
        dsimp only at h
        split at h
        · cases h; assumption
        · cases h
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hc : readCellI H p with
      | some sk =>
        rw [hc] at h
        dsimp only at h
        cases hh : readNnI H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNnI H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st =>
            rw [hh, ht] at h
            cases h
            show (sh.wf && st.wf) = true
            rw [readNnI_wf hh, readNnI_wf ht]; rfl
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h; exact readNnI_wf h

-- ---------------------------------------------------------------------------
-- The subject
-- ---------------------------------------------------------------------------

/-- **The head atom at `q`**, through `K`-thunks: the address of its
    `Atom` wrapper and its sketch. -/
def headAtom (H : List Cell) : Nat → Nat → Option (Nat × AtomSk)
  | 0, _ => none
  | n + 1, q =>
    match readAtom H q with
    | some ask => some (q, ask)
    | none =>
      match readInd H q with
      | some R => headAtom H n R
      | none => none

/-- The head atom read back: the wrapper's read-back, reached by
    contraction. -/
theorem headAtom_peel {H : List Cell} : ∀ {n q a : Nat} {ask : AtomSk}, headAtom H n q = some (a, ask) →
    ∀ {F : Nat} {u : OTerm}, otermAt H F q = some u →
      readAtom H a = some ask ∧ ∃ G v, G ≤ F ∧ otermAt H G a = some v ∧ ORed u v
  | 0, _, _, _, h, _, _, _ => nomatch h
  | n + 1, q, a, ask, h, F, u, hu => by
    unfold headAtom at h
    cases ha : readAtom H q with
    | some ask' =>
      rw [ha] at h
      cases h
      exact ⟨ha, F, u, Nat.le_refl _, hu, .refl _⟩
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hi : readInd H q with
      | none => rw [hi] at h; cases h
      | some R =>
        rw [hi] at h
        dsimp only at h
        obtain ⟨f, tr, rfl, hR, hred⟩ := readInd_peel hi hu
        obtain ⟨h1, G, v, hG, hv, hred'⟩ := headAtom_peel h hR
        exact ⟨h1, G, v, by omega, hv, hred.trans hred'⟩

/-- A noun that reads as an atom has a head atom at any larger fuel. -/
theorem headAtom_of_atom {H : List Cell} : ∀ {n m q : Nat} {bs : List Bool}, readNnI H n q = some (.atom bs) →
    n ≤ m → ∃ x, headAtom H m q = some x
  | 0, _, _, _, h, _ => nomatch h
  | n + 1, m, q, bs, h, hnm => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold readNnI at h
    unfold headAtom
    cases ha : readAtom H q with
    | some ask => exact ⟨_, rfl⟩
    | none =>
      rw [ha] at h
      dsimp only at h ⊢
      cases hc : readCellI H q with
      | some sk =>
        rw [hc] at h
        dsimp only at h
        cases hh : readNnI H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNnI H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st => rw [hh, ht] at h; cases h
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H q with
        | none => rw [hi] at h; cases h
        | some R =>
          rw [hi] at h
          dsimp only at h ⊢
          exact headAtom_of_atom h (by omega)

/-- **The subject at `p`**, read once, through `K`-thunks: the noun and the
    cells the output reuses, as `readSubj`; the root followed through
    thunks within the fuel. -/
def readSubjI (H : List Cell) : Nat → Nat → Option (Nn × Option CellSk × Option AtomSk × List ConsSk)
  | 0, _ => none
  | n + 1, p =>
    match readAtom H p with
    | some sk =>
      match readBitsI H H.length sk.b with
      | some (bs, sks) => if canonB bs then some (.atom bs, none, some sk, sks) else none
      | none => none
    | none =>
      match readCellI H p with
      | some csk =>
        match headAtom H H.length csk.h with
        | some (_, ask) =>
          match readBitsI H H.length ask.b with
          | some (bs, sks) =>
            if canonB bs then
              match readNnI H H.length csk.t with
              | some r => some (.cell (.atom bs) r, some csk, some ask, sks)
              | none => none
            else none
          | none => none
        | none =>
          match readNnI H H.length csk.h, readNnI H H.length csk.t with
          | some hh, some tt => some (.cell hh tt, some csk, none, [])
          | _, _ => none
      | none =>
        match readInd H p with
        | some R => readSubjI H n R
        | none => none

/-- **The subject read back** reduces to its encoding. -/
theorem readSubjI_ot {H : List Cell} : ∀ {n p : Nat} {s : Nn} {csk : Option CellSk} {ask : Option AtomSk}
    {sks : List ConsSk}, readSubjI H n p = some (s, csk, ask, sks) → ∀ {F : Nat} {u : OTerm},
    otermAt H F p = some u → ORed u (encNn s).toO
  | 0, _, _, _, _, _, h, _, _, _ => nomatch h
  | n + 1, p, s, csk, ask, sks, h, F, u, hu => by
    unfold readSubjI at h
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h
      dsimp only at h
      cases hb : readBitsI H H.length sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks'⟩ := q
        rw [hb] at h
        dsimp only at h
        split at h
        · cases h
          obtain ⟨f, tb, rfl, rfl, htb, _⟩ := readAtom_peel ha hu
          exact ORed.atomO (readBitsI_ot hb htb)
        · cases h
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hc : readCellI H p with
      | some csk' =>
        rw [hc] at h
        dsimp only at h
        obtain ⟨f, th, tt, tk, rfl, rfl, hth, _, hred, ⟨g, htt⟩, _⟩ := readCellI_peel hc hu
        cases ha2 : headAtom H H.length csk'.h with
        | some x =>
          obtain ⟨a, ask'⟩ := x
          rw [ha2] at h
          dsimp only at h
          cases hb : readBitsI H H.length ask'.b with
          | none => rw [hb] at h; cases h
          | some q =>
            obtain ⟨bs, sks'⟩ := q
            rw [hb] at h
            dsimp only at h
            split at h
            · cases ht : readNnI H H.length csk'.t with
              | none => rw [ht] at h; cases h
              | some r =>
                rw [ht] at h
                cases h
                obtain ⟨hra, G, v, _, hv, hred'⟩ := headAtom_peel ha2 hth
                obtain ⟨f', tb, rfl, rfl, htb, _⟩ := readAtom_peel hra hv
                have e1 : ORed th (atomT (bl bs)).toO := hred'.trans (ORed.atomO (readBitsI_ot hb htb))
                have e2 := readNnI_ot ht htt
                show ORed _ (cellO (atomT (bl bs)).toO (encNn r).toO)
                refine .appR _ (.appR _ (.appR _ (.app (.appR _ (.appR _ (.appR _ e1))) ?_)))
                exact hred.trans (.appR _ e2)
            · cases h
        | none =>
          rw [ha2] at h
          dsimp only at h
          cases hh : readNnI H H.length csk'.h with
          | none => rw [hh] at h; cases h
          | some hh' =>
            cases ht : readNnI H H.length csk'.t with
            | none => rw [hh, ht] at h; cases h
            | some tt' =>
              rw [hh, ht] at h
              cases h
              have e1 := readNnI_ot hh hth
              have e2 := readNnI_ot ht htt
              show ORed _ (cellO (encNn hh').toO (encNn tt').toO)
              refine .appR _ (.appR _ (.appR _ (.app (.appR _ (.appR _ (.appR _ e1))) ?_)))
              exact hred.trans (.appR _ e2)
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R =>
          rw [hi] at h
          dsimp only at h
          obtain ⟨f, tr, rfl, hR, hred⟩ := readInd_peel hi hu
          exact hred.trans (readSubjI_ot h hR)

/-- A read subject is well formed. -/
theorem readSubjI_wf {H : List Cell} : ∀ {n p : Nat} {s : Nn} {csk : Option CellSk} {ask : Option AtomSk}
    {sks : List ConsSk}, readSubjI H n p = some (s, csk, ask, sks) → s.wf = true
  | 0, _, _, _, _, _, h => nomatch h
  | n + 1, p, s, csk, ask, sks, h => by
    unfold readSubjI at h
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h
      dsimp only at h
      cases hb : readBitsI H H.length sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks'⟩ := q
        rw [hb] at h
        dsimp only at h
        split at h
        · cases h; assumption
        · cases h
    | none =>
      rw [ha] at h
      dsimp only at h
      cases hc : readCellI H p with
      | some csk' =>
        rw [hc] at h
        dsimp only at h
        cases ha2 : headAtom H H.length csk'.h with
        | some x =>
          obtain ⟨a, ask'⟩ := x
          rw [ha2] at h
          dsimp only at h
          cases hb : readBitsI H H.length ask'.b with
          | none => rw [hb] at h; cases h
          | some q =>
            obtain ⟨bs, sks'⟩ := q
            rw [hb] at h
            dsimp only at h
            split at h
            · rename_i hcan
              cases ht : readNnI H H.length csk'.t with
              | none => rw [ht] at h; cases h
              | some r =>
                rw [ht] at h
                cases h
                show (canonB bs && r.wf) = true
                rw [hcan, readNnI_wf ht]; rfl
            · cases h
        | none =>
          rw [ha2] at h
          dsimp only at h
          cases hh : readNnI H H.length csk'.h with
          | none => rw [hh] at h; cases h
          | some hh' =>
            cases ht : readNnI H H.length csk'.t with
            | none => rw [hh, ht] at h; cases h
            | some tt' =>
              rw [hh, ht] at h
              cases h
              show (hh'.wf && tt'.wf) = true
              rw [readNnI_wf hh, readNnI_wf ht]; rfl
      | none =>
        rw [hc] at h
        dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h; exact readSubjI_wf h

-- ---------------------------------------------------------------------------
-- The output, read back
-- ---------------------------------------------------------------------------

/-- **The output `Cell` wrapper reads back** over the input's tail slot as
    the input holds it (`cell_ot` for a slot of any read-back). -/
theorem cell_otG {H cs : List Cell} (hs : slotsOK (H ++ cs) = true) (csk : CellSk) (c : Nat)
    (hcell : ∀ i, i < 7 → (H ++ cs)[c + i]? = (cellCells c csk)[i]?)
    (ha1 : isSKK H csk.a1 = true) (ha2 : isSKK H csk.a2 = true) (hs3 : isS H csk.s3 = true)
    (hsi : isSI H csk.si = true) {fk : Nat} {tk : OTerm} (hkt : otermAt H fk csk.kt = some tk)
    {fh : Nat} {th : OTerm} (hh : otermAt (H ++ cs) fh (c + 7) = some th) {G : Nat}
    (hG1 : fk + 4 ≤ G) (hG2 : fh + 7 ≤ G) (hG3 : 8 ≤ G) :
    otermAt (H ++ cs) G c = some (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ
      (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ th)) ⬝ₒ tk)))) := by
  have hK := K_ot (slots_K hs) (F := 1) (Nat.le_refl _)
  have hkt' := otermAt_append (cs := cs) hkt
  refine app_ot (F := G) (g := G - 1) (hcell 0 (by omega)) hK ?_ (by omega) (by omega)
  refine app_ot (F := G - 1) (g := G - 2) (hcell 1 (by omega)) (isSKK_ot' ha1 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 2) (g := G - 3) (hcell 2 (by omega)) (isSKK_ot' ha2 (F := 3) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 3) (f := G - 4) (hcell 3 (by omega)) ?_ hkt' (by omega) (by omega)
  refine app_ot (F := G - 4) (g := G - 5) (hcell 4 (by omega)) (isS_ot' hs3 (F := 1) (Nat.le_refl _)) ?_ (by omega) (by omega)
  refine app_ot (F := G - 5) (g := G - 6) (hcell 5 (by omega)) (isSI_ot' hsi (F := 2) (Nat.le_refl _)) ?_ (by omega) (by omega)
  exact app_ot (F := G - 6) (hcell 6 (by omega)) hK hh (by omega) (by omega)

/-- The output's `Cell` wrapper, over a head that reduces to `h` and a tail
    slot that reduces to `K t`, reduces to `cellO h t`. -/
theorem ORed.cellG {th h tk t : OTerm} (hh : ORed th h) (ht : ORed tk (.K ⬝ₒ t)) :
    ORed (.K ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ th)) ⬝ₒ tk))))
      (DecJet.cellO h t) :=
  .appR _ (.appR _ (.appR _ (.app (.appR _ (.appR _ (.appR _ hh))) ht)))

/-- **The output's bits read back**, reducing to `bl (decB bs)`: the
    rewritten `Cons` cells at `c`, over the input's `S` and `S I` cells and
    its shared tail, the input's chain through thunks. -/
theorem bitsI_ot {H cs : List Cell} (hs : slotsOK (H ++ cs) = true) :
    ∀ (n : Nat) (bs : List Bool) (sks : List ConsSk) (c p F : Nat) (u : OTerm), canonB bs = true → bs ≠ [] →
      readBitsI H n p = some (bs, sks) → otermAt H F p = some u →
      (∀ i, i < (bitCells c bs sks).length → (H ++ cs)[c + i]? = (bitCells c bs sks)[i]?) →
      ∀ G, F + 1 ≤ G → ∃ v, otermAt (H ++ cs) G (bitsRoot c bs) = some v ∧ ORed v (bl (decB bs)).toO
  | 0, _, _, _, _, _, _, _, _, hr, _, _, _, _ => nomatch hr
  | n + 1, bs, sks, c, p, F, u, hcan, hne, hr, hu, hcells, G, hG => by
    unfold readBitsI at hr
    split at hr
    · cases hr; exact absurd rfl hne
    · cases hc : readCons H p with
      | none =>
        rw [hc] at hr
        dsimp only at hr
        cases hi : readInd H p with
        | none => rw [hi] at hr; cases hr
        | some R =>
          rw [hi] at hr
          dsimp only at hr
          obtain ⟨f, tr, rfl, hR, _⟩ := readInd_peel hi hu
          exact bitsI_ot hs n bs sks c R f tr hcan hne hr hR hcells G (by omega)
      | some q =>
        obtain ⟨b', sk⟩ := q
        rw [hc] at hr
        dsimp only at hr
        cases hr' : readBitsI H n sk.t with
        | none => rw [hr'] at hr; cases hr
        | some q' =>
          obtain ⟨bs', sks'⟩ := q'
          rw [hr'] at hr
          cases hr
          obtain ⟨f, tt, rfl, hf2, rfl, htt, hss, hc5⟩ := readCons_peel hc hu
          have htt' : ORed tt (bl bs').toO := readBitsI_ot hr' htt
          have hK := K_ot (slots_K hs) (F := 1) (Nat.le_refl _)
          have hS : otermAt (H ++ cs) 1 sk.s = some .S :=
            S_ot (H := H ++ cs) (by
              unfold isS
              rw [List.getElem?_append_left (by
                have := isS_eq hss; rw [List.getElem?_eq_some_iff] at this; exact this.1)]
              exact hss) (F := 1) (Nat.le_refl _)
          have hSI := otermAt_append (cs := cs) (isSI_ot hc5 (F := 2) (Nat.le_refl _))
          cases b' with
          | false =>
            have hne' : bs' ≠ [] := by cases bs' with | nil => cases hcan | cons _ _ => exact List.cons_ne_nil _ _
            rw [bitCells_cons_false] at hcells
            have cell : ∀ i, i < 6 → (H ++ cs)[c + i]? =
                [Cell.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 0,
                 .app 0 (bitsRoot (c + 6) bs')][i]? := fun i hi => by
              rw [hcells i (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
                List.getElem?_append_left (by simp only [List.length_cons, List.length_nil]; omega)]
            obtain ⟨v', hv', hred'⟩ := bitsI_ot hs n bs' sks' (c + 6) sk.t (f + 1) tt (canonB_cons hcan hne') hne' hr' htt
              (fun i hi => by
                have := hcells (6 + i) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                rw [show c + (6 + i) = c + 6 + i by omega] at this
                rw [this, show 6 + i = i + 6 by omega]
                rfl) (G - 3) (by omega)
            refine ⟨.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ .K)) ⬝ₒ (.K ⬝ₒ v')), ?_, ?_⟩
            · show otermAt (H ++ cs) G (if dropped (false :: bs') then 0 else c) = _
              rw [show dropped (false :: bs') = false from rfl, if_neg (by decide)]
              refine app_ot (F := G) (g := G - 1) (cell 0 (by omega)) hK ?_ (by omega) (by omega)
              refine app_ot (F := G - 1) (f := G - 2) (g := G - 2) (cell 1 (by omega)) ?_ ?_ (by omega) (by omega)
              · refine app_ot (F := G - 2) (g := G - 3) (cell 2 (by omega)) hS ?_ (by omega) (by omega)
                refine app_ot (F := G - 3) (g := G - 4) (cell 3 (by omega)) hSI ?_ (by omega) (by omega)
                exact app_ot (F := G - 4) (cell 4 (by omega)) hK hK (by omega) (by omega)
              · exact app_ot (F := G - 2) (cell 5 (by omega)) hK hv' (by omega) (by omega)
            · show ORed _ (consO (boolT true).toO (bl (decB bs')).toO)
              exact ORed.consO hred'
          | true =>
            cases bs' with
            | nil =>
              refine ⟨.K, ?_, .refl _⟩
              show otermAt (H ++ cs) G (if dropped [true] then 0 else c) = some .K
              rw [show dropped [true] = true from rfl, if_pos rfl]
              exact K_ot (slots_K hs) (F := G) (by omega)
            | cons b2 bs2 =>
              have hcl : bitCells c (true :: b2 :: bs2) (sk :: sks') =
                  [.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 2,
                   .app 0 sk.t] := by
                show (if b2 :: bs2 = [] then [] else _) = _
                rw [if_neg (List.cons_ne_nil _ _)]
              rw [hcl] at hcells
              have cell : ∀ i, i < 6 → (H ++ cs)[c + i]? =
                  [Cell.app 0 (c + 1), .app (c + 2) (c + 5), .app sk.s (c + 3), .app sk.c5 (c + 4), .app 0 2,
                   .app 0 sk.t][i]? := fun i hi => hcells i (by simp only [List.length_cons, List.length_nil]; omega)
              have htail := otermAt_append (cs := cs) htt
              have hd : decB (true :: b2 :: bs2) = false :: b2 :: bs2 := by
                show (if b2 :: bs2 = [] then [] else _) = _
                rw [if_neg (List.cons_ne_nil _ _)]
              refine ⟨.K ⬝ₒ (.S ⬝ₒ (.S ⬝ₒ .I ⬝ₒ (.K ⬝ₒ (.K ⬝ₒ .I))) ⬝ₒ (.K ⬝ₒ tt)), ?_, ?_⟩
              · show otermAt (H ++ cs) G (if dropped (true :: b2 :: bs2) then 0 else c) = _
                rw [show dropped (true :: b2 :: bs2) = false from rfl, if_neg (by decide)]
                refine app_ot (F := G) (g := G - 1) (cell 0 (by omega)) hK ?_ (by omega) (by omega)
                refine app_ot (F := G - 1) (f := G - 2) (g := G - 2) (cell 1 (by omega)) ?_ ?_ (by omega) (by omega)
                · refine app_ot (F := G - 2) (g := G - 3) (cell 2 (by omega)) hS ?_ (by omega) (by omega)
                  refine app_ot (F := G - 3) (g := G - 4) (cell 3 (by omega)) hSI ?_ (by omega) (by omega)
                  exact app_ot (F := G - 4) (cell 4 (by omega)) hK (slot2_ot hs (F := 2) (Nat.le_refl _)) (by omega) (by omega)
                · exact app_ot (F := G - 2) (cell 5 (by omega)) hK htail (by omega) (by omega)
              · rw [hd]
                show ORed _ (consO (boolT false).toO (bl (b2 :: bs2)).toO)
                exact ORed.consO htt'

/-- **The output read back**, case by case, from the subject's cells: it
    reduces to the encoded outcome. -/
theorem out_otI {H cs : List Cell} (hs : slotsOK H = true) :
    ∀ (n p : Nat) {s : Nn} {csk : Option CellSk} {ask : Option AtomSk} {sks : List ConsSk} {root F : Nat}
      {N : OTerm}, readSubjI H n p = some (s, csk, ask, sks) → outCells H.length s csk ask sks = some (cs, root) →
      otermAt H F p = some N → F ≤ H.length + 1 →
      ∃ v, otermAt (H ++ cs) ((H ++ cs).length + 1) root = some v ∧ ORed v (encO (decSpec s)).toO
  | 0, _, _, _, _, _, _, _, _, hr, _, _, _ => nomatch hr
  | n + 1, p, s, csk, ask, sks, root, F, N, hr, hout, hN, hF => by
    have hs' := slotsOK_append (cs := cs) hs
    have hcell : ∀ i, i < cs.length → (H ++ cs)[H.length + i]? = cs[i]? := fun i _ => at_written rfl
    have hlen : (H ++ cs).length = H.length + cs.length := List.length_append ..
    unfold readSubjI at hr
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at hr
      dsimp only at hr
      cases hb : readBitsI H H.length sk.b with
      | none => rw [hb] at hr; cases hr
      | some q =>
        obtain ⟨bs, sks'⟩ := q
        rw [hb] at hr
        dsimp only at hr
        split at hr
        · cases hr
          unfold outCells at hout
          cases hout
          refine ⟨errO, ?_, .refl _⟩
          rw [hlen, errCells_length]
          exact err_ot hs' (hcell 0 (by rw [errCells_length]; omega)) (hcell 1 (by rw [errCells_length]; omega))
            (hcell 2 (by rw [errCells_length]; omega)) (by omega)
        · cases hr
    | none =>
      rw [ha] at hr
      dsimp only at hr
      cases hc : readCellI H p with
      | none =>
        rw [hc] at hr
        dsimp only at hr
        cases hi : readInd H p with
        | none => rw [hi] at hr; cases hr
        | some R =>
          rw [hi] at hr
          dsimp only at hr
          obtain ⟨f, tr, rfl, hR, _⟩ := readInd_peel hi hN
          exact out_otI hs n R hr hout hR (by omega)
      | some csk' =>
        rw [hc] at hr
        dsimp only at hr
        obtain ⟨f, th, tt, tk, rfl, rfl, hth, hkt, hred, ⟨g, htt⟩, ha1, ha2, hs3, hsi⟩ := readCellI_peel hc hN
        cases ha2' : headAtom H H.length csk'.h with
        | some x =>
          obtain ⟨a, ask'⟩ := x
          rw [ha2'] at hr
          dsimp only at hr
          cases hb : readBitsI H H.length ask'.b with
          | none => rw [hb] at hr; cases hr
          | some q =>
            obtain ⟨bs, sks'⟩ := q
            rw [hb] at hr
            dsimp only at hr
            split at hr
            · rename_i hcan
              cases ht : readNnI H H.length csk'.t with
              | none => rw [ht] at hr; cases hr
              | some r0 =>
                rw [ht] at hr
                cases hr
                obtain ⟨hra, G0, v0, hG0, hv0, _⟩ := headAtom_peel ha2' hth
                obtain ⟨f', tb, rfl, rfl, htb, hb1, hb2, hb3, hbsi⟩ := readAtom_peel hra hv0
                have htr := readNnI_ot ht htt
                cases bs with
                | nil =>
                  unfold outCells at hout
                  cases hout
                  refine ⟨errO, ?_, .refl _⟩
                  have hl15 : (cellCells H.length csk' ++ atomCells (H.length + 7) ask' 0 ++ errCells (H.length + 12)).length = 15 := by
                    simp only [List.length_append, cellCells_length, atomCells_length, errCells_length]
                  rw [hlen, hl15]
                  exact err_ot hs' (hcell 12 (by rw [hl15]; omega)) (hcell 13 (by rw [hl15]; omega))
                    (hcell 14 (by rw [hl15]; omega)) (by omega)
                | cons b bs =>
                  unfold outCells at hout
                  cases hout
                  rw [hlen]
                  generalize hL : (cellCells H.length csk' ++ atomCells (H.length + 7) ask' (bitsRoot (H.length + 12) (b :: bs)) ++
                      bitCells (H.length + 12) (b :: bs) sks).length = L at hcell hlen
                  have hL12 : 12 + (bitCells (H.length + 12) (b :: bs) sks).length = L := by
                    rw [← hL]; simp only [List.length_append, cellCells_length, atomCells_length]
                  obtain ⟨vb, hvb, hredb⟩ := bitsI_ot (G := H.length + L + 1 - 12) hs' H.length (b :: bs) sks (H.length + 12)
                    ask'.b f' tb hcan (List.cons_ne_nil _ _) hb htb
                    (fun i hi => by
                      rw [show H.length + 12 + i = H.length + (12 + i) by omega, hcell (12 + i) (by omega),
                        getElem?_after12 (by simp only [List.length_append, cellCells_length, atomCells_length])])
                    (by omega)
                  have hatom := atom_ot (G := H.length + L + 1 - 7) hs' ask' (H.length + 7) (bitsRoot (H.length + 12) (b :: bs))
                    (fun i hi => by
                      rw [show H.length + 7 + i = H.length + (7 + i) by omega, hcell (7 + i) (by omega),
                        List.getElem?_append_left (by simp only [List.length_append, cellCells_length, atomCells_length]; omega),
                        List.getElem?_append_right (by rw [cellCells_length]; omega),
                        cellCells_length, show 7 + i - 7 = i by omega])
                    hb1 hb2 hb3 hbsi hvb (by omega) (by omega)
                  have hcellT := cell_otG (G := H.length + L + 1) hs' csk' H.length
                    (fun i hi => by
                      rw [hcell i (by omega),
                        List.getElem?_append_left (by simp only [List.length_append, cellCells_length, atomCells_length]; omega),
                        List.getElem?_append_left (by rw [cellCells_length]; omega)])
                    ha1 ha2 hs3 hsi hkt hatom (by omega) (by omega) (by omega)
                  refine ⟨_, hcellT, ?_⟩
                  show ORed _ (cellO (atomO (bl (decB (b :: bs))).toO) (encNn r0).toO)
                  exact ORed.cellG (ORed.atomO hredb) (hred.trans (.appR _ htr))
            · cases hr
        | none =>
          rw [ha2'] at hr
          dsimp only at hr
          cases hh : readNnI H H.length csk'.h with
          | none => rw [hh] at hr; cases hr
          | some hh' =>
            cases ht : readNnI H H.length csk'.t with
            | none => rw [hh, ht] at hr; cases hr
            | some tt' =>
              rw [hh, ht] at hr
              cases hr
              cases hh' with
              | atom b =>
                exfalso
                obtain ⟨x, hx⟩ := headAtom_of_atom hh (Nat.le_refl _)
                rw [ha2'] at hx; cases hx
              | cell h1 t1 =>
                unfold outCells at hout
                cases hout
                refine ⟨errO, ?_, .refl _⟩
                have hl15 : (cellCells H.length csk' ++ List.replicate 5 (Cell.app 0 0) ++ errCells (H.length + 12)).length = 15 := by
                  simp only [List.length_append, cellCells_length, List.length_replicate, errCells_length]
                rw [hlen, hl15]
                exact err_ot hs' (hcell 12 (by rw [hl15]; omega)) (hcell 13 (by rw [hl15]; omega))
                  (hcell 14 (by rw [hl15]; omega)) (by omega)

-- ---------------------------------------------------------------------------
-- The row
-- ---------------------------------------------------------------------------

/-- **The jet's row, reading through `K`-thunks**: `decRow` with the subject
    read by `readSubjI`. -/
def decRowI (M : List Cell) (J : Nat) (r : Row) : Option Row :=
  let H := M.take r.ctr
  match H[r.hd]? with
  | some (.atom j') =>
    if j' = J ∧ slotsOK H = true then
      match popN H 1 r.stk with
      | some ([p], rest) =>
        match readSubjI H H.length p with
        | some (s, csk, ask, sks) =>
          if headFits s then
            match outCells r.ctr s csk ask sks with
            | some (cells, root) =>
              if wrs M r.ctr cells then some ⟨root, rest, r.ctr + cells.length⟩ else none
            | none => none
          else none
        | none => none
      | _ => none
    else none
  | _ => none

theorem decRowI_unfold {M : List Cell} {J : Nat} {r r' : Row} (h : decRowI M J r = some r') :
    let H := M.take r.ctr
    ∃ p rest s csk ask sks cells root, H[r.hd]? = some (.atom J) ∧ slotsOK H = true ∧
      popN H 1 r.stk = some ([p], rest) ∧ readSubjI H H.length p = some (s, csk, ask, sks) ∧ headFits s = true ∧
      outCells r.ctr s csk ask sks = some (cells, root) ∧ wrs M r.ctr cells = true ∧
      r' = ⟨root, rest, r.ctr + cells.length⟩ := by
  unfold decRowI at h
  dsimp only at h ⊢
  generalize M.take r.ctr = H at h ⊢
  cases hhd : H[r.hd]? with
  | none => rw [hhd] at h; cases h
  | some cell =>
    rw [hhd] at h
    cases cell with
    | atom j' =>
      dsimp only at h
      by_cases hcond : j' = J ∧ slotsOK H = true
      · rw [if_pos hcond] at h
        obtain ⟨rfl, hs⟩ := hcond
        cases hpop : popN H 1 r.stk with
        | none => rw [hpop] at h; cases h
        | some q =>
          obtain ⟨qs, rest⟩ := q
          rw [hpop] at h
          match qs, h with
          | [p], h =>
            dsimp only at h
            cases hrd : readSubjI H H.length p with
            | none => rw [hrd] at h; cases h
            | some q4 =>
              obtain ⟨s, csk, ask, sks⟩ := q4
              rw [hrd] at h
              dsimp only at h
              by_cases hfit : headFits s = true
              · rw [if_pos hfit] at h
                cases hout : outCells r.ctr s csk ask sks with
                | none => rw [hout] at h; cases h
                | some q2 =>
                  obtain ⟨cells, root⟩ := q2
                  rw [hout] at h
                  dsimp only at h
                  cases hw : wrs M r.ctr cells with
                  | false => rw [hw] at h; cases h
                  | true =>
                    rw [hw] at h
                    cases h
                    exact ⟨p, rest, s, csk, ask, sks, cells, root, rfl, hs, rfl, hrd, hfit, hout, hw, rfl⟩
              · rw [if_neg hfit] at h; cases h
          | [], h => cases h
          | _ :: _ :: _, h => cases h
      · rw [if_neg hcond] at h; cases h
    | _ => cases h

/-- **A jet row, read back**: the state is `J ⬝ u ⬝ R` with `u ↠ encNn s`
    for a subject `s` in the domain, and the next state `v ⬝ R` with
    `v ↠ encO (decSpec s)`. -/
theorem decRowI_step {M : List Cell} {J : Nat} {r r' : Row} (h : decRowI M J r = some r') (hc : r.ctr ≤ M.length)
    {t : OTerm} (hdec : odecode (st M r) = some t) :
    r'.ctr ≤ M.length ∧ ∃ (s : Dom) (u v : OTerm) (R : List OTerm), t = _root_.appL (.var J) (u :: R) ∧
      ORed u (encNn s.1).toO ∧ odecode (st M r') = some (_root_.appL v R) ∧ ORed v (encO (decSpec s.1)).toO := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, hhd, hs, hpop, hrd, hfit, hout, hw, rfl⟩ := decRowI_unfold h
  generalize hH : M.take r.ctr = H at hhd hs hpop hrd hout
  have hHl : H.length = r.ctr := by rw [← hH, List.length_take]; omega
  have htake := take_of_wrs hw
  rw [hH] at htake
  have hlen' : (M.take (r.ctr + cells.length)).length = r.ctr + cells.length := by
    rw [htake, List.length_append, hHl]
  refine ⟨?_, ?_⟩
  · show r.ctr + cells.length ≤ M.length
    rw [List.length_take] at hlen'
    omega
  · obtain ⟨hdt, args, h1, h2, rfl⟩ := odecode_eq hdec
    replace h1 : otermAt H (H.length + 1) r.hd = some hdt := by rw [← hH]; exact h1
    replace h2 : ostackAt H (H.length + 1) r.stk = some args := by rw [← hH]; exact h2
    have hj : hdt = .var J := by
      unfold otermAt at h1; rw [hhd] at h1; cases h1; rfl
    obtain ⟨Ns, R, G, hG, hargs, hNl, hpl, hok, hR⟩ := popN_ospec 1 hpop h2
    match Ns, hNl, hok with
    | [N], _, ⟨hN, _⟩ =>
      have hNe := readSubjI_ot hrd hN
      rw [← hHl] at hout
      obtain ⟨v, hroot, hv⟩ := out_otI hs H.length p hrd hout hN (Nat.le_refl _)
      refine ⟨⟨s, readSubjI_wf hrd, hfit⟩, N, v, R, by rw [hargs, hj]; rfl, hNe, ?_, hv⟩
      show odecode ⟨M.take (r.ctr + cells.length), root, rest⟩ = _
      rw [htake]
      apply odecode_of hroot
      exact ostackAt_grow hR (by rw [List.length_append]; omega)

/-- A jet row moves the counter forward and stays within the memory. -/
theorem decRowI_ctr_len {M : List Cell} {J : Nat} {r r' : Row} (h : decRowI M J r = some r')
    (hc : r.ctr ≤ M.length) : r.ctr ≤ r'.ctr ∧ r'.ctr ≤ M.length := by
  obtain ⟨_, _, _, _, _, _, cells, _, _, _, _, _, _, _, hw, rfl⟩ := decRowI_unfold h
  have ht := take_of_wrs hw
  have hl := congrArg List.length ht
  rw [List.length_take, List.length_append, List.length_take] at hl
  exact ⟨Nat.le_add_right _ _, by show r.ctr + cells.length ≤ M.length; omega⟩

-- ---------------------------------------------------------------------------
-- The reader extends `decRow`'s
-- ---------------------------------------------------------------------------

theorem readInd_none_of_K {H : List Cell} {p f x : Nat} (hp : H[p]? = some (.app f x)) (hf : isK H f = true) :
    readInd H p = none := by
  unfold readInd; rw [hp]; dsimp only; rw [isK_eq hf]

theorem readInd_none_of_S {H : List Cell} {p f x : Nat} (hp : H[p]? = some (.app f x)) (hf : isSKK H f = true) :
    readInd H p = none := by
  unfold readInd; rw [hp]; dsimp only
  unfold isSKK at hf
  split at hf
  · rename_i s kk hs
    rw [hs]; dsimp only
    have : isK H s = false := by
      simp only [Bool.and_eq_true] at hf
      unfold isK; rw [isS_eq hf.1]; rfl
    rw [if_neg (by rw [this]; decide)]
  · cases hf

theorem readBits_readBitsI {H : List Cell} : ∀ {n p : Nat} {x : List Bool × List ConsSk},
    readBits H n p = some x → readBitsI H n p = some x
  | 0, _, _, h => nomatch h
  | n + 1, p, x, h => by
    unfold readBits at h; unfold readBitsI
    split at h
    · rename_i hk; rw [if_pos hk]; exact h
    · rename_i hk
      rw [if_neg hk]
      cases hc : readCons H p with
      | none => rw [hc] at h; cases h
      | some q =>
        rw [hc] at h; dsimp only at h ⊢
        cases hr : readBits H n q.2.t with
        | none => rw [hr] at h; cases h
        | some q' => rw [hr] at h; rw [readBits_readBitsI hr]; exact h

theorem readCell_readCellI {H : List Cell} {p : Nat} {sk : CellSk} (h : readCell H p = some sk) :
    readCellI H p = some sk := by
  unfold readCell at h
  unfold readCellI
  split at h <;> try cases h
  rename_i k0 y1 hp
  rw [hp]; dsimp only
  split at h <;> try cases h
  rename_i a1 y2 h1
  rw [h1]; dsimp only
  split at h <;> try cases h
  rename_i a2 y3 h2
  rw [h2]; dsimp only
  split at h <;> try cases h
  rename_i p1 kt h3
  rw [h3]; dsimp only
  split at h <;> try cases h
  rename_i s3 p2 k6 t h4 h5
  rw [h4]; dsimp only
  split at h <;> try cases h
  rename_i si kh h6
  rw [h6]; dsimp only
  split at h <;> try cases h
  rename_i k5 hh h7
  rw [h7]; dsimp only
  split at h
  · rename_i hall
    cases h
    simp only [Bool.and_eq_true] at hall
    obtain ⟨⟨⟨⟨⟨⟨hk0, ha1⟩, ha2⟩, hs3⟩, hsi⟩, hk5⟩, hk6⟩ := hall
    rw [if_pos (by simp only [hk0, ha1, ha2, hs3, hsi, hk5, Bool.and_self])]
    have : ktAt H kt = some t := by unfold ktAt; rw [h5]; dsimp only; rw [if_pos hk6]
    rw [this]
  · cases h

theorem readCell_ind {H : List Cell} {p : Nat} {sk : CellSk} (h : readCell H p = some sk) : readInd H p = none := by
  unfold readCell at h
  split at h <;> try cases h
  rename_i k0 y1 hp
  repeat (split at h <;> try cases h)
  rename_i hall
  simp only [Bool.and_eq_true] at hall
  exact readInd_none_of_K hp hall.1.1.1.1.1.1

theorem readAtom_ind {H : List Cell} {p : Nat} {sk : AtomSk} (h : readAtom H p = some sk) : readInd H p = none := by
  unfold readAtom at h
  split at h <;> try cases h
  rename_i a1 x1 hp
  repeat (split at h <;> try cases h)
  rename_i hall
  simp only [Bool.and_eq_true] at hall
  exact readInd_none_of_S hp hall.1.1.1.1

theorem readNn_readNnI {H : List Cell} : ∀ {n p : Nat} {s : Nn}, readNn H n p = some s → readNnI H n p = some s
  | 0, _, _, h => nomatch h
  | n + 1, p, s, h => by
    unfold readNn at h; unfold readNnI
    cases ha : readAtom H p with
    | some sk =>
      rw [ha] at h; dsimp only at h ⊢
      cases hb : readBits H (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q => rw [hb] at h; rw [readBits_readBitsI hb]; exact h
    | none =>
      rw [ha] at h; dsimp only at h ⊢
      cases hc : readCell H p with
      | none => rw [hc] at h; cases h
      | some sk =>
        rw [hc] at h; dsimp only at h
        rw [readCell_readCellI hc]; dsimp only
        cases hh : readNn H n sk.h with
        | none => rw [hh] at h; cases h
        | some sh =>
          cases ht : readNn H n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some st => rw [hh, ht] at h; rw [readNn_readNnI hh, readNn_readNnI ht]; exact h

/-- **The reader extends `readSubj`**: a subject laid out without thunks is
    read the same. -/
theorem readSubj_readSubjI {H : List Cell} {p : Nat} {x : Nn × Option CellSk × Option AtomSk × List ConsSk}
    (hn : 1 ≤ H.length) (h : readSubj H p = some x) : ∀ n, 1 ≤ n → readSubjI H n p = some x := by
  intro n hn'
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨L, hL⟩ : ∃ L, H.length = L + 1 := ⟨H.length - 1, by omega⟩
  unfold readSubj at h; unfold readSubjI
  cases ha : readAtom H p with
  | some sk =>
    rw [ha] at h; dsimp only at h ⊢
    cases hb : readBits H H.length sk.b with
    | none => rw [hb] at h; cases h
    | some q => rw [hb] at h; rw [readBits_readBitsI hb]; exact h
  | none =>
    rw [ha] at h; dsimp only at h ⊢
    cases hc : readCell H p with
    | none => rw [hc] at h; cases h
    | some csk =>
      rw [hc] at h; dsimp only at h
      rw [readCell_readCellI hc]; dsimp only
      cases ha2 : readAtom H csk.h with
      | some ask =>
        rw [ha2] at h; dsimp only at h
        have hhd : headAtom H H.length csk.h = some (csk.h, ask) := by
          rw [hL]; unfold headAtom; rw [ha2]
        rw [hhd]; dsimp only
        cases hb : readBits H H.length ask.b with
        | none => rw [hb] at h; cases h
        | some q =>
          rw [hb] at h; rw [readBits_readBitsI hb]; dsimp only at h ⊢
          split at h
          · rename_i hcan
            rw [if_pos hcan]
            cases ht : readNn H H.length csk.t with
            | none => rw [ht] at h; cases h
            | some r => rw [ht] at h; rw [readNn_readNnI ht]; exact h
          · cases h
      | none =>
        rw [ha2] at h; dsimp only at h
        cases hh : readNn H H.length csk.h with
        | none => rw [hh] at h; cases h
        | some hh' =>
          cases ht : readNn H H.length csk.t with
          | none => rw [hh, ht] at h; cases h
          | some tt' =>
            rw [hh, ht] at h
            -- the head is a cell (`readAtom` failed), so not a thunk
            have hci : readInd H csk.h = none := by
              rw [hL] at hh
              unfold readNn at hh
              rw [ha2] at hh; dsimp only at hh
              cases hc2 : readCell H csk.h with
              | none => rw [hc2] at hh; cases hh
              | some _ => exact readCell_ind hc2
            have hhd : headAtom H H.length csk.h = none := by
              rw [hL]; unfold headAtom; rw [ha2]; dsimp only; rw [hci]
            rw [hhd]; dsimp only
            rw [readNn_readNnI hh, readNn_readNnI ht]; exact h

/-- **`decRowI` extends `decRow`**: on a subject laid out without thunks the
    rows agree. -/
theorem decRow_decRowI {M : List Cell} {J : Nat} {r r' : Row} (h : decRow M J r = some r') :
    decRowI M J r = some r' := by
  obtain ⟨p, rest, s, csk, ask, sks, cells, root, hhd, hs, hpop, hrd, hfit, hout, hw, rfl⟩ := decRow_unfold h
  have hn : 1 ≤ (M.take r.ctr).length := by have := slots_len hs; omega
  have hrd' := readSubj_readSubjI hn hrd _ hn
  unfold decRowI
  dsimp only
  rw [hhd]; dsimp only
  rw [if_pos ⟨rfl, hs⟩, hpop]; dsimp only
  rw [hrd']; dsimp only
  rw [if_pos hfit, hout]; dsimp only
  rw [if_pos hw]

-- ---------------------------------------------------------------------------
-- Head reduction with the jet, up to `K`-contraction
-- ---------------------------------------------------------------------------

/-- **Head reduction with the `dec` jet through thunks**: SKI's head rules,
    and the jet on an argument that reduces to an encoded subject, to a
    term that reduces to the encoded outcome. -/
inductive JStepI (J : Nat) : OTerm → OTerm → Prop
  | head {t u : OTerm} (h : OStep t u) : JStepI J t u
  | jet (s : Dom) {u v : OTerm} (hu : ORed u (encNn s.1).toO) (hv : ORed v (encO (decSpec s.1)).toO)
      (R : List OTerm) : JStepI J (_root_.appL (.var J) (u :: R)) (_root_.appL v R)

inductive JStepsI (J : Nat) : OTerm → OTerm → Prop
  | refl (t : OTerm) : JStepsI J t t
  | step {t t' u : OTerm} (h : JStepI J t t') (hs : JStepsI J t' u) : JStepsI J t u

theorem JStepsI.trans {J : Nat} {t u v : OTerm} (h₁ : JStepsI J t u) (h₂ : JStepsI J u v) : JStepsI J t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step h _ ih => exact .step h (ih h₂)

/-- **A jet row reads back as one step of `JStepI`.** -/
theorem decRowI_jstep {M : List Cell} {J : Nat} {r r' : Row} (h : decRowI M J r = some r') (hc : r.ctr ≤ M.length)
    {t : OTerm} (hdec : odecode (st M r) = some t) :
    r'.ctr ≤ M.length ∧ ∃ t', odecode (st M r') = some t' ∧ JStepI J t t' := by
  obtain ⟨h1, s, u, v, R, rfl, hu, hd, hv⟩ := decRowI_step h hc hdec
  exact ⟨h1, _, hd, .jet s hu hv R⟩

theorem appT_wsteps (E E' : Term) (h : WSteps E E') : ∀ (as : List Term), WSteps (appT E as) (appT E' as)
  | [] => h
  | a :: as => appT_wsteps (E ⬝ a) (E' ⬝ a) (WSteps.left a h) as

/-- **Closing a run to `K`**: with any implementation of the contract in the
    jet's place, a run of `JStepI` from `t` to `K` makes `t` reduce to `K`.
    The jet's step closes to two reductions to a common term (the closed
    outcome over the rest), and a term reduces to `K` exactly when any of
    its reducts does (`wsteps_K_iff`, Church–Rosser). -/
theorem JStepsI.close_K {J : Nat} (σ : Nat → Term) (hσ : DataJet.Implements decContract (σ J))
    {t : OTerm} (h : JStepsI J t .K) : WSteps (t.close σ) Term.K := by
  generalize hK : OTerm.K = k at h
  induction h with
  | refl _ => subst hK; exact .refl _
  | step hs _ ih =>
    have ih := ih hK
    cases hs with
    | head hst => exact (WSteps.single (OStep.close σ hst).weak).trans ih
    | @jet s u v hu hv R =>
      rw [_root_.close_appL] at ih
      have e : (_root_.appL (.var J) (u :: R)).close σ = appT (σ J ⬝ u.close σ) (R.map (OTerm.close σ)) := by
        rw [_root_.close_appL]; rfl
      rw [e]
      have hP : WSteps (σ J ⬝ u.close σ) (encO (decSpec s.1)) := by
        refine (WSteps.right _ (hu.close σ)).trans ?_
        rw [close_toO]
        exact hσ s
      have hv' := hv.close σ
      rw [close_toO] at hv'
      have e1 := (wsteps_K_iff (appT_wsteps _ _ hv' (R.map (OTerm.close σ)))).1 ih
      exact (wsteps_K_iff (appT_wsteps _ _ hP (R.map (OTerm.close σ)))).2 e1

end DecJet
