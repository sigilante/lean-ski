import Ski.Circuit.CompDTraceRead

/-!
# The honest DEC rows of a jet call

`decair.rs`'s `Reader` in Lean, along `Ski/DecInd.lean`'s readers through
`K`-thunks: a call at key `key` (the jet row's counter) on the subject at
`p` has one row per cell pattern of its subject (`DecT.callRows`): an
indirection row per thunk at its root (`DecJet.readSubjI`), the subject's
wrapper, then, for a cell, its head (role `1`) and tail (role `2`) nouns
(`nounRows`, along `DecJet.readNnI`: an indirection row per thunk, a
wrapper, its tail slot bare or behind a thunk, `IKT`), and for an atom its
bits' chain (`bitsRows`, along `DecJet.readBitsI`: a `Cons` per bit, the
head's in mode `0` under the borrow, the others in mode `1`, an indirection
row per thunk on the chain; a last `Cons` says so, and the chain ends at a
nil, marked `TERM` after a last `Cons`, unmarked at level `0` for an empty
atom).  The subject's row carries the head's verdict (`headV`): a crash,
or the rewritten bits' cell count.

**`DecT.callRows_ok`**: when the jet's reader succeeds (`readSubjI`, the
head fitting `W`), every row of the call is well formed and reads memory
cells.
-/

namespace Circuit

open B Air

namespace DecT

def nilRow (key p : Nat) (m : Bool) (lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) : DR :=
  ⟨key, 4, 0, m, p, lvl, bw, wc, false, false, false, false, false, term⟩

def consRow (key p : Nat) (m : Bool) (lvl : Nat) (bw : Bool) (wc : Nat) (b last : Bool) : DR :=
  ⟨key, 3, 0, m, p, lvl, bw, wc, b, last, false, false, false, false⟩

/-- An indirection row: a need of role `ro` (`ib = false`), or a chain's
    step in mode `m` at level `lvl` (`ib = true`). -/
def indRow (key p ro : Nat) (ib m : Bool) (lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) : DR :=
  ⟨key, 5, ro, m, p, lvl, bw, wc, false, false, false, ib, false, term⟩

def atomRow (key p ro : Nat) : DR := ⟨key, 2, ro, false, p, 0, false, 0, false, false, false, false, false, false⟩

def cellRow (key p ro : Nat) (err : Bool) (wc : Nat) (ikt : Bool) : DR :=
  ⟨key, 1, ro, false, p, 0, false, wc, false, false, err, false, ikt, false⟩

/-- Whether the bit list at `t` is empty, through thunks. -/
def restNil (H : List Cell) (n t : Nat) : Bool :=
  match DecJet.readBitsI H n t with
  | some (bs, _) => bs.isEmpty
  | none => false

/-- A bit's chain from `p` at level `lvl`, borrow `bw`, `wc` cells written,
    after a list's last `Cons` when `term`. -/
def bitsRows (A : List Cell) (key : Nat) (m : Bool) : Nat → Nat → Nat → Bool → Nat → Bool → List DR
  | 0, _, _, _, _, _ => []
  | n + 1, p, lvl, bw, wc, term =>
    if DecJet.isK (A.take key) p then [nilRow key p m lvl bw wc term]
    else match DecJet.readCons (A.take key) p with
      | some (b, sk) =>
        consRow key p m lvl bw wc b (restNil (A.take key) n sk.t) ::
          bitsRows A key m n sk.t (lvl + 1) (bw && !b)
            (wc + 6 * (if bw && !(b && restNil (A.take key) n sk.t) then 1 else 0)) (restNil (A.take key) n sk.t)
      | none =>
        match DecJet.readInd (A.take key) p with
        | some R => indRow key p 0 true m lvl bw wc term :: bitsRows A key m n R lvl bw wc term
        | none => []

/-- A noun at `p` with the role `ro`; its bits' chains read within the
    whole memory's fuel. -/
def nounRows (A : List Cell) (key : Nat) : Nat → Nat → Nat → List DR
  | 0, _, _ => []
  | n + 1, p, ro =>
    match DecJet.readAtom (A.take key) p with
    | some sk => atomRow key p ro :: bitsRows A key (ro != 1) (A.take key).length sk.b 0 (ro == 1) 0 false
    | none =>
      match DecJet.readCellI (A.take key) p with
      | some sk =>
        cellRow key p ro false 0 (iktOf (A.take key) sk.kt) :: (nounRows A key n sk.h 2 ++ nounRows A key n sk.t 2)
      | none =>
        match DecJet.readInd (A.take key) p with
        | some R => indRow key p ro false false 0 false 0 false :: nounRows A key n R ro
        | none => []

/-- The head's verdict: a crash, or the rewritten bits' cell count. -/
def headV (A : List Cell) (key h : Nat) : Bool × Nat :=
  match DecJet.headAtom (A.take key) (A.take key).length h with
  | some (_, ask) =>
    match DecJet.readBitsI (A.take key) (A.take key).length ask.b with
    | some (b :: bs, sks) => (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length)
    | _ => (true, 0)
  | none => (true, 0)

/-- The subject's rows: its root's thunks, then its wrapper and halves. -/
def subjRows (A : List Cell) (key : Nat) : Nat → Nat → List DR
  | 0, _ => []
  | n + 1, p =>
    match DecJet.readAtom (A.take key) p with
    | some sk => atomRow key p 0 :: bitsRows A key true (A.take key).length sk.b 0 false 0 false
    | none =>
      match DecJet.readCellI (A.take key) p with
      | some csk =>
        cellRow key p 0 (headV A key csk.h).1 (headV A key csk.h).2 (iktOf (A.take key) csk.kt) ::
          (nounRows A key (A.take key).length csk.h 1 ++ nounRows A key (A.take key).length csk.t 2)
      | none =>
        match DecJet.readInd (A.take key) p with
        | some R => indRow key p 0 false false 0 false 0 false :: subjRows A key n R
        | none => []

/-- **The rows of a call** at key `key` on the subject at `p`. -/
def callRows (A : List Cell) (key p : Nat) : List DR := subjRows A key (A.take key).length p

-- ---------------------------------------------------------------------------
-- Every row is well formed and reads memory cells
-- ---------------------------------------------------------------------------

/-- A row's facts: well formed, reading memory cells. -/
def OK (A : List Cell) (d : DR) : Prop := RowOK A d ∧ ReadsOK A d

theorem mkOK {A : List Cell} {d : DR} (hk : 1 ≤ d.kind ∧ d.kind ≤ 5) (hro : d.ro ≤ 2)
    (hc : d.kind = 3 → d.last = true → d.bit = true) (hl : d.kind = 3 → d.m = false → d.lvl < 32)
    (hct : d.kind = 3 → d.term = false) (hnl : d.kind = 4 → d.term = false → d.lvl = 0)
    (hkey : d.key < 2 ^ 24) (hR : ReadsOK A d) : OK A d :=
  ⟨⟨hk, hro, hc, hl, hct, hnl, hkey, fun j hj => (hR j hj).1⟩, hR⟩

/-- `restNil` on a read list. -/
theorem restNil_eq {H : List Cell} {n t : Nat} {bs : List Bool} {sks : List DecJet.ConsSk}
    (h : DecJet.readBitsI H n t = some (bs, sks)) : restNil H n t = bs.isEmpty := by
  unfold restNil; rw [h]

/-- One step of a read list through thunks: a nil, a `Cons`, or a thunk. -/
theorem readBitsI_cases {H : List Cell} {n p : Nat} {bs : List Bool} {sks : List DecJet.ConsSk}
    (h : DecJet.readBitsI H (n + 1) p = some (bs, sks)) :
    (DecJet.isK H p = true ∧ bs = []) ∨
    (∃ b sk bs' sks', DecJet.isK H p = false ∧ DecJet.readCons H p = some (b, sk) ∧
      DecJet.readBitsI H n sk.t = some (bs', sks') ∧ bs = b :: bs' ∧ sks = sk :: sks') ∨
    (∃ R, DecJet.isK H p = false ∧ DecJet.readCons H p = none ∧ DecJet.readInd H p = some R ∧
      DecJet.readBitsI H n R = some (bs, sks)) := by
  unfold DecJet.readBitsI at h
  by_cases hK : DecJet.isK H p = true
  · rw [if_pos hK] at h; cases h; exact .inl ⟨hK, rfl⟩
  · have hK' : DecJet.isK H p = false := by simpa using hK
    rw [if_neg hK] at h
    cases hc : DecJet.readCons H p with
    | some q =>
      obtain ⟨b, sk⟩ := q
      rw [hc] at h
      dsimp only at h
      cases hr : DecJet.readBitsI H n sk.t with
      | none => rw [hr] at h; cases h
      | some q' =>
        obtain ⟨bs', sks'⟩ := q'
        rw [hr] at h
        cases h
        exact .inr (.inl ⟨b, sk, bs', sks', hK', rfl, hr, rfl, rfl⟩)
    | none =>
      rw [hc] at h
      dsimp only at h
      cases hi : DecJet.readInd H p with
      | none => rw [hi] at h; cases h
      | some R => rw [hi] at h; exact .inr (.inr ⟨R, hK', rfl, rfl, h⟩)

/-- The rows of a chain, one step: a nil, a `Cons`, or a thunk. -/
theorem bitsRows_K {A : List Cell} {key n p lvl wc : Nat} {m bw term : Bool}
    (hK : DecJet.isK (A.take key) p = true) :
    bitsRows A key m (n + 1) p lvl bw wc term = [nilRow key p m lvl bw wc term] := by
  simp only [bitsRows, hK, if_true]

theorem bitsRows_cons {A : List Cell} {key n p lvl wc : Nat} {m bw term b : Bool} {sk : DecJet.ConsSk}
    (hK : DecJet.isK (A.take key) p = false) (hc : DecJet.readCons (A.take key) p = some (b, sk)) :
    bitsRows A key m (n + 1) p lvl bw wc term =
      consRow key p m lvl bw wc b (restNil (A.take key) n sk.t) ::
        bitsRows A key m n sk.t (lvl + 1) (bw && !b)
          (wc + 6 * (if bw && !(b && restNil (A.take key) n sk.t) then 1 else 0)) (restNil (A.take key) n sk.t) := by
  simp only [bitsRows, hK, hc]; rfl

theorem bitsRows_ind {A : List Cell} {key n p lvl wc R : Nat} {m bw term : Bool}
    (hK : DecJet.isK (A.take key) p = false) (hc : DecJet.readCons (A.take key) p = none)
    (hi : DecJet.readInd (A.take key) p = some R) :
    bitsRows A key m (n + 1) p lvl bw wc term = indRow key p 0 true m lvl bw wc term :: bitsRows A key m n R lvl bw wc term := by
  simp only [bitsRows, hK, hc, hi]; rfl

section
variable {A : List Cell} {key : Nat} (hkey : key < 2 ^ 24)
include hkey

theorem bitsRows_ok {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) (term : Bool) {bs : List Bool}
    {sks : List DecJet.ConsSk},
    DecJet.readBitsI (A.take key) n p = some (bs, sks) → DecJet.canonB bs = true →
    (m = false → lvl + bs.length ≤ 32) → (term = false → bs = [] → lvl = 0) →
    ∀ d ∈ bitsRows A key m n p lvl bw wc term, OK A d
  | 0, _, _, _, _, _, _, _, h, _, _, _ => by cases h
  | n + 1, p, lvl, bw, wc, term, bs, sks, h, hc, hl, hz => by
    intro d hd
    rcases readBitsI_cases h with ⟨hK, rfl⟩ | ⟨b, sk, bs', sks', hK, hr, hb, rfl, rfl⟩ | ⟨R, hK, hr, hi, hb⟩
    · rw [bitsRows_K hK, List.mem_singleton] at hd; subst hd
      exact mkOK (show 1 ≤ 4 ∧ 4 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun _ ht => hz ht rfl) hkey (nilReads (d := nilRow key p m lvl bw wc term) rfl hK)
    · rw [bitsRows_cons hK hr, restNil_eq hb] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · have hR := consReads (d := consRow key p m lvl bw wc b bs'.isEmpty) rfl hr rfl
        refine mkOK (show 1 ≤ 3 ∧ 3 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun _ hl' => ?_) (fun _ hm => ?_)
          (fun _ => rfl) (fun h => nomatch h) hkey hR.1
        · have : bs' = [] := List.isEmpty_iff.1 hl'
          subst this; exact hc
        · have := hl hm; simp only [List.length_cons] at this
          show lvl < 32; omega
      · exact bitsRows_ok n sk.t (lvl + 1) _ _ _ hb (DecJet.canonB_tail hc)
          (fun hm => by have := hl hm; simp only [List.length_cons] at this; omega)
          (fun ht he => by rw [he] at ht; cases ht) d hd
    · rw [bitsRows_ind hK hr hi] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 5 ∧ 5 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (indReads (d := indRow key p 0 true m lvl bw wc term) rfl hi).1
      · exact bitsRows_ok n R lvl bw wc term hb hc hl hz d hd

omit hkey in
/-- One step of a noun through thunks: an atom, a cell, or a thunk. -/
theorem readNnI_cases {H : List Cell} {n p : Nat} {s : DecJet.Nn} (h : DecJet.readNnI H (n + 1) p = some s) :
    (∃ sk bs sks, DecJet.readAtom H p = some sk ∧ DecJet.readBitsI H (n + 1) sk.b = some (bs, sks) ∧
      DecJet.canonB bs = true ∧ s = .atom bs) ∨
    (∃ sk hh tt, DecJet.readAtom H p = none ∧ DecJet.readCellI H p = some sk ∧ DecJet.readNnI H n sk.h = some hh ∧
      DecJet.readNnI H n sk.t = some tt ∧ s = .cell hh tt) ∨
    (∃ R, DecJet.readAtom H p = none ∧ DecJet.readCellI H p = none ∧ DecJet.readInd H p = some R ∧
      DecJet.readNnI H n R = some s) := by
  unfold DecJet.readNnI at h
  cases ha : DecJet.readAtom H p with
  | some sk =>
    rw [ha] at h; dsimp only at h
    cases hb : DecJet.readBitsI H (n + 1) sk.b with
    | none => rw [hb] at h; cases h
    | some q =>
      obtain ⟨bs, sks⟩ := q
      rw [hb] at h; dsimp only at h
      by_cases hc : DecJet.canonB bs = true
      · rw [if_pos hc] at h; cases h; exact .inl ⟨sk, bs, sks, rfl, hb, hc, rfl⟩
      · rw [if_neg hc] at h; cases h
  | none =>
    rw [ha] at h; dsimp only at h
    cases hc : DecJet.readCellI H p with
    | some sk =>
      rw [hc] at h; dsimp only at h
      cases hh : DecJet.readNnI H n sk.h with
      | none => rw [hh] at h; cases h
      | some hh' =>
        cases ht : DecJet.readNnI H n sk.t with
        | none => rw [hh, ht] at h; cases h
        | some tt' => rw [hh, ht] at h; cases h; exact .inr (.inl ⟨sk, hh', tt', rfl, rfl, hh, ht, rfl⟩)
    | none =>
      rw [hc] at h; dsimp only at h
      cases hi : DecJet.readInd H p with
      | none => rw [hi] at h; cases h
      | some R => rw [hi] at h; exact .inr (.inr ⟨R, rfl, rfl, rfl, h⟩)

omit hkey in
theorem nounRows_atom {n p ro : Nat} {sk : DecJet.AtomSk} (ha : DecJet.readAtom (A.take key) p = some sk) :
    nounRows A key (n + 1) p ro =
      atomRow key p ro :: bitsRows A key (ro != 1) (A.take key).length sk.b 0 (ro == 1) 0 false := by
  simp only [nounRows, ha]

omit hkey in
theorem nounRows_cell {n p ro : Nat} {sk : DecJet.CellSk} (ha : DecJet.readAtom (A.take key) p = none)
    (hc : DecJet.readCellI (A.take key) p = some sk) :
    nounRows A key (n + 1) p ro =
      cellRow key p ro false 0 (iktOf (A.take key) sk.kt) :: (nounRows A key n sk.h 2 ++ nounRows A key n sk.t 2) := by
  simp only [nounRows, ha, hc]

omit hkey in
theorem nounRows_ind {n p ro R : Nat} (ha : DecJet.readAtom (A.take key) p = none)
    (hc : DecJet.readCellI (A.take key) p = none) (hi : DecJet.readInd (A.take key) p = some R) :
    nounRows A key (n + 1) p ro = indRow key p ro false false 0 false 0 false :: nounRows A key n R ro := by
  simp only [nounRows, ha, hc, hi]

theorem nounRows_ok : ∀ (n p ro : Nat) {s : DecJet.Nn}, ro ≤ 2 → n ≤ (A.take key).length →
    DecJet.readNnI (A.take key) n p = some s →
    (ro = 1 → ∀ bs, s = .atom bs → bs.length ≤ 32) → ∀ d ∈ nounRows A key n p ro, OK A d
  | 0, _, _, _, _, _, h, _ => by cases h
  | n + 1, p, ro, s, hro, hn, h, hf => by
    intro d hd
    rcases readNnI_cases h with ⟨sk, bs, sks, ha, hb, hc, rfl⟩ | ⟨sk, hh, tt, ha, hc, h1, h2, rfl⟩ |
      ⟨R, ha, hc, hi, hR⟩
    · rw [nounRows_atom ha] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 2 ∧ 2 ≤ 5 by decide) hro (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (atomReads (d := atomRow key p ro) rfl ha).1
      · refine bitsRows_ok hkey _ sk.b 0 _ 0 false (DecJet.readBitsI_mono hb hn) hc (fun hm => ?_)
          (fun _ _ => rfl) d hd
        have : ro = 1 := by simpa using hm
        have := hf this bs rfl
        omega
    · rw [nounRows_cell ha hc] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 1 ∧ 1 ≤ 5 by decide) hro (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (cellReads (d := cellRow key p ro false 0 _) rfl hc rfl).1
      · rcases List.mem_append.1 hd with hd | hd
        · exact nounRows_ok n sk.h 2 (by decide) (by omega) h1 (fun h => nomatch h) d hd
        · exact nounRows_ok n sk.t 2 (by decide) (by omega) h2 (fun h => nomatch h) d hd
    · rw [nounRows_ind ha hc hi] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 5 ∧ 5 ≤ 5 by decide) hro (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey
          (indReads (d := indRow key p ro false false 0 false 0 false) rfl hi).1
      · exact nounRows_ok n R ro hro (by omega) hR hf d hd

end

/-- **The subject, read once through thunks**, by cases: a thunk at its
    root; an atom; a cell whose head is an atom; a cell whose head is a
    cell. -/
theorem readSubjI_cases {H : List Cell} {n p : Nat} {s : DecJet.Nn} {csk : Option DecJet.CellSk}
    {ask : Option DecJet.AtomSk} {sks : List DecJet.ConsSk}
    (h : DecJet.readSubjI H (n + 1) p = some (s, csk, ask, sks)) :
    (∃ R, DecJet.readAtom H p = none ∧ DecJet.readCellI H p = none ∧ DecJet.readInd H p = some R ∧
      DecJet.readSubjI H n R = some (s, csk, ask, sks)) ∨
    (∃ sk bs, DecJet.readAtom H p = some sk ∧ DecJet.readBitsI H H.length sk.b = some (bs, sks) ∧
      DecJet.canonB bs = true ∧ s = .atom bs ∧ csk = none ∧ ask = some sk) ∨
    (∃ csk' a ask' bs r, DecJet.readAtom H p = none ∧ DecJet.readCellI H p = some csk' ∧
      DecJet.headAtom H H.length csk'.h = some (a, ask') ∧ DecJet.readBitsI H H.length ask'.b = some (bs, sks) ∧
      DecJet.canonB bs = true ∧ DecJet.readNnI H H.length csk'.t = some r ∧ s = .cell (.atom bs) r ∧
      csk = some csk' ∧ ask = some ask') ∨
    (∃ csk' hh tt, DecJet.readAtom H p = none ∧ DecJet.readCellI H p = some csk' ∧
      DecJet.headAtom H H.length csk'.h = none ∧ DecJet.readNnI H H.length csk'.h = some hh ∧
      DecJet.readNnI H H.length csk'.t = some tt ∧ s = .cell hh tt ∧ csk = some csk' ∧ sks = []) := by
  unfold DecJet.readSubjI at h
  cases ha : DecJet.readAtom H p with
  | some sk =>
    rw [ha] at h; dsimp only at h
    cases hb : DecJet.readBitsI H H.length sk.b with
    | none => rw [hb] at h; cases h
    | some q =>
      obtain ⟨bs, sks'⟩ := q
      rw [hb] at h; dsimp only at h
      by_cases hc : DecJet.canonB bs = true
      · rw [if_pos hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .inr (.inl ⟨sk, bs, rfl, hb, hc, rfl, rfl, rfl⟩)
      · rw [if_neg hc] at h; cases h
  | none =>
    rw [ha] at h; dsimp only at h
    cases hc : DecJet.readCellI H p with
    | some csk' =>
      rw [hc] at h; dsimp only at h
      cases hah : DecJet.headAtom H H.length csk'.h with
      | some x =>
        obtain ⟨a, ask'⟩ := x
        rw [hah] at h; dsimp only at h
        cases hb : DecJet.readBitsI H H.length ask'.b with
        | none => rw [hb] at h; cases h
        | some q =>
          obtain ⟨bs, sks'⟩ := q
          rw [hb] at h; dsimp only at h
          by_cases hcn : DecJet.canonB bs = true
          · rw [if_pos hcn] at h
            cases ht : DecJet.readNnI H H.length csk'.t with
            | none => rw [ht] at h; cases h
            | some r =>
              rw [ht] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact .inr (.inr (.inl ⟨csk', a, ask', bs, r, rfl, rfl, hah, hb, hcn, ht, rfl, rfl, rfl⟩))
          · rw [if_neg hcn] at h; cases h
      | none =>
        rw [hah] at h; dsimp only at h
        cases hh : DecJet.readNnI H H.length csk'.h with
        | none => rw [hh] at h; cases h
        | some hn =>
          cases ht : DecJet.readNnI H H.length csk'.t with
          | none => rw [hh, ht] at h; cases h
          | some tn =>
            rw [hh, ht] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -, rfl⟩ := h
            exact .inr (.inr (.inr ⟨csk', hn, tn, rfl, rfl, hah, hh, ht, rfl, rfl, rfl⟩))
    | none =>
      rw [hc] at h; dsimp only at h
      cases hi : DecJet.readInd H p with
      | none => rw [hi] at h; cases h
      | some R => rw [hi] at h; exact .inl ⟨R, rfl, rfl, rfl, h⟩

theorem subjRows_ind {A : List Cell} {key n p R : Nat} (ha : DecJet.readAtom (A.take key) p = none)
    (hc : DecJet.readCellI (A.take key) p = none) (hi : DecJet.readInd (A.take key) p = some R) :
    subjRows A key (n + 1) p = indRow key p 0 false false 0 false 0 false :: subjRows A key n R := by
  simp only [subjRows, ha, hc, hi]

theorem subjRows_atom {A : List Cell} {key n p : Nat} {sk : DecJet.AtomSk} (ha : DecJet.readAtom (A.take key) p = some sk) :
    subjRows A key (n + 1) p = atomRow key p 0 :: bitsRows A key true (A.take key).length sk.b 0 false 0 false := by
  simp only [subjRows, ha]

theorem subjRows_cell {A : List Cell} {key n p : Nat} {csk : DecJet.CellSk} (ha : DecJet.readAtom (A.take key) p = none)
    (hc : DecJet.readCellI (A.take key) p = some csk) :
    subjRows A key (n + 1) p =
      cellRow key p 0 (headV A key csk.h).1 (headV A key csk.h).2 (iktOf (A.take key) csk.kt) ::
        (nounRows A key (A.take key).length csk.h 1 ++ nounRows A key (A.take key).length csk.t 2) := by
  simp only [subjRows, ha, hc]

theorem headRows_ok {A : List Cell} {key : Nat} (hkey : key < 2 ^ 24) : ∀ {n q a : Nat} {ask : DecJet.AtomSk}
    {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.headAtom (A.take key) n q = some (a, ask) →
    DecJet.readBitsI (A.take key) (A.take key).length ask.b = some (bs, sks) → DecJet.canonB bs = true →
    bs.length ≤ 32 → ∀ d ∈ nounRows A key n q 1, OK A d
  | 0, _, _, _, _, _, h, _, _, _ => nomatch h
  | n + 1, q, a, ask, bs, sks, h, hb, hc, hl => by
    intro d hd
    unfold DecJet.headAtom at h
    cases ha : DecJet.readAtom (A.take key) q with
    | some ask' =>
      rw [ha] at h; cases h
      rw [nounRows_atom ha] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 2 ∧ 2 ≤ 5 by decide) (show 1 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (atomReads (d := atomRow key q 1) rfl ha).1
      · exact bitsRows_ok hkey _ ask.b 0 _ 0 false hb hc (fun _ => by omega) (fun _ _ => rfl) d hd
    | none =>
      rw [ha] at h; dsimp only at h
      cases hi : DecJet.readInd (A.take key) q with
      | none => rw [hi] at h; cases h
      | some R =>
        rw [hi] at h; dsimp only at h
        rw [nounRows_ind ha (DecJet.readInd_cellI hi) hi] at hd
        rcases List.mem_cons.1 hd with rfl | hd
        · exact mkOK (show 1 ≤ 5 ∧ 5 ≤ 5 by decide) (show 1 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
            (fun h => nomatch h) (fun h => nomatch h) hkey
            (indReads (d := indRow key q 1 false false 0 false 0 false) rfl hi).1
        · exact headRows_ok hkey h hb hc hl d hd

/-- A noun read as a cell is no head atom. -/
theorem nn_cell_noatom {H : List Cell} : ∀ {n m q : Nat} {bs : List Bool}, DecJet.readNnI H n q = some (.atom bs) →
    n ≤ m → DecJet.headAtom H m q = none → False := by
  intro n m q bs h hnm hh
  obtain ⟨x, hx⟩ := DecJet.headAtom_of_atom h hnm
  rw [hh] at hx; cases hx

/-- **Every row of a call is well formed and reads memory cells**, when
    the jet's reader succeeds and the head fits. -/
theorem subjRows_ok {A : List Cell} {key : Nat} (hkey : key < 2 ^ 24) : ∀ {n p : Nat} {s : DecJet.Nn}
    {csk : Option DecJet.CellSk} {ask : Option DecJet.AtomSk} {sks : List DecJet.ConsSk},
    DecJet.readSubjI (A.take key) n p = some (s, csk, ask, sks) → DecJet.headFits s = true →
    ∀ d ∈ subjRows A key n p, OK A d
  | 0, _, _, _, _, _, h, _ => nomatch h
  | n + 1, p, s, csk, ask, sks, h, hfit => by
    intro d hd
    rcases readSubjI_cases h with ⟨R, ha, hc, hi, hR⟩ | ⟨sk, bs, ha, hb, hcn, rfl, -, -⟩ |
      ⟨csk', a, ask', bs, r, ha, hc, hah, hb, hcn, ht, rfl, -, -⟩ | ⟨csk', hh, tt, ha, hc, hah, hh', ht, rfl, -, -⟩
    · rw [subjRows_ind ha hc hi] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 5 ∧ 5 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey
          (indReads (d := indRow key p 0 false false 0 false 0 false) rfl hi).1
      · exact subjRows_ok hkey hR hfit d hd
    · rw [subjRows_atom ha] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 2 ∧ 2 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (atomReads (d := atomRow key p 0) rfl ha).1
      · exact bitsRows_ok (m := true) hkey _ sk.b 0 false 0 false hb hcn (fun h => nomatch h) (fun _ _ => rfl) d hd
    · rw [subjRows_cell ha hc] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 1 ∧ 1 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (cellReads (d := cellRow key p 0 _ _ _) rfl hc rfl).1
      · rcases List.mem_append.1 hd with hd | hd
        · exact headRows_ok hkey hah hb hcn (by simpa [DecJet.headFits, DecJet.W] using hfit) d hd
        · exact nounRows_ok hkey _ csk'.t 2 (by decide) (Nat.le_refl _) ht (fun h => nomatch h) d hd
    · rw [subjRows_cell ha hc] at hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 1 ∧ 1 ≤ 5 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          (fun h => nomatch h) (fun h => nomatch h) hkey (cellReads (d := cellRow key p 0 _ _ _) rfl hc rfl).1
      · rcases List.mem_append.1 hd with hd | hd
        · exact nounRows_ok hkey _ csk'.h 1 (by decide) (Nat.le_refl _) hh'
            (fun _ bs e => (nn_cell_noatom (e ▸ hh') (Nat.le_refl _) hah).elim) d hd
        · exact nounRows_ok hkey _ csk'.t 2 (by decide) (Nat.le_refl _) ht (fun h => nomatch h) d hd

theorem callRows_ok {A : List Cell} {key : Nat} (hkey : key < 2 ^ 24) {p : Nat} {s : DecJet.Nn}
    {csk : Option DecJet.CellSk} {ask : Option DecJet.AtomSk} {sks : List DecJet.ConsSk}
    (h : DecJet.readSubjI (A.take key) (A.take key).length p = some (s, csk, ask, sks))
    (hfit : DecJet.headFits s = true) : ∀ d ∈ callRows A key p, OK A d :=
  subjRows_ok hkey h hfit

end DecT

end Circuit
