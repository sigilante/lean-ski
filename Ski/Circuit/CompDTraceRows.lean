import Ski.Circuit.CompDTraceRead

/-!
# The honest DEC rows of a jet call

`decair.rs`'s `Reader` in Lean, along `Ski/DecJet.lean`'s readers: a
call at key `key` (the jet row's counter) on the subject at `p` has one row
per cell pattern of its subject (`DecT.callRows`): the subject's wrapper,
then, for a cell, its head (role `1`) and tail (role `2`) nouns
(`nounRows`), each a wrapper and, for an atom, its bits' chain
(`bitsRows`: a `Cons` per bit, the head's in mode `0` under the borrow,
the others in mode `1`; a nil for an empty atom).  The subject's row
carries the head's verdict (`headV`): a crash, or the rewritten bits' cell
count.

**`DecT.callRows_ok`**: when the jet's reader succeeds (`readSubj`, the
head fitting `W`), every row of the call is well formed and reads memory
cells.
-/

namespace Circuit

open B Air

namespace DecT

def nilRow (key p : Nat) (m : Bool) (lvl : Nat) (bw : Bool) (wc : Nat) : DR :=
  ⟨key, 4, 0, m, p, lvl, bw, wc, false, false, false⟩

def consRow (key p : Nat) (m : Bool) (lvl : Nat) (bw : Bool) (wc : Nat) (b last : Bool) : DR :=
  ⟨key, 3, 0, m, p, lvl, bw, wc, b, last, false⟩

def atomRow (key p ro : Nat) : DR := ⟨key, 2, ro, false, p, 0, false, 0, false, false, false⟩

def cellRow (key p ro : Nat) (err : Bool) (wc : Nat) : DR := ⟨key, 1, ro, false, p, 0, false, wc, false, false, err⟩

/-- A bit's chain from `p` at level `lvl`, borrow `bw`, `wc` cells written. -/
def bitsRows (A : List Cell) (key : Nat) (m : Bool) : Nat → Nat → Nat → Bool → Nat → List DR
  | 0, _, _, _, _ => []
  | n + 1, p, lvl, bw, wc =>
    if DecJet.isK (A.take key) p then [nilRow key p m lvl bw wc]
    else match DecJet.readCons (A.take key) p with
      | some (b, sk) =>
        consRow key p m lvl bw wc b (DecJet.isK (A.take key) sk.t) ::
          (if DecJet.isK (A.take key) sk.t then []
           else bitsRows A key m n sk.t (lvl + 1) (bw && !b) (wc + 6 * (if bw then 1 else 0)))
      | none => []

/-- A noun at `p` with the role `ro`. -/
def nounRows (A : List Cell) (key : Nat) : Nat → Nat → Nat → List DR
  | 0, _, _ => []
  | n + 1, p, ro =>
    match DecJet.readAtom (A.take key) p with
    | some sk => atomRow key p ro :: bitsRows A key (ro != 1) (n + 1) sk.b 0 (ro == 1) 0
    | none =>
      match DecJet.readCell (A.take key) p with
      | some sk => cellRow key p ro false 0 :: (nounRows A key n sk.h 2 ++ nounRows A key n sk.t 2)
      | none => []

/-- The head's verdict: a crash, or the rewritten bits' cell count. -/
def headV (A : List Cell) (key h : Nat) : Bool × Nat :=
  match DecJet.readAtom (A.take key) h with
  | some ask =>
    match DecJet.readBits (A.take key) (A.take key).length ask.b with
    | some (b :: bs, sks) => (false, (DecJet.bitCells (key + 12) (b :: bs) sks).length)
    | _ => (true, 0)
  | none => (true, 0)

/-- **The rows of a call** at key `key` on the subject at `p`. -/
def callRows (A : List Cell) (key p : Nat) : List DR :=
  match DecJet.readAtom (A.take key) p with
  | some sk => atomRow key p 0 :: bitsRows A key true (A.take key).length sk.b 0 false 0
  | none =>
    match DecJet.readCell (A.take key) p with
    | some csk =>
      cellRow key p 0 (headV A key csk.h).1 (headV A key csk.h).2 ::
        (nounRows A key (A.take key).length csk.h 1 ++ nounRows A key (A.take key).length csk.t 2)
    | none => []

-- ---------------------------------------------------------------------------
-- Every row is well formed and reads memory cells
-- ---------------------------------------------------------------------------

/-- A row's facts: well formed, reading memory cells. -/
def OK (A : List Cell) (d : DR) : Prop := RowOK A d ∧ ReadsOK A d

theorem mkOK {A : List Cell} {d : DR} (hk : 1 ≤ d.kind ∧ d.kind ≤ 4) (hro : d.ro ≤ 2)
    (hc : d.kind = 3 → d.last = true → d.bit = true) (hl : d.kind = 3 → d.m = false → d.lvl < 32)
    (hkey : d.key < 2 ^ 24) (hR : ReadsOK A d) : OK A d :=
  ⟨⟨hk, hro, hc, hl, hkey, fun j hj => (hR j hj).1⟩, hR⟩

theorem readCons_app {H : List Cell} {p : Nat} {x : Bool × DecJet.ConsSk} (h : DecJet.readCons H p = some x) :
    ∃ a b, H[p]? = some (.app a b) := by
  unfold DecJet.readCons at h
  split at h
  · next a b hp => exact ⟨a, b, hp⟩
  · cases h

theorem readBits_tail {H : List Cell} {n t : Nat} {bs : List Bool} {sks : List DecJet.ConsSk}
    (h : DecJet.readBits H n t = some (bs, sks)) (hK : DecJet.isK H t = false) :
    ∃ x y, H[t]? = some (.app x y) := by
  cases n with
  | zero => cases h
  | succ n =>
    unfold DecJet.readBits at h
    rw [hK, if_neg (by decide)] at h
    split at h
    · next q hq => exact readCons_app hq
    · cases h

theorem readBits_K {H : List Cell} {n t : Nat} {bs : List Bool} {sks : List DecJet.ConsSk}
    (h : DecJet.readBits H n t = some (bs, sks)) (hK : DecJet.isK H t = true) : bs = [] := by
  cases n with
  | zero => cases h
  | succ n =>
    unfold DecJet.readBits at h
    rw [hK, if_pos rfl] at h
    cases h; rfl

section
variable {A : List Cell} {key : Nat} (hkey : key < 2 ^ 24)
include hkey

theorem bitsRows_ok {m : Bool} : ∀ (n p lvl : Nat) (bw : Bool) (wc : Nat) {bs : List Bool} {sks : List DecJet.ConsSk},
    DecJet.readBits (A.take key) n p = some (bs, sks) → DecJet.canonB bs = true →
    (m = false → lvl + bs.length ≤ 32) → ∀ d ∈ bitsRows A key m n p lvl bw wc, OK A d
  | 0, _, _, _, _, _, _, h, _, _ => by cases h
  | n + 1, p, lvl, bw, wc, bs, sks, h, hc, hl => by
    intro d hd
    unfold bitsRows at hd
    unfold DecJet.readBits at h
    by_cases hK : DecJet.isK (A.take key) p = true
    · rw [if_pos hK] at hd
      rw [List.mem_singleton] at hd; subst hd
      exact mkOK (show 1 ≤ 4 ∧ 4 ≤ 4 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h) hkey
        (nilReads (d := nilRow key p m lvl bw wc) rfl hK)
    · rw [if_neg hK] at hd h
      cases hr : DecJet.readCons (A.take key) p with
      | none => rw [hr] at hd; cases hd
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hr] at hd h
        simp only at hd h
        cases hb : DecJet.readBits (A.take key) n sk.t with
        | none => rw [hb] at h; cases h
        | some q2 =>
          obtain ⟨bs', sks'⟩ := q2
          rw [hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rcases List.mem_cons.1 hd with rfl | hd
          · have hR := consReads (d := consRow key p m lvl bw wc b (DecJet.isK (A.take key) sk.t)) rfl hr rfl rfl
              (fun hK' => readBits_tail hb hK')
            refine mkOK (show 1 ≤ 3 ∧ 3 ≤ 4 by decide) (show 0 ≤ 2 by decide) (fun _ hl' => ?_) (fun _ hm => ?_) hkey hR.1
            · have := readBits_K hb hl'
              subst this; exact hc
            · have := hl hm; simp only [List.length_cons] at this
              show lvl < 32; omega
          · by_cases hl' : DecJet.isK (A.take key) sk.t = true
            · rw [if_pos hl'] at hd; cases hd
            · rw [if_neg hl'] at hd
              exact bitsRows_ok n sk.t (lvl + 1) _ _ hb (DecJet.canonB_tail hc)
                (fun hm => by have := hl hm; simp only [List.length_cons] at this; omega) d hd

omit hkey in
theorem readNn_cell {H : List Cell} {n p : Nat} {bs : List Bool} (h : DecJet.readNn H n p = some (.atom bs))
    (ha : DecJet.readAtom H p = none) : False := by
  cases n with
  | zero => cases h
  | succ n =>
    unfold DecJet.readNn at h
    rw [ha] at h
    simp only at h
    split at h
    · split at h
      · cases h
      · cases h
    · cases h

theorem nounRows_ok : ∀ (n p ro : Nat) {s : DecJet.Nn}, ro ≤ 2 → DecJet.readNn (A.take key) n p = some s →
    (ro = 1 → ∀ bs, s = .atom bs → bs.length ≤ 32) → ∀ d ∈ nounRows A key n p ro, OK A d
  | 0, _, _, _, _, h, _ => by cases h
  | n + 1, p, ro, s, hro, h, hf => by
    intro d hd
    unfold nounRows at hd
    unfold DecJet.readNn at h
    cases ha : DecJet.readAtom (A.take key) p with
    | some sk =>
      rw [ha] at hd h
      simp only at hd h
      cases hb : DecJet.readBits (A.take key) (n + 1) sk.b with
      | none => rw [hb] at h; cases h
      | some q =>
        obtain ⟨bs, sks⟩ := q
        rw [hb] at h
        simp only at h
        by_cases hc : DecJet.canonB bs = true
        · rw [if_pos hc] at h
          cases h
          rcases List.mem_cons.1 hd with rfl | hd
          · exact mkOK (show 1 ≤ 2 ∧ 2 ≤ 4 by decide) hro (fun h => nomatch h) (fun h => nomatch h) hkey
              (atomReads (d := atomRow key p ro) rfl ha).1
          · refine bitsRows_ok hkey (n + 1) sk.b 0 _ 0 hb hc (fun hm => ?_) d hd
            have : ro = 1 := by simpa using hm
            have := hf this bs rfl
            omega
        · rw [if_neg hc] at h; cases h
    | none =>
      rw [ha] at hd h
      simp only at hd h
      cases hc : DecJet.readCell (A.take key) p with
      | none => rw [hc] at hd; cases hd
      | some sk =>
        rw [hc] at hd h
        simp only at hd h
        cases hh : DecJet.readNn (A.take key) n sk.h with
        | none => rw [hh] at h; cases h
        | some hn =>
          cases ht : DecJet.readNn (A.take key) n sk.t with
          | none => rw [hh, ht] at h; cases h
          | some tn =>
            rcases List.mem_cons.1 hd with rfl | hd
            · exact mkOK (show 1 ≤ 1 ∧ 1 ≤ 4 by decide) hro (fun h => nomatch h) (fun h => nomatch h) hkey
                (cellReads (d := cellRow key p ro false 0) rfl hc).1
            · rcases List.mem_append.1 hd with hd | hd
              · exact nounRows_ok n sk.h 2 (by decide) hh (fun h => nomatch h) d hd
              · exact nounRows_ok n sk.t 2 (by decide) ht (fun h => nomatch h) d hd

/-- **Every row of a call is well formed and reads memory cells**, when
    the jet's reader succeeds and the head fits. -/
theorem callRows_ok {p : Nat} {s : DecJet.Nn} {csk : Option DecJet.CellSk} {ask : Option DecJet.AtomSk}
    {sks : List DecJet.ConsSk} (h : DecJet.readSubj (A.take key) p = some (s, csk, ask, sks))
    (hfit : DecJet.headFits s = true) : ∀ d ∈ callRows A key p, OK A d := by
  intro d hd
  unfold callRows at hd
  unfold DecJet.readSubj at h
  cases ha : DecJet.readAtom (A.take key) p with
  | some sk =>
    rw [ha] at hd h
    simp only at hd h
    cases hb : DecJet.readBits (A.take key) (A.take key).length sk.b with
    | none => rw [hb] at h; cases h
    | some q =>
      obtain ⟨bs, sks'⟩ := q
      rw [hb] at h
      simp only at h
      by_cases hc : DecJet.canonB bs = true
      · rcases List.mem_cons.1 hd with rfl | hd
        · exact mkOK (show 1 ≤ 2 ∧ 2 ≤ 4 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
            hkey (atomReads (d := atomRow key p 0) rfl ha).1
        · exact bitsRows_ok (m := true) hkey _ sk.b 0 false 0 hb hc (fun h => nomatch h) d hd
      · rw [if_neg hc] at h; cases h
  | none =>
    rw [ha] at hd h
    simp only at hd h
    cases hc : DecJet.readCell (A.take key) p with
    | none => rw [hc] at hd; cases hd
    | some csk' =>
      rw [hc] at hd h
      simp only at hd h
      rcases List.mem_cons.1 hd with rfl | hd
      · exact mkOK (show 1 ≤ 1 ∧ 1 ≤ 4 by decide) (show 0 ≤ 2 by decide) (fun h => nomatch h) (fun h => nomatch h)
          hkey (cellReads (d := cellRow key p 0 (headV A key csk'.h).1 (headV A key csk'.h).2) rfl hc).1
      · cases hah : DecJet.readAtom (A.take key) csk'.h with
        | some ask' =>
          rw [hah] at h
          simp only at h
          cases hb : DecJet.readBits (A.take key) (A.take key).length ask'.b with
          | none => rw [hb] at h; cases h
          | some q =>
            obtain ⟨bs, sks'⟩ := q
            rw [hb] at h
            simp only at h
            by_cases hcn : DecJet.canonB bs = true
            · rw [if_pos hcn] at h
              cases ht : DecJet.readNn (A.take key) (A.take key).length csk'.t with
              | none => rw [ht] at h; cases h
              | some r =>
                rw [ht] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -, -, -⟩ := h
                have hL : (A.take key).length = (A.take key).length - 1 + 1 := by
                  cases hl : (A.take key).length with
                  | zero => rw [hl] at hb; cases hb
                  | succ k => rfl
                have hhn : DecJet.readNn (A.take key) (A.take key).length csk'.h = some (.atom bs) := by
                  rw [hL]; unfold DecJet.readNn; rw [hah]; simp only; rw [← hL, hb]; simp only [if_pos hcn]
                rcases List.mem_append.1 hd with hd | hd
                · refine nounRows_ok hkey _ csk'.h 1 (by decide) hhn (fun _ bs' e => ?_) d hd
                  cases e
                  simpa [DecJet.headFits, DecJet.W] using hfit
                · exact nounRows_ok hkey _ csk'.t 2 (by decide) ht (fun h => nomatch h) d hd
            · rw [if_neg hcn] at h; cases h
        | none =>
          rw [hah] at h
          simp only at h
          cases hh : DecJet.readNn (A.take key) (A.take key).length csk'.h with
          | none => rw [hh] at h; cases h
          | some hn =>
            cases ht : DecJet.readNn (A.take key) (A.take key).length csk'.t with
            | none => rw [hh, ht] at h; cases h
            | some tn =>
              rcases List.mem_append.1 hd with hd | hd
              · exact nounRows_ok hkey _ csk'.h 1 (by decide) hh
                  (fun _ bs e => absurd (e ▸ hh) (fun h' => readNn_cell h' hah)) d hd
              · exact nounRows_ok hkey _ csk'.t 2 (by decide) ht (fun h => nomatch h) d hd

end

end DecT

end Circuit
