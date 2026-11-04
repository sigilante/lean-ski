import Ski.Circuit.CompDTree

/-!
# The circuit with the `dec` jet: the head's chain

At a jet row's key, the head atom's bits are read by a chain in mode `0`,
under a borrow from the bottom bit (`DecJet.decB`), through any thunks.

- **`DecJet.walkS`**: the chain's states, step by step, as a function of the
  memory and the head's bits' root: a thunk passes to its target, a `Cons`
  to its tail one level up, under the borrow's step, counting the cells it
  rewrites.  Whether a `Cons` is the last is whether its tail's run of
  thunks ends at `K` (`lastAt`).
- **Forward**: a step marked as a list's end reads the empty list
  (`CompDOK.chain_term`); an unmarked step above level `0` a non-empty one
  (`CompDOK.chain_nonterm`).
- **No chain row is a stray** (`CompDOK.on_walk`): every mode-`0` `Cons` or
  nil row at the key that does not end a list is a state of the walk from
  the head's bits, by induction on the level, each step traced back through
  its run of thunks (`CompDOK.chain_back'`) to the head's `Atom` row or the
  `Cons` row one level below.
- **`DecJet.walkS_end`**: the last `Cons` reached counts every rewritten cell.
-/

namespace DecJet

def nwr : Bool → List Bool → Nat
  | _, [] => 0
  | bw, b :: bs => (if bw && !(b && bs.isEmpty) then 1 else 0) + nwr (bw && !b) bs

/-- **The list at `t` is empty**: its run of thunks ends at `K`. -/
def lastAt (H : List Cell) (t : Nat) : Bool :=
  (List.range (H.length + 1)).any fun j => match iterI H j t with
    | some x => isK H x
    | none => false

theorem readBitsI_ind_inv {H : List Cell} {n p R : Nat} (hi : readInd H p = some R) :
    readBitsI H (n + 1) p = readBitsI H n R := by
  conv => lhs; unfold readBitsI
  rw [if_neg (by rw [readInd_isK hi]; decide), readInd_cons hi]
  dsimp only; rw [hi]

theorem readBitsI_inv {H : List Cell} {n p : Nat} {x : List Bool × List ConsSk} (h : readBitsI H n p = some x) :
    ∃ n', n = n' + 1 ∧ ((isK H p = true ∧ x = ([], [])) ∨
      (∃ b sk bs sks, isK H p = false ∧ readCons H p = some (b, sk) ∧ readBitsI H n' sk.t = some (bs, sks) ∧
        x = (b :: bs, sk :: sks)) ∨
      (∃ R, readInd H p = some R ∧ readBitsI H n' R = some x)) := by
  cases n with
  | zero => cases h
  | succ n =>
    refine ⟨n, rfl, ?_⟩
    unfold readBitsI at h
    split at h
    · rename_i hk; cases h; exact .inl ⟨hk, rfl⟩
    · rename_i hk
      cases hc : readCons H p with
      | some q =>
        obtain ⟨b, sk⟩ := q
        rw [hc] at h; dsimp only at h
        cases hr : readBitsI H n sk.t with
        | none => rw [hr] at h; cases h
        | some q' =>
          obtain ⟨bs, sks⟩ := q'
          rw [hr] at h; cases h
          exact .inr (.inl ⟨b, sk, bs, sks, by simpa using hk, rfl, hr, rfl⟩)
      | none =>
        rw [hc] at h; dsimp only at h
        cases hi : readInd H p with
        | none => rw [hi] at h; cases h
        | some R => rw [hi] at h; exact .inr (.inr ⟨R, rfl, h⟩)

theorem iterI_K {H : List Cell} {x : Nat} (hk : isK H x = true) : ∀ j, j ≠ 0 → iterI H j x = none
  | 0, h => absurd rfl h
  | j + 1, _ => by
    have : readInd H x = none := by
      cases hi : readInd H x with
      | none => rfl
      | some R => rw [readInd_isK hi] at hk; cases hk
    show (match readInd H x with | some y => iterI H j y | none => none) = _
    rw [this]

theorem isK_lt {H : List Cell} {x : Nat} (hk : isK H x = true) : x < H.length := by
  unfold isK at hk
  cases e : H[x]? with
  | none => rw [e] at hk; cases hk
  | some c => exact (List.getElem?_eq_some_iff.1 e).1

theorem isK_noind {H : List Cell} {x : Nat} (hk : isK H x = true) : readInd H x = none := by
  cases hi : readInd H x with
  | none => rfl
  | some R => rw [readInd_isK hi] at hk; cases hk

theorem readCons_noind {H : List Cell} {x : Nat} {r : Bool × ConsSk} (hc : readCons H x = some r) : readInd H x = none := by
  cases hi : readInd H x with
  | none => rfl
  | some R => rw [readInd_cons hi] at hc; cases hc

theorem readCons_notK {H : List Cell} {x : Nat} {r : Bool × ConsSk} (hc : readCons H x = some r) : isK H x = false := by
  cases hk : isK H x with
  | false => rfl
  | true => have := isK_eq hk; unfold readCons at hc; rw [this] at hc; cases hc

/-- **`lastAt` is the list's emptiness.** -/
theorem lastAt_eq {H : List Cell} : ∀ {n t : Nat} {bs : List Bool} {sks : List ConsSk},
    readBitsI H n t = some (bs, sks) → lastAt H t = bs.isEmpty := by
  -- the run from `t` ends at `K` exactly when the list is empty
  have key : ∀ {n t : Nat} {bs : List Bool} {sks : List ConsSk}, readBitsI H n t = some (bs, sks) →
      (bs = [] → ∃ j x, iterI H j t = some x ∧ isK H x = true) ∧
      (bs ≠ [] → ∀ j x, iterI H j t = some x → isK H x = false) := by
    intro n
    induction n with
    | zero => intro t bs sks h; cases h
    | succ n ih =>
      intro t bs sks h
      obtain ⟨n', e, hc⟩ := readBitsI_inv h
      cases e
      rcases hc with ⟨hk, hx⟩ | ⟨b, sk, bs', sks', hk, hcons, _, hx⟩ | ⟨R, hi, hr⟩
      · cases hx
        exact ⟨fun _ => ⟨0, t, rfl, hk⟩, fun h => absurd rfl h⟩
      · cases hx
        refine ⟨fun h => (nomatch h), fun _ j x hj => ?_⟩
        cases j with
        | zero => cases hj; exact hk
        | succ j =>
          have : iterI H (j + 1) t = none := by
            show (match readInd H t with | some y => iterI H j y | none => none) = _
            rw [readCons_noind hcons]
          rw [this] at hj; cases hj
      · obtain ⟨i1, i2⟩ := ih hr
        refine ⟨fun h0 => ?_, fun hne j x hj => ?_⟩
        · obtain ⟨j, x, hj, hk⟩ := i1 h0
          exact ⟨j + 1, x, by rw [iterI_succ hi]; exact hj, hk⟩
        · cases j with
          | zero => cases hj; exact readInd_isK hi
          | succ j => rw [iterI_succ hi] at hj; exact i2 hne j x hj
  intro n t bs sks h
  obtain ⟨k1, k2⟩ := key h
  cases bs with
  | nil =>
    obtain ⟨j, x, hj, hk⟩ := k1 rfl
    have hb := iterI_bound hj (isK_lt hk) (isK_noind hk)
    show (List.range (H.length + 1)).any _ = true
    exact List.any_eq_true.2 ⟨j, List.mem_range.2 (by omega), by rw [hj]; exact hk⟩
  | cons b bs =>
    show (List.range (H.length + 1)).any _ = false
    refine List.any_eq_false.2 fun j _ => ?_
    cases hj : iterI H j t with
    | none => simp
    | some x => simp [k2 (List.cons_ne_nil _ _) j x hj]

/-- **The head chain's states**, step by step: the pointer, the level, the
    borrow and the cells written. -/
def walkS (H : List Cell) (b0 : Nat) : Nat → Option (Nat × Nat × Bool × Nat)
  | 0 => some (b0, 0, true, 0)
  | j + 1 =>
    match walkS H b0 j with
    | some (a, l, bw, wc) =>
      match readInd H a with
      | some R => some (R, l, bw, wc)
      | none =>
        match readCons H a with
        | some (b, sk) => some (sk.t, l + 1, bw && !b, wc + if bw && !(b && lastAt H sk.t) then 6 else 0)
        | none => none
    | none => none

theorem walkS_ind {H : List Cell} {b0 j a l : Nat} {bw : Bool} {wc R : Nat}
    (hw : walkS H b0 j = some (a, l, bw, wc)) (hi : readInd H a = some R) : walkS H b0 (j + 1) = some (R, l, bw, wc) := by
  show (match walkS H b0 j with
    | some (a, l, bw, wc) =>
      match readInd H a with
      | some R => some (R, l, bw, wc)
      | none =>
        match readCons H a with
        | some (b, sk) => some (sk.t, l + 1, bw && !b, wc + if bw && !(b && lastAt H sk.t) then 6 else 0)
        | none => none
    | none => none) = _
  rw [hw]; dsimp only; rw [hi]

theorem walkS_cons {H : List Cell} {b0 j a l : Nat} {bw : Bool} {wc : Nat} {b : Bool} {sk : ConsSk}
    (hw : walkS H b0 j = some (a, l, bw, wc)) (hi : readInd H a = none) (hc : readCons H a = some (b, sk)) :
    walkS H b0 (j + 1) = some (sk.t, l + 1, bw && !b, wc + if bw && !(b && lastAt H sk.t) then 6 else 0) := by
  show (match walkS H b0 j with
    | some (a, l, bw, wc) =>
      match readInd H a with
      | some R => some (R, l, bw, wc)
      | none =>
        match readCons H a with
        | some (b, sk) => some (sk.t, l + 1, bw && !b, wc + if bw && !(b && lastAt H sk.t) then 6 else 0)
        | none => none
    | none => none) = _
  rw [hw]; dsimp only; rw [hi]; dsimp only; rw [hc]

theorem walkS_stop {H : List Cell} {b0 j a l : Nat} {bw : Bool} {wc : Nat}
    (hw : walkS H b0 j = some (a, l, bw, wc)) (hi : readInd H a = none) (hc : readCons H a = none) :
    walkS H b0 (j + 1) = none := by
  show (match walkS H b0 j with
    | some (a, l, bw, wc) =>
      match readInd H a with
      | some R => some (R, l, bw, wc)
      | none =>
        match readCons H a with
        | some (b, sk) => some (sk.t, l + 1, bw && !b, wc + if bw && !(b && lastAt H sk.t) then 6 else 0)
        | none => none
    | none => none) = _
  rw [hw]; dsimp only; rw [hi]; dsimp only; rw [hc]

theorem walkS_none {H : List Cell} {b0 : Nat} : ∀ {j : Nat}, walkS H b0 j = none → ∀ i, walkS H b0 (j + i) = none := by
  intro j hj i
  induction i with
  | zero => exact hj
  | succ i ih =>
    show (match walkS H b0 (j + i) with
      | some (a, l, bw, wc) =>
        match readInd H a with
        | some R => some (R, l, bw, wc)
        | none =>
          match readCons H a with
          | some (b, sk) => some (sk.t, l + 1, bw && !b, wc + if bw && !(b && lastAt H sk.t) then 6 else 0)
          | none => none
      | none => none) = none
    rw [ih]

theorem walkS_iter {H : List Cell} {b0 j l : Nat} {bw : Bool} {wc : Nat} :
    ∀ (m a : Nat) {x : Nat}, walkS H b0 j = some (a, l, bw, wc) → iterI H m a = some x →
      walkS H b0 (j + m) = some (x, l, bw, wc)
  | 0, a, x, hw, hit => by cases hit; exact hw
  | m + 1, a, x, hw, hit => by
    cases hi : readInd H a with
    | none =>
      have : iterI H (m + 1) a = none := by
        show (match readInd H a with | some y => iterI H m y | none => none) = _
        rw [hi]
      rw [this] at hit; cases hit
    | some R =>
      rw [iterI_succ hi] at hit
      have := walkS_iter (j := j + 1) m R (walkS_ind hw hi) hit
      rw [show j + 1 + m = j + (m + 1) by omega] at this
      exact this

/-- **The head chain's last `Cons` counts every rewritten cell.** -/
theorem walkS_end {H : List Cell} {b0 : Nat} : ∀ (n : Nat) (bs : List Bool) (sks : List ConsSk) (j a l : Nat)
    (bw : Bool) (wc : Nat), readBitsI H n a = some (bs, sks) → walkS H b0 j = some (a, l, bw, wc) →
    ∀ (i a' l' : Nat) (bw' : Bool) (wc' : Nat) (b' : Bool) (sk' : ConsSk),
      walkS H b0 (j + i) = some (a', l', bw', wc') → readInd H a' = none → readCons H a' = some (b', sk') →
      lastAt H sk'.t = true → bs ≠ [] ∧ wc' + (if bw' && !b' then 6 else 0) = wc + 6 * nwr bw bs := by
  intro n
  induction n with
  | zero => intro bs sks j a l bw wc hr; cases hr
  | succ n ih =>
    intro bs sks j a l bw wc hr hw i a' l' bw' wc' b' sk' hw' hi' hc' hl'
    obtain ⟨n', e, hcs⟩ := readBitsI_inv hr
    cases e
    rcases hcs with ⟨hk, hx⟩ | ⟨b, sk, bs', sks', hk, hcons, hr', hx⟩ | ⟨R, hi, hr'⟩
    · -- `K`: the walk stops here
      exfalso
      have hci : readCons H a = none := by
        have := isK_eq hk; unfold readCons; rw [this]
      have hstop := walkS_stop hw (isK_noind hk) hci
      cases i with
      | zero => rw [Nat.add_zero, hw] at hw'; cases hw'; rw [hci] at hc'; cases hc'
      | succ i =>
        have := walkS_none hstop i
        rw [show j + 1 + i = j + (i + 1) by omega, hw'] at this; cases this
    · cases hx
      have hni := readCons_noind hcons
      have hstep := walkS_cons hw hni hcons
      rw [lastAt_eq hr'] at hstep
      refine ⟨List.cons_ne_nil _ _, ?_⟩
      cases i with
      | zero =>
        rw [Nat.add_zero, hw] at hw'
        cases hw'
        rw [hcons] at hc'
        cases hc'
        have hnil : bs' = [] := by
          have := lastAt_eq hr'; rw [hl'] at this
          cases bs' with
          | nil => rfl
          | cons _ _ => cases this
        subst hnil
        simp only [nwr, List.isEmpty_nil, Bool.and_true]
        split <;> simp
      | succ i =>
        rw [show j + (i + 1) = (j + 1) + i by omega] at hw'
        obtain ⟨_, e⟩ := ih bs' sks' (j + 1) sk.t _ _ _ hr' hstep i a' l' bw' wc' b' sk' hw' hi' hc' hl'
        rw [e]
        simp only [nwr]
        cases bw <;> cases b <;> cases bs'.isEmpty <;> simp <;> omega
    · -- a thunk: the walk passes to its target
      have hstep := walkS_ind hw hi
      cases i with
      | zero => rw [Nat.add_zero, hw] at hw'; cases hw'; rw [hi] at hi'; cases hi'
      | succ i =>
        rw [show j + (i + 1) = (j + 1) + i by omega] at hw'
        exact ih bs sks (j + 1) R _ _ _ hr' hstep i a' l' bw' wc' b' sk' hw' hi' hc' hl'

end DecJet

namespace Circuit

open B Air DecJet

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

/-- **A step marked as a list's end reads the empty list.** -/
theorem CompDOK.chain_term : ∀ (nf : Nat) (k a m l bw wc : F) (bs : List Bool) (sks : List ConsSk),
    ChainSent D [k, a, m + ofN 2 * 1, l, bw, wc] → (m = 0 ∨ m = 1) →
    readBitsI ((memOf Mm).take k.val) nf a.val = some (bs, sks) → bs = [] := by
  intro nf
  induction nf with
  | zero => intro _ _ _ _ _ _ _ _ _ _ hr; cases hr
  | succ nf ih =>
    intro k a m l bw wc bs sks hs hm hr
    obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
    have hf := decRowF_of h.dec hq
    have hmt := bits2 hm (.inr rfl) hf.mode hf.term e2
    rcases hkn with hkc | hkn | hkb
    · have ht := hf.consTerm
      rw [hkc, one_mul', ← hmt.2] at ht; exact absurd ht (by decide)
    · have hk : DKind D q 4 := by
        rcases h.kind_of_cn hq (.inr hkn) with hd | hd
        · rw [hd.2.2.2.2.1] at hkn; exact absurd hkn (by decide)
        · exact hd
      have hK := h.nilRead hq hk
      rw [← e0, ← e1] at hK
      obtain ⟨_, e, hcs⟩ := readBitsI_inv hr
      rcases hcs with ⟨_, hx⟩ | ⟨_, _, _, _, hk', _⟩ | ⟨R, hi, _⟩
      · cases hx; rfl
      · rw [hK] at hk'; cases hk'
      · rw [isK_noind hK] at hi; cases hi
    · have hk := kind_of_inb hf hkb
      obtain ⟨hi, _⟩ := h.indRead hq hk
      rw [← e0, ← e1] at hi
      rw [readBitsI_ind_inv hi] at hr
      have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3),
          D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM, D.main q Dec.LVL, D.main q Dec.BW,
          D.main q Dec.WC] := .inr (.inr ⟨q, hq, hkb, rfl⟩)
      rw [← e0, ← hmt.1, ← hmt.2] at hsent
      exact ih _ _ _ _ _ _ _ _ hsent hm hr

/-- **An unmarked step above level `0` reads a non-empty list.** -/
theorem CompDOK.chain_nonterm : ∀ (nf : Nat) (k a m l bw wc : F) (bs : List Bool) (sks : List ConsSk),
    ChainSent D [k, a, m, l, bw, wc] → (m = 0 ∨ m = 1) → l ≠ 0 →
    readBitsI ((memOf Mm).take k.val) nf a.val = some (bs, sks) → bs ≠ [] := by
  intro nf
  induction nf with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ hr; cases hr
  | succ nf ih =>
    intro k a m l bw wc bs sks hs hm hl hr
    obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
    have hf := decRowF_of h.dec hq
    have hmt := bits2 hm (.inl rfl) hf.mode hf.term (by rw [show ofN 2 * (0 : F) = 0 by decide, add_zero']; exact e2)
    rcases hkn with hkc | hkn | hkb
    · have hk : DKind D q 3 := by
        rcases h.kind_of_cn hq (.inl hkc) with hd | hd
        · exact hd
        · rw [hd.2.2.2.1] at hkc; exact absurd hkc (by decide)
      obtain ⟨hnk, hrc⟩ := h.consRead hq hk
      rw [← e0, ← e1] at hnk hrc
      obtain ⟨_, e, hcs⟩ := readBitsI_inv hr
      rcases hcs with ⟨hk', _⟩ | ⟨_, _, _, _, _, _, _, hx⟩ | ⟨R, hi, _⟩
      · rw [hnk] at hk'; cases hk'
      · cases hx; exact List.cons_ne_nil _ _
      · rw [readCons_noind hrc] at hi; cases hi
    · have hz := hf.nilLvl
      rw [hkn, one_mul', ← hmt.2, show (1 : F) - 0 = 1 by decide, one_mul'] at hz
      exact absurd (by rw [e3, hz]) hl
    · have hk := kind_of_inb hf hkb
      obtain ⟨hi, _⟩ := h.indRead hq hk
      rw [← e0, ← e1] at hi
      rw [readBitsI_ind_inv hi] at hr
      have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3),
          D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM, D.main q Dec.LVL, D.main q Dec.BW,
          D.main q Dec.WC] := .inr (.inr ⟨q, hq, hkb, rfl⟩)
      rw [← e0, ← hmt.1, ← hmt.2, show ofN 2 * (0 : F) = 0 by decide, add_zero', ← e3] at hsent
      exact ih _ _ _ _ _ _ _ _ hsent hm hl hr

/-- **A step travels along a run of thunks**: each thunk's row passes it on. -/
theorem CompDOK.chain_run : ∀ (j : Nat) (k a mf l bw wc : F) {x : Nat}, ChainSent D [k, a, mf, l, bw, wc] →
    iterI ((memOf Mm).take k.val) j a.val = some x → ∃ x' : F, x'.val = x ∧ ChainSent D [k, x', mf, l, bw, wc] := by
  intro j
  induction j with
  | zero => intro k a mf l bw wc x hs hj; cases hj; exact ⟨a, rfl, hs⟩
  | succ j ih =>
    intro k a mf l bw wc x hs hj
    cases hi : readInd ((memOf Mm).take k.val) a.val with
    | none =>
      have : iterI ((memOf Mm).take k.val) (j + 1) a.val = none := by
        show (match readInd _ a.val with | some y => iterI _ j y | none => none) = _
        rw [hi]
      rw [this] at hj; cases hj
    | some R =>
      rw [iterI_succ hi] at hj
      obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs
      simp only [List.cons.injEq, and_true] at e
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
      have hf := decRowF_of h.dec hq
      rcases hkn with hkc | hkn | hkb
      · rw [e0, e1, h.cn_noind hq (.inl hkc)] at hi; cases hi
      · rw [e0, e1, h.cn_noind hq (.inr hkn)] at hi; cases hi
      · obtain ⟨hi', _⟩ := h.indRead hq (kind_of_inb hf hkb)
        rw [← e0, ← e1, hi] at hi'
        cases hi'
        have hsent : ChainSent D [D.main q Dec.KEY, D.main q (Dec.DFLD + 3),
            D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM, D.main q Dec.LVL, D.main q Dec.BW,
            D.main q Dec.WC] := .inr (.inr ⟨q, hq, hkb, rfl⟩)
        rw [← e0, ← e2, ← e3, ← e4, ← e5] at hsent
        exact ih _ _ _ _ _ _ hsent hj

/-- An unmarked step's run of thunks never ends at `K` above level `0`. -/
theorem CompDOK.chain_run_K (j : Nat) (k a l bw wc : F) {x : Nat} (hs : ChainSent D [k, a, 0, l, bw, wc])
    (hj : iterI ((memOf Mm).take k.val) j a.val = some x) (hx : isK ((memOf Mm).take k.val) x = true) : l = 0 := by
  obtain ⟨x', hx', hs'⟩ := h.chain_run j k a 0 l bw wc hs hj
  obtain ⟨q, hq, hkn, e⟩ := h.chain_recv hs'
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
  have hf := decRowF_of h.dec hq
  rw [← hx', e0, e1] at hx
  rcases hkn with hkc | hkn | hkb
  · rcases h.kind_of_cn hq (.inl hkc) with hd | hd
    · rw [(h.consRead hq hd).1] at hx; cases hx
    · rw [hd.2.2.2.1] at hkc; exact absurd hkc (by decide)
  · have hmt := bits2_zero hf.mode hf.term e2.symm
    have hz := hf.nilLvl
    rw [hkn, one_mul', hmt.2, show (1 : F) - 0 = 1 by decide, one_mul'] at hz
    rw [e3, hz]
  · rw [readInd_isK (h.indRead hq (kind_of_inb hf hkb)).1] at hx; cases hx

variable {r0 : Nat} (hr0 : r0 < C.h) (hp0 : C.main r0 DECSEL = 1)
include hr0 hp0

/-- **No chain row is a stray**: a mode-`0` `Cons` or nil row at the key,
    not a list's end, is a state of the walk from the head's bits. -/
theorem CompDOK.on_walk {R m0 ma A : Nat} {csk : CellSk} {ask : AtomSk}
    (hR : iterI ((memOf Mm).take (C.main r0 CTR).val) m0 (C.main r0 (FLD + 2)).val = some R)
    (hc : readCellI ((memOf Mm).take (C.main r0 CTR).val) R = some csk)
    (hA : iterI ((memOf Mm).take (C.main r0 CTR).val) ma csk.h = some A)
    (hask : readAtom ((memOf Mm).take (C.main r0 CTR).val) A = some ask) :
    ∀ (m q : Nat), q < D.h → (D.main q Dec.KCONS = 1 ∨ D.main q Dec.KNIL = 1) → D.main q Dec.KEY = C.main r0 CTR →
      D.main q Dec.MODE + ofN 2 * D.main q Dec.TERM = 0 → (D.main q Dec.LVL).val = m →
      ∃ j, walkS ((memOf Mm).take (C.main r0 CTR).val) ask.b j =
        some ((D.main q Dec.PC).val, m, decide (D.main q Dec.BW = 1), (D.main q Dec.WC).val) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q hq hkn hkey hmf hlvl
    have hrec := h.chain_sent ⟨q, hq, by rcases hkn with a | a; exact .inl a; exact .inr (.inl a), rfl⟩
    rw [hmf] at hrec
    obtain ⟨j0, p, _, h0, hit⟩ := h.chain_back' hrec (h.cn_noind hq hkn)
      (by rcases h.kind_of_cn hq hkn with hd | hd <;> exact h.pc_lt hq hd (by decide))
    rw [hkey] at hit
    rcases h0 with ⟨qa, hqa, hka, e⟩ | ⟨q', hq', hcs, e⟩ <;> simp only [List.cons.injEq, and_true] at e
    · -- sent by the head's `Atom` row
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
      have hfa := decRowF_of h.dec hqa
      have hk2 : DKind D qa 2 := by
        obtain ⟨dk, hd⟩ := dkind_of hfa
        rw [hd.2.2.1] at hka
        have : dk = 2 := by by_cases e : dk = 2; exact e; rw [if_neg e] at hka; exact absurd hka (by decide)
        subst this; exact hd
      have hsum : D.main qa Dec.KCELL + D.main qa Dec.KATOM = 1 := by rw [hk2.2.1, hk2.2.2.1]; decide
      have h1 : D.main qa Dec.H1 = 1 := by
        rcases hfa.h1 with z | z <;> rw [z] at e2
        · exact absurd e2 (by decide)
        · exact z
      have hro : D.main qa Dec.RO = 1 := by
        rcases h.role_of hqa hsum with ⟨_, z, _⟩ | ⟨_, _, r⟩ | ⟨_, z, _⟩
        · rw [h1] at z; exact absurd z (by decide)
        · exact r
        · rw [h1] at z; exact absurd z (by decide)
      have hkey' : D.main qa Dec.KEY = C.main r0 CTR := by rw [← e0, hkey]
      obtain ⟨_, _, hpc⟩ := h.head_pc hr0 hp0 hR hc hqa hsum hro hkey'
      have hra := (h.atomRead hqa hk2).1
      rw [hkey'] at hra
      have eA : A = (D.main qa Dec.PC).val := iterI_det hA (readAtom_ind hask) hpc (readAtom_ind hra)
      rw [← eA, hask] at hra
      cases hra
      refine ⟨j0, ?_⟩
      rw [e1] at hit
      have := walkS_iter (H := (memOf Mm).take (C.main r0 CTR).val) (b0 := (D.main qa (Dec.DFLD + 45)).val) (j := 0)
        (l := 0) (bw := true) (wc := 0) j0 _ rfl hit
      rw [Nat.zero_add] at this
      rw [this, ← hlvl, e3, e5, e4, h1]
      rfl
    · -- sent by the `Cons` row one level below
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
      have hf' := decRowF_of h.dec hq'
      have hkc' := cons_of_csend hf' hcs
      have hml := bits2_zero hf'.mode hf'.last e2.symm
      have hlv := dec_level h.dec hq' hkc' hml.1
      unfold DecJet.W at hlv
      have hm : m = (D.main q' Dec.LVL).val + 1 := by rw [← hlvl, e3]; exact val_succ_lt hlv
      have hkey' : D.main q' Dec.KEY = C.main r0 CTR := by rw [← e0, hkey]
      obtain ⟨j', hw⟩ := ih _ (by omega) q' hq' (.inl hkc') hkey' (by rw [← h.cons_mf hq' hkc', hml.1]) rfl
      have hk3 : DKind D q' 3 := by
        rcases h.kind_of_cn hq' (.inl hkc') with hd | hd
        · exact hd
        · rw [hd.2.2.2.1] at hkc'; exact absurd hkc' (by decide)
      obtain ⟨_, hrc⟩ := h.consRead hq' hk3
      rw [hkey'] at hrc
      have hni := readCons_noind hrc
      have hstep := walkS_cons hw hni hrc
      -- the tail is not a list's end
      have hlast : lastAt ((memOf Mm).take (C.main r0 CTR).val) (D.main q' (Dec.DFLD + 29)).val = false := by
        have hs' : ChainSent D [D.main q' Dec.KEY, D.main q' (Dec.DFLD + 29),
            D.main q' Dec.MODE + ofN 2 * D.main q' Dec.ISLAST, D.main q' Dec.LVL + 1, D.main q' Dec.NBW,
            D.main q' Dec.WCN] := .inr (.inl ⟨q', hq', hcs, rfl⟩)
        rw [hml.1, hml.2, show (0 : F) + ofN 2 * 0 = 0 by decide, hkey'] at hs'
        have hl1 : D.main q' Dec.LVL + 1 ≠ 0 := by
          intro z; have h2 := val_succ_lt hlv; rw [z] at h2; exact absurd h2 (by show ¬ (0 = _ + 1); omega)
        show (List.range _).any _ = false
        refine List.any_eq_false.2 fun j _ => ?_
        cases hj : iterI ((memOf Mm).take (C.main r0 CTR).val) j (D.main q' (Dec.DFLD + 29)).val with
        | none => simp
        | some x =>
          simp only [Bool.not_eq_true]
          cases hx : isK ((memOf Mm).take (C.main r0 CTR).val) x with
          | false => rfl
          | true => exact absurd (h.chain_run_K j _ _ _ _ _ hs' hj hx) hl1
      rw [hlast] at hstep
      have hit' := walkS_iter (j := j' + 1) j0 p.val (H := (memOf Mm).take (C.main r0 CTR).val) (b0 := ask.b)
        (by rw [e1]; exact hstep) hit
      refine ⟨j' + 1 + j0, ?_⟩
      rw [hit', hm]
      -- the received state is the sent one
      have hwr : D.main q' Dec.WRITES = D.main q' Dec.BW := by
        rw [hf'.writes, hf'.dropped, hml.2, mul_zero', show ∀ x : F, x - 0 = x from fun x => by
          rw [sub_eq_add_neg']; show x + -0 = x; rw [show -(0 : F) = 0 by decide, add_zero']]
      have hPP : P = 2013265921 := rfl
      rw [e4, e5, hf'.nbw, hf'.wcn, hwr]
      have hwc := (h.chain_wc _ q' hq' (.inl hkc') (by rw [← h.cons_mf hq' hkc', hml.1]) rfl).2
      rcases hf'.bw with a | a <;> rcases hf'.bit with b | b <;> rw [a, b]
      · rw [show ofN 6 * (0 : F) = 0 by decide, add_zero']; rfl
      · rw [show ofN 6 * (0 : F) = 0 by decide, add_zero']; rfl
      · rw [show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]; rfl
      · rw [show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]; rfl

end

end Circuit
