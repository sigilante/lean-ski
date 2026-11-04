import Ski.Circuit.CompDMatch

/-!
# The circuit with the `dec` jet: indirection chains end

An indirection row passes a need or a chain's step on, unchanged but for
the pointer, from a `K`-thunk to its target.  Reading backwards from a row
that is not an indirection, the senders could in principle go round a
cycle of thunks forever; they cannot, because the target of a thunk is a
function of the memory (`DecJet.readInd`): a run of more thunk steps than
there are cells repeats a cell (`pigeon`), so the point it reaches is on a
cycle of thunks and is itself a thunk (`iterI_long`).  A `Cons`, a nil, a
`Cell` or an `Atom` is not.

- **`CompDOK.chain_back`**: a chain's step received at a pointer that is
  not a thunk was sent, through a run of thunks at most as long as the
  memory below the key, by an `Atom` row or a `Cons` row.
- **`CompDOK.need_back`**: a need received at a pointer that is not a
  thunk was sent the same way by the CPU's jet row or a `Cell` row.
-/

namespace DecJet

/-- **`n` thunk steps from `x`.** -/
def iterI (H : List Cell) : Nat → Nat → Option Nat
  | 0, x => some x
  | n + 1, x =>
    match readInd H x with
    | some y => iterI H n y
    | none => none

theorem iterI_succ {H : List Cell} {n x y : Nat} (h : readInd H x = some y) : iterI H (n + 1) x = iterI H n y := by
  show (match readInd H x with | some y => iterI H n y | none => none) = _
  rw [h]

theorem iterI_add {H : List Cell} : ∀ (m n x : Nat) {y : Nat}, iterI H m x = some y → iterI H (m + n) x = iterI H n y
  | 0, n, x, y, h => by cases h; rw [Nat.zero_add]
  | m + 1, n, x, y, h => by
    cases hi : readInd H x with
    | none =>
      have : iterI H (m + 1) x = none := by
        show (match readInd H x with | some y => iterI H m y | none => none) = _
        rw [hi]
      rw [this] at h; cases h
    | some z =>
      rw [iterI_succ hi] at h
      rw [show m + 1 + n = (m + n) + 1 by omega, iterI_succ hi]
      exact iterI_add m n z h

theorem readInd_lt {H : List Cell} {x y : Nat} (h : readInd H x = some y) : x < H.length := by
  obtain ⟨f, w, k, hp, _, _⟩ := readInd_eq h
  exact (List.getElem?_eq_some_iff.1 hp).1

/-- **Pigeonhole**: `N + 1` values below `N` repeat. -/
theorem pigeon : ∀ (N : Nat) (g : Nat → Nat), (∀ i, i ≤ N → g i < N) → ∃ i j, i < j ∧ j ≤ N ∧ g i = g j
  | 0, g, h => absurd (h 0 (Nat.le_refl _)) (Nat.not_lt_zero _)
  | N + 1, g, h => by
    cases hb : (List.range (N + 1)).any (fun i => g i == g (N + 1)) with
    | true =>
      obtain ⟨i, hi, e⟩ := List.any_eq_true.1 hb
      exact ⟨i, N + 1, List.mem_range.1 hi, Nat.le_refl _, beq_iff_eq.1 e⟩
    | false =>
      have hne : ∀ i, i ≤ N → g i ≠ g (N + 1) := by
        intro i hi e
        have := List.any_eq_false.1 hb i (List.mem_range.2 (by omega))
        rw [e] at this; exact this (beq_self_eq_true _)
      let g' : Nat → Nat := fun i => if g i = N then g (N + 1) else g i
      have hg' : ∀ i, i ≤ N → g' i < N := by
        intro i hi
        show (if g i = N then g (N + 1) else g i) < N
        have h1 := h i (by omega)
        have h2 := h (N + 1) (Nat.le_refl _)
        split
        · next e =>
          have : g (N + 1) ≠ N := fun e' => hne i hi (by rw [e, e'])
          omega
        · next e => omega
      obtain ⟨i, j, hij, hj, e⟩ := pigeon N g' hg'
      refine ⟨i, j, hij, by omega, ?_⟩
      simp only [g'] at e
      by_cases a : g i = N <;> by_cases b : g j = N <;> simp only [a, b, if_true, if_false] at e
      · rw [a, b]
      · exact absurd e.symm (hne j hj)
      · exact absurd e (hne i (by omega))
      · exact e

/-- A point on a cycle of thunks is a thunk, and so is every point after it. -/
theorem periodic_after {H : List Cell} {a z : Nat} (hz : iterI H (a + 1) z = some z) :
    ∀ (b : Nat) {w : Nat}, iterI H b z = some w → ∃ c, iterI H (c + 1) w = some w
  | 0, w, h => by cases h; exact ⟨a, hz⟩
  | b + 1, w, h => by
    cases hi : readInd H z with
    | none =>
      have : iterI H (b + 1) z = none := by
        show (match readInd H z with | some y => iterI H b y | none => none) = _
        rw [hi]
      rw [this] at h; cases h
    | some z' =>
      rw [iterI_succ hi] at h
      have hz' : iterI H (a + 1) z' = some z' := by
        rw [iterI_succ hi] at hz
        have := iterI_add a 1 z' hz
        rw [this, iterI_succ hi]; rfl
      exact periodic_after hz' b h

theorem iterI_none {H : List Cell} : ∀ {i x : Nat}, iterI H i x = none → ∀ n, iterI H (i + n) x = none
  | 0, x, h, _ => by cases h
  | i + 1, x, h, n => by
    cases hi : readInd H x with
    | none =>
      rw [show i + 1 + n = (i + n) + 1 by omega]
      show (match readInd H x with | some y => iterI H (i + n) y | none => none) = _
      rw [hi]
    | some z =>
      rw [iterI_succ hi] at h
      rw [show i + 1 + n = (i + n) + 1 by omega, iterI_succ hi]
      exact iterI_none h n

/-- **A run of thunks longer than the memory ends at a thunk.** -/
theorem iterI_long {H : List Cell} {x p : Nat} (h : iterI H (H.length + 1) x = some p) : readInd H p ≠ none := by
  -- the points along the run
  have hpt : ∀ i, i ≤ H.length + 1 → ∃ y, iterI H i x = some y := by
    intro i hi
    cases e : iterI H i x with
    | some y => exact ⟨y, rfl⟩
    | none =>
      exfalso
      have := iterI_none e (H.length + 1 - i)
      rw [show H.length + 1 = i + (H.length + 1 - i) by omega, this] at h
      cases h
  let g : Nat → Nat := fun i => (iterI H i x).getD 0
  have hg : ∀ i, i ≤ H.length → g i < H.length := by
    intro i hi
    obtain ⟨y, hy⟩ := hpt i (by omega)
    obtain ⟨y', hy'⟩ := hpt (i + 1) (by omega)
    have e := iterI_add i 1 x hy
    rw [hy'] at e
    cases hr : readInd H y with
    | none =>
      have : iterI H 1 y = none := by
        show (match readInd H y with | some y => iterI H 0 y | none => none) = _
        rw [hr]
      rw [this] at e; cases e
    | some _ => show (iterI H i x).getD 0 < _; rw [hy]; exact readInd_lt hr
  obtain ⟨i, j, hij, hj, e⟩ := pigeon H.length g hg
  obtain ⟨yi, hyi⟩ := hpt i (by omega)
  obtain ⟨yj, hyj⟩ := hpt j (by omega)
  have e' : yi = yj := by
    have : g i = yi := by show (iterI H i x).getD 0 = _; rw [hyi]; rfl
    have h2 : g j = yj := by show (iterI H j x).getD 0 = _; rw [hyj]; rfl
    rw [← this, ← h2, e]
  subst e'
  have hcyc : iterI H (j - i - 1 + 1) yi = some yi := by
    have := iterI_add i (j - i) x hyi
    rw [show i + (j - i) = j by omega, hyj] at this
    rw [show j - i - 1 + 1 = j - i by omega]; exact this.symm
  have hp : iterI H (H.length + 1 - i) yi = some p := by
    have := iterI_add i (H.length + 1 - i) x hyi
    rw [show i + (H.length + 1 - i) = H.length + 1 by omega, h] at this
    exact this.symm
  obtain ⟨c, hc⟩ := periodic_after hcyc _ hp
  intro hn
  have : iterI H (c + 1) p = none := by
    show (match readInd H p with | some y => iterI H c y | none => none) = _
    rw [hn]
  rw [this] at hc; cases hc

end DecJet

namespace Circuit

open B Air DecJet

/-- A chain's step sent by an `Atom` or a `Cons` row: not by an indirection. -/
def ChainSent0 (D : Table) (v : List F) : Prop :=
  (∃ q, q < D.h ∧ D.main q Dec.KATOM = 1 ∧
    v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 45), 1 - D.main q Dec.H1, 0, D.main q Dec.H1, 0]) ∨
  (∃ q, q < D.h ∧ D.main q Dec.CSEND = 1 ∧
    v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 29), D.main q Dec.MODE + ofN 2 * D.main q Dec.ISLAST,
      D.main q Dec.LVL + 1, D.main q Dec.NBW, D.main q Dec.WCN])

/-- A need sent by the CPU's jet row or a `Cell` row: not by an indirection. -/
def NeedSent0 (C D : Table) (v : List F) : Prop :=
  (∃ r, r < C.h ∧ C.main r DECSEL = 1 ∧ v = [C.main r CTR, C.main r (FLD + 2), 0]) ∨
  (∃ q, q < D.h ∧ D.main q Dec.KCELL = 1 ∧
    (v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 43), ofN 2 - D.main q Dec.H0] ∨
      v = [D.main q Dec.KEY, D.main q (Dec.DFLD + 53), ofN 2]))

theorem kind5_of {D : Table} {q : Nat} (hf : DecRowF D q) (h : D.main q Dec.KIND = 1) : DKind D q 5 := by
  obtain ⟨dk, hd⟩ := dkind_of hf
  rw [hd.2.2.2.2.2] at h
  have : dk = 5 := by by_cases e : dk = 5; exact e; rw [if_neg e] at h; exact absurd h (by decide)
  subst this; exact hd

theorem kind_of_inb {D : Table} {q : Nat} (hf : DecRowF D q) (h : D.main q Dec.INB = 1) : DKind D q 5 := by
  apply kind5_of hf
  rw [hf.inb] at h
  rcases hf.kind with a | a <;> rcases hf.ib with b | b <;> rw [a, b] at h <;> first | exact absurd h (by decide) | exact a

theorem kind_of_inn {D : Table} {q : Nat} (hf : DecRowF D q) (h : D.main q Dec.INN = 1) : DKind D q 5 := by
  apply kind5_of hf
  rw [hf.inn] at h
  rcases hf.kind with a | a <;> rcases hf.ib with b | b <;> rw [a, b] at h <;> first | exact absurd h (by decide) | exact a

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
include h

theorem CompDOK.kind_of_ka {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCELL + D.main q Dec.KATOM = 1) :
    DKind D q 1 ∨ DKind D q 2 := by
  obtain ⟨dk, hd⟩ := dkind_of (decRowF_of h.dec hq)
  rw [hd.2.1, hd.2.2.1] at hk
  rcases (show dk = 0 ∨ dk = 1 ∨ dk = 2 ∨ dk = 3 ∨ dk = 4 ∨ dk = 5 by have := hd.1; omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd hk (by decide)
  · exact .inl hd
  · exact .inr hd
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

theorem CompDOK.kind_of_cn {q : Nat} (hq : q < D.h) (hk : D.main q Dec.KCONS = 1 ∨ D.main q Dec.KNIL = 1) :
    DKind D q 3 ∨ DKind D q 4 := by
  obtain ⟨dk, hd⟩ := dkind_of (decRowF_of h.dec hq)
  rw [hd.2.2.2.1, hd.2.2.2.2.1] at hk
  rcases (show dk = 0 ∨ dk = 1 ∨ dk = 2 ∨ dk = 3 ∨ dk = 4 ∨ dk = 5 by have := hd.1; omega) with
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inl hd
    | exact .inr hd
    | (rcases hk with hk | hk <;> exact absurd hk (by decide))

/-- One step back along a chain: a step was sent by an `Atom` or `Cons`
    row, or by an indirection at a thunk whose target is the step's pointer,
    which itself received the step. -/
theorem CompDOK.chain_step {k x mf l bw wc : F} (hs : ChainSent D [k, x, mf, l, bw, wc]) :
    ChainSent0 D [k, x, mf, l, bw, wc] ∨
      ∃ x' : F, readInd ((memOf Mm).take k.val) x'.val = some x.val ∧ ChainSent D [k, x', mf, l, bw, wc] := by
  rcases hs with hs | hs | ⟨q, hq, hk, e⟩
  · exact .inl (.inl hs)
  · exact .inl (.inr hs)
  · right
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
    have hi := (h.indRead hq (kind_of_inb (decRowF_of h.dec hq) hk)).1
    refine ⟨D.main q Dec.PC, by rw [e0, e1]; exact hi, ?_⟩
    have := h.chain_sent ⟨q, hq, .inr (.inr hk), rfl⟩
    rw [← e0, ← e2, ← e3, ← e4, ← e5] at this
    exact this

/-- **A chain's step goes back to an `Atom` or `Cons` row**, through at most
    `n` thunks, or through more than `n`. -/
theorem CompDOK.chain_back (k mf l bw wc : F) : ∀ (n : Nat) (x : F), ChainSent D [k, x, mf, l, bw, wc] →
    (∃ (m : Nat) (p : F), m ≤ n ∧ ChainSent0 D [k, p, mf, l, bw, wc] ∧ iterI ((memOf Mm).take k.val) m p.val = some x.val) ∨
    (∃ y, iterI ((memOf Mm).take k.val) (n + 1) y = some x.val) := by
  intro n
  induction n with
  | zero =>
    intro x hs
    rcases h.chain_step hs with h0 | ⟨x', hi, _⟩
    · exact .inl ⟨0, x, Nat.le_refl _, h0, rfl⟩
    · exact .inr ⟨x'.val, by rw [iterI_succ hi]; rfl⟩
  | succ n ih =>
    intro x hs
    rcases h.chain_step hs with h0 | ⟨x', hi, hs'⟩
    · exact .inl ⟨0, x, Nat.zero_le _, h0, rfl⟩
    · rcases ih x' hs' with ⟨m, p, hm, h0, hp⟩ | ⟨y, hy⟩
      · refine .inl ⟨m + 1, p, by omega, h0, ?_⟩
        rw [iterI_add m 1 _ hp, iterI_succ hi]; rfl
      · refine .inr ⟨y, ?_⟩
        rw [iterI_add (n + 1) 1 _ hy, iterI_succ hi]; rfl

/-- **A step received at a non-thunk** was sent by an `Atom` or `Cons` row,
    through at most as many thunks as the memory below the key has cells. -/
theorem CompDOK.chain_back' {k x mf l bw wc : F} (hs : ChainSent D [k, x, mf, l, bw, wc])
    (hx : readInd ((memOf Mm).take k.val) x.val = none) :
    ∃ (m : Nat) (p : F), ChainSent0 D [k, p, mf, l, bw, wc] ∧ iterI ((memOf Mm).take k.val) m p.val = some x.val := by
  rcases h.chain_back k mf l bw wc _ x hs with ⟨m, p, _, h0, hp⟩ | ⟨y, hy⟩
  · exact ⟨m, p, h0, hp⟩
  · exact absurd hx (iterI_long hy)

/-- One step back along the need tree. -/
theorem CompDOK.need_step {k x ρ : F} (hs : NeedSent C D [k, x, ρ]) :
    NeedSent0 C D [k, x, ρ] ∨
      ∃ x' : F, readInd ((memOf Mm).take k.val) x'.val = some x.val ∧ NeedSent C D [k, x', ρ] := by
  rcases hs with hs | hs | ⟨q, hq, hk, e⟩
  · exact .inl (.inl hs)
  · exact .inl (.inr hs)
  · right
    simp only [List.cons.injEq, and_true] at e
    obtain ⟨e0, e1, e2⟩ := e
    have hi := (h.indRead hq (kind_of_inn (decRowF_of h.dec hq) hk)).1
    refine ⟨D.main q Dec.PC, by rw [e0, e1]; exact hi, ?_⟩
    have := h.need_sent ⟨q, hq, .inr hk, rfl⟩
    rw [← e0, ← e2] at this
    exact this

theorem CompDOK.need_back (k ρ : F) : ∀ (n : Nat) (x : F), NeedSent C D [k, x, ρ] →
    (∃ (m : Nat) (p : F), NeedSent0 C D [k, p, ρ] ∧ iterI ((memOf Mm).take k.val) m p.val = some x.val) ∨
    (∃ y, iterI ((memOf Mm).take k.val) (n + 1) y = some x.val) := by
  intro n
  induction n with
  | zero =>
    intro x hs
    rcases h.need_step hs with h0 | ⟨x', hi, _⟩
    · exact .inl ⟨0, x, h0, rfl⟩
    · exact .inr ⟨x'.val, by rw [iterI_succ hi]; rfl⟩
  | succ n ih =>
    intro x hs
    rcases h.need_step hs with h0 | ⟨x', hi, hs'⟩
    · exact .inl ⟨0, x, h0, rfl⟩
    · rcases ih x' hs' with ⟨m, p, h0, hp⟩ | ⟨y, hy⟩
      · refine .inl ⟨m + 1, p, h0, ?_⟩
        rw [iterI_add m 1 _ hp, iterI_succ hi]; rfl
      · refine .inr ⟨y, ?_⟩
        rw [iterI_add (n + 1) 1 _ hy, iterI_succ hi]; rfl

/-- **A need received at a non-thunk** was sent by the CPU or a `Cell` row,
    through a run of thunks. -/
theorem CompDOK.need_back' {k x ρ : F} (hs : NeedSent C D [k, x, ρ])
    (hx : readInd ((memOf Mm).take k.val) x.val = none) :
    ∃ (m : Nat) (p : F), NeedSent0 C D [k, p, ρ] ∧ iterI ((memOf Mm).take k.val) m p.val = some x.val := by
  rcases h.need_back k ρ _ x hs with ⟨m, p, h0, hp⟩ | ⟨y, hy⟩
  · exact ⟨m, p, h0, hp⟩
  · exact absurd hx (iterI_long hy)

end

end Circuit
