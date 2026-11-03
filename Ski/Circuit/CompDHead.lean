import Ski.Circuit.CompDTree

/-!
# The circuit with the `dec` jet: the head's chain

At a jet row's key, the head atom's bits are read by a chain in mode `0`,
under a borrow from the bottom bit (`DecJet.decB`).

- **`DecJet.walk`**: the chain's states, level by level, as a function of
  the memory and the head's bits' root: the pointer, the borrow, and the
  cells written so far.
- **No chain row is a stray** (`CompDOK.on_walk`): every mode-`0` row at the
  key is at its level's state of the walk from the head's bits, by
  induction on the level, since each step was sent by the head's `Atom`
  row or by the row one level below.
- **The chain writes the decrement** (`CompDOK.head_fwd`): along the bits,
  each row under the borrow writes its rewritten `Cons` and the link to it,
  as `DecJet.bitCells` lays them out, and every level is below `32`.
-/

namespace DecJet

/-- **The head chain's states**: the pointer, the borrow and the cells
    written, at each level. -/
def walk (H : List Cell) (b0 : Nat) : Nat → Option (Nat × Bool × Nat)
  | 0 => some (b0, true, 0)
  | j + 1 =>
    match walk H b0 j with
    | some (a, bw, wc) =>
      match readCons H a with
      | some (b, sk) => some (sk.t, bw && !b, wc + if bw && !(b && isK H sk.t) then 6 else 0)
      | none => none
    | none => none

theorem walk_succ {H : List Cell} {b0 j a : Nat} {bw : Bool} {wc : Nat} {b : Bool} {sk : ConsSk}
    (hw : walk H b0 j = some (a, bw, wc)) (hc : readCons H a = some (b, sk)) :
    walk H b0 (j + 1) = some (sk.t, bw && !b, wc + if bw && !(b && isK H sk.t) then 6 else 0) := by
  show (match walk H b0 j with
    | some (a, bw, wc) =>
      match readCons H a with
      | some (b, sk) => some (sk.t, bw && !b, wc + if bw && !(b && isK H sk.t) then 6 else 0)
      | none => none
    | none => none) = _
  rw [hw]; dsimp only; rw [hc]

end DecJet

namespace Circuit

open B Air DecJet

section

variable {hd0 stk0 ctr0 n nilA J : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
  {C Mm Pg Wt Sg D : Table}
  (h : CompDOK hd0 stk0 ctr0 n nilA J heap N W roots C Mm Pg Wt Sg D)
  {r0 : Nat} (hr0 : r0 < C.h) (hp0 : C.main r0 DECSEL = 1)
include h hr0 hp0

/-- **No chain row is a stray**: a mode-`0` row at the key sits at its
    level's state of the walk from the head's bits. -/
theorem CompDOK.on_walk {csk : CellSk}
    (hc : readCell ((memOf Mm).take (C.main r0 CTR).val) (C.main r0 (FLD + 2)).val = some csk) :
    ∀ (m q : Nat), q < D.h → (D.main q Dec.KCONS = 1 ∨ D.main q Dec.KNIL = 1) → D.main q Dec.KEY = C.main r0 CTR →
      D.main q Dec.MODE = 0 → (D.main q Dec.LVL).val = m →
      ∃ ask, readAtom ((memOf Mm).take (C.main r0 CTR).val) csk.h = some ask ∧
        walk ((memOf Mm).take (C.main r0 CTR).val) ask.b m =
          some ((D.main q Dec.PC).val, decide (D.main q Dec.BW = 1), (D.main q Dec.WC).val) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro q hq hkn hkey hmode hlvl
    rcases h.chain_sent ⟨q, hq, hkn, rfl⟩ with ⟨qa, hqa, hka, e⟩ | ⟨q', hq', hcs, e⟩ <;>
      simp only [List.cons.injEq, and_true] at e
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
        rw [hmode] at e2
        rcases hfa.h1 with z | z <;> rw [z] at e2
        · exact absurd e2 (by decide)
        · exact z
      have hro : D.main qa Dec.RO = 1 := by
        rcases h.role_of hqa hsum with ⟨_, z, _⟩ | ⟨_, _, r⟩ | ⟨_, z, _⟩
        · rw [h1] at z; exact absurd z (by decide)
        · exact r
        · rw [h1] at z; exact absurd z (by decide)
      have hkey' : D.main qa Dec.KEY = C.main r0 CTR := by rw [← e0, hkey]
      have hpc := h.head_pc hr0 hp0 hc hqa hsum hro hkey'
      have hra := (h.atomRead hqa hk2).1
      rw [hkey', hpc] at hra
      refine ⟨_, hra, ?_⟩
      rw [← hlvl, e3, show (0 : F).val = 0 from rfl, e1, e4, h1, e5]
      rfl
    · -- sent by the row one level below
      obtain ⟨e0, e1, e2, e3, e4, e5⟩ := e
      have hf' := decRowF_of h.dec hq'
      obtain ⟨hkc', hl'⟩ := cons_of_csend hf' hcs
      have hm' : D.main q' Dec.MODE = 0 := by rw [← e2, hmode]
      have hlv := dec_level h.dec hq' hkc' hm'
      unfold DecJet.W at hlv
      have hm : m = (D.main q' Dec.LVL).val + 1 := by rw [← hlvl, e3]; exact val_succ_lt hlv
      have hkey' : D.main q' Dec.KEY = C.main r0 CTR := by rw [← e0, hkey]
      obtain ⟨ask, hra, hw⟩ := ih _ (by omega) q' hq' (.inl hkc') hkey' hm' rfl
      refine ⟨ask, hra, ?_⟩
      have hk3 : DKind D q' 3 := by
        obtain ⟨dk, hd⟩ := dkind_of hf'
        rw [hd.2.2.2.1] at hkc'
        have : dk = 3 := by by_cases e : dk = 3; exact e; rw [if_neg e] at hkc'; exact absurd hkc' (by decide)
        subst this; exact hd
      obtain ⟨_, hrc, _, hnl⟩ := h.consRead hq' hk3
      rw [hkey'] at hrc hnl
      have hnk := isK_app (hnl hl')
      rw [hm, walk_succ hw hrc, hnk]
      -- the received state is the sent one
      have hwc := (h.chain_wc _ _ _ _ _ _ (by rw [← hm']; exact h.chain_sent ⟨q', hq', .inl hkc', rfl⟩) rfl).2
      have hwr : D.main q' Dec.WRITES = D.main q' Dec.BW := by
        rw [hf'.writes, hf'.dropped, hl', mul_zero', show ∀ x : F, x - 0 = x from fun x => by
          rw [sub_eq_add_neg']; show x + -0 = x; rw [show -(0 : F) = 0 by decide, add_zero']]
      have hPP : P = 2013265921 := rfl
      rw [e1, e4, e5, hf'.nbw, hf'.wcn, hwr]
      rcases hf'.bw with a | a <;> rcases hf'.bit with b | b <;> rw [a, b]
      · rw [show ofN 6 * (0 : F) = 0 by decide, add_zero']; rfl
      · rw [show ofN 6 * (0 : F) = 0 by decide, add_zero']; rfl
      · rw [show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]; rfl
      · rw [show ofN 6 * (1 : F) = ofN 6 by decide, val_add_nat (by omega)]; rfl

end

end Circuit
