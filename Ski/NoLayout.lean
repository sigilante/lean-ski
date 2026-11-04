import Ski.Heap

/-!
# Why a term cannot lay out the `dec` jet's argument

The `dec` jet's row (`Ski/DecJet.lean`, `decRow`) reads its subject from
memory: the cells of `encNn s`, each wrapper (`atomT`'s `S (K K)` cells,
`cellT`'s `K`, a bit's `K b`) an application cell whose *function* is a
constant combinator and whose *argument* is the field.  Inside a compiled
loop the subject is a computed value, so a normaliser would have to write
those cells.  The machine (`Ski/Heap.lean`) writes exactly one application
cell per contraction, `y z` in `S x y z ⟶ x z (y z)`, from the stack
entries `y` and `z`; and the next head is `x`, the entry above them.

This module proves the invariant that settles what such a normaliser can
do.  Mark the input-dependent cells by a predicate `D` (an input's own
cells, and every cell built from one).  Then along the head and the stack,
top first, no input-independent entry ever follows an input-dependent one
(`Mono`), and no application cell has an input-dependent function over an
input-independent argument (`CellsOK`).  Both survive every transition
(`inv_step`), so they hold on every reachable state (`inv_reach`).

**`S_cont_const`**: whenever an `S` contraction writes a cell `y z` whose
function `y` is input-independent (a constant wrapper, as every wrapper of
`encNn` is), its continuation `x` is input-independent too.  So the
continuation that receives a freshly written wrapper is constant code:
it cannot be a dynamic return address carrying the rest of the
traversal, and everything input-dependent on the stack lies below the new
cell, where the head (always the top entry) cannot reach it without first
consuming the cell or folding it into the function position of another
cell (`y z` with `y` the new cell, read back only by running it).  A
dynamic continuation receives a fresh cell only inside such a fold, as the
thunk `K R w` (`release/nock/decloop/layout` in skinock exhibits the
12-combinator term that does it, and a search over all terms up to 10
leaves finds none that hands it over bare).  Laying out a two-field cell,
both fields computed, needs both: hence a jet row that reads `K R w` at its
slots, a circuit change, not a term.
-/

set_option linter.unusedSimpArgs false

namespace NoLayout

open Mach

/-- **The stack's order**: top first, once an entry (or the head, the flag
    `b`) is input-dependent, every entry below it is. -/
inductive Mono (D : Nat → Prop) (H : List Cell) : Nat → Prop → Prop
  | nil {s : Nat} {b : Prop} : H[s]? = some .nil → Mono D H s b
  | cons {s x r : Nat} {b : Prop} : H[s]? = some (.cons x r) → (b → D x) → Mono D H r (b ∨ D x) → Mono D H s b

/-- **The cells**: an input-dependent function has an input-dependent
    argument, and a cell with an input-dependent part is input-dependent. -/
def CellsOK (D : Nat → Prop) (H : List Cell) : Prop :=
  ∀ (a f x : Nat), H[a]? = some (.app f x) → (D f → D x) ∧ (D f ∨ D x → D a)

/-- Every pointer in a cell, and the cell itself, is below the heap's
    length. -/
def ptrsLt (n : Nat) : Cell → Prop
  | .app f x => f < n ∧ x < n
  | .cons x r => x < n ∧ r < n
  | _ => True

def WF (H : List Cell) : Prop := ∀ (a : Nat) (c : Cell), H[a]? = some c → ptrsLt H.length c

/-- **The invariant** of a state. -/
def Inv (D : Nat → Prop) (m : Mach) : Prop :=
  WF m.heap ∧ m.hd < m.heap.length ∧ m.stk < m.heap.length ∧ CellsOK D m.heap ∧ Mono D m.heap m.stk (D m.hd)

theorem Mono.weaken {D : Nat → Prop} {H : List Cell} {s : Nat} {b : Prop} (h : Mono D H s b) :
    ∀ {b' : Prop}, (b' → b) → Mono D H s b' := by
  induction h with
  | nil hs => intro b' _; exact .nil hs
  | cons hs hx _ ih =>
    intro b' hb
    exact .cons hs (fun h => hx (hb h)) (ih (fun h => h.elim (fun h => Or.inl (hb h)) Or.inr))

theorem lt_of_get {H : List Cell} {a : Nat} {c : Cell} (h : H[a]? = some c) : a < H.length := by
  rcases Nat.lt_or_ge a H.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem get_app_left {H : List Cell} {a : Nat} {c : Cell} (cs : List Cell) (h : H[a]? = some c) :
    (H ++ cs)[a]? = some c := by
  rw [List.getElem?_append_left (lt_of_get h)]; exact h

/-- `Mono` survives an append and a change of `D` above the old cells. -/
theorem Mono.transfer {D D' : Nat → Prop} {H : List Cell} (cs : List Cell) (hwf : WF H)
    (hD : ∀ a, a < H.length → (D a ↔ D' a)) {s : Nat} {b : Prop} (h : Mono D H s b) :
    Mono D' (H ++ cs) s b := by
  induction h with
  | nil hs => exact .nil (get_app_left cs hs)
  | cons hs hx _ ih =>
    have hxl := (hwf _ _ hs).1
    exact .cons (get_app_left cs hs) (fun hb => (hD _ hxl).1 (hx hb))
      (ih.weaken (fun h => h.elim Or.inl (fun h => Or.inr ((hD _ hxl).2 h))))

theorem WF.append {H : List Cell} (hwf : WF H) (cs : List Cell)
    (hcs : ∀ (i : Nat) (c : Cell), cs[i]? = some c → ptrsLt (H ++ cs).length c) : WF (H ++ cs) := by
  intro a c hc
  by_cases ha : a < H.length
  · rw [List.getElem?_append_left ha] at hc
    have := hwf a c hc
    cases c <;> simp only [ptrsLt, List.length_append] at this ⊢ <;> omega
  · rw [List.getElem?_append_right (by omega)] at hc
    exact hcs _ _ hc

theorem CellsOK.transfer {D D' : Nat → Prop} {H : List Cell} (cs : List Cell) (hwf : WF H)
    (hD : ∀ a, a < H.length → (D a ↔ D' a)) (h : CellsOK D H)
    (hcs : ∀ (i f x : Nat), cs[i]? = some (.app f x) → (D' f → D' x) ∧ (D' f ∨ D' x → D' (H.length + i))) :
    CellsOK D' (H ++ cs) := by
  intro a f x hc
  by_cases ha : a < H.length
  · rw [List.getElem?_append_left ha] at hc
    obtain ⟨hf, hx⟩ := hwf a _ hc
    obtain ⟨h1, h2⟩ := h a f x hc
    rw [← hD f hf, ← hD x hx, ← hD a ha]
    exact ⟨h1, h2⟩
  · rw [List.getElem?_append_right (by omega)] at hc
    have := hcs _ f x hc
    rwa [show H.length + (a - H.length) = a by omega] at this

/-- **The invariant survives a transition**, with `D` extended to the new
    cell `y z` of an `S` step (input-dependent when `y` or `z` is). -/
theorem inv_step {D : Nat → Prop} {m m' : Mach} (hI : Inv D m) (h : mstep m = some m') :
    ∃ D' : Nat → Prop, (∀ a, a < m.heap.length → (D a ↔ D' a)) ∧ Inv D' m' := by
  obtain ⟨hwf, hhd, hstk, hcells, hmono⟩ := hI
  unfold mstep Mach.get at h
  cases hc : m.heap[m.hd]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc] at h
    cases c with
    | app f x =>
      simp only [alloc, Option.some.injEq] at h; subst h
      obtain ⟨hfl, hxl⟩ := hwf _ _ hc
      obtain ⟨h1, h2⟩ := hcells _ f x hc
      refine ⟨D, fun _ _ => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact hwf.append [.cons x m.stk] (fun i c hi => by
          cases i with
          | zero => cases hi; simp [ptrsLt]; omega
          | succ i => simp at hi)
      · simp [alloc]; omega
      · simp [alloc]
      · exact hcells.transfer [.cons x m.stk] hwf (fun _ _ => Iff.rfl) (fun i f' x' hi => by
          cases i with
          | zero => cases hi
          | succ i => simp at hi)
      · simp only [alloc]
        refine .cons (x := x) (r := m.stk) (by simp) h1 ?_
        exact (hmono.transfer [.cons x m.stk] hwf (fun _ _ => Iff.rfl)).weaken h2
    | I =>
      cases hs : m.heap[m.stk]? with
      | none => simp [hs] at h
      | some sc =>
        simp only [hs] at h
        cases sc with
        | cons x s =>
          simp only [alloc, Option.some.injEq] at h; subst h
          obtain ⟨hxl, hsl⟩ := hwf _ _ hs
          refine ⟨D, fun _ _ => Iff.rfl, hwf, hxl, hsl, hcells, ?_⟩
          cases hmono with
          | nil h0 => rw [hs] at h0; cases h0
          | cons h0 hx hr =>
            rw [hs] at h0; cases h0
            exact hr.weaken Or.inr
        | _ => cases h
    | K =>
      cases hs : m.heap[m.stk]? with
      | none => simp [hs] at h
      | some sc =>
        simp only [hs] at h
        cases sc with
        | cons x s1 =>
          cases hs1 : m.heap[s1]? with
          | none => simp [hs1] at h
          | some sc1 =>
            simp only [hs1] at h
            cases sc1 with
            | cons y s2 =>
              simp only [alloc, Option.some.injEq] at h; subst h
              obtain ⟨hxl, _⟩ := hwf _ _ hs
              obtain ⟨_, hs2l⟩ := hwf _ _ hs1
              refine ⟨D, fun _ _ => Iff.rfl, hwf, hxl, hs2l, hcells, ?_⟩
              cases hmono with
              | nil h0 => rw [hs] at h0; cases h0
              | cons h0 _ hr =>
                rw [hs] at h0; cases h0
                cases hr with
                | nil h0 => rw [hs1] at h0; cases h0
                | cons h0 _ hr2 =>
                  rw [hs1] at h0; cases h0
                  exact hr2.weaken (fun h => Or.inl (Or.inr h))
            | _ => cases h
        | _ => cases h
    | S =>
      cases hs : m.heap[m.stk]? with
      | none => simp [hs] at h
      | some sc =>
        simp only [hs] at h
        cases sc with
        | cons x s1 =>
          cases hs1 : m.heap[s1]? with
          | none => simp [hs1] at h
          | some sc1 =>
            simp only [hs1] at h
            cases sc1 with
            | cons y s2 =>
              cases hs2 : m.heap[s2]? with
              | none => simp [hs2] at h
              | some sc2 =>
                simp only [hs2] at h
                cases sc2 with
                | cons z s3 =>
                  simp only [alloc, Option.some.injEq] at h; subst h
                  obtain ⟨hxl, _⟩ := hwf _ _ hs
                  obtain ⟨hyl, _⟩ := hwf _ _ hs1
                  obtain ⟨hzl, hs3l⟩ := hwf _ _ hs2
                  -- the order along the stack: `x`, `y`, `z`, then `s3`
                  obtain ⟨hdx, hdy, hdz, hr3⟩ : (D m.hd → D x) ∧ (D m.hd ∨ D x → D y) ∧
                      (D m.hd ∨ D x ∨ D y → D z) ∧ Mono D m.heap s3 (D m.hd ∨ D x ∨ D y ∨ D z) := by
                    cases hmono with
                    | nil h0 => rw [hs] at h0; cases h0
                    | cons h0 h0x hr =>
                      rw [hs] at h0; cases h0
                      cases hr with
                      | nil h1 => rw [hs1] at h1; cases h1
                      | cons h1 h1y hr1 =>
                        rw [hs1] at h1; cases h1
                        cases hr1 with
                        | nil h2 => rw [hs2] at h2; cases h2
                        | cons h2 h2z hr2 =>
                          rw [hs2] at h2; cases h2
                          refine ⟨h0x, h1y, fun h => h2z (h.elim (fun h => Or.inl (Or.inl h))
                            (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)), hr2.weaken ?_⟩
                          intro h
                          rcases h with h | h | h | h
                          · exact Or.inl (Or.inl (Or.inl h))
                          · exact Or.inl (Or.inl (Or.inr h))
                          · exact Or.inl (Or.inr h)
                          · exact Or.inr h
                  let n := m.heap.length
                  let D' : Nat → Prop := fun a => if a = n then (D y ∨ D z) else D a
                  have hD : ∀ a, a < n → (D a ↔ D' a) := fun a ha => by
                    simp only [D', if_neg (Nat.ne_of_lt ha)]
                  have hDy : D' y ↔ D y := (hD y hyl).symm
                  have hDz : D' z ↔ D z := (hD z hzl).symm
                  have hDx : D' x ↔ D x := (hD x hxl).symm
                  have hDn : D' n ↔ (D y ∨ D z) := by simp only [D', if_pos rfl]
                  let cs : List Cell := [.app y z, .cons n s3, .cons z (n + 1)]
                  have hheap : (((m.heap ++ [Cell.app y z]) ++ [Cell.cons n s3]) ++ [Cell.cons z (n + 1)]) =
                      m.heap ++ cs := by simp [cs]
                  refine ⟨D', hD, ?_⟩
                  simp only [alloc, List.length_append, List.length_singleton]
                  rw [hheap]
                  have hlen : (m.heap ++ cs).length = n + 3 := by simp [cs, n]
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · exact hwf.append cs (fun i c hi => by
                      rw [hlen]
                      match i, hi with
                      | 0, hi => cases hi; exact ⟨by omega, by omega⟩
                      | 1, hi => cases hi; exact ⟨by omega, by omega⟩
                      | 2, hi => cases hi; exact ⟨by omega, by omega⟩
                      | _ + 3, hi => simp [cs] at hi)
                  · dsimp only; rw [hlen]; omega
                  · dsimp only; rw [hlen]; omega
                  · refine hcells.transfer cs hwf hD (fun i f' x' hi => ?_)
                    match i, hi with
                    | 0, hi =>
                      simp only [cs, List.getElem?_cons_zero, Option.some.injEq, Cell.app.injEq] at hi
                      obtain ⟨rfl, rfl⟩ := hi
                      rw [hDy, hDz, Nat.add_zero, hDn]
                      exact ⟨fun h => hdz (Or.inr (Or.inr h)), id⟩
                    | 1, hi => simp [cs] at hi
                    | 2, hi => simp [cs] at hi
                    | _ + 3, hi => simp [cs] at hi
                  · have g2 : (m.heap ++ cs)[n + 2]? = some (.cons z (n + 1)) := by
                      rw [List.getElem?_append_right (by omega)]; simp [cs, n]
                    have g1 : (m.heap ++ cs)[n + 1]? = some (.cons n s3) := by
                      rw [List.getElem?_append_right (by omega)]; simp [cs, n]
                    refine .cons g2 (fun h => hDz.2 (hdz (Or.inr (Or.inl (hDx.1 h))))) ?_
                    refine .cons g1 (fun h => hDn.2 (Or.inr (h.elim (fun h => hdz (Or.inr (Or.inl (hDx.1 h)))) hDz.1))) ?_
                    refine (hr3.transfer cs hwf hD).weaken ?_
                    intro h
                    rcases h with (h | h) | h
                    · exact Or.inr (Or.inl (hDx.1 h))
                    · exact Or.inr (Or.inr (Or.inr (hDz.1 h)))
                    · rcases hDn.1 h with h | h
                      · exact Or.inr (Or.inr (Or.inl h))
                      · exact Or.inr (Or.inr (Or.inr h))
                | _ => cases h
            | _ => cases h
        | _ => cases h
    | _ => cases h

/-- States reachable by transitions. -/
inductive Reach : Mach → Mach → Prop
  | refl (m : Mach) : Reach m m
  | step {m m' m'' : Mach} : mstep m = some m' → Reach m' m'' → Reach m m''

/-- **The invariant holds on every reachable state**, with `D` extended to
    the cells the run writes and unchanged on the cells already there. -/
theorem inv_reach {m m' : Mach} (hr : Reach m m') :
    ∀ {D : Nat → Prop}, Inv D m → ∃ D' : Nat → Prop, (∀ a, a < m.heap.length → (D a ↔ D' a)) ∧ Inv D' m' := by
  induction hr with
  | refl m => intro D hI; exact ⟨D, fun _ _ => Iff.rfl, hI⟩
  | step h _ ih =>
    intro D hI
    obtain ⟨D1, hD1, hI1⟩ := inv_step hI h
    obtain ⟨D2, hD2, hI2⟩ := ih hI1
    obtain ⟨cs, hcs⟩ := mstep_append h
    refine ⟨D2, fun a ha => (hD1 a ha).trans (hD2 a ?_), hI2⟩
    rw [hcs, List.length_append]; omega

/-- **The continuation of an `S` over a constant function is constant**: at
    an `S` contraction `S x y z`, an input-independent `y` (the function of
    the cell `y z` the step writes) forces an input-independent `x`. -/
theorem S_cont_const {D : Nat → Prop} {m : Mach} (hI : Inv D m) {x s1 y s2 : Nat}
    (hs : m.heap[m.stk]? = some (.cons x s1)) (hs1 : m.heap[s1]? = some (.cons y s2)) (hy : ¬ D y) : ¬ D x := by
  obtain ⟨_, _, _, _, hmono⟩ := hI
  cases hmono with
  | nil h0 => rw [hs] at h0; cases h0
  | cons h0 _ hr =>
    rw [hs] at h0; cases h0
    cases hr with
    | nil h1 => rw [hs1] at h1; cases h1
    | cons h1 h1y _ =>
      rw [hs1] at h1; cases h1
      exact fun hx => hy (h1y (Or.inr hx))

/-- **On a run**: from a state satisfying the invariant (the program's
    cells input-independent, the input's cells input-dependent, the stack in
    order), every `S` contraction that writes a constant-function cell has a
    constant continuation. -/
theorem run_S_cont_const {D : Nat → Prop} {m m' : Mach} (hI : Inv D m) (hr : Reach m m') :
    ∃ D' : Nat → Prop, (∀ a, a < m.heap.length → (D a ↔ D' a)) ∧
      ∀ {x s1 y s2 : Nat}, m'.heap[m'.stk]? = some (.cons x s1) → m'.heap[s1]? = some (.cons y s2) →
        ¬ D' y → ¬ D' x := by
  obtain ⟨D', hD', hI'⟩ := inv_reach hr hI
  exact ⟨D', hD', fun hs hs1 hy => S_cont_const hI' hs hs1 hy⟩

end NoLayout
