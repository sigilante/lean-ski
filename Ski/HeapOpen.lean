import Ski.Heap
import Ski.Abs

open Term

/-!
# The heap machine on open terms: atoms as probe markers

A closed term is read back by applying it to fresh markers and seeing which
one reaches the head: SKIjack's `run.decode` and Avon's probes (§17 of
`avon/DESIGN.md`).  A marker must be inert, and no closed `{S, K, I}` term
is, so the machine has an `atom` cell with no rule.  A state with atoms
reads back as an open term (`OTerm`), each atom `n` as the variable `n`,
and the variables are inert under open head reduction (`OStep`).

**The theorems.**
- `omstep_some`: every transition of the machine is an unwind, which keeps
  the open term the state reads back, or a contraction, which is one
  `OStep`.
- `odecode_oload`: an open term loaded into the machine reads back as
  itself.
- `omachine_run`: every state reachable from the loaded term reads back as
  an open-head-reduct of it.
- `atom_head`: a state whose head cell is the atom `i` reads back as the
  variable `i` applied to the state's arguments, so no rule applies to it
  (`ONeutral.no_step`).

So a run of `t X₁ … Xₙ` that halts with the atom `i` at the head proves
`t X₁ … Xₙ ⟶* Xᵢ a₁ … aₖ`.  That is how a probe names a Scott
constructor: by the marker its datum selects.
-/

namespace Mach

/-- The open term stored at an address; an atom reads as a variable. -/
def otermAt (heap : List Cell) : Nat → Nat → Option OTerm
  | 0, _ => none
  | f + 1, a =>
    match heap[a]? with
    | some .S => some .S
    | some .K => some .K
    | some .I => some .I
    | some (.atom n) => some (.var n)
    | some (.app g x) =>
      match otermAt heap f g, otermAt heap f x with
      | some tg, some tx => some (tg ⬝ₒ tx)
      | _, _ => none
    | _ => none

/-- The arguments on the stack, top first, as open terms. -/
def ostackAt (heap : List Cell) : Nat → Nat → Option (List OTerm)
  | 0, _ => none
  | f + 1, a =>
    match heap[a]? with
    | some .nil => some []
    | some (.cons x r) =>
      match otermAt heap (f + 1) x, ostackAt heap f r with
      | some tx, some rest => some (tx :: rest)
      | _, _ => none
    | _ => none

/-- The open term a state denotes. -/
def odecode (m : Mach) : Option OTerm :=
  match otermAt m.heap (m.heap.length + 1) m.hd, ostackAt m.heap (m.heap.length + 1) m.stk with
  | some h, some args => some (appL h args)
  | _, _ => none

theorem otermAt_append : ∀ {f : Nat} {heap cs : List Cell} {a : Nat} {t : OTerm},
    otermAt heap f a = some t → otermAt (heap ++ cs) f a = some t
  | 0, _, _, _, _, h => by cases h
  | f + 1, heap, cs, a, t, h => by
    unfold otermAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      rw [get_append hc]
      cases c with
      | S => exact h
      | K => exact h
      | I => exact h
      | atom _ => exact h
      | app g x =>
        dsimp only at h ⊢
        cases hg : otermAt heap f g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : otermAt heap f x with
          | none => rw [hg, hx] at h; cases h
          | some tx =>
            rw [hg, hx] at h
            rw [otermAt_append hg, otermAt_append hx]
            exact h
      | nil => cases h
      | cons _ _ => cases h

theorem otermAt_mono : ∀ {f k : Nat} {heap : List Cell} {a : Nat} {t : OTerm},
    otermAt heap f a = some t → f ≤ k → otermAt heap k a = some t
  | 0, _, _, _, _, h, _ => by cases h
  | f + 1, 0, _, _, _, _, hle => by omega
  | f + 1, k + 1, heap, a, t, h, hle => by
    unfold otermAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | S => exact h
      | K => exact h
      | I => exact h
      | atom _ => exact h
      | app g x =>
        dsimp only at h ⊢
        cases hg : otermAt heap f g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : otermAt heap f x with
          | none => rw [hg, hx] at h; cases h
          | some tx =>
            rw [hg, hx] at h
            rw [otermAt_mono hg (by omega), otermAt_mono hx (by omega)]
            exact h
      | nil => cases h
      | cons _ _ => cases h

theorem ostackAt_append : ∀ {f : Nat} {heap cs : List Cell} {a : Nat} {ts : List OTerm},
    ostackAt heap f a = some ts → ostackAt (heap ++ cs) f a = some ts
  | 0, _, _, _, _, h => by cases h
  | f + 1, heap, cs, a, ts, h => by
    unfold ostackAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      rw [get_append hc]
      cases c with
      | nil => exact h
      | cons x r =>
        dsimp only at h ⊢
        cases hx : otermAt heap (f + 1) x with
        | none => rw [hx] at h; cases h
        | some tx =>
          cases hr : ostackAt heap f r with
          | none => rw [hx, hr] at h; cases h
          | some rest =>
            rw [hx, hr] at h
            rw [otermAt_append hx, ostackAt_append hr]
            exact h
      | _ => cases h

theorem ostackAt_mono : ∀ {f k : Nat} {heap : List Cell} {a : Nat} {ts : List OTerm},
    ostackAt heap f a = some ts → f ≤ k → ostackAt heap k a = some ts
  | 0, _, _, _, _, h, _ => by cases h
  | f + 1, 0, _, _, _, _, hle => by omega
  | f + 1, k + 1, heap, a, ts, h, hle => by
    unfold ostackAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | nil => exact h
      | cons x r =>
        dsimp only at h ⊢
        cases hx : otermAt heap (f + 1) x with
        | none => rw [hx] at h; cases h
        | some tx =>
          cases hr : ostackAt heap f r with
          | none => rw [hx, hr] at h; cases h
          | some rest =>
            rw [hx, hr] at h
            rw [otermAt_mono hx (by omega), ostackAt_mono hr (by omega)]
            exact h
      | _ => cases h

theorem otermAt_grow {heap cs : List Cell} {f k a : Nat} {t : OTerm}
    (h : otermAt heap f a = some t) (hk : f ≤ k) : otermAt (heap ++ cs) k a = some t :=
  otermAt_mono (otermAt_append h) hk

theorem ostackAt_grow {heap cs : List Cell} {f k a : Nat} {ts : List OTerm}
    (h : ostackAt heap f a = some ts) (hk : f ≤ k) : ostackAt (heap ++ cs) k a = some ts :=
  ostackAt_mono (ostackAt_append h) hk

theorem otermAt_cell {heap : List Cell} {f a : Nat} {t : OTerm} (h : otermAt heap (f + 1) a = some t) :
    (heap[a]? = some .S ∧ t = .S) ∨ (heap[a]? = some .K ∧ t = .K) ∨ (heap[a]? = some .I ∧ t = .I) ∨
    (∃ n, heap[a]? = some (.atom n) ∧ t = .var n) ∨
    ∃ g x tg tx, heap[a]? = some (.app g x) ∧ otermAt heap f g = some tg ∧
      otermAt heap f x = some tx ∧ t = tg ⬝ₒ tx := by
  unfold otermAt at h
  cases hc : heap[a]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    cases c with
    | S => cases h; exact .inl ⟨rfl, rfl⟩
    | K => cases h; exact .inr (.inl ⟨rfl, rfl⟩)
    | I => cases h; exact .inr (.inr (.inl ⟨rfl, rfl⟩))
    | atom n => cases h; exact .inr (.inr (.inr (.inl ⟨n, rfl, rfl⟩)))
    | app g x =>
      dsimp only at h
      cases hg : otermAt heap f g with
      | none => rw [hg] at h; cases h
      | some tg =>
        cases hx : otermAt heap f x with
        | none => rw [hg, hx] at h; cases h
        | some tx =>
          rw [hg, hx] at h
          cases h
          exact .inr (.inr (.inr (.inr ⟨g, x, tg, tx, rfl, hg, hx, rfl⟩)))
    | nil => cases h
    | cons _ _ => cases h

theorem ostackAt_cell {heap : List Cell} {f a : Nat} {ts : List OTerm}
    (h : ostackAt heap (f + 1) a = some ts) :
    (heap[a]? = some .nil ∧ ts = []) ∨
    ∃ x r tx rest, heap[a]? = some (.cons x r) ∧ otermAt heap (f + 1) x = some tx ∧
      ostackAt heap f r = some rest ∧ ts = tx :: rest := by
  unfold ostackAt at h
  cases hc : heap[a]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    cases c with
    | nil => cases h; exact .inl ⟨rfl, rfl⟩
    | cons x r =>
      dsimp only at h
      cases hx : otermAt heap (f + 1) x with
      | none => rw [hx] at h; cases h
      | some tx =>
        cases hr : ostackAt heap f r with
        | none => rw [hx, hr] at h; cases h
        | some rest =>
          rw [hx, hr] at h
          cases h
          exact .inr ⟨x, r, tx, rest, rfl, hx, hr, rfl⟩
    | _ => cases h

theorem odecode_eq {m : Mach} {t : OTerm} (h : odecode m = some t) :
    ∃ hd args, otermAt m.heap (m.heap.length + 1) m.hd = some hd ∧
      ostackAt m.heap (m.heap.length + 1) m.stk = some args ∧ t = appL hd args := by
  unfold odecode at h
  cases h1 : otermAt m.heap (m.heap.length + 1) m.hd with
  | none => rw [h1] at h; cases h
  | some hd =>
    cases h2 : ostackAt m.heap (m.heap.length + 1) m.stk with
    | none => rw [h1, h2] at h; cases h
    | some args =>
      rw [h1, h2] at h
      cases h
      exact ⟨hd, args, rfl, rfl, rfl⟩

theorem odecode_of {m : Mach} {hd : OTerm} {args : List OTerm}
    (h1 : otermAt m.heap (m.heap.length + 1) m.hd = some hd)
    (h2 : ostackAt m.heap (m.heap.length + 1) m.stk = some args) :
    odecode m = some (appL hd args) := by
  unfold odecode; rw [h1, h2]

/-- A step at the head of a spine is a step of the spine. -/
theorem OStep.appL : ∀ (as : List OTerm) {t u : OTerm}, OStep t u → OStep (appL t as) (appL u as)
  | [], _, _, h => h
  | a :: as, _, _, h => OStep.appL as (.left a h)

theorem ONeutral.appL : ∀ (as : List OTerm) {t : OTerm}, ONeutral t → ONeutral (appL t as)
  | [], _, h => h
  | a :: as, _, h => ONeutral.appL as (.app a h)

-- ---------------------------------------------------------------------------
-- Each transition is an unwind or an open head step
-- ---------------------------------------------------------------------------

/-- **Each transition is an unwind or a contraction**, read back as open
    terms: an unwind keeps the open term, a contraction is one `OStep`. -/
theorem omstep_some {m m' : Mach} {t : OTerm} (hdec : odecode m = some t) (hm : mstep m = some m') :
    odecode m' = some t ∨ ∃ u, OStep t u ∧ odecode m' = some u := by
  match odecode_eq hdec with
  | ⟨h, args, h1, h2, ht⟩ =>
    subst ht
    have hmm : mstep m = some m' := hm
    unfold mstep get at hmm
    match otermAt_cell h1 with
    | .inr (.inr (.inr (.inr ⟨g, x, tg, tx, hc, hg, hx, hh⟩))) =>
      -- unwind
      subst hh
      rw [hc] at hmm
      dsimp only [alloc] at hmm
      cases hmm
      left
      have eg : otermAt (m.heap ++ [Cell.cons x m.stk])
          ((m.heap ++ [Cell.cons x m.stk]).length + 1) g = some tg :=
        otermAt_grow hg (by rw [length_concat]; omega)
      have es : ostackAt (m.heap ++ [Cell.cons x m.stk]) ((m.heap ++ [Cell.cons x m.stk]).length + 1)
          m.heap.length = some (tx :: args) := by
        rw [length_concat]
        unfold ostackAt
        rw [getElem?_concat]
        dsimp only
        rw [otermAt_grow hx (by omega), ostackAt_grow h2 (by omega)]
      exact odecode_of (m := ⟨m.heap ++ [Cell.cons x m.stk], g, m.heap.length⟩)
        (hd := tg) (args := tx :: args) eg es
    | .inr (.inr (.inr (.inl ⟨n, hc, _⟩))) =>
      -- an atom has no rule
      rw [hc] at hmm
      cases hmm
    | .inr (.inr (.inl ⟨hc, hh⟩)) =>
      -- I
      subst hh
      rw [hc] at hmm
      match ostackAt_cell h2 with
      | .inl ⟨hs, _⟩ => rw [hs] at hmm; cases hmm
      | .inr ⟨x, r, tx, rest, hs, hx, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        cases hmm
        right
        exact ⟨appL tx rest, OStep.appL rest (.I tx), odecode_of hx (ostackAt_mono hr (Nat.le_succ _))⟩
    | .inr (.inl ⟨hc, hh⟩) =>
      -- K
      subst hh
      rw [hc] at hmm
      match ostackAt_cell h2 with
      | .inl ⟨hs, _⟩ => rw [hs] at hmm; cases hmm
      | .inr ⟨x, r, tx, rest, hs, hx, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        dsimp only at hmm
        cases hL : m.heap.length with
        | zero => rw [hL] at hr; cases hr
        | succ L =>
          rw [hL] at hr
          match ostackAt_cell hr with
          | .inl ⟨hs2, _⟩ => rw [hs2] at hmm; cases hmm
          | .inr ⟨y, r2, ty, rest2, hs2, _, hr2, hb⟩ =>
            subst hb
            rw [hs2] at hmm
            cases hmm
            right
            refine ⟨appL tx rest2, OStep.appL rest2 (.K tx ty), ?_⟩
            refine odecode_of hx (ostackAt_mono hr2 ?_)
            rw [hL]
            exact Nat.le_trans (Nat.le_succ L) (Nat.le_succ _)
    | .inl ⟨hc, hh⟩ =>
      -- S
      subst hh
      rw [hc] at hmm
      match ostackAt_cell h2 with
      | .inl ⟨hs, _⟩ => rw [hs] at hmm; cases hmm
      | .inr ⟨x, r, tx, rest, hs, hx, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        dsimp only at hmm
        cases hL : m.heap.length with
        | zero => rw [hL] at hr; cases hr
        | succ L =>
          rw [hL] at hr
          match ostackAt_cell hr with
          | .inl ⟨hs2, _⟩ => rw [hs2] at hmm; cases hmm
          | .inr ⟨y, r2, ty, rest2, hs2, hy, hr2, hb⟩ =>
            subst hb
            rw [hs2] at hmm
            dsimp only at hmm
            cases L with
            | zero => cases hr2
            | succ L =>
              match ostackAt_cell hr2 with
              | .inl ⟨hs3, _⟩ => rw [hs3] at hmm; cases hmm
              | .inr ⟨z, r3, tz, rest3, hs3, hz, hr3, hc'⟩ =>
                subst hc'
                rw [hs3] at hmm
                dsimp only [alloc] at hmm
                cases hmm
                right
                refine ⟨appL (tx ⬝ₒ tz ⬝ₒ (ty ⬝ₒ tz)) rest3, OStep.appL rest3 (.S tx ty tz), ?_⟩
                -- the three new cells, at `n`, `n + 1`, `n + 2`
                generalize hH : (((m.heap ++ [Cell.app y z]) ++ [Cell.cons m.heap.length r3]) ++
                  [Cell.cons z (m.heap ++ [Cell.app y z]).length]) = H
                have hHlen : H.length = m.heap.length + 3 := by rw [← hH]; simp
                have getc2 : H[m.heap.length + 2]? = some (Cell.cons z (m.heap.length + 1)) := by
                  rw [← hH]; simp
                have getc1 : H[m.heap.length + 1]? = some (Cell.cons m.heap.length r3) := by
                  rw [← hH]; simp
                have getyz : H[m.heap.length]? = some (Cell.app y z) := by
                  rw [← hH]; simp
                have pre : ∃ cs, H = m.heap ++ cs :=
                  ⟨[Cell.app y z, Cell.cons m.heap.length r3, Cell.cons z (m.heap.length + 1)],
                    by rw [← hH]; simp⟩
                match pre with
                | ⟨cs, hcs⟩ =>
                  have tX : otermAt H (H.length + 1) x = some tx := by
                    rw [hcs]; exact otermAt_grow hx (by rw [← hcs, hHlen]; omega)
                  have tZ : ∀ k, m.heap.length + 1 ≤ k → otermAt H k z = some tz := fun k hk => by
                    rw [hcs]; exact otermAt_grow hz (by rw [hL] at hk; omega)
                  have tY : ∀ k, m.heap.length + 1 ≤ k → otermAt H k y = some ty := fun k hk => by
                    rw [hcs]; exact otermAt_grow hy (by rw [hL] at hk; omega)
                  have sR : ∀ k, m.heap.length ≤ k → ostackAt H k r3 = some rest3 := fun k hk => by
                    rw [hcs]; exact ostackAt_grow hr3 (by rw [hL] at hk; omega)
                  have tYZ : otermAt H (m.heap.length + 2) m.heap.length = some (ty ⬝ₒ tz) := by
                    unfold otermAt; rw [getyz]; dsimp only
                    rw [tY _ (by omega), tZ _ (by omega)]
                  have s1 : ostackAt H (m.heap.length + 3) (m.heap.length + 1) =
                      some ((ty ⬝ₒ tz) :: rest3) := by
                    unfold ostackAt; rw [getc1]; dsimp only
                    rw [otermAt_mono tYZ (by omega), sR _ (by omega)]
                  have s2 : ostackAt H (H.length + 1) (m.heap.length + 2) =
                      some (tz :: (ty ⬝ₒ tz) :: rest3) := by
                    rw [hHlen]; unfold ostackAt; rw [getc2]; dsimp only
                    rw [tZ _ (by omega), s1]
                  have hd' := odecode_of (m := ⟨H, x, m.heap.length + 2⟩) tX s2
                  have e2 : (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length r3]).length =
                      m.heap.length + 2 := by simp
                  rw [e2]
                  exact hd'

/-- **An atom at the head**: the state reads back as the variable applied to
    the state's arguments, a spine no rule applies to. -/
theorem atom_head {m : Mach} {t : OTerm} {i : Nat} (hdec : odecode m = some t)
    (hi : m.heap[m.hd]? = some (.atom i)) : ∃ args, t = appL (.var i) args ∧ ONeutral t := by
  match odecode_eq hdec with
  | ⟨h, args, h1, _, ht⟩ =>
    match otermAt_cell h1 with
    | .inr (.inr (.inr (.inl ⟨n, hc, hh⟩))) =>
      rw [hi] at hc
      cases hc
      subst hh
      exact ⟨args, ht, ht ▸ ONeutral.appL args (.var i)⟩
    | .inl ⟨hc, _⟩ => rw [hi] at hc; cases hc
    | .inr (.inl ⟨hc, _⟩) => rw [hi] at hc; cases hc
    | .inr (.inr (.inl ⟨hc, _⟩)) => rw [hi] at hc; cases hc
    | .inr (.inr (.inr (.inr ⟨_, _, _, _, hc, _⟩))) => rw [hi] at hc; cases hc

-- ---------------------------------------------------------------------------
-- Loading an open term
-- ---------------------------------------------------------------------------

/-- Write an open term into the heap, children first; a variable `n` is the
    atom `n`. -/
def obuild : List Cell → OTerm → List Cell × Nat
  | h, .S => alloc h .S
  | h, .K => alloc h .K
  | h, .I => alloc h .I
  | h, .var n => alloc h (.atom n)
  | h, .app f a =>
    let (h1, pf) := obuild h f
    let (h2, pa) := obuild h1 a
    alloc h2 (.app pf pa)

/-- `obuild` over an array: the same cells, in time linear in the term
    (the size read before the push, as in `buildA`). -/
def obuildA : Array Cell → OTerm → Array Cell × Nat
  | h, .S => let n := h.size; (h.push .S, n)
  | h, .K => let n := h.size; (h.push .K, n)
  | h, .I => let n := h.size; (h.push .I, n)
  | h, .var n => let k := h.size; (h.push (.atom n), k)
  | h, .app f a =>
    let (h1, pf) := obuildA h f
    let (h2, pa) := obuildA h1 a
    let n := h2.size
    (h2.push (.app pf pa), n)

theorem obuildA_eq : ∀ (t : OTerm) (h : Array Cell),
    ((obuildA h t).1.toList, (obuildA h t).2) = obuild h.toList t
  | .S, h => by simp [obuildA, obuild, alloc]
  | .K, h => by simp [obuildA, obuild, alloc]
  | .I, h => by simp [obuildA, obuild, alloc]
  | .var n, h => by simp [obuildA, obuild, alloc]
  | .app f a, h => by
    have ef := obuildA_eq f h
    have ea := obuildA_eq a (obuildA h f).1
    unfold obuildA obuild
    rw [← ef]
    dsimp only
    rw [← ea]
    simp [alloc]

def obuildFast (h : List Cell) (t : OTerm) : List Cell × Nat :=
  let r := obuildA h.toArray t
  (r.1.toList, r.2)

/-- Compiled code builds over an array; proofs keep `obuild`. -/
@[csimp] theorem obuild_eq_obuildFast : @obuild = @obuildFast := by
  funext h t
  unfold obuildFast
  rw [obuildA_eq, List.toList_toArray]

theorem obuild_spec : ∀ (t : OTerm) (h : List Cell),
    ∃ cs, (obuild h t).1 = h ++ cs ∧ (obuild h t).2 < (obuild h t).1.length ∧
      otermAt (obuild h t).1 ((obuild h t).2 + 1) (obuild h t).2 = some t
  | .S, h => ⟨[.S], rfl, by simp [obuild, alloc], by simp [obuild, alloc, otermAt]⟩
  | .K, h => ⟨[.K], rfl, by simp [obuild, alloc], by simp [obuild, alloc, otermAt]⟩
  | .I, h => ⟨[.I], rfl, by simp [obuild, alloc], by simp [obuild, alloc, otermAt]⟩
  | .var n, h => ⟨[.atom n], rfl, by simp [obuild, alloc], by simp [obuild, alloc, otermAt]⟩
  | .app f a, h => by
    match obuild_spec f h with
    | ⟨cs1, e1, l1, t1⟩ =>
      match obuild_spec a (obuild h f).1 with
      | ⟨cs2, e2, l2, t2⟩ =>
        refine ⟨cs1 ++ cs2 ++ [.app (obuild h f).2 (obuild (obuild h f).1 a).2], ?_, ?_, ?_⟩
        · show (obuild (obuild h f).1 a).1 ++ [_] = _
          rw [e2, e1]; simp
        · show (obuild (obuild h f).1 a).1.length < ((obuild (obuild h f).1 a).1 ++ [_]).length
          simp
        · show otermAt ((obuild (obuild h f).1 a).1 ++ [.app (obuild h f).2 (obuild (obuild h f).1 a).2])
            ((obuild (obuild h f).1 a).1.length + 1) (obuild (obuild h f).1 a).1.length = some (f ⬝ₒ a)
          unfold otermAt
          rw [getElem?_concat]
          dsimp only
          have ef : otermAt ((obuild (obuild h f).1 a).1 ++ [.app (obuild h f).2 (obuild (obuild h f).1 a).2])
              (obuild (obuild h f).1 a).1.length (obuild h f).2 = some f := by
            rw [e2]
            refine otermAt_mono (otermAt_append (otermAt_append t1)) ?_
            have : (obuild h f).2 + 1 ≤ (obuild h f).1.length := l1
            rw [List.length_append]
            omega
          have ea : otermAt ((obuild (obuild h f).1 a).1 ++ [.app (obuild h f).2 (obuild (obuild h f).1 a).2])
              (obuild (obuild h f).1 a).1.length (obuild (obuild h f).1 a).2 = some a :=
            otermAt_mono (otermAt_append t2) l2
          rw [ef, ea]

/-- The machine loaded with an open term: its heap, the term's address, an
    empty stack. -/
def oload (t : OTerm) : Mach :=
  let (h, p) := obuild [] t
  ⟨h ++ [.nil], p, h.length⟩

theorem odecode_oload (t : OTerm) : odecode (oload t) = some t := by
  match obuild_spec t [] with
  | ⟨_, _, l, ht⟩ =>
    have e : odecode ⟨(obuild [] t).1 ++ [.nil], (obuild [] t).2, (obuild [] t).1.length⟩ =
        some (appL t []) := by
      apply odecode_of
      · exact otermAt_mono (otermAt_append ht) (by rw [length_concat]; omega)
      · rw [length_concat]; unfold ostackAt; rw [getElem?_concat]
    exact e

-- ---------------------------------------------------------------------------
-- Runs
-- ---------------------------------------------------------------------------

/-- Reachability by transitions. -/
inductive MSteps : Mach → Mach → Prop
  | refl (m : Mach) : MSteps m m
  | step {m m1 m2 : Mach} : mstep m = some m1 → MSteps m1 m2 → MSteps m m2

theorem MSteps.snoc {m m1 m2 : Mach} (h : MSteps m m1) (hs : mstep m1 = some m2) : MSteps m m2 := by
  induction h with
  | refl _ => exact .step hs (.refl _)
  | step h1 _ ih => exact .step h1 (ih hs)

/-- **Runs are open head reduction.**  A state reachable from a state that
    reads back as `t` reads back as an open-head-reduct of `t`. -/
theorem omachine_run {m m' : Mach} {t : OTerm} (hdec : odecode m = some t) (h : MSteps m m') :
    ∃ u, odecode m' = some u ∧ OSteps t u := by
  induction h generalizing t with
  | refl _ => exact ⟨t, hdec, .refl t⟩
  | step hs _ ih =>
    cases omstep_some hdec hs with
    | inl h1 =>
      obtain ⟨u, hu, hsteps⟩ := ih h1
      exact ⟨u, hu, hsteps⟩
    | inr h1 =>
      obtain ⟨u1, hstep, hu1⟩ := h1
      obtain ⟨u, hu, hsteps⟩ := ih hu1
      exact ⟨u, hu, .step hstep hsteps⟩

end Mach
