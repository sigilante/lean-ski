import Ski.Fuel

open Term

/-!
# L2: the prover's representation — a write-once heap machine

A term lives in a heap of cells: the three combinators, applications and
argument-stack cells, each pointing only at cells allocated before it.  The
machine is Krivine-style: a head pointer and a stack pointer.

- **Unwind.**  An application at the head moves its function to the head
  and pushes its argument: one stack cell.
- **`I`, `K`.**  The head takes its arguments off the stack.
- **`S`.**  `S x y z` becomes `x` with `z` and `y z` pushed: exactly three
  cells, `y z` and two stack cells.

Every cell is written once, at the address the allocation counter gives —
the heap's length — and a transition only appends (`mstep_append`), so a
read of address `a` always returns what was written there, and a memory
argument need only check that every read was previously written.  Nothing is overwritten, so no work is shared: a contraction here is
a contraction of the term, and the contraction count is L1's.

`decode` reads a state back as a term.  Each transition is an unwind, which
keeps the term and shrinks the head, or a contraction, which is `step?`
(`mstep_some`); the machine stops only at a weak head normal form
(`mstep_none`).  Loaded with a term (`load`, `decode_load`), it halts on `v`
exactly when the term evaluates to `v` (`machine_eval`), after as many
contractions as `runF` counts (`machine_count`).
-/

/-- A heap cell.  Pointers are addresses of earlier cells.  An `atom` is an
    inert leaf with no rule: a probe marker, which a closed term never
    contains (`Ski/HeapOpen.lean` reads states with atoms as open terms). -/
inductive Cell where
  | S | K | I
  | app (f a : Nat)
  | nil
  | cons (arg rest : Nat)
  | atom (n : Nat)
  deriving DecidableEq, Repr

/-- A machine state: the heap, the head pointer, the stack pointer. -/
structure Mach where
  heap : List Cell
  hd : Nat
  stk : Nat
  deriving DecidableEq, Repr

namespace Mach

def get (m : Mach) (a : Nat) : Option Cell := m.heap[a]?

/-- Write a cell at the counter, the heap's length. -/
def alloc (heap : List Cell) (c : Cell) : List Cell × Nat := (heap ++ [c], heap.length)

/-- The term stored at an address; the fuel is the address bound. -/
def termAt (heap : List Cell) : Nat → Nat → Option Term
  | 0, _ => none
  | f + 1, a =>
    match heap[a]? with
    | some .S => some .S
    | some .K => some .K
    | some .I => some .I
    | some (.app g x) =>
      match termAt heap f g, termAt heap f x with
      | some tg, some tx => some (tg ⬝ tx)
      | _, _ => none
    | _ => none

/-- The arguments on the stack, top first. -/
def stackAt (heap : List Cell) : Nat → Nat → Option (List Term)
  | 0, _ => none
  | f + 1, a =>
    match heap[a]? with
    | some .nil => some []
    | some (.cons x r) =>
      match termAt heap (f + 1) x, stackAt heap f r with
      | some tx, some rest => some (tx :: rest)
      | _, _ => none
    | _ => none

/-- A term applied to arguments, first argument innermost. -/
def apps : Term → List Term → Term
  | t, [] => t
  | t, a :: as => apps (t ⬝ a) as

/-- The term a state denotes. -/
def decode (m : Mach) : Option Term :=
  match termAt m.heap (m.heap.length + 1) m.hd, stackAt m.heap (m.heap.length + 1) m.stk with
  | some h, some args => some (apps h args)
  | _, _ => none

/-- One transition, or `none` at a weak head normal form. -/
def mstep (m : Mach) : Option Mach :=
  match m.get m.hd with
  | some (.app f x) =>
    let (h1, c) := alloc m.heap (.cons x m.stk)
    some ⟨h1, f, c⟩
  | some .I =>
    match m.get m.stk with
    | some (.cons x s) => some ⟨m.heap, x, s⟩
    | _ => none
  | some .K =>
    match m.get m.stk with
    | some (.cons x s1) =>
      match m.get s1 with
      | some (.cons _ s2) => some ⟨m.heap, x, s2⟩
      | _ => none
    | _ => none
  | some .S =>
    match m.get m.stk with
    | some (.cons x s1) =>
      match m.get s1 with
      | some (.cons y s2) =>
        match m.get s2 with
        | some (.cons z s3) =>
          let (h1, yz) := alloc m.heap (.app y z)
          let (h2, c1) := alloc h1 (.cons yz s3)
          let (h3, c2) := alloc h2 (.cons z c1)
          some ⟨h3, x, c2⟩
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Whether a transition is a contraction (a rule fired) or an unwind. -/
def isContraction (m : Mach) : Bool :=
  match m.get m.hd with
  | some (.app _ _) => false
  | _ => true


theorem get_append {heap cs : List Cell} {a : Nat} {c : Cell} (h : heap[a]? = some c) :
    (heap ++ cs)[a]? = some c := by
  have ha : a < heap.length := by
    rcases Nat.lt_or_ge a heap.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; cases h
  rw [List.getElem?_append_left ha]; exact h

theorem termAt_append : ∀ {f : Nat} {heap cs : List Cell} {a : Nat} {t : Term},
    termAt heap f a = some t → termAt (heap ++ cs) f a = some t
  | 0, _, _, _, _, h => by cases h
  | f + 1, heap, cs, a, t, h => by
    unfold termAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      rw [get_append hc]
      cases c with
      | S => exact h
      | K => exact h
      | I => exact h
      | app g x =>
        dsimp only at h ⊢
        cases hg : termAt heap f g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : termAt heap f x with
          | none => rw [hg, hx] at h; cases h
          | some tx =>
            rw [hg, hx] at h
            rw [termAt_append hg, termAt_append hx]
            exact h
      | nil => cases h
      | cons _ _ => cases h
      | atom _ => cases h

theorem termAt_mono : ∀ {f k : Nat} {heap : List Cell} {a : Nat} {t : Term},
    termAt heap f a = some t → f ≤ k → termAt heap k a = some t
  | 0, _, _, _, _, h, _ => by cases h
  | f + 1, 0, _, _, _, _, hle => by omega
  | f + 1, k + 1, heap, a, t, h, hle => by
    unfold termAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | S => exact h
      | K => exact h
      | I => exact h
      | app g x =>
        dsimp only at h ⊢
        cases hg : termAt heap f g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : termAt heap f x with
          | none => rw [hg, hx] at h; cases h
          | some tx =>
            rw [hg, hx] at h
            rw [termAt_mono hg (by omega), termAt_mono hx (by omega)]
            exact h
      | nil => cases h
      | cons _ _ => cases h
      | atom _ => cases h

theorem stackAt_append : ∀ {f : Nat} {heap cs : List Cell} {a : Nat} {ts : List Term},
    stackAt heap f a = some ts → stackAt (heap ++ cs) f a = some ts
  | 0, _, _, _, _, h => by cases h
  | f + 1, heap, cs, a, ts, h => by
    unfold stackAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      rw [get_append hc]
      cases c with
      | nil => exact h
      | cons x r =>
        dsimp only at h ⊢
        cases hx : termAt heap (f + 1) x with
        | none => rw [hx] at h; cases h
        | some tx =>
          cases hr : stackAt heap f r with
          | none => rw [hx, hr] at h; cases h
          | some rest =>
            rw [hx, hr] at h
            rw [termAt_append hx, stackAt_append hr]
            exact h
      | _ => cases h

theorem stackAt_mono : ∀ {f k : Nat} {heap : List Cell} {a : Nat} {ts : List Term},
    stackAt heap f a = some ts → f ≤ k → stackAt heap k a = some ts
  | 0, _, _, _, _, h, _ => by cases h
  | f + 1, 0, _, _, _, _, hle => by omega
  | f + 1, k + 1, heap, a, ts, h, hle => by
    unfold stackAt at h ⊢
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | nil => exact h
      | cons x r =>
        dsimp only at h ⊢
        cases hx : termAt heap (f + 1) x with
        | none => rw [hx] at h; cases h
        | some tx =>
          cases hr : stackAt heap f r with
          | none => rw [hx, hr] at h; cases h
          | some rest =>
            rw [hx, hr] at h
            rw [termAt_mono hx (by omega), stackAt_mono hr (by omega)]
            exact h
      | _ => cases h

theorem getElem?_concat (l : List Cell) (c : Cell) : (l ++ [c])[l.length]? = some c := by
  rw [List.getElem?_append_right (Nat.le_refl _)]; simp

theorem termAt_cell {heap : List Cell} {f a : Nat} {t : Term} (h : termAt heap (f + 1) a = some t) :
    (heap[a]? = some .S ∧ t = .S) ∨ (heap[a]? = some .K ∧ t = .K) ∨ (heap[a]? = some .I ∧ t = .I) ∨
    ∃ g x tg tx, heap[a]? = some (.app g x) ∧ termAt heap f g = some tg ∧
      termAt heap f x = some tx ∧ t = tg ⬝ tx := by
  unfold termAt at h
  cases hc : heap[a]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    cases c with
    | S => cases h; exact .inl ⟨rfl, rfl⟩
    | K => cases h; exact .inr (.inl ⟨rfl, rfl⟩)
    | I => cases h; exact .inr (.inr (.inl ⟨rfl, rfl⟩))
    | app g x =>
      dsimp only at h
      cases hg : termAt heap f g with
      | none => rw [hg] at h; cases h
      | some tg =>
        cases hx : termAt heap f x with
        | none => rw [hg, hx] at h; cases h
        | some tx =>
          rw [hg, hx] at h
          cases h
          exact .inr (.inr (.inr ⟨g, x, tg, tx, rfl, hg, hx, rfl⟩))
    | nil => cases h
    | cons _ _ => cases h
    | atom _ => cases h

theorem stackAt_cell {heap : List Cell} {f a : Nat} {ts : List Term}
    (h : stackAt heap (f + 1) a = some ts) :
    (heap[a]? = some .nil ∧ ts = []) ∨
    ∃ x r tx rest, heap[a]? = some (.cons x r) ∧ termAt heap (f + 1) x = some tx ∧
      stackAt heap f r = some rest ∧ ts = tx :: rest := by
  unfold stackAt at h
  cases hc : heap[a]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    cases c with
    | nil => cases h; exact .inl ⟨rfl, rfl⟩
    | cons x r =>
      dsimp only at h
      cases hx : termAt heap (f + 1) x with
      | none => rw [hx] at h; cases h
      | some tx =>
        cases hr : stackAt heap f r with
        | none => rw [hx, hr] at h; cases h
        | some rest =>
          rw [hx, hr] at h
          cases h
          exact .inr ⟨x, r, tx, rest, rfl, hx, hr, rfl⟩
    | _ => cases h

theorem apps_cons (t a : Term) (as : List Term) : apps t (a :: as) = apps (t ⬝ a) as := rfl

theorem step?_apps : ∀ {as : List Term} {t u : Term}, step? t = some u →
    step? (apps t as) = some (apps u as)
  | [], _, _, h => h
  | a :: as, t, u, h => by
    rw [apps_cons, apps_cons]
    exact step?_apps (step?_complete (Step.left a (step?_sound h)))

theorem decode_eq {m : Mach} {t : Term} (h : decode m = some t) :
    ∃ hd args, termAt m.heap (m.heap.length + 1) m.hd = some hd ∧
      stackAt m.heap (m.heap.length + 1) m.stk = some args ∧ t = apps hd args := by
  unfold decode at h
  cases h1 : termAt m.heap (m.heap.length + 1) m.hd with
  | none => rw [h1] at h; cases h
  | some hd =>
    cases h2 : stackAt m.heap (m.heap.length + 1) m.stk with
    | none => rw [h1, h2] at h; cases h
    | some args =>
      rw [h1, h2] at h
      cases h
      exact ⟨hd, args, rfl, rfl, rfl⟩

theorem decode_of {m : Mach} {hd : Term} {args : List Term}
    (h1 : termAt m.heap (m.heap.length + 1) m.hd = some hd)
    (h2 : stackAt m.heap (m.heap.length + 1) m.stk = some args) :
    decode m = some (apps hd args) := by
  unfold decode; rw [h1, h2]

theorem length_concat (l : List Cell) (c : Cell) : (l ++ [c]).length = l.length + 1 := by simp

/-- The size of a term: the head measure unwinding decreases. -/
def tsize : Term → Nat
  | .app f a => tsize f + tsize a + 1
  | _ => 1

/-- The size of the decoded head. -/
def hsize (m : Mach) : Nat := ((termAt m.heap (m.heap.length + 1) m.hd).map tsize).getD 0

theorem mstep_none {m : Mach} {t : Term} (hdec : decode m = some t) (hm : mstep m = none) :
    step? t = none := by
  match decode_eq hdec with
  | ⟨h, args, h1, h2, ht⟩ =>
    subst ht
    have hmm : mstep m = none := hm
    unfold mstep get at hmm
    match termAt_cell h1 with
    | .inl ⟨hc, hh⟩ =>
      subst hh
      rw [hc] at hmm
      match stackAt_cell h2 with
      | .inl ⟨_, ha⟩ => subst ha; rfl
      | .inr ⟨x, r, tx, rest, hs, _, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        dsimp only at hmm
        cases hL : m.heap.length with
        | zero => rw [hL] at hr; cases hr
        | succ L =>
          rw [hL] at hr
          match stackAt_cell hr with
          | .inl ⟨_, hb⟩ => subst hb; rfl
          | .inr ⟨y, r2, ty, rest2, hs2, _, hr2, hb⟩ =>
            subst hb
            rw [hs2] at hmm
            dsimp only at hmm
            cases L with
            | zero => cases hr2
            | succ L =>
              match stackAt_cell hr2 with
              | .inl ⟨_, hc'⟩ => subst hc'; rfl
              | .inr ⟨z, r3, tz, rest3, hs3, _, _, hc'⟩ =>
                rw [hs3] at hmm
                cases hmm
    | .inr (.inl ⟨hc, hh⟩) =>
      subst hh
      rw [hc] at hmm
      match stackAt_cell h2 with
      | .inl ⟨_, ha⟩ => subst ha; rfl
      | .inr ⟨x, r, tx, rest, hs, _, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        dsimp only at hmm
        cases hL : m.heap.length with
        | zero => rw [hL] at hr; cases hr
        | succ L =>
          rw [hL] at hr
          match stackAt_cell hr with
          | .inl ⟨_, hb⟩ => subst hb; rfl
          | .inr ⟨y, r2, ty, rest2, hs2, _, _, hb⟩ =>
            rw [hs2] at hmm
            cases hmm
    | .inr (.inr (.inl ⟨hc, hh⟩)) =>
      subst hh
      rw [hc] at hmm
      match stackAt_cell h2 with
      | .inl ⟨_, ha⟩ => subst ha; rfl
      | .inr ⟨x, r, tx, rest, hs, _, _, ha⟩ =>
        rw [hs] at hmm
        cases hmm
    | .inr (.inr (.inr ⟨g, x, tg, tx, hc, _, _, _⟩)) =>
      rw [hc] at hmm
      cases hmm

/-- Append-and-grow: a term or stack readable before an allocation is
    readable after, at any larger fuel. -/
theorem termAt_grow {heap cs : List Cell} {f k a : Nat} {t : Term}
    (h : termAt heap f a = some t) (hk : f ≤ k) : termAt (heap ++ cs) k a = some t :=
  termAt_mono (termAt_append h) hk

theorem stackAt_grow {heap cs : List Cell} {f k a : Nat} {ts : List Term}
    (h : stackAt heap f a = some ts) (hk : f ≤ k) : stackAt (heap ++ cs) k a = some ts :=
  stackAt_mono (stackAt_append h) hk

/-- **Each transition is an unwind or a contraction.**  An unwind leaves the
    decoded term and shrinks the head; a contraction is `step?`. -/
theorem mstep_some {m m' : Mach} {t : Term} (hdec : decode m = some t) (hm : mstep m = some m') :
    (isContraction m = false ∧ decode m' = some t ∧ hsize m' < hsize m) ∨
    (isContraction m = true ∧ ∃ u, step? t = some u ∧ decode m' = some u) := by
  match decode_eq hdec with
  | ⟨h, args, h1, h2, ht⟩ =>
    subst ht
    have hmm : mstep m = some m' := hm
    unfold mstep get at hmm
    match termAt_cell h1 with
    | .inr (.inr (.inr ⟨g, x, tg, tx, hc, hg, hx, hh⟩)) =>
      -- unwind
      subst hh
      rw [hc] at hmm
      dsimp only [alloc] at hmm
      cases hmm
      left
      refine ⟨by unfold isContraction get; rw [hc], ?_, ?_⟩
      · have eg : termAt (m.heap ++ [Cell.cons x m.stk]) ((m.heap ++ [Cell.cons x m.stk]).length + 1) g = some tg :=
          termAt_grow hg (by rw [length_concat]; omega)
        have es : stackAt (m.heap ++ [Cell.cons x m.stk]) ((m.heap ++ [Cell.cons x m.stk]).length + 1)
            m.heap.length = some (tx :: args) := by
          rw [length_concat]
          unfold stackAt
          rw [getElem?_concat]
          dsimp only
          rw [termAt_grow hx (by omega), stackAt_grow h2 (by omega)]
        exact decode_of (m := ⟨m.heap ++ [Cell.cons x m.stk], g, m.heap.length⟩) (hd := tg) (args := tx :: args) eg es
      · unfold hsize
        have eg : termAt (m.heap ++ [Cell.cons x m.stk]) ((m.heap ++ [Cell.cons x m.stk]).length + 1) g = some tg :=
          termAt_grow hg (by rw [length_concat]; omega)
        show ((termAt (m.heap ++ [Cell.cons x m.stk]) ((m.heap ++ [Cell.cons x m.stk]).length + 1) g).map tsize).getD 0 <
          ((termAt m.heap (m.heap.length + 1) m.hd).map tsize).getD 0
        rw [eg, h1]
        show tsize tg < tsize tg + tsize tx + 1
        omega
    | .inr (.inr (.inl ⟨hc, hh⟩)) =>
      -- I
      subst hh
      rw [hc] at hmm
      match stackAt_cell h2 with
      | .inl ⟨hs, _⟩ => rw [hs] at hmm; cases hmm
      | .inr ⟨x, r, tx, rest, hs, hx, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        cases hmm
        right
        refine ⟨by unfold isContraction get; rw [hc], apps tx rest, ?_, ?_⟩
        · exact step?_apps (step?_complete (Step.I tx))
        · exact decode_of hx (stackAt_mono hr (Nat.le_succ _))
    | .inr (.inl ⟨hc, hh⟩) =>
      -- K
      subst hh
      rw [hc] at hmm
      match stackAt_cell h2 with
      | .inl ⟨hs, _⟩ => rw [hs] at hmm; cases hmm
      | .inr ⟨x, r, tx, rest, hs, hx, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        dsimp only at hmm
        cases hL : m.heap.length with
        | zero => rw [hL] at hr; cases hr
        | succ L =>
          rw [hL] at hr
          match stackAt_cell hr with
          | .inl ⟨hs2, _⟩ => rw [hs2] at hmm; cases hmm
          | .inr ⟨y, r2, ty, rest2, hs2, _, hr2, hb⟩ =>
            subst hb
            rw [hs2] at hmm
            cases hmm
            right
            refine ⟨by unfold isContraction get; rw [hc], apps tx rest2, ?_, ?_⟩
            · exact step?_apps (step?_complete (Step.K tx ty))
            · refine decode_of hx (stackAt_mono hr2 ?_)
              rw [hL]
              exact Nat.le_trans (Nat.le_succ L) (Nat.le_succ _)
    | .inl ⟨hc, hh⟩ =>
      -- S
      subst hh
      rw [hc] at hmm
      match stackAt_cell h2 with
      | .inl ⟨hs, _⟩ => rw [hs] at hmm; cases hmm
      | .inr ⟨x, r, tx, rest, hs, hx, hr, ha⟩ =>
        subst ha
        rw [hs] at hmm
        dsimp only at hmm
        cases hL : m.heap.length with
        | zero => rw [hL] at hr; cases hr
        | succ L =>
          rw [hL] at hr
          match stackAt_cell hr with
          | .inl ⟨hs2, _⟩ => rw [hs2] at hmm; cases hmm
          | .inr ⟨y, r2, ty, rest2, hs2, hy, hr2, hb⟩ =>
            subst hb
            rw [hs2] at hmm
            dsimp only at hmm
            cases L with
            | zero => cases hr2
            | succ L =>
              match stackAt_cell hr2 with
              | .inl ⟨hs3, _⟩ => rw [hs3] at hmm; cases hmm
              | .inr ⟨z, r3, tz, rest3, hs3, hz, hr3, hc'⟩ =>
                subst hc'
                rw [hs3] at hmm
                dsimp only [alloc] at hmm
                cases hmm
                right
                refine ⟨by unfold isContraction get; rw [hc],
                  apps (tx ⬝ tz ⬝ (ty ⬝ tz)) rest3, ?_, ?_⟩
                · exact step?_apps (step?_complete (Step.S tx ty tz))
                · -- the three new cells, at `n`, `n + 1`, `n + 2`
                  have e1 : ((m.heap ++ [Cell.app y z]) ++ [Cell.cons m.heap.length r3]) =
                      m.heap ++ ([Cell.app y z] ++ [Cell.cons m.heap.length r3]) := List.append_assoc ..
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
                    have tX : termAt H (H.length + 1) x = some tx := by
                      rw [hcs]; exact termAt_grow hx (by rw [← hcs, hHlen]; omega)
                    have tZ : ∀ k, m.heap.length + 1 ≤ k → termAt H k z = some tz := fun k hk => by
                      rw [hcs]; exact termAt_grow hz (by rw [hL] at hk; omega)
                    have tY : ∀ k, m.heap.length + 1 ≤ k → termAt H k y = some ty := fun k hk => by
                      rw [hcs]; exact termAt_grow hy (by rw [hL] at hk; omega)
                    have sR : ∀ k, m.heap.length ≤ k → stackAt H k r3 = some rest3 := fun k hk => by
                      rw [hcs]; exact stackAt_grow hr3 (by rw [hL] at hk; omega)
                    have tYZ : termAt H (m.heap.length + 2) m.heap.length = some (ty ⬝ tz) := by
                      unfold termAt; rw [getyz]; dsimp only
                      rw [tY _ (by omega), tZ _ (by omega)]
                    have s1 : stackAt H (m.heap.length + 3) (m.heap.length + 1) =
                        some ((ty ⬝ tz) :: rest3) := by
                      unfold stackAt; rw [getc1]; dsimp only
                      rw [termAt_mono tYZ (by omega), sR _ (by omega)]
                    have s2 : stackAt H (H.length + 1) (m.heap.length + 2) =
                        some (tz :: (ty ⬝ tz) :: rest3) := by
                      rw [hHlen]; unfold stackAt; rw [getc2]; dsimp only
                      rw [tZ _ (by omega), s1]
                    have hd' := decode_of (m := ⟨H, x, m.heap.length + 2⟩) tX s2
                    have e2 : (m.heap ++ [Cell.app y z] ++ [Cell.cons m.heap.length r3]).length =
                        m.heap.length + 2 := by simp
                    rw [e2]
                    exact hd'

/-- Run for at most `k` transitions, counting contractions. -/
def mrunC : Nat → Mach → Option (Mach × Nat)
  | 0, _ => none
  | k + 1, m =>
    match mstep m with
    | none => some (m, 0)
    | some m' =>
      if isContraction m then (mrunC k m').map (fun p => (p.1, p.2 + 1)) else mrunC k m'

/-- **The machine is sound, and counts L1's contractions.**  A run that
    halts after `c` contractions reads back the value `runF` reaches in `c`. -/
theorem mrunC_sound : ∀ {k : Nat} {m m' : Mach} {c : Nat} {t : Term},
    decode m = some t → mrunC k m = some (m', c) →
    ∃ v, decode m' = some v ∧ runF (c + 1) t = some (v, c)
  | 0, _, _, _, _, _, h => by cases h
  | k + 1, m, m', c, t, hd, h => by
    unfold mrunC at h
    cases hs : mstep m with
    | none =>
      rw [hs] at h
      cases h
      refine ⟨t, hd, ?_⟩
      show (match step? t with
        | none => some (t, 0)
        | some t' => (runF 0 t').map (fun p => (p.1, p.2 + 1))) = some (t, 0)
      rw [mstep_none hd hs]
    | some m1 =>
      rw [hs] at h
      dsimp only at h
      match mstep_some hd hs with
      | .inl ⟨hc, hd1, _⟩ =>
        rw [hc] at h
        exact mrunC_sound hd1 h
      | .inr ⟨hc, u, hu, hd1⟩ =>
        rw [hc] at h
        skip
        cases hr : mrunC k m1 with
        | none => rw [hr] at h; cases h
        | some p =>
          rw [hr] at h
          cases h
          match mrunC_sound hd1 hr with
          | ⟨v, hv, hrun⟩ =>
            refine ⟨v, hv, ?_⟩
            show (match step? t with
              | none => some (t, 0)
              | some t' => (runF (p.2 + 1) t').map (fun p => (p.1, p.2 + 1))) = some (v, p.2 + 1)
            rw [hu]
            dsimp only
            rw [hrun]
            rfl

/-- Reachability, with the contractions on the way. -/
inductive Reach : Mach → Mach → Nat → Prop
  | refl (m : Mach) : Reach m m 0
  | unwind {m m1 m2 : Mach} {c : Nat} : mstep m = some m1 → isContraction m = false →
      Reach m1 m2 c → Reach m m2 c
  | contract {m m1 m2 : Mach} {c : Nat} : mstep m = some m1 → isContraction m = true →
      Reach m1 m2 c → Reach m m2 (c + 1)

theorem mrunC_of_reach {m m' : Mach} {c : Nat} (h : Reach m m' c) (hn : mstep m' = none) :
    ∃ k, mrunC k m = some (m', c) := by
  induction h with
  | refl m => exact ⟨1, by unfold mrunC; rw [hn]⟩
  | @unwind m m1 m2 c hs hc _ ih =>
    match ih hn with
    | ⟨k, hk⟩ => exact ⟨k + 1, by unfold mrunC; rw [hs]; dsimp only; rw [hc]; exact hk⟩
  | @contract m m1 m2 c hs hc _ ih =>
    match ih hn with
    | ⟨k, hk⟩ => exact ⟨k + 1, by unfold mrunC; rw [hs]; dsimp only; rw [hc, if_pos rfl, hk]; rfl⟩

/-- **The machine is complete.**  From a state reading back a term that
    evaluates, the machine halts on the value. -/
theorem reach_of_evalF : ∀ {n : Nat} {t v : Term}, evalF n t = some v →
    ∀ (N : Nat) {m : Mach}, hsize m ≤ N → decode m = some t →
    ∃ m' c, Reach m m' c ∧ mstep m' = none ∧ decode m' = some v
  | 0, _, _, h, _, _, _, _ => by cases h
  | n + 1, t, v, h, N, m, hN, hd => by
    cases hs : mstep m with
    | none =>
      have hn := mstep_none hd hs
      have : v = t := by
        have h' : (match step? t with | none => some t | some t' => evalF n t') = some v := h
        rw [hn] at h'; cases h'; rfl
      subst this
      exact ⟨m, 0, .refl m, hs, hd⟩
    | some m1 =>
      match mstep_some hd hs with
      | .inl ⟨hc, hd1, hlt⟩ =>
        cases N with
        | zero => exact absurd (Nat.lt_of_lt_of_le hlt hN) (Nat.not_lt_zero _)
        | succ N =>
          match reach_of_evalF h N (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hN)) hd1 with
          | ⟨m', c, hr, hn, hv⟩ => exact ⟨m', c, .unwind hs hc hr, hn, hv⟩
      | .inr ⟨hc, u, hu, hd1⟩ =>
        have h' : (match step? t with | none => some t | some t' => evalF n t') = some v := h
        rw [hu] at h'
        match reach_of_evalF h' (hsize m1) (Nat.le_refl _) hd1 with
        | ⟨m', c, hr, hn, hv⟩ => exact ⟨m', c + 1, .contract hs hc hr, hn, hv⟩

-- ---------------------------------------------------------------------------
-- Loading a term
-- ---------------------------------------------------------------------------

/-- Write a term into the heap, children first. -/
def build : List Cell → Term → List Cell × Nat
  | h, .S => alloc h .S
  | h, .K => alloc h .K
  | h, .I => alloc h .I
  | h, .app f a =>
    let (h1, pf) := build h f
    let (h2, pa) := build h1 a
    alloc h2 (.app pf pa)

/-- `build` over an array: the same cells, in time linear in the term.  The
    size is read before the push, so the array stays unshared and each push
    writes in place; read after, it would copy the array at every cell. -/
def buildA : Array Cell → Term → Array Cell × Nat
  | h, .S => let n := h.size; (h.push .S, n)
  | h, .K => let n := h.size; (h.push .K, n)
  | h, .I => let n := h.size; (h.push .I, n)
  | h, .app f a =>
    let (h1, pf) := buildA h f
    let (h2, pa) := buildA h1 a
    let n := h2.size
    (h2.push (.app pf pa), n)

theorem buildA_eq : ∀ (t : Term) (h : Array Cell),
    ((buildA h t).1.toList, (buildA h t).2) = build h.toList t
  | .S, h => by simp [buildA, build, alloc]
  | .K, h => by simp [buildA, build, alloc]
  | .I, h => by simp [buildA, build, alloc]
  | .app f a, h => by
    have ef := buildA_eq f h
    have ea := buildA_eq a (buildA h f).1
    unfold buildA build
    rw [← ef]
    dsimp only
    rw [← ea]
    simp [alloc]

def buildFast (h : List Cell) (t : Term) : List Cell × Nat :=
  let r := buildA h.toArray t
  (r.1.toList, r.2)

/-- Compiled code builds over an array; proofs keep `build`. -/
@[csimp] theorem build_eq_buildFast : @build = @buildFast := by
  funext h t
  unfold buildFast
  rw [buildA_eq, List.toList_toArray]

theorem build_spec : ∀ (t : Term) (h : List Cell),
    ∃ cs, (build h t).1 = h ++ cs ∧ (build h t).2 < (build h t).1.length ∧
      termAt (build h t).1 ((build h t).2 + 1) (build h t).2 = some t
  | .S, h => ⟨[.S], rfl, by simp [build, alloc], by simp [build, alloc, termAt]⟩
  | .K, h => ⟨[.K], rfl, by simp [build, alloc], by simp [build, alloc, termAt]⟩
  | .I, h => ⟨[.I], rfl, by simp [build, alloc], by simp [build, alloc, termAt]⟩
  | .app f a, h => by
    match build_spec f h with
    | ⟨cs1, e1, l1, t1⟩ =>
      match build_spec a (build h f).1 with
      | ⟨cs2, e2, l2, t2⟩ =>
        refine ⟨cs1 ++ cs2 ++ [.app (build h f).2 (build (build h f).1 a).2], ?_, ?_, ?_⟩
        · show (build (build h f).1 a).1 ++ [_] = _
          rw [e2, e1]; simp
        · show (build (build h f).1 a).1.length < ((build (build h f).1 a).1 ++ [_]).length
          simp
        · show termAt ((build (build h f).1 a).1 ++ [.app (build h f).2 (build (build h f).1 a).2])
            ((build (build h f).1 a).1.length + 1) (build (build h f).1 a).1.length = some (f ⬝ a)
          unfold termAt
          rw [getElem?_concat]
          dsimp only
          have ef : termAt ((build (build h f).1 a).1 ++ [.app (build h f).2 (build (build h f).1 a).2])
              (build (build h f).1 a).1.length (build h f).2 = some f := by
            rw [e2]
            refine termAt_mono (termAt_append (termAt_append t1)) ?_
            have : (build h f).2 + 1 ≤ (build h f).1.length := l1
            rw [List.length_append]
            omega
          have ea : termAt ((build (build h f).1 a).1 ++ [.app (build h f).2 (build (build h f).1 a).2])
              (build (build h f).1 a).1.length (build (build h f).1 a).2 = some a :=
            termAt_mono (termAt_append t2) l2
          rw [ef, ea]

/-- The machine loaded with a term: its heap, the term's address, an empty stack. -/
def load (t : Term) : Mach :=
  let (h, p) := build [] t
  ⟨h ++ [.nil], p, h.length⟩

theorem decode_load (t : Term) : decode (load t) = some t := by
  match build_spec t [] with
  | ⟨_, _, l, ht⟩ =>
    have e : decode ⟨(build [] t).1 ++ [.nil], (build [] t).2, (build [] t).1.length⟩ = some (apps t []) := by
      apply decode_of
      · exact termAt_mono (termAt_append ht) (by rw [length_concat]; omega)
      · rw [length_concat]; unfold stackAt; rw [getElem?_concat]
    exact e

/-- **L2 computes L1.**  The machine loaded with `t` halts, after `c`
    contractions, on a state reading back `v`, exactly when `t` evaluates to
    `v`; and then `runF` counts the same `c`. -/
theorem machine_eval (t v : Term) :
    (∃ k m' c, mrunC k (load t) = some (m', c) ∧ decode m' = some v) ↔ Eval t v := by
  constructor
  · intro ⟨k, m', c, hr, hv⟩
    match mrunC_sound (decode_load t) hr with
    | ⟨v', hv', hrun⟩ =>
      rw [hv] at hv'
      cases hv'
      have e := runF_evalF (k := c + 1) (t := t)
      rw [hrun] at e
      exact evalF_sound e.symm
  · intro he
    match evalF_complete he with
    | ⟨n, hn⟩ =>
      match reach_of_evalF hn (hsize (load t)) (Nat.le_refl _) (decode_load t) with
      | ⟨m', c, hr, hstop, hv⟩ =>
        match mrunC_of_reach hr hstop with
        | ⟨k, hk⟩ => exact ⟨k, m', c, hk, hv⟩

theorem machine_count {k c : Nat} {t v : Term} {m' : Mach}
    (h : mrunC k (load t) = some (m', c)) (hv : decode m' = some v) : runF (c + 1) t = some (v, c) := by
  match mrunC_sound (decode_load t) h with
  | ⟨v', hv', hrun⟩ =>
    rw [hv] at hv'
    cases hv'
    exact hrun

/-- **Write-once.**  A transition only appends to the heap: no cell is ever
    rewritten, so a read of an address returns what was first written there. -/
theorem mstep_append {m m' : Mach} (h : mstep m = some m') : ∃ cs, m'.heap = m.heap ++ cs := by
  unfold mstep get at h
  cases hc : m.heap[m.hd]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    cases c with
    | app f x => dsimp only [alloc] at h; cases h; exact ⟨_, rfl⟩
    | I =>
      dsimp only at h
      split at h
      · cases h; exact ⟨[], by simp⟩
      · cases h
    | K =>
      dsimp only at h
      split at h
      · split at h
        · cases h; exact ⟨[], by simp⟩
        · cases h
      · cases h
    | S =>
      dsimp only at h
      split at h
      · split at h
        · split at h
          · dsimp only [alloc] at h; cases h; exact ⟨_, by rw [List.append_assoc, List.append_assoc]⟩
          · cases h
        · cases h
      · cases h
    | nil => cases h
    | cons _ _ => cases h
    | atom _ => cases h

end Mach
