import Ski.Heap
import Ski.Compile
import Ski.Transfer

open Term

/-!
# Supercombinator jets: instantiation is weak reduction

SKIjack compiles a lifted λ-chain to a closed combinator, `absN xs body`,
applied to its captured variables (`wrapLift`).  Applied to all its
arguments it reduces to the body with the arguments substituted, which
`absN_beta_close` proves once for every body.  A **supercombinator jet**
does that reduction in one step: it pops the arguments' pointers and
writes the body's cells, each variable replaced by its argument's pointer
(`instStep`).  That is template instantiation, and it is §18.1 of
Avon's `docs/DESIGN.md`.

**The theorem** (`inst_sound_g`): when the head is `absN xs body`, the
stack holds `|xs|` arguments, and every other variable of the body, a
*global*, points to a cell holding its meaning `γ`, the state after an
instantiation reads back as a weak reduct of the state before; the head
must read `(absN xs body).close γ`.  Globals let a body name its closed
subterms instead of writing them (`instStepG`).  `inst_sound` is the case
with no globals.

**The corollary** (`jet_run_eval`): a run that mixes machine transitions
with licensed instantiations, and halts on a weak head normal form, proves
normal-order evaluation, up to weak reduction of the value:
standardization (`eval_of_wsteps`) carries the weak reduction to normal
order.  The value's head and arity are the unjetted value's
(`jet_run_shape`).

An instantiation moves argument pointers and never reads the cells they
point to, so it cannot quote a running term.
-/

namespace Mach

-- ---------------------------------------------------------------------------
-- Pointer environments
-- ---------------------------------------------------------------------------

/-- `e` with the pointer `p` for `x`. -/
def updN (e : Nat → Nat) (x p : Nat) : Nat → Nat := fun y => if y = x then p else e y

/-- `e` with the pointers for the formals, first to last. -/
def overrideN : (Nat → Nat) → List Nat → List Nat → Nat → Nat
  | e, x :: xs, p :: ps => overrideN (updN e x p) xs ps
  | e, _, _ => e

theorem overrideN_notin : ∀ (e : Nat → Nat) (xs ps : List Nat) (x : Nat), x ∉ xs →
    overrideN e xs ps x = e x
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, _ => rfl
  | e, y :: ys, p :: ps, x, hx => by
    show overrideN (updN e y p) ys ps x = e x
    rw [overrideN_notin _ ys ps x (fun h => hx (.tail _ h))]
    unfold updN
    rw [if_neg (fun h => hx (by rw [h]; exact .head _))]

theorem overrideC_notin : ∀ (γ : Nat → Term) (xs : List Nat) (Ns : List Term) (x : Nat), x ∉ xs →
    overrideC γ xs Ns x = γ x
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, _ => rfl
  | γ, y :: ys, N :: Ns, x, hx => by
    show overrideC (updC γ y N) ys Ns x = γ x
    rw [overrideC_notin _ ys Ns x (fun h => hx (.tail _ h))]
    unfold updC
    rw [if_neg (fun h => hx (by rw [h]; exact .head _))]

/-- Pointers `ps` hold the terms `Ns`, one for one. -/
def PtrsOK (heap : List Cell) (F : Nat) : List Nat → List Term → Prop
  | [], [] => True
  | p :: ps, N :: Ns => termAt heap F p = some N ∧ PtrsOK heap F ps Ns
  | _, _ => False

/-- A formal's pointer holds the formal's term. -/
theorem override_ptr {heap : List Cell} {F : Nat} :
    ∀ (xs : List Nat) (e : Nat → Nat) (γ : Nat → Term) (ps : List Nat) (Ns : List Term) (x : Nat),
      x ∈ xs → PtrsOK heap F ps Ns → ps.length = xs.length →
      termAt heap F (overrideN e xs ps x) = some (overrideC γ xs Ns x)
  | [], _, _, _, _, _, hx, _, _ => by cases hx
  | _ :: _, _, _, [], _, _, _, _, hl => by cases hl
  | _ :: _, _, _, _ :: _, [], _, _, hok, _ => by cases hok
  | y :: ys, e, γ, p :: ps, N :: Ns, x, hx, hok, hl => by
    show termAt heap F (overrideN (updN e y p) ys ps x) = some (overrideC (updC γ y N) ys Ns x)
    by_cases hin : x ∈ ys
    · exact override_ptr ys _ _ ps Ns x hin hok.2 (Nat.succ.inj hl)
    · rw [overrideN_notin _ ys ps x hin, overrideC_notin _ ys Ns x hin]
      have hxy : x = y := by
        cases hx with
        | head => rfl
        | tail _ h => exact absurd h hin
      subst hxy
      unfold updN updC
      rw [if_pos rfl, if_pos rfl]
      exact hok.1

-- ---------------------------------------------------------------------------
-- Popping the arguments
-- ---------------------------------------------------------------------------

/-- The pointers of the top `k` arguments, and the rest of the stack. -/
def popN (heap : List Cell) : Nat → Nat → Option (List Nat × Nat)
  | 0, s => some ([], s)
  | k + 1, s =>
    match heap[s]? with
    | some (.cons x r) => (popN heap k r).map fun p => (x :: p.1, p.2)
    | _ => none

theorem PtrsOK.mono {heap : List Cell} {F G : Nat} (hFG : F ≤ G) :
    ∀ {ps : List Nat} {Ns : List Term}, PtrsOK heap F ps Ns → PtrsOK heap G ps Ns
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨termAt_mono h.1 hFG, PtrsOK.mono hFG h.2⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem popN_spec {heap : List Cell} : ∀ (k : Nat) {s F : Nat} {args : List Term} {ps : List Nat} {r : Nat},
    popN heap k s = some (ps, r) → stackAt heap F s = some args →
    ∃ Ns rest G, G ≤ F ∧ args = Ns ++ rest ∧ Ns.length = k ∧ ps.length = k ∧
      PtrsOK heap F ps Ns ∧ stackAt heap G r = some rest
  | 0, s, F, args, ps, r, hp, hs => by
    cases hp
    exact ⟨[], args, F, Nat.le_refl F, rfl, rfl, rfl, trivial, hs⟩
  | k + 1, s, F, args, ps, r, hp, hs => by
    unfold popN at hp
    cases hc : heap[s]? with
    | none => rw [hc] at hp; cases hp
    | some c =>
      rw [hc] at hp
      cases c with
      | cons x r0 =>
        dsimp only at hp
        cases hq : popN heap k r0 with
        | none => rw [hq] at hp; cases hp
        | some q =>
          obtain ⟨ps0, r1⟩ := q
          rw [hq] at hp
          cases hp
          cases F with
          | zero => unfold stackAt at hs; cases hs
          | succ f =>
            unfold stackAt at hs
            rw [hc] at hs
            dsimp only at hs
            cases hx : termAt heap (f + 1) x with
            | none => rw [hx] at hs; cases hs
            | some tx =>
              cases hr : stackAt heap f r0 with
              | none => rw [hx, hr] at hs; cases hs
              | some rest0 =>
                rw [hx, hr] at hs
                cases hs
                obtain ⟨Ns, rest, G, hG, he, hlN, hlp, hok, hrest⟩ := popN_spec k hq hr
                refine ⟨tx :: Ns, rest, G, by omega, by rw [he]; rfl, by simp [hlN], by simp [hlp],
                  ⟨hx, hok.mono (Nat.le_succ f)⟩, hrest⟩
      | _ => cases hp

-- ---------------------------------------------------------------------------
-- Writing the body
-- ---------------------------------------------------------------------------

/-- Write an open term's cells, children first, each variable replaced by
    the pointer `env` gives it (no cell is written for a variable). -/
def ibuild (env : Nat → Nat) : List Cell → OTerm → List Cell × Nat
  | h, .S => alloc h .S
  | h, .K => alloc h .K
  | h, .I => alloc h .I
  | h, .var x => (h, env x)
  | h, .app f a =>
    let (h1, pf) := ibuild env h f
    let (h2, pa) := ibuild env h1 a
    alloc h2 (.app pf pa)

theorem ibuild_spec (env : Nat → Nat) (σ : Nat → Term) : ∀ (t : OTerm) (h : List Cell),
    (∀ x, Occ x t → termAt h (h.length + 1) (env x) = some (σ x)) →
    ∃ cs, (ibuild env h t).1 = h ++ cs ∧
      termAt (ibuild env h t).1 ((ibuild env h t).1.length + 1) (ibuild env h t).2 = some (t.close σ)
  | .S, h, _ => ⟨[.S], rfl, by simp [ibuild, alloc, termAt, OTerm.close]⟩
  | .K, h, _ => ⟨[.K], rfl, by simp [ibuild, alloc, termAt, OTerm.close]⟩
  | .I, h, _ => ⟨[.I], rfl, by simp [ibuild, alloc, termAt, OTerm.close]⟩
  | .var x, h, henv => ⟨[], by simp [ibuild], by
      show termAt h (h.length + 1) (env x) = some (σ x)
      exact henv x (Occ.var x)⟩
  | .app f a, h, henv => by
    obtain ⟨cs1, e1, t1⟩ := ibuild_spec env σ f h (fun x hx => henv x (Occ.left a hx))
    have henv2 : ∀ x, Occ x a →
        termAt (ibuild env h f).1 ((ibuild env h f).1.length + 1) (env x) = some (σ x) := by
      intro x hx
      rw [e1]
      exact termAt_grow (henv x (.right f hx)) (by simp)
    obtain ⟨cs2, e2, t2⟩ := ibuild_spec env σ a (ibuild env h f).1 henv2
    refine ⟨cs1 ++ cs2 ++ [.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2], ?_, ?_⟩
    · show (ibuild env (ibuild env h f).1 a).1 ++ [_] = _
      rw [e2, e1]; simp
    · show termAt ((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2])
          (((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2]).length + 1)
          (ibuild env (ibuild env h f).1 a).1.length = some ((f.close σ) ⬝ (a.close σ))
      rw [length_concat]
      unfold termAt
      rw [getElem?_concat]
      dsimp only
      have ef : termAt ((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2])
          ((ibuild env (ibuild env h f).1 a).1.length + 1) (ibuild env h f).2 = some (f.close σ) := by
        rw [e2, List.append_assoc]
        refine termAt_grow t1 ?_
        simp
      have ea : termAt ((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2])
          ((ibuild env (ibuild env h f).1 a).1.length + 1) (ibuild env (ibuild env h f).1 a).2 =
          some (a.close σ) :=
        termAt_grow t2 (Nat.le_refl _)
      rw [ef, ea]

-- ---------------------------------------------------------------------------
-- The instantiation step
-- ---------------------------------------------------------------------------

/-- **An instantiation with globals**: pop `|xs|` arguments' pointers and
    write `body` with each formal replaced by its argument's pointer and
    every other variable by the pointer `genv` gives it, a public cell.  The
    head becomes the body's root; the stack, the rest. -/
def instStepG (xs : List Nat) (body : OTerm) (genv : Nat → Nat) (m : Mach) : Option Mach :=
  match popN m.heap xs.length m.stk with
  | some (ps, r) =>
    let (h', root) := ibuild (overrideN genv xs ps) m.heap body
    some ⟨h', root, r⟩
  | none => none

/-- **An instantiation**: `instStepG` with no globals, every variable of
    the body a formal. -/
def instStep (xs : List Nat) (body : OTerm) (m : Mach) : Option Mach :=
  instStepG xs body (fun _ => 0) m

theorem apps_eq_appT : ∀ (t : Term) (as : List Term), apps t as = appT t as
  | _, [] => rfl
  | t, a :: as => apps_eq_appT (t ⬝ a) as

/-- **Instantiation with globals is weak reduction.**  When every variable
    of the body outside `xs` points (by `genv`) to a cell holding its
    meaning under `γ`, and the head is the compiled supercombinator
    `absN xs body` with those meanings, an instantiation leaves a state
    that reads back as a weak reduct of the state before. -/
theorem inst_sound_g {xs : List Nat} {body : OTerm} {genv : Nat → Nat} {γ : Nat → Term}
    {m m' : Mach} {t : Term}
    (hglob : ∀ x, Occ x body → x ∉ xs → termAt m.heap (m.heap.length + 1) (genv x) = some (γ x))
    (hhd : termAt m.heap (m.heap.length + 1) m.hd = some ((absN xs body).close γ))
    (hdec : decode m = some t) (hstep : instStepG xs body genv m = some m') :
    ∃ t', decode m' = some t' ∧ WSteps t t' := by
  obtain ⟨hdT, args, h1, h2, ht⟩ := decode_eq hdec
  rw [hhd] at h1
  cases h1
  unfold instStepG at hstep
  cases hp : popN m.heap xs.length m.stk with
  | none => rw [hp] at hstep; cases hstep
  | some q =>
    obtain ⟨ps, r⟩ := q
    rw [hp] at hstep
    dsimp only at hstep
    cases hstep
    obtain ⟨Ns, rest, G, hG, hargs, hlN, hlp, hok, hrest⟩ := popN_spec xs.length hp h2
    let σ := overrideC γ xs Ns
    let env := overrideN genv xs ps
    have henv : ∀ x, Occ x body → termAt m.heap (m.heap.length + 1) (env x) = some (σ x) := by
      intro x hx
      by_cases hin : x ∈ xs
      · exact override_ptr xs _ _ ps Ns x hin hok hlp
      · show termAt _ _ (overrideN genv xs ps x) = some (overrideC γ xs Ns x)
        rw [overrideN_notin _ xs ps x hin, overrideC_notin _ xs Ns x hin]
        exact hglob x hx hin
    obtain ⟨cs, e, hroot⟩ := ibuild_spec env σ body m.heap henv
    refine ⟨apps (body.close σ) rest, ?_, ?_⟩
    · apply decode_of hroot
      show stackAt (ibuild env m.heap body).1 ((ibuild env m.heap body).1.length + 1) r = some rest
      rw [e]
      exact stackAt_grow hrest (by simp; omega)
    · rw [ht, hargs, apps_eq_appT, apps_eq_appT, appT_append]
      exact WSteps.appT (absN_beta_close xs body γ Ns (by rw [hlN])) rest

/-- **Instantiation is weak reduction.**  When the head is the compiled
    supercombinator `absN xs body`, whose body's variables are among `xs`,
    an instantiation leaves a state that reads back as a weak reduct of the
    state before. -/
theorem inst_sound {xs : List Nat} {body : OTerm} {m m' : Mach} {t : Term}
    (hclosed : ∀ x, Occ x body → x ∈ xs)
    (hhd : termAt m.heap (m.heap.length + 1) m.hd = some (toTerm (absN xs body)))
    (hdec : decode m = some t) (hstep : instStep xs body m = some m') :
    ∃ t', decode m' = some t' ∧ WSteps t t' :=
  inst_sound_g (γ := fun _ => K) (fun x hx hn => absurd (hclosed x hx) hn) hhd hdec hstep

-- ---------------------------------------------------------------------------
-- Jetted runs
-- ---------------------------------------------------------------------------

/-- A licensed template: formals, a body whose variables are among them. -/
structure Template where
  xs : List Nat
  body : OTerm
  closed : ∀ x, Occ x body → x ∈ xs

/-- One step of a jetted run: a machine transition, or an instantiation of
    a template `absN xs body` whose compiled form, with its globals' meanings
    `γ`, is at the head, each global pointing (by `genv`) to a cell that
    holds its meaning. -/
inductive JStep : Mach → Mach → Prop
  | mach {m m' : Mach} : mstep m = some m' → JStep m m'
  | inst {m m' : Mach} (xs : List Nat) (body : OTerm) (genv : Nat → Nat) (γ : Nat → Term) :
      (∀ x, Occ x body → x ∉ xs → termAt m.heap (m.heap.length + 1) (genv x) = some (γ x)) →
      termAt m.heap (m.heap.length + 1) m.hd = some ((absN xs body).close γ) →
      instStepG xs body genv m = some m' → JStep m m'

/-- A licensed closed template instantiates as a jetted step. -/
theorem JStep.ofTemplate {m m' : Mach} (g : Template)
    (hhd : termAt m.heap (m.heap.length + 1) m.hd = some (toTerm (absN g.xs g.body)))
    (hi : instStep g.xs g.body m = some m') : JStep m m' :=
  .inst g.xs g.body (fun _ => 0) (fun _ => K) (fun x hx hn => absurd (g.closed x hx) hn) hhd hi

inductive JSteps : Mach → Mach → Prop
  | refl (m : Mach) : JSteps m m
  | step {m m1 m2 : Mach} : JStep m m1 → JSteps m1 m2 → JSteps m m2

/-- A jetted run reads back as weak reduction. -/
theorem jsteps_wsteps {m m' : Mach} {t : Term} (hdec : decode m = some t) (h : JSteps m m') :
    ∃ u, decode m' = some u ∧ WSteps t u := by
  induction h generalizing t with
  | refl _ => exact ⟨t, hdec, .refl t⟩
  | step hs _ ih =>
    cases hs with
    | mach hm =>
      match mstep_some hdec hm with
      | .inl ⟨_, hd1, _⟩ =>
        obtain ⟨u, hu, hw⟩ := ih hd1
        exact ⟨u, hu, hw⟩
      | .inr ⟨_, u1, hu1, hd1⟩ =>
        obtain ⟨u, hu, hw⟩ := ih hd1
        exact ⟨u, hu, .step (Step.weak (step?_sound hu1)) hw⟩
    | inst xs body genv γ hglob hhd hi =>
      obtain ⟨u1, hd1, hw1⟩ := inst_sound_g hglob hhd hdec hi
      obtain ⟨u, hu, hw⟩ := ih hd1
      exact ⟨u, hu, hw1.trans hw⟩

/-- **A jetted run proves evaluation.**  A jetted run from the loaded term
    that halts on a weak head normal form `v` proves that the term
    evaluates, in normal order, to a value that weakly reduces to `v`. -/
theorem jet_run_eval {t v : Term} {m' : Mach} (h : JSteps (load t) m') (hv : decode m' = some v)
    (hw : Whnf v) : ∃ v', Eval t v' ∧ WSteps v' v := by
  obtain ⟨u, hu, hwu⟩ := jsteps_wsteps (decode_load t) h
  rw [hv] at hu
  cases hu
  exact eval_of_wsteps hwu hw

end Mach
