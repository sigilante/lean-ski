import Ski.Inst
import Ski.Open

open Term

/-!
# The small lemma: weak reduction keeps a stuck spine's head and arity

A weak step contracts a redex anywhere, but a stuck spine has no redex at
its head: a variable, or a combinator short of its arguments.  So every
weak step of it happens inside an argument, and the head and the number of
arguments never change.

- `small_lemma` (open terms): a spine headed by the variable `i` weakly
  reduces only to spines headed by `i`, with as many arguments.
- `small_lemma_whnf` (closed terms): a weak head normal form weakly reduces
  only to weak head normal forms with the same head combinator and arity.

**Why it is needed.**  A jetted run proves weak reduction, not normal-order
reduction.  By standardization it still proves a normal-order value, but
one that only weakly reduces to the run's value (`Mach.jet_run_eval`).
The small lemma says the two agree on what a reader looks at: the head
and the arity (`jet_run_shape`).  A Scott Boolean is `K` or `K I`, and a
Scott constructor is told apart by its head and its number of arguments,
so a jetted run reads back the same datum as an unjetted one.
-/

-- ---------------------------------------------------------------------------
-- Open terms: a variable at the head
-- ---------------------------------------------------------------------------

/-- The head variable and the number of arguments of a variable-headed
    spine. -/
def nhead : OTerm → Option (Nat × Nat)
  | .var i => some (i, 0)
  | .app f _ => (nhead f).map fun p => (p.1, p.2 + 1)
  | _ => none

theorem nhead_step {t u : OTerm} (h : OWStep t u) : ∀ {p : Nat × Nat}, nhead t = some p → nhead u = some p := by
  induction h with
  | S f g x => intro p hp; simp [nhead] at hp
  | K x y => intro p hp; simp [nhead] at hp
  | I x => intro p hp; simp [nhead] at hp
  | @left f f' x _ ih =>
    intro p hp
    unfold nhead at hp ⊢
    cases hf : nhead f with
    | none => rw [hf] at hp; cases hp
    | some q =>
      rw [hf] at hp
      rw [ih hf]
      exact hp
  | right f _ _ => intro p hp; exact hp

theorem nhead_steps {t u : OTerm} (h : OWSteps t u) : ∀ {p : Nat × Nat}, nhead t = some p → nhead u = some p := by
  induction h with
  | refl _ => exact id
  | step hs _ ih => exact fun hp => ih (nhead_step hs hp)

theorem nhead_appL : ∀ (as : List OTerm) {t : OTerm} {i n : Nat}, nhead t = some (i, n) →
    nhead (appL t as) = some (i, n + as.length)
  | [], _, _, _, h => h
  | a :: as, t, i, n, h => by
    have h1 : nhead (t ⬝ₒ a) = some (i, n + 1) := by
      show (nhead t).map _ = _
      rw [h]; rfl
    rw [show n + (a :: as).length = n + 1 + as.length by simp; omega]
    exact nhead_appL as h1

theorem appL_snoc : ∀ (t x : OTerm) (as : List OTerm), appL t (as ++ [x]) = appL t as ⬝ₒ x
  | _, _, [] => rfl
  | t, x, a :: as => appL_snoc (t ⬝ₒ a) x as

theorem nhead_inv : ∀ {w : OTerm} {i n : Nat}, nhead w = some (i, n) →
    ∃ args, w = appL (.var i) args ∧ args.length = n
  | .var j, i, n, h => by
    simp [nhead] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | .app f x, i, n, h => by
    unfold nhead at h
    cases hf : nhead f with
    | none => rw [hf] at h; cases h
    | some q =>
      rw [hf] at h
      obtain ⟨j, m⟩ := q
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨args, hargs, hl⟩ := nhead_inv hf
      exact ⟨args ++ [x], by rw [appL_snoc, hargs], by simp [hl]⟩
  | .S, _, _, h => by simp [nhead] at h
  | .K, _, _, h => by simp [nhead] at h
  | .I, _, _, h => by simp [nhead] at h

/-- **The small lemma.**  A spine headed by the variable `i` weakly reduces
    only to spines headed by `i`, with as many arguments. -/
theorem small_lemma {i : Nat} {args : List OTerm} {w : OTerm}
    (h : OWSteps (appL (.var i) args) w) :
    ∃ args', w = appL (.var i) args' ∧ args'.length = args.length := by
  have h0 : nhead (appL (.var i) args) = some (i, 0 + args.length) := nhead_appL args rfl
  rw [Nat.zero_add] at h0
  exact nhead_inv (nhead_steps h h0)

-- ---------------------------------------------------------------------------
-- Closed terms: a combinator short of its arguments
-- ---------------------------------------------------------------------------

/-- The head combinator (0, 1, 2 for `S`, `K`, `I`) and the number of
    arguments of a spine. -/
def chead : Term → Nat × Nat
  | .S => (0, 0)
  | .K => (1, 0)
  | .I => (2, 0)
  | .app f _ => ((chead f).1, (chead f).2 + 1)

theorem whnf_wstep {v w : Term} (hv : Whnf v) (h : WStep v w) : Whnf w ∧ chead w = chead v := by
  cases hv with
  | S => cases h
  | K => cases h
  | I => cases h
  | S1 x =>
    cases h with
    | left _ h' => cases h'
    | right _ _ => exact ⟨.S1 _, rfl⟩
  | S2 x y =>
    cases h with
    | left _ h' =>
      cases h' with
      | left _ h'' => cases h''
      | right _ _ => exact ⟨.S2 _ _, rfl⟩
    | right _ _ => exact ⟨.S2 _ _, rfl⟩
  | K1 x =>
    cases h with
    | left _ h' => cases h'
    | right _ _ => exact ⟨.K1 _, rfl⟩

/-- **The small lemma, closed.**  A weak head normal form weakly reduces
    only to weak head normal forms with the same head combinator and
    arity. -/
theorem small_lemma_whnf {v w : Term} (hv : Whnf v) (h : WSteps v w) : Whnf w ∧ chead w = chead v := by
  induction h with
  | refl _ => exact ⟨hv, rfl⟩
  | step hs _ ih =>
    obtain ⟨hw1, e1⟩ := whnf_wstep hv hs
    obtain ⟨hw, e⟩ := ih hw1
    exact ⟨hw, e.trans e1⟩

/-- **A jetted run reads back what an unjetted one does.**  A jetted run
    from the loaded term that halts on a weak head normal form `v` proves
    that the term evaluates, in normal order, to a value with `v`'s head
    combinator and arity. -/
theorem jet_run_shape {t v : Term} {m' : Mach} (h : Mach.JSteps (Mach.load t) m')
    (hv : Mach.decode m' = some v) (hw : Whnf v) : ∃ v', Eval t v' ∧ chead v' = chead v := by
  obtain ⟨v', he, hwv⟩ := Mach.jet_run_eval h hv hw
  exact ⟨v', he, (small_lemma_whnf he.2 hwv).2.symm⟩
