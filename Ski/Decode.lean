import Ski.Words
open Term

/-!
# The decode relation

A Nock result is a noun and equals another syntactically.  An SKI result is
a term, and a compiled word returns its value with unreduced fields:
`wPop` on `Push a t` returns `RVal` applied to `K ⬝ K ⬝ a ⬝ t ⬝ k`, not to
`t`.  Values are read by probing, as SKIlark's reader does: apply the term
to one continuation per constructor and see which continuation the
reduction reaches, then read that continuation's arguments the same way.

`DecNat t n` and its siblings say that `t` probes to `n` **at every choice
of continuations**.  A fixed set of markers would be enough to read a
value, but a word receives its input under the next word's continuations,
not under the reader's, so the leaf contracts need the universal form.
The markers reappear in the functionality proofs: choosing `S` and `K` so
that each constructor's probe ends in a distinct weak head normal form
turns `steps_whnf_det` into a case split (`DecNat.functional` and its
siblings).

The relations are closed under backward reduction (`DecNat.of_steps` and
so on), so "`t` reduces to a term that probes to `v`" and "`t` probes to
`v`" coincide (`decodes_iff`).  Each field reached by a probe is a thunk,
`K ⬝ x ⬝ k` rather than `x` (see the `*_elim` lemmas of `Ski/Scott.lean`);
the constructor lemmas `dec_suc`, `dec_push` and the rest absorb that.
-/

-- ---------------------------------------------------------------------------
-- Probing, by recursion on the value
-- ---------------------------------------------------------------------------

/-- `nat === Zero | Suc nat` -/
def DecNat : Term → Nat → Prop
  | t, 0 => ∀ k0 k1, Steps (t ⬝ k0 ⬝ k1) k0
  | t, n + 1 => ∀ k0 k1, ∃ f, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f) ∧ DecNat f n

mutual
  /-- `item === Num nat | Quot quot` -/
  def DecItem : Term → Item → Prop
    | t, .num n => ∀ k0 k1, ∃ f, Steps (t ⬝ k0 ⬝ k1) (k0 ⬝ f) ∧ DecNat f n
    | t, .quot q => ∀ k0 k1, ∃ f, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f) ∧ DecQuot f q
  /-- `quot === QCons item quot | QUnit item | QThen quot` -/
  def DecQuot : Term → Quotation → Prop
    | t, .cons x r => ∀ k0 k1 k2, ∃ f g,
        Steps (t ⬝ k0 ⬝ k1 ⬝ k2) (k0 ⬝ f ⬝ g) ∧ DecItem f x ∧ DecQuot g r
    | t, .unit x => ∀ k0 k1 k2, ∃ f, Steps (t ⬝ k0 ⬝ k1 ⬝ k2) (k1 ⬝ f) ∧ DecItem f x
    | t, .then r => ∀ k0 k1 k2, ∃ f, Steps (t ⬝ k0 ⬝ k1 ⬝ k2) (k2 ⬝ f) ∧ DecQuot f r
end

/-- `stack === Empty | Push item stack` -/
def DecStack : Term → Stack → Prop
  | t, [] => ∀ k0 k1, Steps (t ⬝ k0 ⬝ k1) k0
  | t, a :: s => ∀ k0 k1, ∃ f g,
      Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f ⬝ g) ∧ DecItem f a ∧ DecStack g s

/-- `result === RVal stack | RErr | RTime`.  `RTime` decodes to nothing. -/
def Decodes : Term → Outcome → Prop
  | t, .val s => ∀ k0 k1 k2, ∃ f, Steps (t ⬝ k0 ⬝ k1 ⬝ k2) (k0 ⬝ f) ∧ DecStack f s
  | t, .err => ∀ k0 k1 k2, Steps (t ⬝ k0 ⬝ k1 ⬝ k2) k1

-- ---------------------------------------------------------------------------
-- Closure under backward reduction
-- ---------------------------------------------------------------------------

theorem Steps.app2 {t u : Term} (a b : Term) (h : Steps t u) :
    Steps (t ⬝ a ⬝ b) (u ⬝ a ⬝ b) :=
  Steps.left b (Steps.left a h)

theorem Steps.app3 {t u : Term} (a b c : Term) (h : Steps t u) :
    Steps (t ⬝ a ⬝ b ⬝ c) (u ⬝ a ⬝ b ⬝ c) :=
  Steps.left c (Steps.app2 a b h)

theorem DecNat.of_steps {t u : Term} {n : Nat} (h : Steps t u) (hu : DecNat u n) :
    DecNat t n := by
  cases n with
  | zero => exact fun k0 k1 => (h.app2 k0 k1).trans (hu k0 k1)
  | succ n =>
    intro k0 k1
    cases hu k0 k1 with
    | intro f hf => exact ⟨f, (h.app2 k0 k1).trans hf.1, hf.2⟩

theorem DecItem.of_steps {t u : Term} {x : Item} (h : Steps t u) (hu : DecItem u x) :
    DecItem t x := by
  cases x with
  | num n =>
    intro k0 k1
    cases hu k0 k1 with
    | intro f hf => exact ⟨f, (h.app2 k0 k1).trans hf.1, hf.2⟩
  | quot q =>
    intro k0 k1
    cases hu k0 k1 with
    | intro f hf => exact ⟨f, (h.app2 k0 k1).trans hf.1, hf.2⟩

theorem DecQuot.of_steps {t u : Term} {q : Quotation} (h : Steps t u) (hu : DecQuot u q) :
    DecQuot t q := by
  cases q with
  | cons x r =>
    intro k0 k1 k2
    cases hu k0 k1 k2 with
    | intro f hf =>
      cases hf with
      | intro g hg => exact ⟨f, g, (h.app3 k0 k1 k2).trans hg.1, hg.2⟩
  | unit x =>
    intro k0 k1 k2
    cases hu k0 k1 k2 with
    | intro f hf => exact ⟨f, (h.app3 k0 k1 k2).trans hf.1, hf.2⟩
  | «then» r =>
    intro k0 k1 k2
    cases hu k0 k1 k2 with
    | intro f hf => exact ⟨f, (h.app3 k0 k1 k2).trans hf.1, hf.2⟩

theorem DecStack.of_steps {t u : Term} {s : Stack} (h : Steps t u) (hu : DecStack u s) :
    DecStack t s := by
  cases s with
  | nil => exact fun k0 k1 => (h.app2 k0 k1).trans (hu k0 k1)
  | cons a s =>
    intro k0 k1
    cases hu k0 k1 with
    | intro f hf =>
      cases hf with
      | intro g hg => exact ⟨f, g, (h.app2 k0 k1).trans hg.1, hg.2⟩

theorem Decodes.of_steps {t u : Term} {o : Outcome} (h : Steps t u) (hu : Decodes u o) :
    Decodes t o := by
  cases o with
  | val s =>
    intro k0 k1 k2
    cases hu k0 k1 k2 with
    | intro f hf => exact ⟨f, (h.app3 k0 k1 k2).trans hf.1, hf.2⟩
  | err => exact fun k0 k1 k2 => (h.app3 k0 k1 k2).trans (hu k0 k1 k2)

/-- "Reduces to a term that probes to `o`" is "probes to `o`". -/
theorem decodes_iff {t : Term} {o : Outcome} :
    Decodes t o ↔ ∃ u, Steps t u ∧ Decodes u o :=
  ⟨fun h => ⟨t, .refl t, h⟩, fun ⟨_, hs, hu⟩ => Decodes.of_steps hs hu⟩

-- ---------------------------------------------------------------------------
-- Thunks: the fields a probe reaches
-- ---------------------------------------------------------------------------

/-- The first field of every constructor: `K ⬝ x ⬝ k ⟶ x`. -/
theorem steps_thunk1 (x k : Term) : Steps (K ⬝ x ⬝ k) x := .single (.K x k)

/-- The second field of `Push` and `QCons`: `K ⬝ K ⬝ x ⬝ y ⬝ k ⟶* y`. -/
theorem steps_thunk2 (x y k : Term) : Steps (K ⬝ K ⬝ x ⬝ y ⬝ k) y :=
  .step (.left k (.left y (.K K x))) (.single (.K y k))

-- ---------------------------------------------------------------------------
-- Constructor lemmas: each Scott constructor, applied to decoding fields,
-- decodes to the constructed value
-- ---------------------------------------------------------------------------

theorem dec_zero : DecNat Scott.Zero 0 := fun k0 k1 => Scott.Zero_elim k0 k1

theorem dec_suc {f : Term} {n : Nat} (h : DecNat f n) : DecNat (Scott.Suc ⬝ f) (n + 1) :=
  fun k0 k1 => ⟨_, Scott.Suc_elim f k0 k1, DecNat.of_steps (steps_thunk1 f k1) h⟩

theorem dec_num {f : Term} {n : Nat} (h : DecNat f n) : DecItem (Scott.Num ⬝ f) (.num n) :=
  fun k0 k1 => ⟨_, Scott.Num_elim f k0 k1, DecNat.of_steps (steps_thunk1 f k0) h⟩

theorem dec_quot {f : Term} {q : Quotation} (h : DecQuot f q) :
    DecItem (Scott.Quot ⬝ f) (.quot q) :=
  fun k0 k1 => ⟨_, Scott.Quot_elim f k0 k1, DecQuot.of_steps (steps_thunk1 f k1) h⟩

theorem dec_qcons {f g : Term} {x : Item} {r : Quotation} (hf : DecItem f x) (hg : DecQuot g r) :
    DecQuot (Scott.QCons ⬝ f ⬝ g) (.cons x r) :=
  fun k0 k1 k2 => ⟨_, _, Scott.QCons_elim f g k0 k1 k2,
    DecItem.of_steps (steps_thunk1 f k0) hf, DecQuot.of_steps (steps_thunk2 f g k0) hg⟩

theorem dec_qunit {f : Term} {x : Item} (h : DecItem f x) :
    DecQuot (Scott.QUnit ⬝ f) (.unit x) :=
  fun k0 k1 k2 => ⟨_, Scott.QUnit_elim f k0 k1 k2, DecItem.of_steps (steps_thunk1 f k1) h⟩

theorem dec_qthen {f : Term} {r : Quotation} (h : DecQuot f r) :
    DecQuot (Scott.QThen ⬝ f) (.then r) :=
  fun k0 k1 k2 => ⟨_, Scott.QThen_elim f k0 k1 k2, DecQuot.of_steps (steps_thunk1 f k2) h⟩

theorem dec_empty : DecStack Scott.Empty [] := fun k0 k1 => Scott.Empty_elim k0 k1

theorem dec_push {f g : Term} {a : Item} {s : Stack} (hf : DecItem f a) (hg : DecStack g s) :
    DecStack (Scott.Push ⬝ f ⬝ g) (a :: s) :=
  fun k0 k1 => ⟨_, _, Scott.Push_elim f g k0 k1,
    DecItem.of_steps (steps_thunk1 f k1) hf, DecStack.of_steps (steps_thunk2 f g k1) hg⟩

theorem dec_rval {f : Term} {s : Stack} (h : DecStack f s) : Decodes (Scott.RVal ⬝ f) (.val s) :=
  fun k0 k1 k2 => ⟨_, Scott.RVal_elim f k0 k1 k2, DecStack.of_steps (steps_thunk1 f k0) h⟩

theorem dec_rerr : Decodes Scott.RErr .err := fun k0 k1 k2 => Scott.RErr_elim k0 k1 k2

-- ---------------------------------------------------------------------------
-- Encoded values decode to themselves
-- ---------------------------------------------------------------------------

theorem encNat_dec (n : Nat) : DecNat (encNat n) n := by
  induction n with
  | zero => exact dec_zero
  | succ n ih => exact dec_suc ih

mutual
  theorem encItem_dec : (x : Item) → DecItem (encItem x) x
    | .num n => dec_num (encNat_dec n)
    | .quot q => dec_quot (encQuot_dec q)
  theorem encQuot_dec : (q : Quotation) → DecQuot (encQuot q) q
    | .cons x r => dec_qcons (encItem_dec x) (encQuot_dec r)
    | .unit x => dec_qunit (encItem_dec x)
    | .then r => dec_qthen (encQuot_dec r)
end

theorem encStack_dec (s : Stack) : DecStack (encStack s) s := by
  induction s with
  | nil => exact dec_empty
  | cons a s ih => exact dec_push (encItem_dec a) ih

-- ---------------------------------------------------------------------------
-- Decoding is a function
--
-- Each proof probes both derivations at the same markers, chosen so that
-- the constructors' probes end in distinct weak head normal forms; then
-- `steps_whnf_det` equates the ends, and constructor injectivity either
-- refutes the case or hands over the fields.
-- ---------------------------------------------------------------------------

theorem DecNat.functional {t : Term} {n m : Nat} (hn : DecNat t n) (hm : DecNat t m) :
    n = m := by
  induction n generalizing t m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      cases hm K S with
      | intro f hf =>
        have h := steps_whnf_det (hn K S) .K hf.1 (.S1 f)
        cases h
  | succ n ih =>
    cases m with
    | zero =>
      cases hn K S with
      | intro f hf =>
        have h := steps_whnf_det hf.1 (.S1 f) (hm K S) .K
        cases h
    | succ m =>
      cases hn K S with
      | intro f hf =>
        cases hm K S with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.S1 f) hf'.1 (.S1 f')
          cases h
          rw [ih hf.2 hf'.2]

mutual
  theorem DecItem.functional {t : Term} :
      (x y : Item) → DecItem t x → DecItem t y → x = y
    | .num n, .num m, hx, hy => by
      cases hx S K with
      | intro f hf =>
        cases hy S K with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.S1 f) hf'.1 (.S1 f')
          cases h
          rw [DecNat.functional hf.2 hf'.2]
    | .num n, .quot q, hx, hy => by
      cases hx S K with
      | intro f hf =>
        cases hy S K with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.S1 f) hf'.1 (.K1 f')
          cases h
    | .quot q, .num n, hx, hy => by
      cases hx S K with
      | intro f hf =>
        cases hy S K with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.K1 f) hf'.1 (.S1 f')
          cases h
    | .quot q, .quot r, hx, hy => by
      cases hx S K with
      | intro f hf =>
        cases hy S K with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.K1 f) hf'.1 (.K1 f')
          cases h
          rw [DecQuot.functional q r hf.2 hf'.2]
  theorem DecQuot.functional {t : Term} :
      (q r : Quotation) → DecQuot t q → DecQuot t r → q = r
    | .cons x q, .cons y r, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          cases hy S K S with
          | intro f' hf' =>
            cases hf' with
            | intro g' hg' =>
              have h := steps_whnf_det hg.1 (.S2 f g) hg'.1 (.S2 f' g')
              cases h
              rw [DecItem.functional x y hg.2.1 hg'.2.1, DecQuot.functional q r hg.2.2 hg'.2.2]
    | .cons x q, .unit y, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          cases hy S K S with
          | intro f' hf' =>
            have h := steps_whnf_det hg.1 (.S2 f g) hf'.1 (.K1 f')
            cases h
    | .cons x q, .then r, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          cases hy S K S with
          | intro f' hf' =>
            have h := steps_whnf_det hg.1 (.S2 f g) hf'.1 (.S1 f')
            cases h
    | .unit x, .cons y r, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hy S K S with
        | intro f' hf' =>
          cases hf' with
          | intro g' hg' =>
            have h := steps_whnf_det hf.1 (.K1 f) hg'.1 (.S2 f' g')
            cases h
    | .unit x, .unit y, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hy S K S with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.K1 f) hf'.1 (.K1 f')
          cases h
          rw [DecItem.functional x y hf.2 hf'.2]
    | .unit x, .then r, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hy S K S with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.K1 f) hf'.1 (.S1 f')
          cases h
    | .then q, .cons y r, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hy S K S with
        | intro f' hf' =>
          cases hf' with
          | intro g' hg' =>
            have h := steps_whnf_det hf.1 (.S1 f) hg'.1 (.S2 f' g')
            cases h
    | .then q, .unit y, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hy S K S with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.S1 f) hf'.1 (.K1 f')
          cases h
    | .then q, .then r, hx, hy => by
      cases hx S K S with
      | intro f hf =>
        cases hy S K S with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.S1 f) hf'.1 (.S1 f')
          cases h
          rw [DecQuot.functional q r hf.2 hf'.2]
end

theorem DecStack.functional {t : Term} {s s' : Stack} (hs : DecStack t s) (hs' : DecStack t s') :
    s = s' := by
  induction s generalizing t s' with
  | nil =>
    cases s' with
    | nil => rfl
    | cons b s' =>
      cases hs' K S with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          have h := steps_whnf_det (hs K S) .K hg.1 (.S2 f g)
          cases h
  | cons a s ih =>
    cases s' with
    | nil =>
      cases hs K S with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          have h := steps_whnf_det hg.1 (.S2 f g) (hs' K S) .K
          cases h
    | cons b s' =>
      cases hs K S with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          cases hs' K S with
          | intro f' hf' =>
            cases hf' with
            | intro g' hg' =>
              have h := steps_whnf_det hg.1 (.S2 f g) hg'.1 (.S2 f' g')
              cases h
              rw [DecItem.functional a b hg.2.1 hg'.2.1, ih hg.2.2 hg'.2.2]

/-- **Decoding is a function.**  A term decodes to at most one outcome. -/
theorem Decodes.functional {t : Term} {o o' : Outcome} (ho : Decodes t o) (ho' : Decodes t o') :
    o = o' := by
  cases o with
  | val s =>
    cases o' with
    | val s' =>
      cases ho S K S with
      | intro f hf =>
        cases ho' S K S with
        | intro f' hf' =>
          have h := steps_whnf_det hf.1 (.S1 f) hf'.1 (.S1 f')
          cases h
          rw [DecStack.functional hf.2 hf'.2]
    | err =>
      cases ho S K S with
      | intro f hf =>
        have h := steps_whnf_det hf.1 (.S1 f) (ho' S K S) .K
        cases h
  | err =>
    cases o' with
    | val s' =>
      cases ho' S K S with
      | intro f hf =>
        have h := steps_whnf_det (ho S K S) .K hf.1 (.S1 f)
        cases h
    | err => rfl
