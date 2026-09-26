import Ski.Words
open Term

set_option linter.unusedSectionVars false

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

## Quotations

A table with `n` static quotations has `n + 3` `quot` constructors, so a
quotation is probed at a function `ks` of `n + 3` continuations, applied
by `appF`: the `k`-th static quotation reaches `ks k`, and the runtime
constructors reach `ks n`, `ks (n + 1)` and `ks (n + 2)`.  `KitElim` holds
the table's elimination lemmas, which the constructor lemmas need; the
functionality proof picks, for each pair of constructors, markers whose
probes end in distinct weak head normal forms.
-/

-- ---------------------------------------------------------------------------
-- Probing, by recursion on the value
-- ---------------------------------------------------------------------------

/-- `t` applied to the continuations `ks 0, …, ks (m - 1)`. -/
def appF (t : Term) (ks : Nat → Term) : Nat → Term
  | 0 => t
  | m + 1 => appF t ks m ⬝ ks m

variable [Kit]

/-- `nat === Zero | Suc nat` -/
def DecNat : Term → Nat → Prop
  | t, 0 => ∀ k0 k1, Steps (t ⬝ k0 ⬝ k1) k0
  | t, n + 1 => ∀ k0 k1, ∃ f, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f) ∧ DecNat f n

mutual
  /-- `item === Num nat | Quot quot` -/
  def DecItem : Term → Item → Prop
    | t, .num n => ∀ k0 k1, ∃ f, Steps (t ⬝ k0 ⬝ k1) (k0 ⬝ f) ∧ DecNat f n
    | t, .quot q => ∀ k0 k1, ∃ f, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f) ∧ DecQuot f q
  /-- `quot === Q_0 | … | Q_(n-1) | QCons item quot | QUnit item | QThen quot` -/
  def DecQuot : Term → Quotation → Prop
    | t, .stat k => k < Kit.n ∧ ∀ ks, Steps (appF t ks (Kit.n + 3)) (ks k)
    | t, .cons x r => ∀ ks, ∃ f g,
        Steps (appF t ks (Kit.n + 3)) (ks Kit.n ⬝ f ⬝ g) ∧ DecItem f x ∧ DecQuot g r
    | t, .unit x => ∀ ks, ∃ f,
        Steps (appF t ks (Kit.n + 3)) (ks (Kit.n + 1) ⬝ f) ∧ DecItem f x
    | t, .then r => ∀ ks, ∃ f,
        Steps (appF t ks (Kit.n + 3)) (ks (Kit.n + 2) ⬝ f) ∧ DecQuot f r
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

theorem Steps.appF {t u : Term} (ks : Nat → Term) (h : Steps t u) :
    ∀ m, Steps (appF t ks m) (appF u ks m)
  | 0 => h
  | m + 1 => Steps.left (ks m) (Steps.appF ks h m)

theorem DecQuot.of_steps {t u : Term} {q : Quotation} (h : Steps t u) (hu : DecQuot u q) :
    DecQuot t q := by
  cases q with
  | stat k => exact ⟨hu.1, fun ks => (h.appF ks _).trans (hu.2 ks)⟩
  | cons x r =>
    intro ks
    cases hu ks with
    | intro f hf =>
      cases hf with
      | intro g hg => exact ⟨f, g, (h.appF ks _).trans hg.1, hg.2⟩
  | unit x =>
    intro ks
    cases hu ks with
    | intro f hf => exact ⟨f, (h.appF ks _).trans hf.1, hf.2⟩
  | «then» r =>
    intro ks
    cases hu ks with
    | intro f hf => exact ⟨f, (h.appF ks _).trans hf.1, hf.2⟩

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

/-- A table's `quot` constructors eliminate as Scott constructors do.  The
    kernel checks these per table (`Ski/Table.lean`). -/
class KitElim [Kit] : Prop where
  Qs_elim : ∀ k, k < Kit.n → ∀ ks, Steps (appF (Kit.Qs k) ks (Kit.n + 3)) (ks k)
  QCons_elim : ∀ x r ks, Steps (appF (Kit.QCons ⬝ x ⬝ r) ks (Kit.n + 3))
    (ks Kit.n ⬝ (K ⬝ x ⬝ ks Kit.n) ⬝ (K ⬝ K ⬝ x ⬝ r ⬝ ks Kit.n))
  QUnit_elim : ∀ x ks, Steps (appF (Kit.QUnit ⬝ x) ks (Kit.n + 3))
    (ks (Kit.n + 1) ⬝ (K ⬝ x ⬝ ks (Kit.n + 1)))
  QThen_elim : ∀ x ks, Steps (appF (Kit.QThen ⬝ x) ks (Kit.n + 3))
    (ks (Kit.n + 2) ⬝ (K ⬝ x ⬝ ks (Kit.n + 2)))

variable [KitElim]

theorem dec_stat {k : Nat} (hk : k < Kit.n) : DecQuot (Kit.Qs k) (.stat k) :=
  ⟨hk, KitElim.Qs_elim k hk⟩

theorem dec_qcons {f g : Term} {x : Item} {r : Quotation} (hf : DecItem f x) (hg : DecQuot g r) :
    DecQuot (Kit.QCons ⬝ f ⬝ g) (.cons x r) :=
  fun ks => ⟨_, _, KitElim.QCons_elim f g ks,
    DecItem.of_steps (steps_thunk1 f _) hf, DecQuot.of_steps (steps_thunk2 f g _) hg⟩

theorem dec_qunit {f : Term} {x : Item} (h : DecItem f x) :
    DecQuot (Kit.QUnit ⬝ f) (.unit x) :=
  fun ks => ⟨_, KitElim.QUnit_elim f ks, DecItem.of_steps (steps_thunk1 f _) h⟩

theorem dec_qthen {f : Term} {r : Quotation} (h : DecQuot f r) :
    DecQuot (Kit.QThen ⬝ f) (.then r) :=
  fun ks => ⟨_, KitElim.QThen_elim f ks, DecQuot.of_steps (steps_thunk1 f _) h⟩

theorem dec_empty : DecStack Scott.Empty [] := fun k0 k1 => Scott.Empty_elim k0 k1

theorem dec_push {f g : Term} {a : Item} {s : Stack} (hf : DecItem f a) (hg : DecStack g s) :
    DecStack (Scott.Push ⬝ f ⬝ g) (a :: s) :=
  fun k0 k1 => ⟨_, _, Scott.Push_elim f g k0 k1,
    DecItem.of_steps (steps_thunk1 f k1) hf, DecStack.of_steps (steps_thunk2 f g k1) hg⟩

theorem dec_rval {f : Term} {s : Stack} (h : DecStack f s) : Decodes (Scott.RVal ⬝ f) (.val s) :=
  fun k0 k1 k2 => ⟨_, Scott.RVal_elim f k0 k1 k2, DecStack.of_steps (steps_thunk1 f k0) h⟩

theorem dec_rerr : Decodes Scott.RErr .err := fun k0 k1 k2 => Scott.RErr_elim k0 k1 k2

/-- `RTime`, the fuelled `apply`'s timeout, decodes to no outcome: probed at
    `S`, `K`, `I` it ends in `I`, where a value ends in `S ⬝ f` and an error
    in `K`. -/
theorem rtime_decodes_nothing (o : Outcome) : ¬ Decodes Scott.RTime o := by
  intro h
  cases o with
  | val s =>
    cases h S K I with
    | intro f hf =>
      have e := steps_whnf_det hf.1 (.S1 f) (Scott.RTime_elim S K I) .I
      cases e
  | err =>
    have e := steps_whnf_det (h S K I) .K (Scott.RTime_elim S K I) .I
    cases e

-- ---------------------------------------------------------------------------
-- Encoded values decode to themselves
-- ---------------------------------------------------------------------------

theorem encNat_dec (n : Nat) : DecNat (encNat n) n := by
  induction n with
  | zero => exact dec_zero
  | succ n ih => exact dec_suc ih

mutual
  theorem encItem_dec : (x : Item) → x.ok Kit.n = true → DecItem (encItem x) x
    | .num n, _ => dec_num (encNat_dec n)
    | .quot q, h => dec_quot (encQuot_dec q h)
  theorem encQuot_dec : (q : Quotation) → q.ok Kit.n = true → DecQuot (encQuot q) q
    | .stat k, h => dec_stat (of_decide_eq_true h)
    | .cons x r, h => by
      simp only [Quotation.ok, Bool.and_eq_true] at h
      exact dec_qcons (encItem_dec x h.1) (encQuot_dec r h.2)
    | .unit x, h => dec_qunit (encItem_dec x h)
    | .then r, h => dec_qthen (encQuot_dec r h)
end

theorem encStack_dec : (s : Stack) → s.all (Item.ok Kit.n) = true → DecStack (encStack s) s
  | [], _ => dec_empty
  | a :: s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact dec_push (encItem_dec a h.1) (encStack_dec s h.2)

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

/-- Probe markers: `K` at `k`, `S` elsewhere, and the reverse. -/
def mkK (k : Nat) : Nat → Term := fun i => if i = k then K else S
def mkS (k : Nat) : Nat → Term := fun i => if i = k then S else K

theorem mkK_self (k : Nat) : mkK k k = K := by simp [mkK]
theorem mkK_ne {i k : Nat} (h : i ≠ k) : mkK k i = S := by simp [mkK, h]
theorem mkS_self (k : Nat) : mkS k k = S := by simp [mkS]
theorem mkS_ne {i k : Nat} (h : i ≠ k) : mkS k i = K := by simp [mkS, h]

theorem DecQuot.probeK {t : Term} {k : Nat} (h : DecQuot t (.stat k)) :
    Steps (appF t (mkK k) (Kit.n + 3)) K := by
  have e := h.2 (mkK k)
  rwa [mkK_self] at e

theorem DecQuot.probeS {t : Term} {k : Nat} (h : DecQuot t (.stat k)) :
    Steps (appF t (mkS k) (Kit.n + 3)) S := by
  have e := h.2 (mkS k)
  rwa [mkS_self] at e

/-- The runtime constructors, probed at `mkK (n + 1)`: `S f g`, `K f`, `S f`. -/
theorem DecQuot.probe_cons {t : Term} {x : Item} {r : Quotation} (h : DecQuot t (.cons x r)) :
    ∃ f g, Steps (appF t (mkK (Kit.n + 1)) (Kit.n + 3)) (S ⬝ f ⬝ g) ∧ DecItem f x ∧ DecQuot g r := by
  cases h (mkK (Kit.n + 1)) with
  | intro f hf =>
    cases hf with
    | intro g hg =>
      rw [mkK_ne (by omega)] at hg
      exact ⟨f, g, hg⟩

theorem DecQuot.probe_unit {t : Term} {x : Item} (h : DecQuot t (.unit x)) :
    ∃ f, Steps (appF t (mkK (Kit.n + 1)) (Kit.n + 3)) (K ⬝ f) ∧ DecItem f x := by
  cases h (mkK (Kit.n + 1)) with
  | intro f hf =>
    rw [mkK_self] at hf
    exact ⟨f, hf⟩

theorem DecQuot.probe_then {t : Term} {r : Quotation} (h : DecQuot t (.then r)) :
    ∃ f, Steps (appF t (mkK (Kit.n + 1)) (Kit.n + 3)) (S ⬝ f) ∧ DecQuot f r := by
  cases h (mkK (Kit.n + 1)) with
  | intro f hf =>
    rw [mkK_ne (by omega)] at hf
    exact ⟨f, hf⟩

-- Distinct constructors never decode the same term.

theorem DecQuot.stat_stat {t : Term} {k j : Nat} (hx : DecQuot t (.stat k))
    (hy : DecQuot t (.stat j)) : k = j := by
  cases Nat.decEq k j with
  | isTrue h => exact h
  | isFalse h =>
    have e := hy.2 (mkK k)
    rw [mkK_ne (Ne.symm h)] at e
    have e' := steps_whnf_det hx.probeK .K e .S
    cases e'

theorem DecQuot.stat_cons {t : Term} {k : Nat} {y : Item} {r : Quotation}
    (hx : DecQuot t (.stat k)) (hy : DecQuot t (.cons y r)) : False := by
  cases hy (mkK k) with | intro f hf => cases hf with | intro g hg =>
  rw [mkK_ne (Nat.ne_of_gt hx.1)] at hg
  have e := steps_whnf_det hx.probeK .K hg.1 (.S2 f g)
  cases e

theorem DecQuot.stat_unit {t : Term} {k : Nat} {y : Item}
    (hx : DecQuot t (.stat k)) (hy : DecQuot t (.unit y)) : False := by
  cases hy (mkS k) with | intro f hf =>
  rw [mkS_ne (by have := hx.1; omega)] at hf
  have e := steps_whnf_det hx.probeS .S hf.1 (.K1 f)
  cases e

theorem DecQuot.stat_then {t : Term} {k : Nat} {r : Quotation}
    (hx : DecQuot t (.stat k)) (hy : DecQuot t (.then r)) : False := by
  cases hy (mkK k) with | intro f hf =>
  rw [mkK_ne (by have := hx.1; omega)] at hf
  have e := steps_whnf_det hx.probeK .K hf.1 (.S1 f)
  cases e

theorem DecQuot.cons_unit {t : Term} {x y : Item} {q : Quotation}
    (hx : DecQuot t (.cons x q)) (hy : DecQuot t (.unit y)) : False := by
  cases hx.probe_cons with | intro f hf => cases hf with | intro g hg =>
  cases hy.probe_unit with | intro f' hf' =>
  have e := steps_whnf_det hg.1 (.S2 f g) hf'.1 (.K1 f')
  cases e

theorem DecQuot.cons_then {t : Term} {x : Item} {q r : Quotation}
    (hx : DecQuot t (.cons x q)) (hy : DecQuot t (.then r)) : False := by
  cases hx.probe_cons with | intro f hf => cases hf with | intro g hg =>
  cases hy.probe_then with | intro f' hf' =>
  have e := steps_whnf_det hg.1 (.S2 f g) hf'.1 (.S1 f')
  cases e

theorem DecQuot.unit_then {t : Term} {x : Item} {r : Quotation}
    (hx : DecQuot t (.unit x)) (hy : DecQuot t (.then r)) : False := by
  cases hx.probe_unit with | intro f hf =>
  cases hy.probe_then with | intro f' hf' =>
  have e := steps_whnf_det hf.1 (.K1 f) hf'.1 (.S1 f')
  cases e

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
    | .stat k, .stat j, hx, hy => by rw [DecQuot.stat_stat hx hy]
    | .stat _, .cons _ _, hx, hy => (DecQuot.stat_cons hx hy).elim
    | .stat _, .unit _, hx, hy => (DecQuot.stat_unit hx hy).elim
    | .stat _, .then _, hx, hy => (DecQuot.stat_then hx hy).elim
    | .cons _ _, .stat _, hx, hy => (DecQuot.stat_cons hy hx).elim
    | .unit _, .stat _, hx, hy => (DecQuot.stat_unit hy hx).elim
    | .then _, .stat _, hx, hy => (DecQuot.stat_then hy hx).elim
    | .cons _ _, .unit _, hx, hy => (DecQuot.cons_unit hx hy).elim
    | .cons _ _, .then _, hx, hy => (DecQuot.cons_then hx hy).elim
    | .unit _, .cons _ _, hx, hy => (DecQuot.cons_unit hy hx).elim
    | .unit _, .then _, hx, hy => (DecQuot.unit_then hx hy).elim
    | .then _, .cons _ _, hx, hy => (DecQuot.cons_then hy hx).elim
    | .then _, .unit _, hx, hy => (DecQuot.unit_then hy hx).elim
    | .cons x q, .cons y r, hx, hy => by
      cases hx.probe_cons with | intro f hf => cases hf with | intro g hg =>
      cases hy.probe_cons with | intro f' hf' => cases hf' with | intro g' hg' =>
      have e := steps_whnf_det hg.1 (.S2 f g) hg'.1 (.S2 f' g')
      cases e
      rw [DecItem.functional x y hg.2.1 hg'.2.1, DecQuot.functional q r hg.2.2 hg'.2.2]
    | .unit x, .unit y, hx, hy => by
      cases hx.probe_unit with | intro f hf =>
      cases hy.probe_unit with | intro f' hf' =>
      have e := steps_whnf_det hf.1 (.K1 f) hf'.1 (.K1 f')
      cases e
      rw [DecItem.functional x y hf.2 hf'.2]
    | .then q, .then r, hx, hy => by
      cases hx.probe_then with | intro f hf =>
      cases hy.probe_then with | intro f' hf' =>
      have e := steps_whnf_det hf.1 (.S1 f) hf'.1 (.S1 f')
      cases e
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
