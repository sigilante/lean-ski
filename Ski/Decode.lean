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

## Probing at variables

`DecNat t n` and its siblings probe `t` at **fresh variables**
(`Ski/Open.lean`): `t` applied to the variables `vars b 0, vars b 1, …`,
for every `b` above `t`'s own variables, must head-reduce to the variable
of its constructor applied to fields that decode in turn (`DecNatO` and
its siblings, on open terms).  A closed term decodes when its open image
does.

What a word needs is the closed form: probed at *any* closed continuations
`k0, k1, …`, the term head-reduces exactly to the constructor's
continuation applied to decoding fields.  That is `DecNat.probe_zero` and
its siblings, by substituting the continuations for the variables, since
head reduction commutes with substitution.  The generic probe implies
every closed one; the converse, that exact probing at every closed
continuation implies probing at variables, is not proved, so this relation
is at least as strong as closed probing and not shown equal to it.

Two things follow that exact probing at closed continuations does not
obviously give.

- **Closure under backward weak reduction** (`DecNat.of_wsteps` and the
  rest, `Contract.of_wsteps` in `Ski/Leaf.lean`): if `t` weakly reduces to
  `u` and `u` decodes, `t` does.  A probe of `u` ends in a variable-headed
  term; by G1's split, `t`'s probe head-reduces to a term that reaches it
  by internal parallel steps, and those cannot change a variable at the
  head, so `t`'s probe ends at the same variable with fields that weakly
  reduce to `u`'s.
- **Functionality** (`Decodes.functional` and the rest), with no markers:
  two probes of one term at the same variables end in the same stuck term,
  and distinct constructors end at distinct variables.

The fields a probe reaches are thunks, `K ⬝ x ⬝ k` rather than `x` (the
`*_elim` lemmas of `Ski/Scott.lean`); the constructor lemmas `dec_suc`,
`dec_push` and the rest absorb that through backward closure.

## Quotations

A table with `n` static quotations has `n + 3` `quot` constructors, so a
quotation is probed at `n + 3` variables: the `k`-th static quotation
reaches `vars b k`, and the runtime constructors reach `vars b n`,
`vars b (n + 1)` and `vars b (n + 2)`.  `KitElim` holds the table's
elimination lemmas on open terms, which the constructor lemmas need.
-/

-- ---------------------------------------------------------------------------
-- Probing at fresh variables, by recursion on the value
-- ---------------------------------------------------------------------------

variable [Kit]

/-- `nat === Zero | Suc nat` -/
def DecNatO : OTerm → Nat → Prop
  | t, 0 => ∀ b, Fresh b t → OSteps (appO t (vars b) 2) (.var (0 + b))
  | t, n + 1 => ∀ b, Fresh b t → ∃ f,
      OSteps (appO t (vars b) 2) (.var (1 + b) ⬝ₒ f) ∧ DecNatO f n

mutual
  /-- `item === Num nat | Quot quot` -/
  def DecItemO : OTerm → Item → Prop
    | t, .num n => ∀ b, Fresh b t → ∃ f,
        OSteps (appO t (vars b) 2) (.var (0 + b) ⬝ₒ f) ∧ DecNatO f n
    | t, .quot q => ∀ b, Fresh b t → ∃ f,
        OSteps (appO t (vars b) 2) (.var (1 + b) ⬝ₒ f) ∧ DecQuotO f q
  /-- `quot === Q_0 | … | Q_(n-1) | QCons item quot | QUnit item | QThen quot` -/
  def DecQuotO : OTerm → Quotation → Prop
    | t, .stat k => k < Kit.n ∧ ∀ b, Fresh b t →
        OSteps (appO t (vars b) (Kit.n + 3)) (.var (k + b))
    | t, .cons x r => ∀ b, Fresh b t → ∃ f g,
        OSteps (appO t (vars b) (Kit.n + 3)) (.var (Kit.n + b) ⬝ₒ f ⬝ₒ g) ∧
          DecItemO f x ∧ DecQuotO g r
    | t, .unit x => ∀ b, Fresh b t → ∃ f,
        OSteps (appO t (vars b) (Kit.n + 3)) (.var ((Kit.n + 1) + b) ⬝ₒ f) ∧ DecItemO f x
    | t, .then r => ∀ b, Fresh b t → ∃ f,
        OSteps (appO t (vars b) (Kit.n + 3)) (.var ((Kit.n + 2) + b) ⬝ₒ f) ∧ DecQuotO f r
end

/-- `stack === Empty | Push item stack` -/
def DecStackO : OTerm → Stack → Prop
  | t, [] => ∀ b, Fresh b t → OSteps (appO t (vars b) 2) (.var (0 + b))
  | t, a :: s => ∀ b, Fresh b t → ∃ f g,
      OSteps (appO t (vars b) 2) (.var (1 + b) ⬝ₒ f ⬝ₒ g) ∧ DecItemO f a ∧ DecStackO g s

/-- `result === RVal stack | RErr | RTime`.  `RTime` decodes to nothing. -/
def DecodesO : OTerm → Outcome → Prop
  | t, .val s => ∀ b, Fresh b t → ∃ f,
      OSteps (appO t (vars b) 3) (.var (0 + b) ⬝ₒ f) ∧ DecStackO f s
  | t, .err => ∀ b, Fresh b t → OSteps (appO t (vars b) 3) (.var (1 + b))

/-- A closed term decodes when its open image does. -/
def DecNat (t : Term) (n : Nat) : Prop := DecNatO t.toO n
def DecItem (t : Term) (x : Item) : Prop := DecItemO t.toO x
def DecQuot (t : Term) (q : Quotation) : Prop := DecQuotO t.toO q
def DecStack (t : Term) (s : Stack) : Prop := DecStackO t.toO s
def Decodes (t : Term) (o : Outcome) : Prop := DecodesO t.toO o

-- ---------------------------------------------------------------------------
-- Probes move along substitutions
-- ---------------------------------------------------------------------------

/-- A probe at `vars b0`, substituted, is a probe of the substituted term at
    any `vars b`. -/
theorem probe_subst {t E : OTerm} {m b0 : Nat} (τ : Nat → OTerm) (b : Nat) (ht : Fresh b0 t)
    (h : OSteps (appO t (vars b0) m) E) :
    OSteps (appO (t.subst τ) (vars b) m) (E.subst (shiftAt τ b0 b)) := by
  have h' := h.subst (shiftAt τ b0 b)
  rw [subst_appO, subst_shiftAt ht] at h'
  have e : (fun i => (vars b0 i).subst (shiftAt τ b0 b)) = vars b :=
    funext fun i => shiftAt_at τ b0 b i
  rw [e] at h'
  exact h'

theorem subst_end (τ : Nat → OTerm) (b0 b j : Nat) :
    (OTerm.var (j + b0)).subst (shiftAt τ b0 b) = .var (j + b) :=
  shiftAt_at τ b0 b j

theorem DecNatO.subst : ∀ {n : Nat} {t : OTerm} (τ : Nat → OTerm), DecNatO t n →
    DecNatO (t.subst τ) n
  | 0, t, τ, h => by
    intro b _
    cases fresh_exists t with
    | intro b0 hb0 =>
      have e := probe_subst τ b hb0 (h b0 hb0)
      rw [subst_end] at e
      exact e
  | n + 1, t, τ, h => by
    intro b _
    cases fresh_exists t with
    | intro b0 hb0 =>
      cases h b0 hb0 with
      | intro f hf =>
        have e := probe_subst τ b hb0 hf.1
        simp only [OTerm.subst, shiftAt_at] at e
        exact ⟨_, e, DecNatO.subst _ hf.2⟩

mutual
  theorem DecItemO.subst : ∀ {x : Item} {t : OTerm} (τ : Nat → OTerm), DecItemO t x →
      DecItemO (t.subst τ) x
    | .num n, t, τ, h => by
      intro b _
      cases fresh_exists t with
      | intro b0 hb0 =>
        cases h b0 hb0 with
        | intro f hf =>
          have e := probe_subst τ b hb0 hf.1
          simp only [OTerm.subst, shiftAt_at] at e
          exact ⟨_, e, DecNatO.subst _ hf.2⟩
    | .quot q, t, τ, h => by
      intro b _
      cases fresh_exists t with
      | intro b0 hb0 =>
        cases h b0 hb0 with
        | intro f hf =>
          have e := probe_subst τ b hb0 hf.1
          simp only [OTerm.subst, shiftAt_at] at e
          exact ⟨_, e, DecQuotO.subst _ hf.2⟩
  theorem DecQuotO.subst : ∀ {q : Quotation} {t : OTerm} (τ : Nat → OTerm), DecQuotO t q →
      DecQuotO (t.subst τ) q
    | .stat k, t, τ, h => by
      refine ⟨h.1, fun b _ => ?_⟩
      cases fresh_exists t with
      | intro b0 hb0 =>
        have e := probe_subst τ b hb0 (h.2 b0 hb0)
        rw [subst_end] at e
        exact e
    | .cons x r, t, τ, h => by
      intro b _
      cases fresh_exists t with
      | intro b0 hb0 =>
        cases h b0 hb0 with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            have e := probe_subst τ b hb0 hg.1
            simp only [OTerm.subst, shiftAt_at] at e
            exact ⟨_, _, e, DecItemO.subst _ hg.2.1, DecQuotO.subst _ hg.2.2⟩
    | .unit x, t, τ, h => by
      intro b _
      cases fresh_exists t with
      | intro b0 hb0 =>
        cases h b0 hb0 with
        | intro f hf =>
          have e := probe_subst τ b hb0 hf.1
          simp only [OTerm.subst, shiftAt_at] at e
          exact ⟨_, e, DecItemO.subst _ hf.2⟩
    | .then r, t, τ, h => by
      intro b _
      cases fresh_exists t with
      | intro b0 hb0 =>
        cases h b0 hb0 with
        | intro f hf =>
          have e := probe_subst τ b hb0 hf.1
          simp only [OTerm.subst, shiftAt_at] at e
          exact ⟨_, e, DecQuotO.subst _ hf.2⟩
end

theorem DecStackO.subst : ∀ {s : Stack} {t : OTerm} (τ : Nat → OTerm), DecStackO t s →
    DecStackO (t.subst τ) s
  | [], t, τ, h => by
    intro b _
    cases fresh_exists t with
    | intro b0 hb0 =>
      have e := probe_subst τ b hb0 (h b0 hb0)
      rw [subst_end] at e
      exact e
  | a :: s, t, τ, h => by
    intro b _
    cases fresh_exists t with
    | intro b0 hb0 =>
      cases h b0 hb0 with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          have e := probe_subst τ b hb0 hg.1
          simp only [OTerm.subst, shiftAt_at] at e
          exact ⟨_, _, e, DecItemO.subst _ hg.2.1, DecStackO.subst _ hg.2.2⟩

theorem DecodesO.subst {o : Outcome} {t : OTerm} (τ : Nat → OTerm) (h : DecodesO t o) :
    DecodesO (t.subst τ) o := by
  cases o with
  | val s =>
    intro b _
    cases fresh_exists t with
    | intro b0 hb0 =>
      cases h b0 hb0 with
      | intro f hf =>
        have e := probe_subst τ b hb0 hf.1
        simp only [OTerm.subst, shiftAt_at] at e
        exact ⟨_, e, DecStackO.subst _ hf.2⟩
  | err =>
    intro b _
    cases fresh_exists t with
    | intro b0 hb0 =>
      have e := probe_subst τ b hb0 (h b0 hb0)
      rw [subst_end] at e
      exact e

-- ---------------------------------------------------------------------------
-- Closure under backward weak reduction
-- ---------------------------------------------------------------------------

theorem DecNatO.of_owsteps : ∀ {n : Nat} {t u : OTerm}, OWSteps t u → DecNatO u n →
    DecNatO t n
  | 0, _, _, h, hu => fun b hb =>
    owsteps_var0 ((OWSteps.appO _ h 2).trans (hu b (hb.of_owsteps h)).weak)
  | _ + 1, _, _, h, hu => fun b hb =>
    match hu b (hb.of_owsteps h) with
    | ⟨_, hf⟩ =>
      match owsteps_var1 ((OWSteps.appO _ h 2).trans hf.1.weak) with
      | ⟨_, h1, h2⟩ => ⟨_, h1, DecNatO.of_owsteps h2 hf.2⟩

mutual
  theorem DecItemO.of_owsteps : ∀ {x : Item} {t u : OTerm}, OWSteps t u → DecItemO u x →
      DecItemO t x
    | .num _, _, _, h, hu => fun b hb =>
      match hu b (hb.of_owsteps h) with
      | ⟨_, hf⟩ =>
        match owsteps_var1 ((OWSteps.appO _ h 2).trans hf.1.weak) with
        | ⟨_, h1, h2⟩ => ⟨_, h1, DecNatO.of_owsteps h2 hf.2⟩
    | .quot _, _, _, h, hu => fun b hb =>
      match hu b (hb.of_owsteps h) with
      | ⟨_, hf⟩ =>
        match owsteps_var1 ((OWSteps.appO _ h 2).trans hf.1.weak) with
        | ⟨_, h1, h2⟩ => ⟨_, h1, DecQuotO.of_owsteps h2 hf.2⟩
  theorem DecQuotO.of_owsteps : ∀ {q : Quotation} {t u : OTerm}, OWSteps t u → DecQuotO u q →
      DecQuotO t q
    | .stat _, _, _, h, hu => ⟨hu.1, fun b hb =>
      owsteps_var0 ((OWSteps.appO _ h _).trans (hu.2 b (hb.of_owsteps h)).weak)⟩
    | .cons _ _, _, _, h, hu => fun b hb =>
      match hu b (hb.of_owsteps h) with
      | ⟨_, _, hg⟩ =>
        match owsteps_var2 ((OWSteps.appO _ h _).trans hg.1.weak) with
        | ⟨_, _, h1, h2, h3⟩ =>
          ⟨_, _, h1, DecItemO.of_owsteps h2 hg.2.1, DecQuotO.of_owsteps h3 hg.2.2⟩
    | .unit _, _, _, h, hu => fun b hb =>
      match hu b (hb.of_owsteps h) with
      | ⟨_, hf⟩ =>
        match owsteps_var1 ((OWSteps.appO _ h _).trans hf.1.weak) with
        | ⟨_, h1, h2⟩ => ⟨_, h1, DecItemO.of_owsteps h2 hf.2⟩
    | .then _, _, _, h, hu => fun b hb =>
      match hu b (hb.of_owsteps h) with
      | ⟨_, hf⟩ =>
        match owsteps_var1 ((OWSteps.appO _ h _).trans hf.1.weak) with
        | ⟨_, h1, h2⟩ => ⟨_, h1, DecQuotO.of_owsteps h2 hf.2⟩
end

theorem DecStackO.of_owsteps : ∀ {s : Stack} {t u : OTerm}, OWSteps t u → DecStackO u s →
    DecStackO t s
  | [], _, _, h, hu => fun b hb =>
    owsteps_var0 ((OWSteps.appO _ h 2).trans (hu b (hb.of_owsteps h)).weak)
  | _ :: _, _, _, h, hu => fun b hb =>
    match hu b (hb.of_owsteps h) with
    | ⟨_, _, hg⟩ =>
      match owsteps_var2 ((OWSteps.appO _ h 2).trans hg.1.weak) with
      | ⟨_, _, h1, h2, h3⟩ =>
        ⟨_, _, h1, DecItemO.of_owsteps h2 hg.2.1, DecStackO.of_owsteps h3 hg.2.2⟩

theorem DecodesO.of_owsteps {o : Outcome} {t u : OTerm} (h : OWSteps t u) (hu : DecodesO u o) :
    DecodesO t o := by
  cases o with
  | val s =>
    intro b hb
    cases hu b (hb.of_owsteps h) with
    | intro f hf =>
      cases owsteps_var1 ((OWSteps.appO _ h 3).trans hf.1.weak) with
      | intro f' h' => exact ⟨f', h'.1, DecStackO.of_owsteps h'.2 hf.2⟩
  | err =>
    intro b hb
    exact owsteps_var0 ((OWSteps.appO _ h 3).trans (hu b (hb.of_owsteps h)).weak)

/-- **Decoding is closed under backward weak reduction.** -/
theorem DecNat.of_wsteps {t u : Term} {n : Nat} (h : WSteps t u) (hu : DecNat u n) :
    DecNat t n := DecNatO.of_owsteps h.toO hu

theorem DecItem.of_wsteps {t u : Term} {x : Item} (h : WSteps t u) (hu : DecItem u x) :
    DecItem t x := DecItemO.of_owsteps h.toO hu

theorem DecQuot.of_wsteps {t u : Term} {q : Quotation} (h : WSteps t u) (hu : DecQuot u q) :
    DecQuot t q := DecQuotO.of_owsteps h.toO hu

theorem DecStack.of_wsteps {t u : Term} {s : Stack} (h : WSteps t u) (hu : DecStack u s) :
    DecStack t s := DecStackO.of_owsteps h.toO hu

theorem Decodes.of_wsteps {t u : Term} {o : Outcome} (h : WSteps t u) (hu : Decodes u o) :
    Decodes t o := DecodesO.of_owsteps h.toO hu

theorem Steps.app2 {t u : Term} (a b : Term) (h : Steps t u) :
    Steps (t ⬝ a ⬝ b) (u ⬝ a ⬝ b) :=
  Steps.left b (Steps.left a h)

theorem Steps.app3 {t u : Term} (a b c : Term) (h : Steps t u) :
    Steps (t ⬝ a ⬝ b ⬝ c) (u ⬝ a ⬝ b ⬝ c) :=
  Steps.left c (Steps.app2 a b h)

theorem Steps.appF {t u : Term} (ks : Nat → Term) (h : Steps t u) :
    ∀ m, Steps (appF t ks m) (appF u ks m)
  | 0 => h
  | m + 1 => Steps.left (ks m) (Steps.appF ks h m)

theorem DecNat.of_steps {t u : Term} {n : Nat} (h : Steps t u) (hu : DecNat u n) :
    DecNat t n := DecNat.of_wsteps h.weak hu

theorem DecItem.of_steps {t u : Term} {x : Item} (h : Steps t u) (hu : DecItem u x) :
    DecItem t x := DecItem.of_wsteps h.weak hu

theorem DecQuot.of_steps {t u : Term} {q : Quotation} (h : Steps t u) (hu : DecQuot u q) :
    DecQuot t q := DecQuot.of_wsteps h.weak hu

theorem DecStack.of_steps {t u : Term} {s : Stack} (h : Steps t u) (hu : DecStack u s) :
    DecStack t s := DecStack.of_wsteps h.weak hu

theorem Decodes.of_steps {t u : Term} {o : Outcome} (h : Steps t u) (hu : Decodes u o) :
    Decodes t o := Decodes.of_wsteps h.weak hu

/-- "Reduces to a term that probes to `o`" is "probes to `o`". -/
theorem decodes_iff {t : Term} {o : Outcome} :
    Decodes t o ↔ ∃ u, Steps t u ∧ Decodes u o :=
  ⟨fun h => ⟨t, .refl t, h⟩, fun ⟨_, hs, hu⟩ => Decodes.of_steps hs hu⟩

-- ---------------------------------------------------------------------------
-- The closed probes: at any continuations, exactly
-- ---------------------------------------------------------------------------

/-- A probe of a closed term at `vars 0`, closed by `σ`. -/
theorem probe_close {t : Term} {m : Nat} {E : OTerm} (σ : Nat → Term)
    (h : OSteps (appO t.toO (vars 0) m) E) : Steps (appF t (fun i => σ i) m) (E.close σ) := by
  have h' := h.close σ
  rw [close_appO, close_toO] at h'
  exact h'

/-- Fields of an open probe, closed, decode. -/
theorem DecNatO.close {f : OTerm} {n : Nat} (σ : Nat → Term) (h : DecNatO f n) :
    DecNat (f.close σ) n := by
  show DecNatO (f.close σ).toO n
  rw [toO_close]
  exact h.subst _

theorem DecItemO.close {f : OTerm} {x : Item} (σ : Nat → Term) (h : DecItemO f x) :
    DecItem (f.close σ) x := by
  show DecItemO (f.close σ).toO x
  rw [toO_close]
  exact h.subst _

theorem DecQuotO.close {f : OTerm} {q : Quotation} (σ : Nat → Term) (h : DecQuotO f q) :
    DecQuot (f.close σ) q := by
  show DecQuotO (f.close σ).toO q
  rw [toO_close]
  exact h.subst _

theorem DecStackO.close {f : OTerm} {s : Stack} (σ : Nat → Term) (h : DecStackO f s) :
    DecStack (f.close σ) s := by
  show DecStackO (f.close σ).toO s
  rw [toO_close]
  exact h.subst _

/-- Two continuations, as a substitution. -/
def pick2 (k0 k1 : Term) : Nat → Term
  | 0 => k0
  | 1 => k1
  | _ => K

/-- Three continuations, as a substitution. -/
def pick3 (k0 k1 k2 : Term) : Nat → Term
  | 0 => k0
  | 1 => k1
  | 2 => k2
  | _ => K

theorem DecNat.probe_zero {t : Term} (h : DecNat t 0) (k0 k1 : Term) :
    Steps (t ⬝ k0 ⬝ k1) k0 :=
  probe_close (pick2 k0 k1) (h 0 (fresh_toO t 0))

theorem DecNat.probe_succ {t : Term} {n : Nat} (h : DecNat t (n + 1)) (k0 k1 : Term) :
    ∃ f, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f) ∧ DecNat f n :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, hf⟩ => ⟨_, probe_close (pick2 k0 k1) hf.1, hf.2.close _⟩

theorem DecItem.probe_num {t : Term} {n : Nat} (h : DecItem t (.num n)) (k0 k1 : Term) :
    ∃ f, Steps (t ⬝ k0 ⬝ k1) (k0 ⬝ f) ∧ DecNat f n :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, hf⟩ => ⟨_, probe_close (pick2 k0 k1) hf.1, hf.2.close _⟩

theorem DecItem.probe_quot {t : Term} {q : Quotation} (h : DecItem t (.quot q)) (k0 k1 : Term) :
    ∃ f, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f) ∧ DecQuot f q :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, hf⟩ => ⟨_, probe_close (pick2 k0 k1) hf.1, hf.2.close _⟩

theorem DecQuot.probe_stat {t : Term} {k : Nat} (h : DecQuot t (.stat k)) :
    k < Kit.n ∧ ∀ ks, Steps (appF t ks (Kit.n + 3)) (ks k) :=
  ⟨h.1, fun ks => probe_close ks (h.2 0 (fresh_toO t 0))⟩

theorem DecQuot.probe_cons {t : Term} {x : Item} {r : Quotation} (h : DecQuot t (.cons x r))
    (ks : Nat → Term) :
    ∃ f g, Steps (appF t ks (Kit.n + 3)) (ks Kit.n ⬝ f ⬝ g) ∧ DecItem f x ∧ DecQuot g r :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, _, hg⟩ => ⟨_, _, probe_close ks hg.1, hg.2.1.close _, hg.2.2.close _⟩

theorem DecQuot.probe_unit {t : Term} {x : Item} (h : DecQuot t (.unit x)) (ks : Nat → Term) :
    ∃ f, Steps (appF t ks (Kit.n + 3)) (ks (Kit.n + 1) ⬝ f) ∧ DecItem f x :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, hf⟩ => ⟨_, probe_close ks hf.1, hf.2.close _⟩

theorem DecQuot.probe_then {t : Term} {r : Quotation} (h : DecQuot t (.then r)) (ks : Nat → Term) :
    ∃ f, Steps (appF t ks (Kit.n + 3)) (ks (Kit.n + 2) ⬝ f) ∧ DecQuot f r :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, hf⟩ => ⟨_, probe_close ks hf.1, hf.2.close _⟩

theorem DecStack.probe_nil {t : Term} (h : DecStack t []) (k0 k1 : Term) :
    Steps (t ⬝ k0 ⬝ k1) k0 :=
  probe_close (pick2 k0 k1) (h 0 (fresh_toO t 0))

theorem DecStack.probe_cons {t : Term} {a : Item} {s : Stack} (h : DecStack t (a :: s))
    (k0 k1 : Term) :
    ∃ f g, Steps (t ⬝ k0 ⬝ k1) (k1 ⬝ f ⬝ g) ∧ DecItem f a ∧ DecStack g s :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, _, hg⟩ => ⟨_, _, probe_close (pick2 k0 k1) hg.1, hg.2.1.close _, hg.2.2.close _⟩

theorem Decodes.probe_val {t : Term} {s : Stack} (h : Decodes t (.val s)) (k0 k1 k2 : Term) :
    ∃ f, Steps (t ⬝ k0 ⬝ k1 ⬝ k2) (k0 ⬝ f) ∧ DecStack f s :=
  match h 0 (fresh_toO t 0) with
  | ⟨_, hf⟩ => ⟨_, probe_close (pick3 k0 k1 k2) hf.1, hf.2.close _⟩

theorem Decodes.probe_err {t : Term} (h : Decodes t .err) (k0 k1 k2 : Term) :
    Steps (t ⬝ k0 ⬝ k1 ⬝ k2) k1 :=
  probe_close (pick3 k0 k1 k2) (h 0 (fresh_toO t 0))

-- ---------------------------------------------------------------------------
-- Thunks: the fields a probe reaches
-- ---------------------------------------------------------------------------

/-- The first field of every constructor: `K ⬝ x ⬝ k ⟶ x`. -/
theorem steps_thunk1 (x k : Term) : Steps (K ⬝ x ⬝ k) x := .single (.K x k)

/-- The second field of `Push` and `QCons`: `K ⬝ K ⬝ x ⬝ y ⬝ k ⟶* y`. -/
theorem steps_thunk2 (x y k : Term) : Steps (K ⬝ K ⬝ x ⬝ y ⬝ k) y :=
  .step (.left k (.left y (.K K x))) (.single (.K y k))

theorem owsteps_thunk1 (x k : OTerm) : OWSteps (.K ⬝ₒ x ⬝ₒ k) x := (OSteps.single (.K x k)).weak

theorem owsteps_thunk2 (x y k : OTerm) : OWSteps (.K ⬝ₒ .K ⬝ₒ x ⬝ₒ y ⬝ₒ k) y :=
  (OSteps.step (.left k (.left y (.K .K x))) (.single (.K y k))).weak

-- ---------------------------------------------------------------------------
-- Constructor lemmas: each Scott constructor, applied to decoding fields,
-- decodes to the constructed value
-- ---------------------------------------------------------------------------

theorem dec_zero : DecNat Scott.Zero 0 := fun _ _ => Scott.Zero_oelim _ _

theorem dec_suc {f : Term} {n : Nat} (h : DecNat f n) : DecNat (Scott.Suc ⬝ f) (n + 1) :=
  fun _ _ => ⟨_, Scott.Suc_oelim _ _ _, DecNatO.of_owsteps (owsteps_thunk1 _ _) h⟩

theorem dec_num {f : Term} {n : Nat} (h : DecNat f n) : DecItem (Scott.Num ⬝ f) (.num n) :=
  fun _ _ => ⟨_, Scott.Num_oelim _ _ _, DecNatO.of_owsteps (owsteps_thunk1 _ _) h⟩

theorem dec_quot {f : Term} {q : Quotation} (h : DecQuot f q) :
    DecItem (Scott.Quot ⬝ f) (.quot q) :=
  fun _ _ => ⟨_, Scott.Quot_oelim _ _ _, DecQuotO.of_owsteps (owsteps_thunk1 _ _) h⟩

/-- A table's `quot` constructors eliminate as Scott constructors do, on open
    terms.  The kernel checks these per table (`Ski/Table.lean`). -/
class KitElim [Kit] : Prop where
  Qs_elim : ∀ k, k < Kit.n → ∀ ks : Nat → OTerm,
    OSteps (appO (Kit.Qs k).toO ks (Kit.n + 3)) (ks k)
  QCons_elim : ∀ (x r : OTerm) (ks : Nat → OTerm),
    OSteps (appO (Kit.QCons.toO ⬝ₒ x ⬝ₒ r) ks (Kit.n + 3))
      (ks Kit.n ⬝ₒ (.K ⬝ₒ x ⬝ₒ ks Kit.n) ⬝ₒ (.K ⬝ₒ .K ⬝ₒ x ⬝ₒ r ⬝ₒ ks Kit.n))
  QUnit_elim : ∀ (x : OTerm) (ks : Nat → OTerm),
    OSteps (appO (Kit.QUnit.toO ⬝ₒ x) ks (Kit.n + 3))
      (ks (Kit.n + 1) ⬝ₒ (.K ⬝ₒ x ⬝ₒ ks (Kit.n + 1)))
  QThen_elim : ∀ (x : OTerm) (ks : Nat → OTerm),
    OSteps (appO (Kit.QThen.toO ⬝ₒ x) ks (Kit.n + 3))
      (ks (Kit.n + 2) ⬝ₒ (.K ⬝ₒ x ⬝ₒ ks (Kit.n + 2)))

variable [KitElim]

theorem dec_stat {k : Nat} (hk : k < Kit.n) : DecQuot (Kit.Qs k) (.stat k) :=
  ⟨hk, fun b _ => KitElim.Qs_elim k hk (vars b)⟩

theorem dec_qcons {f g : Term} {x : Item} {r : Quotation} (hf : DecItem f x) (hg : DecQuot g r) :
    DecQuot (Kit.QCons ⬝ f ⬝ g) (.cons x r) :=
  fun b _ => ⟨_, _, KitElim.QCons_elim _ _ (vars b),
    DecItemO.of_owsteps (owsteps_thunk1 _ _) hf, DecQuotO.of_owsteps (owsteps_thunk2 _ _ _) hg⟩

theorem dec_qunit {f : Term} {x : Item} (h : DecItem f x) :
    DecQuot (Kit.QUnit ⬝ f) (.unit x) :=
  fun b _ => ⟨_, KitElim.QUnit_elim _ (vars b), DecItemO.of_owsteps (owsteps_thunk1 _ _) h⟩

theorem dec_qthen {f : Term} {r : Quotation} (h : DecQuot f r) :
    DecQuot (Kit.QThen ⬝ f) (.then r) :=
  fun b _ => ⟨_, KitElim.QThen_elim _ (vars b), DecQuotO.of_owsteps (owsteps_thunk1 _ _) h⟩

theorem dec_empty : DecStack Scott.Empty [] := fun _ _ => Scott.Empty_oelim _ _

theorem dec_push {f g : Term} {a : Item} {s : Stack} (hf : DecItem f a) (hg : DecStack g s) :
    DecStack (Scott.Push ⬝ f ⬝ g) (a :: s) :=
  fun _ _ => ⟨_, _, Scott.Push_oelim _ _ _ _,
    DecItemO.of_owsteps (owsteps_thunk1 _ _) hf, DecStackO.of_owsteps (owsteps_thunk2 _ _ _) hg⟩

theorem dec_rval {f : Term} {s : Stack} (h : DecStack f s) : Decodes (Scott.RVal ⬝ f) (.val s) :=
  fun _ _ => ⟨_, Scott.RVal_oelim _ _ _ _, DecStackO.of_owsteps (owsteps_thunk1 _ _) h⟩

theorem dec_rerr : Decodes Scott.RErr .err := fun _ _ => Scott.RErr_oelim _ _ _

/-- `RTime`, the fuelled `apply`'s timeout, decodes to no outcome: probed at
    `S`, `K`, `I` it ends in `I`, where a value ends in `S ⬝ f` and an error
    in `K`. -/
theorem rtime_decodes_nothing (o : Outcome) : ¬ Decodes Scott.RTime o := by
  intro h
  cases o with
  | val s =>
    cases h.probe_val S K I with
    | intro f hf =>
      have e := steps_whnf_det hf.1 (.S1 f) (Scott.RTime_elim S K I) .I
      cases e
  | err =>
    have e := steps_whnf_det (h.probe_err S K I) .K (Scott.RTime_elim S K I) .I
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
-- Both derivations are probed at the same fresh variables.  The probes end in
-- stuck terms, so `osteps_neutral_det` equates the ends; distinct
-- constructors end at distinct variables, and equal ends hand over the
-- fields.
-- ---------------------------------------------------------------------------

theorem ONeutral.v1 (c : Nat) (f : OTerm) : ONeutral (.var c ⬝ₒ f) := .app _ (.var c)

theorem ONeutral.v2 (c : Nat) (f g : OTerm) : ONeutral (.var c ⬝ₒ f ⬝ₒ g) :=
  .app _ (.app _ (.var c))

theorem DecNatO.functional : ∀ {n m : Nat} {t : OTerm}, DecNatO t n → DecNatO t m → n = m := by
  intro n
  induction n with
  | zero =>
    intro m t hn hm
    cases fresh_exists t with
    | intro b hb =>
      cases m with
      | zero => rfl
      | succ m =>
        cases hm b hb with
        | intro f hf =>
          have e := osteps_neutral_det (hn b hb) (.var _) hf.1 (.v1 _ _)
          cases e
  | succ n ih =>
    intro m t hn hm
    cases fresh_exists t with
    | intro b hb =>
      cases hn b hb with
      | intro f hf =>
        cases m with
        | zero =>
          have e := osteps_neutral_det hf.1 (.v1 _ _) (hm b hb) (.var _)
          cases e
        | succ m =>
          cases hm b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            cases e
            rw [ih hf.2 hf'.2]

mutual
  theorem DecItemO.functional {t : OTerm} :
      (x y : Item) → DecItemO t x → DecItemO t y → x = y
    | .num n, .num m, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            cases e
            rw [DecNatO.functional hf.2 hf'.2]
    | .num n, .quot q, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            injection e with e1
            injection e1 with e2
            exact absurd e2 (by omega)
    | .quot q, .num n, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            injection e with e1
            injection e1 with e2
            exact absurd e2 (by omega)
    | .quot q, .quot r, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            cases e
            rw [DecQuotO.functional q r hf.2 hf'.2]
  theorem DecQuotO.functional {t : OTerm} :
      (q r : Quotation) → DecQuotO t q → DecQuotO t r → q = r
    | .stat k, .stat j, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        have e := osteps_neutral_det (hx.2 b hb) (.var _) (hy.2 b hb) (.var _)
        injection e with e1
        rw [Nat.add_right_cancel e1]
    | .stat _, .cons _ _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hy b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            have e := osteps_neutral_det (hx.2 b hb) (.var _) hg.1 (.v2 _ _ _)
            cases e
    | .stat _, .unit _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hy b hb with
        | intro f hf =>
          have e := osteps_neutral_det (hx.2 b hb) (.var _) hf.1 (.v1 _ _)
          cases e
    | .stat _, .then _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hy b hb with
        | intro f hf =>
          have e := osteps_neutral_det (hx.2 b hb) (.var _) hf.1 (.v1 _ _)
          cases e
    | .cons _ _, .stat _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            have e := osteps_neutral_det (hy.2 b hb) (.var _) hg.1 (.v2 _ _ _)
            cases e
    | .unit _, .stat _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          have e := osteps_neutral_det (hy.2 b hb) (.var _) hf.1 (.v1 _ _)
          cases e
    | .then _, .stat _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          have e := osteps_neutral_det (hy.2 b hb) (.var _) hf.1 (.v1 _ _)
          cases e
    | .cons x q, .cons y r, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            cases hy b hb with
            | intro f' hf' =>
              cases hf' with
              | intro g' hg' =>
                have e := osteps_neutral_det hg.1 (.v2 _ _ _) hg'.1 (.v2 _ _ _)
                cases e
                rw [DecItemO.functional x y hg.2.1 hg'.2.1, DecQuotO.functional q r hg.2.2 hg'.2.2]
    | .cons _ _, .unit _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            cases hy b hb with
            | intro f' hf' =>
              have e := osteps_neutral_det hg.1 (.v2 _ _ _) hf'.1 (.v1 _ _)
              injection e with e1
              cases e1
    | .cons _ _, .then _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            cases hy b hb with
            | intro f' hf' =>
              have e := osteps_neutral_det hg.1 (.v2 _ _ _) hf'.1 (.v1 _ _)
              injection e with e1
              cases e1
    | .unit _, .cons _ _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hy b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            cases hx b hb with
            | intro f' hf' =>
              have e := osteps_neutral_det hg.1 (.v2 _ _ _) hf'.1 (.v1 _ _)
              injection e with e1
              cases e1
    | .then _, .cons _ _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hy b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            cases hx b hb with
            | intro f' hf' =>
              have e := osteps_neutral_det hg.1 (.v2 _ _ _) hf'.1 (.v1 _ _)
              injection e with e1
              cases e1
    | .unit x, .unit y, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            cases e
            rw [DecItemO.functional x y hf.2 hf'.2]
    | .unit _, .then _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            injection e with e1
            injection e1 with e2
            exact absurd e2 (by omega)
    | .then _, .unit _, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            injection e with e1
            injection e1 with e2
            exact absurd e2 (by omega)
    | .then q, .then r, hx, hy => by
      cases fresh_exists t with
      | intro b hb =>
        cases hx b hb with
        | intro f hf =>
          cases hy b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            cases e
            rw [DecQuotO.functional q r hf.2 hf'.2]
end

theorem DecStackO.functional : ∀ {s s' : Stack} {t : OTerm}, DecStackO t s → DecStackO t s' →
    s = s' := by
  intro s
  induction s with
  | nil =>
    intro s' t hs hs'
    cases fresh_exists t with
    | intro b hb =>
      cases s' with
      | nil => rfl
      | cons _ _ =>
        cases hs' b hb with
        | intro f hf =>
          cases hf with
          | intro g hg =>
            have e := osteps_neutral_det (hs b hb) (.var _) hg.1 (.v2 _ _ _)
            cases e
  | cons a s ih =>
    intro s' t hs hs'
    cases fresh_exists t with
    | intro b hb =>
      cases hs b hb with
      | intro f hf =>
        cases hf with
        | intro g hg =>
          cases s' with
          | nil =>
            have e := osteps_neutral_det hg.1 (.v2 _ _ _) (hs' b hb) (.var _)
            cases e
          | cons a' s' =>
            cases hs' b hb with
            | intro f' hf' =>
              cases hf' with
              | intro g' hg' =>
                have e := osteps_neutral_det hg.1 (.v2 _ _ _) hg'.1 (.v2 _ _ _)
                cases e
                rw [DecItemO.functional a a' hg.2.1 hg'.2.1, ih hg.2.2 hg'.2.2]

theorem DecodesO.functional {t : OTerm} {o o' : Outcome} (ho : DecodesO t o)
    (ho' : DecodesO t o') : o = o' := by
  cases fresh_exists t with
  | intro b hb =>
    cases o with
    | val s =>
      cases ho b hb with
      | intro f hf =>
        cases o' with
        | val s' =>
          cases ho' b hb with
          | intro f' hf' =>
            have e := osteps_neutral_det hf.1 (.v1 _ _) hf'.1 (.v1 _ _)
            cases e
            rw [DecStackO.functional hf.2 hf'.2]
        | err =>
          have e := osteps_neutral_det hf.1 (.v1 _ _) (ho' b hb) (.var _)
          cases e
    | err =>
      cases o' with
      | val s' =>
        cases ho' b hb with
        | intro f' hf' =>
          have e := osteps_neutral_det (ho b hb) (.var _) hf'.1 (.v1 _ _)
          cases e
      | err => rfl

theorem DecNat.functional {t : Term} {n m : Nat} (hn : DecNat t n) (hm : DecNat t m) : n = m :=
  DecNatO.functional hn hm

theorem DecItem.functional {t : Term} (x y : Item) (hx : DecItem t x) (hy : DecItem t y) :
    x = y := DecItemO.functional x y hx hy

theorem DecQuot.functional {t : Term} (q r : Quotation) (hq : DecQuot t q) (hr : DecQuot t r) :
    q = r := DecQuotO.functional q r hq hr

theorem DecStack.functional {t : Term} {s s' : Stack} (hs : DecStack t s) (hs' : DecStack t s') :
    s = s' := DecStackO.functional hs hs'

/-- **Decoding is a function.**  A term decodes to at most one outcome. -/
theorem Decodes.functional {t : Term} {o o' : Outcome} (ho : Decodes t o) (ho' : Decodes t o') :
    o = o' := DecodesO.functional ho ho'
