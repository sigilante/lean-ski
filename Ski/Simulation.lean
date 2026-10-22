import Ski.Laws
open Term Front

set_option linter.unusedSectionVars false

/-!
# The compiler simulates the source semantics

`Ski/Front.lean` reads SKIjack source and `Ski/Compile.lean` compiles it.
This file gives the source its own operational semantics and proves that
the compiled term of every source term reduces, by weak reduction, the
way the source says: **every source step is matched by zero or more weak
SKI steps**, through a translation relation (`simulation`,
`simulation_steps`).

## The source semantics

A program `P` names each global: a Scott constructor (`GDef.ctor a j m`,
the `j`-th of `m` with `a` fields) or a lowered equation
(`GDef.eqn`, `Ski/Front.lean`).  Source terms (`Cl`) are closed:

- `const t`, an opaque closed term (the value of an unused variable);
- `gref n`, a global;
- `clo caps ps b ρ`, a λ-lifted closure: the λ chain with parameters `ps`
  and body `b`, which captured the binders `caps`, in the environment `ρ`;
- `app f a`.

`inst sc ρ e` instantiates a lowered expression in an environment: its
λ chains become closures, as `Ski/Compile.lean` lifts them.  `SStep`
reduces anywhere outside a closure, as weak reduction does:

- **β**: a closure applied to all its parameters steps to its body,
  instantiated with the parameters bound;
- **δ**: an equation applied to all its parameters steps to its body; a
  recursive equation binds its self-parameter to itself;
- **case**: a constructor applied to its fields and to one continuation
  per constructor of its type steps to its own continuation applied to
  the fields.  A lowered case is its scrutinee applied to the
  continuations in declaration order (`Ski/Front.lean`), so this is case
  analysis.

A closure reduces only when applied to all its parameters: `skijack`
lifts each λ chain to one combinator, and a combinator reduces only with
all its arguments, so partial application is not a source step.

## The translation

`Tr genv P c t` says `t` is a compiled form of `c`, given the compiled
globals `genv`.  It is a relation, not a function, for one reason: `Y`
unrolls a recursive global to a self-reference `fixSelf F z` that is not
the global's compiled term `Y ⬝ F` but behaves as it does (`Tr.self`,
the invariant `Ski/Apply.lean` uses).  Otherwise it is the compiler:
constants are themselves, globals their compiled terms, applications
applications, and a closure the compiled λ chain closed by any
environment its values translate to.

`Fixed P genv` says `genv` is what the compiler gives for `P`: each
constructor's Scott term, and each equation compiled with its globals
resolved by `genv` itself.  For the kernel's source, `kernel_fixed`
checks that the front end's `compileFile` gives such an environment.
-/

-- ---------------------------------------------------------------------------
-- λ chains
-- ---------------------------------------------------------------------------

/-- A λ chain's parameters and body. -/
def Src.peel : Src → List Nat × Src
  | .lam x b => (x :: b.peel.1, b.peel.2)
  | e => ([], e)

theorem Front.CSrc.occurs_resolve (env : Nm → Term) (x : Nat) :
    ∀ e : CSrc, (e.resolve env).occurs x = e.occurs x
  | .glob _ => rfl
  | .var _ => rfl
  | .app f a => by
    show ((f.resolve env).occurs x || (a.resolve env).occurs x) = (f.occurs x || a.occurs x)
    rw [occurs_resolve env x f, occurs_resolve env x a]
  | .lam y b => by
    show (y != x && (b.resolve env).occurs x) = (y != x && b.occurs x)
    rw [occurs_resolve env x b]

theorem Front.CSrc.peel_resolve (env : Nm → Term) :
    ∀ e : CSrc, (e.resolve env).peel = (e.peel.1, e.peel.2.resolve env)
  | .glob _ => rfl
  | .var _ => rfl
  | .app _ _ => rfl
  | .lam x b => by
    show (x :: (b.resolve env).peel.1, (b.resolve env).peel.2) = (x :: b.peel.1, b.peel.2.resolve env)
    rw [peel_resolve env b]

/-- A λ chain lifts to one combinator over its captures and all its
    parameters. -/
theorem compLam_chain : ∀ (e : Src) (caps ps : List Nat),
    compLam caps ps e = wrapLift caps (ps ++ e.peel.1) (comp (caps ++ (ps ++ e.peel.1)) e.peel.2)
  | .glob _, caps, ps => by
    show wrapLift caps ps _ = wrapLift caps (ps ++ []) (comp (caps ++ (ps ++ [])) _)
    rw [List.append_nil]
    rfl
  | .var _, caps, ps => by
    show wrapLift caps ps _ = wrapLift caps (ps ++ []) (comp (caps ++ (ps ++ [])) _)
    rw [List.append_nil]
    rfl
  | .app _ _, caps, ps => by
    show wrapLift caps ps _ = wrapLift caps (ps ++ []) (comp (caps ++ (ps ++ [])) _)
    rw [List.append_nil]
    rfl
  | .lam y b, caps, ps => by
    show compLam caps (ps ++ [y]) b = _
    rw [compLam_chain b caps (ps ++ [y])]
    show wrapLift caps (ps ++ [y] ++ b.peel.1) (comp (caps ++ (ps ++ [y] ++ b.peel.1)) b.peel.2) =
      wrapLift caps (ps ++ (y :: b.peel.1)) (comp (caps ++ (ps ++ (y :: b.peel.1))) b.peel.2)
    rw [List.append_assoc]
    rfl

-- ---------------------------------------------------------------------------
-- The source semantics
-- ---------------------------------------------------------------------------

/-- A global: a Scott constructor, or an equation. -/
inductive GDef
  | ctor (a j m : Nat)
  | eqn (e : FEqn)
  deriving DecidableEq

/-- Closed source terms. -/
inductive Cl
  | const (t : Term)
  | gref (n : Nm)
  | clo (caps ps : List Nat) (b : CSrc) (ρ : Nat → Cl)
  | app (f a : Cl)

/-- `f` applied to `as`, first to last. -/
def Cl.apps : Cl → List Cl → Cl
  | f, [] => f
  | f, a :: as => Cl.apps (.app f a) as

/-- The value of an unbound variable. -/
def junk : Nat → Cl := fun _ => .const K

def updCl (ρ : Nat → Cl) (x : Nat) (v : Cl) : Nat → Cl := fun y => if y = x then v else ρ y

/-- `ρ` with the arguments for the formals, first to last. -/
def overrideCl : (Nat → Cl) → List Nat → List Cl → Nat → Cl
  | ρ, x :: xs, v :: vs => overrideCl (updCl ρ x v) xs vs
  | ρ, _, _ => ρ

/-- A lowered expression in scope `sc` and environment `ρ`: its λ chains
    become closures, capturing the binders of `sc` they name, as `comp`
    lifts them. -/
def inst (sc : List Nat) (ρ : Nat → Cl) : CSrc → Cl
  | .glob n => .gref n
  | .var x => ρ x
  | .app f a => .app (inst sc ρ f) (inst sc ρ a)
  | .lam x b => .clo (sc.filter fun s => (CSrc.lam x b).occurs s) (x :: b.peel.1) b.peel.2 ρ

/-- **The source semantics**: one step of a program `P`. -/
inductive SStep (P : Nm → Option GDef) : Cl → Cl → Prop
  | beta {caps ps : List Nat} {b : CSrc} {ρ : Nat → Cl} {args : List Cl} :
      args.length = ps.length →
      SStep P ((Cl.clo caps ps b ρ).apps args) (inst (caps ++ ps) (overrideCl ρ ps args) b)
  | delta {n : Nm} {ps : List Nat} {b : CSrc} {args : List Cl} :
      P n = some (.eqn ⟨ps, none, b⟩) → args.length = ps.length →
      SStep P ((Cl.gref n).apps args) (inst ps (overrideCl junk ps args) b)
  | fix {n : Nm} {s : Nat} {ps : List Nat} {b : CSrc} {args : List Cl} :
      P n = some (.eqn ⟨ps, some s, b⟩) → args.length = ps.length →
      SStep P ((Cl.gref n).apps args)
        (inst (s :: ps) (overrideCl junk (s :: ps) (.gref n :: args)) b)
  | ctor {n : Nm} {a j m : Nat} {fs ks : List Cl} :
      P n = some (.ctor a j m) → j < m → fs.length = a → ks.length = m →
      SStep P ((Cl.gref n).apps (fs ++ ks)) ((ks.getD j (.const K)).apps fs)
  | left {f f' : Cl} (a : Cl) : SStep P f f' → SStep P (.app f a) (.app f' a)
  | right (f : Cl) {a a' : Cl} : SStep P a a' → SStep P (.app f a) (.app f a')

inductive SSteps (P : Nm → Option GDef) : Cl → Cl → Prop
  | refl (c : Cl) : SSteps P c c
  | step {c c' c'' : Cl} : SStep P c c' → SSteps P c' c'' → SSteps P c c''

-- ---------------------------------------------------------------------------
-- The translation
-- ---------------------------------------------------------------------------

/-- The body of a recursive equation, abstracted over its self-parameter
    and parameters: `Y` is applied to it. -/
def recBody (genv : Nm → Term) (s : Nat) (ps : List Nat) (b : CSrc) : Term :=
  toTerm (absN (s :: ps) (comp (s :: ps) (b.resolve genv)))

/-- **`t` is a compiled form of `c`.** -/
inductive Tr (genv : Nm → Term) (P : Nm → Option GDef) : Cl → Term → Prop
  | const (t : Term) : Tr genv P (.const t) t
  | gref (n : Nm) : Tr genv P (.gref n) (genv n)
  | self {n : Nm} {s : Nat} {ps : List Nat} {b : CSrc} {z : Term} :
      P n = some (.eqn ⟨ps, some s, b⟩) → Steps z (fixB (recBody genv s ps b)) →
      Tr genv P (.gref n) (fixSelf (recBody genv s ps b) z)
  | clo {caps ps : List Nat} {b : CSrc} {ρ : Nat → Cl} {γ : Nat → Term} :
      (∀ i, Tr genv P (ρ i) (γ i)) →
      Tr genv P (.clo caps ps b ρ) ((wrapLift caps ps (comp (caps ++ ps) (b.resolve genv))).close γ)
  | app {f a : Cl} {t u : Term} : Tr genv P f t → Tr genv P a u → Tr genv P (.app f a) (t ⬝ u)

/-- `genv` is what the compiler gives for `P`. -/
def Fixed (P : Nm → Option GDef) (genv : Nm → Term) : Prop :=
  (∀ n a j m, P n = some (.ctor a j m) → genv n = toTerm (ctorO a j m)) ∧
  (∀ n e, P n = some (.eqn e) → genv n = e.compile genv)

-- ---------------------------------------------------------------------------
-- Lists of translations
-- ---------------------------------------------------------------------------

/-- Two lists, related pointwise. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

theorem All2.length {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (h : All2 R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem All2.append {α β : Type} {R : α → β → Prop} {as as' : List α} {bs bs' : List β}
    (h : All2 R as bs) (h' : All2 R as' bs') : All2 R (as ++ as') (bs ++ bs') := by
  induction h with
  | nil => exact h'
  | cons r _ ih => exact .cons r ih

/-- Split a pointwise relation at a prefix of the left list. -/
theorem All2.split {α β : Type} {R : α → β → Prop} :
    ∀ {as as' : List α} {bs : List β}, All2 R (as ++ as') bs →
      ∃ bs1 bs2, bs = bs1 ++ bs2 ∧ All2 R as bs1 ∧ All2 R as' bs2
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: as, as', _, .cons r h =>
    match All2.split (as := as) (as' := as') h with
    | ⟨bs1, bs2, e, h1, h2⟩ => ⟨_ :: bs1, bs2, by rw [e]; rfl, .cons r h1, h2⟩

theorem All2.getD {α β : Type} {R : α → β → Prop} {da : α} {db : β} (hd : R da db) :
    ∀ {as : List α} {bs : List β}, All2 R as bs → ∀ j, R (as.getD j da) (bs.getD j db)
  | _, _, .nil, _ => hd
  | _, _, .cons r _, 0 => r
  | _, _, .cons _ h, j + 1 => All2.getD hd h j

section
variable {genv : Nm → Term} {P : Nm → Option GDef}

/-- A translated application of a list. -/
theorem Tr.apps {f : Cl} {t : Term} (hf : Tr genv P f t) :
    ∀ {as : List Cl} {ts : List Term}, All2 (Tr genv P) as ts → Tr genv P (f.apps as) (appT t ts)
  | _, _, .nil => hf
  | _, _, .cons r h => Tr.apps (Tr.app hf r) h

/-- The translation of an applied list is an applied list. -/
theorem Tr.apps_inv : ∀ {as : List Cl} {f : Cl} {t : Term}, Tr genv P (f.apps as) t →
    ∃ tf ts, t = appT tf ts ∧ Tr genv P f tf ∧ All2 (Tr genv P) as ts
  | [], _, _, h => ⟨_, [], rfl, h, .nil⟩
  | a :: as, f, t, h =>
    match Tr.apps_inv (as := as) h with
    | ⟨tfa, ts, e, hfa, hs⟩ => by
      cases hfa with
      | app hf ha => exact ⟨_, _ :: ts, e, hf, .cons ha hs⟩

theorem Tr.override {ρ : Nat → Cl} {γ : Nat → Term} (h : ∀ i, Tr genv P (ρ i) (γ i)) :
    ∀ {xs : List Nat} {as : List Cl} {ts : List Term}, All2 (Tr genv P) as ts →
      ∀ i, Tr genv P (overrideCl ρ xs as i) (overrideC γ xs ts i)
  | [], _, _, .nil, i => h i
  | [], _, _, .cons _ _, i => h i
  | _ :: _, _, _, .nil, i => h i
  | x :: xs, _, _, .cons r hs, i =>
    Tr.override (ρ := updCl ρ x _) (γ := updC γ x _)
      (fun y => by
        unfold updCl updC
        by_cases e : y = x
        · rw [if_pos e, if_pos e]; exact r
        · rw [if_neg e, if_neg e]; exact h y) hs i

theorem Tr.junk : ∀ i, Tr genv P (junk i) ((fun _ => K : Nat → Term) i) := fun _ => .const K

/-- **Compiling commutes with instantiating**: a lowered expression,
    instantiated in an environment, translates to its compiled term closed
    by any environment the values translate to. -/
theorem tr_inst {ρ : Nat → Cl} {γ : Nat → Term} (h : ∀ i, Tr genv P (ρ i) (γ i)) :
    ∀ (sc : List Nat) (e : CSrc), Tr genv P (inst sc ρ e) ((comp sc (e.resolve genv)).close γ)
  | _, .glob n => by
    show Tr genv P (.gref n) ((genv n).toO.close γ)
    rw [close_toO]
    exact .gref n
  | _, .var x => h x
  | sc, .app f a => .app (tr_inst h sc f) (tr_inst h sc a)
  | sc, .lam x b => by
    show Tr genv P (.clo _ _ _ ρ) ((comp sc (Src.lam x (b.resolve genv))).close γ)
    have e : comp sc (Src.lam x (b.resolve genv)) =
        wrapLift (sc.filter fun s => (CSrc.lam x b).occurs s) (x :: b.peel.1)
          (comp ((sc.filter fun s => (CSrc.lam x b).occurs s) ++ (x :: b.peel.1))
            (b.peel.2.resolve genv)) := by
      have ho : (fun s => (Src.lam x (b.resolve genv)).occurs s) = (fun s => (CSrc.lam x b).occurs s) :=
        funext fun s => CSrc.occurs_resolve genv s (.lam x b)
      show compLam (sc.filter fun s => (Src.lam x (b.resolve genv)).occurs s) [x] (b.resolve genv) = _
      rw [ho, compLam_chain, CSrc.peel_resolve]
      rfl
    rw [e]
    exact .clo h

end

-- ---------------------------------------------------------------------------
-- Target lemmas: `Y` unrolls, and a Scott constructor selects
-- ---------------------------------------------------------------------------

theorem ycomb_step (F : Term) : Steps (Ycomb ⬝ F) (fixSelf F (fixB F)) :=
  iter_sound (k := 1) rfl

/-- A self-reference unrolls to the body applied to the next one. -/
theorem fixSelf_unroll {F z : Term} (hz : Steps z (fixB F)) :
    Steps (fixSelf F z) (F ⬝ fixSelf F (I ⬝ z)) :=
  (iter_sound (k := 3) rfl : Steps (fixSelf F z) (z ⬝ (I ⬝ z))).trans
    ((Steps.left (I ⬝ z) hz).trans (iter_sound (k := 5) rfl))

theorem getD_app_left {α : Type} (d : α) :
    ∀ (l1 l2 : List α) (i : Nat), i < l1.length → (l1 ++ l2).getD i d = l1.getD i d
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l1, l2, i + 1, h => by
    rw [List.cons_append, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_app_left d l1 l2 i (Nat.lt_of_succ_lt_succ h)

theorem getD_app_right {α : Type} (d : α) :
    ∀ (l1 l2 : List α) (i : Nat), (l1 ++ l2).getD (l1.length + i) d = l2.getD i d
  | [], _, i => by rw [List.nil_append, List.length_nil, Nat.zero_add]
  | _ :: l1, l2, i => by
    rw [List.cons_append, List.length_cons, Nat.add_right_comm, List.getD_cons_succ]
    exact getD_app_right d l1 l2 i

theorem map_getD_range {α : Type} (d : α) : ∀ l : List α,
    (List.range l.length).map (fun i => l.getD i d) = l
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.getD_cons_zero]
    have e : ((fun i => (x :: l).getD i d) ∘ Nat.succ) = (fun i => l.getD i d) :=
      funext fun _ => List.getD_cons_succ
    rw [e, map_getD_range d l]

theorem overrideC_range (γ F : Nat → Term) : ∀ L,
    overrideC γ (List.range L) ((List.range L).map F) = fun y => if y < L then F y else γ y
  | 0 => funext fun y => (if_neg (Nat.not_lt_zero y)).symm
  | L + 1 => by
    have e : List.range (L + 1) = List.range L ++ [L] := List.range_succ
    rw [e, List.map_append, overrideC_append γ _ _ _ _ (List.length_map _), overrideC_range γ F L]
    funext y
    show (if y = L then F L else if y < L then F y else γ y) = if y < L + 1 then F y else γ y
    by_cases h1 : y = L
    · rw [if_pos h1, if_pos (by omega), h1]
    · by_cases h2 : y < L
      · rw [if_neg h1, if_pos h2, if_pos (by omega)]
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]

/-- **A Scott constructor selects, closed**: the constructor at position `j`
    of `m` with `a` fields, applied to its fields and `m` continuations,
    weakly reduces to continuation `j` applied to the fields. -/
theorem ctor_close_beta {a j m : Nat} (hj : j < m) {fs ks : List Term}
    (hf : fs.length = a) (hk : ks.length = m) :
    WSteps (appT (toTerm (ctorO a j m)) (fs ++ ks)) (appT (ks.getD j K) fs) := by
  have hl : (fs ++ ks).length = a + m := by rw [List.length_append, hf, hk]
  have h := absN_beta_close (List.range (a + m)) (appL (.var (a + j)) ((List.range a).map .var))
    (fun _ => K) (fs ++ ks) (by rw [hl, List.length_range])
  have e : fs ++ ks = (List.range (a + m)).map (fun i => (fs ++ ks).getD i K) := by
    have := map_getD_range K (fs ++ ks)
    rw [hl] at this
    exact this.symm
  rw [e, overrideC_range, close_appL, List.map_map] at h
  rw [← e] at h
  have e1 : (OTerm.var (a + j)).close
      (fun y => if y < a + m then (fs ++ ks).getD y K else K) = ks.getD j K := by
    show (if a + j < a + m then (fs ++ ks).getD (a + j) K else K) = ks.getD j K
    rw [if_pos (by omega), ← hf]
    exact getD_app_right K fs ks j
  have e2 : (List.range a).map
      (OTerm.close (fun y => if y < a + m then (fs ++ ks).getD y K else K) ∘ OTerm.var) = fs := by
    have e3 : (List.range a).map
        (OTerm.close (fun y => if y < a + m then (fs ++ ks).getD y K else K) ∘ OTerm.var) =
        (List.range fs.length).map (fun i => fs.getD i K) := by
      rw [hf]
      exact List.map_congr_left fun i hi => by
        have hi' := List.mem_range.mp hi
        show (if i < a + m then (fs ++ ks).getD i K else K) = fs.getD i K
        rw [if_pos (by omega)]
        exact getD_app_left K fs ks i (by omega)
    rw [e3, map_getD_range]
  rw [e1, e2] at h
  exact h

-- ---------------------------------------------------------------------------
-- The simulation
-- ---------------------------------------------------------------------------

section
variable {genv : Nm → Term} {P : Nm → Option GDef}

/-- A translated global that is a recursive equation unrolls to its body
    applied to a self-reference that translates it. -/
theorem Tr.unroll (hP : P n = some (.eqn ⟨ps, some s, b⟩)) (hF : Fixed P genv) {t : Term}
    (ht : Tr genv P (.gref n) t) :
    ∃ z, Steps t (recBody genv s ps b ⬝ fixSelf (recBody genv s ps b) z) ∧
      Steps z (fixB (recBody genv s ps b)) := by
  cases ht with
  | gref _ =>
    rw [hF.2 n _ hP]
    exact ⟨_, (ycomb_step _).trans (fixSelf_unroll (.refl _)), .step (.I _) (.refl _)⟩
  | self hP' hz =>
    rw [hP] at hP'
    cases hP'
    exact ⟨_, fixSelf_unroll hz, .step (.I _) hz⟩

/-- **The simulation.**  If `c` steps to `c'` in the source semantics and
    `t` is a compiled form of `c`, then `t` weakly reduces to a compiled
    form of `c'`. -/
theorem simulation (hF : Fixed P genv) {c c' : Cl} (hs : SStep P c c') :
    ∀ {t : Term}, Tr genv P c t → ∃ t', WSteps t t' ∧ Tr genv P c' t' := by
  induction hs with
  | @beta caps ps b ρ args hl =>
    intro t ht
    cases Tr.apps_inv ht with | intro tf h => cases h with | intro ts h =>
    cases h.2.1 with
    | @clo _ _ _ _ γ hρ =>
      rw [h.1]
      exact ⟨_, wrapLift_beta caps ps _ γ ts (h.2.2.length.symm.trans hl),
        tr_inst (Tr.override hρ h.2.2) _ _⟩
  | @delta n ps b args hP hl =>
    intro t ht
    cases Tr.apps_inv ht with | intro tf h => cases h with | intro ts h =>
    cases h.2.1 with
    | gref _ =>
      rw [h.1, hF.2 n _ hP]
      exact ⟨_, absN_beta_close ps (comp ps (b.resolve genv)) (fun _ => K) ts
          (h.2.2.length.symm.trans hl),
        tr_inst (Tr.override Tr.junk h.2.2) _ _⟩
    | self hP' _ =>
      rw [hP] at hP'
      cases hP'
  | @fix n s ps b args hP hl =>
    intro t ht
    cases Tr.apps_inv ht with | intro tf h => cases h with | intro ts h =>
    cases Tr.unroll hP hF h.2.1 with
    | intro z hz =>
      rw [h.1]
      exact ⟨_, (WSteps.appT hz.1.weak ts).trans
          (absN_beta_close (s :: ps) (comp (s :: ps) (b.resolve genv)) (fun _ => K)
            (fixSelf (recBody genv s ps b) z :: ts)
            (congrArg Nat.succ (h.2.2.length.symm.trans hl))),
        tr_inst (Tr.override Tr.junk (.cons (.self hP hz.2) h.2.2)) _ _⟩
  | @ctor n a j m fs ks hP hj hf hk =>
    intro t ht
    cases Tr.apps_inv ht with | intro tf h => cases h with | intro ts h =>
    cases All2.split h.2.2 with | intro tfs h' => cases h' with | intro tks h' =>
    cases h.2.1 with
    | gref _ =>
      rw [h.1, h'.1, hF.1 n a j m hP]
      exact ⟨_, ctor_close_beta hj (h'.2.1.length.symm.trans hf) (h'.2.2.length.symm.trans hk),
        Tr.apps (All2.getD (.const K) h'.2.2 j) h'.2.1⟩
    | self hP' _ =>
      rw [hP] at hP'
      cases hP'
  | left a _ ih =>
    intro t ht
    cases ht with
    | app hf ha =>
      cases ih hf with
      | intro t' h => exact ⟨_, WSteps.left _ h.1, .app h.2 ha⟩
  | right f _ ih =>
    intro t ht
    cases ht with
    | app hf ha =>
      cases ih ha with
      | intro t' h => exact ⟨_, WSteps.right _ h.1, .app hf h.2⟩

/-- **The simulation, for runs.** -/
theorem simulation_steps (hF : Fixed P genv) {c c' : Cl} (hs : SSteps P c c') :
    ∀ {t : Term}, Tr genv P c t → ∃ t', WSteps t t' ∧ Tr genv P c' t' := by
  induction hs with
  | refl c => exact fun ht => ⟨_, .refl _, ht⟩
  | step s _ ih =>
    intro t ht
    cases simulation hF s ht with
    | intro t1 h1 =>
      cases ih h1.2 with
      | intro t2 h2 => exact ⟨t2, h1.1.trans h2.1, h2.2⟩

end

-- ---------------------------------------------------------------------------
-- The program a source file declares, and its compiled environment
-- ---------------------------------------------------------------------------

/-- A file's globals: each type's constructors, then the equations the
    compiler compiles (`fileFEqns`: the prelude it keeps, its equations,
    a core's under `core.eq`).  A declaration named `S`, `K` or `I` is
    not one: at level 0 those names are always the ISA (`resolveIn`), so
    an object type's leaves of those names are reached only by quotation. -/
def progDefs (src : List Nat) : List (Nm × GDef) :=
  match readFile src with
  | none => []
  | some ds =>
    ((types ds).flatMap (fun d =>
      List.zipWith (fun j p => (p.1, GDef.ctor p.2 j d.ctors.length)) (List.range d.ctors.length)
        d.ctors) ++
    ((fileFEqns ds).getD []).map (fun p => (p.1, GDef.eqn p.2))).filter fun p => !isISA p.1

/-- The program a file declares. -/
def progOf (src : List Nat) : Nm → Option GDef := fun n => (progDefs src).lookup n

/-- The file's globals, as the front end compiles and resolves them: the
    ISA, then the program, then Tier 1. -/
def genvOf (src : List Nat) : Nm → Term := fun n => (resolveIn (compiledEnv false src) n).getD K

/-- Each global of `defs` compiled as the compiler compiles it (by
    `ctorOF` and `compileF`, which the kernel evaluates fast). -/
def fixedCheck (defs : List (Nm × GDef)) (genv : Nm → Term) : Bool :=
  defs.all fun p =>
    match defs.lookup p.1 with
    | some (.ctor a j m) => genv p.1 == toTerm (ctorOF a j m)
    | some (.eqn e) => genv p.1 == e.compileF genv
    | none => true

theorem lookup_some_mem : ∀ {l : List (Nm × GDef)} {n : Nm} {d : GDef},
    l.lookup n = some d → ∃ p ∈ l, p.1 = n
  | [], _, _, h => by cases h
  | (k, b) :: l, n, d, h => by
    by_cases e : n = k
    · exact ⟨(k, b), List.mem_cons_self, e.symm⟩
    · have h' : l.lookup n = some d := by
        rw [List.lookup_cons] at h
        have hb : (n == k) = false := by simpa using e
        rw [hb] at h
        exact h
      match lookup_some_mem h' with
      | ⟨p, hp, hp1⟩ => exact ⟨p, List.mem_cons_of_mem _ hp, hp1⟩

theorem fixed_of_check {defs : List (Nm × GDef)} {genv : Nm → Term}
    (h : fixedCheck defs genv = true) : Fixed (fun n => defs.lookup n) genv := by
  unfold fixedCheck at h
  rw [List.all_eq_true] at h
  constructor
  · intro n a j m hn
    have hn : defs.lookup n = some (.ctor a j m) := hn
    match lookup_some_mem hn with
    | ⟨p, hp, hp1⟩ =>
      have hc := h p hp
      rw [hp1, hn] at hc
      rw [← ctorOF_eq]
      exact beq_iff_eq.mp hc
  · intro n e hn
    have hn : defs.lookup n = some (.eqn e) := hn
    match lookup_some_mem hn with
    | ⟨p, hp, hp1⟩ =>
      have hc := h p hp
      rw [hp1, hn] at hc
      rw [← FEqn.compileF_eq]
      exact beq_iff_eq.mp hc

-- ---------------------------------------------------------------------------
-- The four sources `skijack` compiled
-- ---------------------------------------------------------------------------

set_option maxRecDepth 100000 in
/-- **The front end's compiled kernel is what the compiler gives for the
    kernel's program**, so the simulation applies to it.  (The recursion
    limit is the elaborator's, raised for the kernel's evaluation.) -/
theorem kernel_fixed : Fixed (progOf kernelText) (genvOf kernelText) :=
  fixed_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem corpus_fixed : Fixed (progOf corpusText) (genvOf corpusText) :=
  fixed_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem loop_fixed : Fixed (progOf loopText) (genvOf loopText) :=
  fixed_of_check (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sum_fixed : Fixed (progOf sumText) (genvOf sumText) :=
  fixed_of_check (by decide +kernel)

-- ---------------------------------------------------------------------------
-- An instance: `wPop` on a pushed stack
-- ---------------------------------------------------------------------------

/-- `wPop s = s |> { Empty RErr; Push a t (RVal t) }`, as the front end
    reads it: `s0 a1 t2`. -/
theorem prog_wPop : progOf kernelText (nm! "wPop") = some (.eqn ⟨[0], none,
    .app (.app (.var 0) (.glob (nm! "RErr")))
      (.lam 1 (.lam 2 (.app (.glob (nm! "RVal")) (.var 2))))⟩) := by
  decide +kernel

/-- `Push`, the second of `stack`'s two constructors, has two fields. -/
theorem prog_Push : progOf kernelText (nm! "Push") = some (.ctor 2 1 2) := by decide +kernel

theorem prog_RVal : progOf kernelText (nm! "RVal") = some (.ctor 1 0 3) := by decide +kernel

theorem genv_kernel :
    genvOf kernelText (nm! "wPop") = Scott.wPop ∧ genvOf kernelText (nm! "Push") = Scott.Push ∧
      genvOf kernelText (nm! "RVal") = Scott.RVal := by
  decide +kernel

/-- In the source semantics, `wPop (Push x y)` runs to `RVal y`: `δ` for
    `wPop`, the case on `Push`, then `β` for the branch. -/
theorem wPop_source (x y : Term) :
    SSteps (progOf kernelText)
      ((Cl.gref (nm! "wPop")).apps [(Cl.gref (nm! "Push")).apps [.const x, .const y]])
      (.app (.gref (nm! "RVal")) (.const y)) :=
  .step (.delta prog_wPop rfl)
    (.step (.ctor (fs := [.const x, .const y])
        (ks := [.gref (nm! "RErr"), .clo [] [1, 2] (.app (.glob (nm! "RVal")) (.var 2))
          (overrideCl junk [0] [(Cl.gref (nm! "Push")).apps [.const x, .const y]])])
        prog_Push (by decide) rfl rfl)
      (.step (.beta (args := [.const x, .const y]) rfl) (.refl _)))

/-- **The simulation, applied**: the compiled `wPop` on a compiled `Push`
    weakly reduces to `RVal` of the tail, because the source says so. -/
theorem wPop_push (x y : Term) : WSteps (Scott.wPop ⬝ (Scott.Push ⬝ x ⬝ y)) (Scott.RVal ⬝ y) := by
  have ht : Tr (genvOf kernelText) (progOf kernelText)
      ((Cl.gref (nm! "wPop")).apps [(Cl.gref (nm! "Push")).apps [.const x, .const y]])
      (genvOf kernelText (nm! "wPop") ⬝ (genvOf kernelText (nm! "Push") ⬝ x ⬝ y)) :=
    .app (.gref _) (.app (.app (.gref _) (.const x)) (.const y))
  rw [genv_kernel.1, genv_kernel.2.1] at ht
  cases simulation_steps kernel_fixed (wPop_source x y) ht with
  | intro t' h =>
    cases h.2 with
    | app hf ha =>
      cases ha
      cases hf with
      | gref _ =>
        rw [genv_kernel.2.2] at h
        exact h.1
      | self hP _ =>
        rw [prog_RVal] at hP
        cases hP
