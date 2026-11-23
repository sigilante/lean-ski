import Ski.SelfInterp

open Term

/-!
# Faithfulness at a site: the interpreter over a fifth symbol

§5.2 of the metacircular paper extends the object language with a leaf `Err`
that has no contraction rule, and builds two interpreters that differ only in
the step arm selected when `Err` reaches the head: `errArmAbs`, which exposes
the crash as a value, and `errArmOmg`, which absorbs it into divergence.  Its
Lemma 5.3 says that two interpreters identical except in that arm agree on
every object term whose reduction never brings `Err` into head position.

Here the arm is a parameter.  `wf5 e` is the artifact's five-symbol
interpreter (`tower_harness.py`, `wf5Abs`/`wf5Omg`) with an arbitrary closed
term `e` at the site, so "identical except in the arm" holds by construction;
at the paper's two arms it has the paper's 768 and 771 atoms (`wf5_atoms`).
The paper prints neither term, so only the counts are pinned.

`Run5 k t o` is the object-level run at budget `k`: `val N`, `time`, or
`crash` when `Err` is at the head of a reduct.  `wf5_run` is fuel adequacy
for every arm off the site, and for an arm that answers `errd` on it.

* Lemma 5.3 in the special case ℓ = `Err` for the artifact's interpreter family `wf5 e` (the
  paper quantifies over any leaf ℓ and any two interpreters): `faithful_site` (the paper's
  hypothesis, at every budget) and
  `faithful_run` (the sharper form: no `Err` at the head within the budget).
* The exposing interpreter's column of Table 1: `wf5Abs_run`.

The hiding column ("host diverges") is not formalized.  As in
`Ski/SelfInterp.lean`, `↠` is weak reduction.
-/

namespace SelfInterp

open Requote

-- ---------------------------------------------------------------------------
-- The five-symbol object language
-- ---------------------------------------------------------------------------

/-- Object terms with the fifth leaf. -/
inductive T5
  | S | K | I | Err
  | app : T5 → T5 → T5

infixl:70 " ⬝₅ " => T5.app

/-- The head leaf. -/
def head5 : T5 → T5
  | .app f _ => head5 f
  | t => t

/-- Weak head normal forms: `S`, `K` or `I` short of its arguments. -/
inductive Whnf5 : T5 → Prop
  | S : Whnf5 .S
  | K : Whnf5 .K
  | I : Whnf5 .I
  | S1 (x : T5) : Whnf5 (.S ⬝₅ x)
  | S2 (x y : T5) : Whnf5 (.S ⬝₅ x ⬝₅ y)
  | K1 (x : T5) : Whnf5 (.K ⬝₅ x)

/-- One contraction at the head.  `Err` has no rule. -/
inductive Step5 : T5 → T5 → Prop
  | S (f g x : T5) : Step5 (.S ⬝₅ f ⬝₅ g ⬝₅ x) (f ⬝₅ x ⬝₅ (g ⬝₅ x))
  | K (x y : T5) : Step5 (.K ⬝₅ x ⬝₅ y) x
  | I (x : T5) : Step5 (.I ⬝₅ x) x
  | left {f f' : T5} (x : T5) (h : Step5 f f') : Step5 (f ⬝₅ x) (f' ⬝₅ x)

inductive Steps5 : T5 → T5 → Prop
  | refl (t : T5) : Steps5 t t
  | step {t t' u : T5} (h : Step5 t t') (hs : Steps5 t' u) : Steps5 t u

theorem Whnf5.no_step {t u : T5} (hw : Whnf5 t) (hs : Step5 t u) : False := by
  induction hs with
  | S f g x => cases hw
  | K x y => cases hw
  | I x => cases hw
  | left x h _ =>
    cases hw with
    | S1 _ => cases h
    | K1 _ => cases h
    | S2 _ _ => cases h with | left _ h' => cases h'

theorem Step5.det {t u v : T5} (h₁ : Step5 t u) (h₂ : Step5 t v) : u = v := by
  induction h₁ generalizing v with
  | S f g x =>
    cases h₂ with
    | S => rfl
    | left _ h => exact (Whnf5.no_step (.S2 f g) h).elim
  | K x y =>
    cases h₂ with
    | K => rfl
    | left _ h => exact (Whnf5.no_step (.K1 x) h).elim
  | I x =>
    cases h₂ with
    | I => rfl
    | left _ h => exact (Whnf5.no_step .I h).elim
  | left x h ih =>
    cases h₂ with
    | S => exact (Whnf5.no_step (.S2 _ _) h).elim
    | K => exact (Whnf5.no_step (.K1 _) h).elim
    | I => exact (Whnf5.no_step .I h).elim
    | left _ h' => rw [ih h']

theorem Whnf5.head {t : T5} (hw : Whnf5 t) : head5 t ≠ .Err := by
  cases hw <;> (intro h; cases h)

theorem Step5.head {t u : T5} (hs : Step5 t u) : head5 t ≠ .Err := by
  induction hs with
  | S f g x => intro h; cases h
  | K x y => intro h; cases h
  | I x => intro h; cases h
  | left x _ ih => exact ih

/-- `t` applied to a list of arguments. -/
def appT5 : T5 → List T5 → T5
  | t, [] => t
  | t, a :: as => appT5 (t ⬝₅ a) as

theorem step5_appT {t u : T5} (h : Step5 t u) : ∀ as : List T5, Step5 (appT5 t as) (appT5 u as)
  | [] => h
  | a :: as => step5_appT (.left a h) as

theorem head5_appT (t : T5) : ∀ as : List T5, head5 (appT5 t as) = head5 t
  | [] => rfl
  | a :: as => head5_appT (t ⬝₅ a) as

-- ---------------------------------------------------------------------------
-- The five-continuation encoding
-- ---------------------------------------------------------------------------

/-- The application constructor of the five-symbol type, `encA5`. -/
def app5 : Term := toTerm (ctorO 2 3 5)

/-- The Scott encoding with five continuations, in the order `S`, `K`, `I`,
    application, `Err`. -/
def quote5 : T5 → Term
  | .S => toTerm (ctorO 0 0 5)
  | .K => toTerm (ctorO 0 1 5)
  | .I => toTerm (ctorO 0 2 5)
  | .Err => toTerm (ctorO 0 4 5)
  | .app f a => app5 ⬝ quote5 f ⬝ quote5 a

theorem quote5S_elim (a b c d e : Term) : WSteps (quote5 .S ⬝ a ⬝ b ⬝ c ⬝ d ⬝ e) a :=
  absN_beta_close [0, 1, 2, 3, 4] (.var 0) (fun _ => K) [a, b, c, d, e] rfl

theorem quote5K_elim (a b c d e : Term) : WSteps (quote5 .K ⬝ a ⬝ b ⬝ c ⬝ d ⬝ e) b :=
  absN_beta_close [0, 1, 2, 3, 4] (.var 1) (fun _ => K) [a, b, c, d, e] rfl

theorem quote5I_elim (a b c d e : Term) : WSteps (quote5 .I ⬝ a ⬝ b ⬝ c ⬝ d ⬝ e) c :=
  absN_beta_close [0, 1, 2, 3, 4] (.var 2) (fun _ => K) [a, b, c, d, e] rfl

theorem quote5E_elim (a b c d e : Term) : WSteps (quote5 .Err ⬝ a ⬝ b ⬝ c ⬝ d ⬝ e) e :=
  absN_beta_close [0, 1, 2, 3, 4] (.var 4) (fun _ => K) [a, b, c, d, e] rfl

theorem quote5App_elim (f x : T5) (a b c d e : Term) :
    WSteps (quote5 (f ⬝₅ x) ⬝ a ⬝ b ⬝ c ⬝ d ⬝ e) (d ⬝ quote5 f ⬝ quote5 x) :=
  absN_beta_close [0, 1, 2, 3, 4, 5, 6] (.var 5 ⬝ₒ .var 0 ⬝ₒ .var 1) (fun _ => K)
    [quote5 f, quote5 x, a, b, c, d, e] rfl

/-- The Scott list of the encodings of `xs`. -/
def qlist5 : List T5 → Term
  | [] => nilT
  | a :: as => consT ⬝ quote5 a ⬝ qlist5 as

-- ---------------------------------------------------------------------------
-- The source, as `tower_harness.py` gives it
-- ---------------------------------------------------------------------------

/-- `r5S acc = λ s k i e. s acc`; `r5K`, `r5I`, `r5E` likewise. -/
def r5SBody : OTerm := .var 1 ⬝ₒ .var 0
def r5KBody : OTerm := .var 2 ⬝ₒ .var 0
def r5IBody : OTerm := .var 3 ⬝ₒ .var 0
def r5EBody : OTerm := .var 4 ⬝ₒ .var 0
def r5S : Term := toTerm (absN [0, 1, 2, 3, 4] r5SBody)
def r5K : Term := toTerm (absN [0, 1, 2, 3, 4] r5KBody)
def r5I : Term := toTerm (absN [0, 1, 2, 3, 4] r5IBody)
def r5E : Term := toTerm (absN [0, 1, 2, 3, 4] r5EBody)

/-- `sp5Gen f m acc = m (r5S acc) (r5K acc) (r5I acc) (sp5App f acc) (r5E acc)`.
    `sp5App` has `spApp`'s equation and so is the same term. -/
def sp5GenBody : OTerm :=
  .var 1 ⬝ₒ (r5S.toO ⬝ₒ .var 2) ⬝ₒ (r5K.toO ⬝ₒ .var 2) ⬝ₒ (r5I.toO ⬝ₒ .var 2)
    ⬝ₒ (spApp.toO ⬝ₒ .var 0 ⬝ₒ .var 2) ⬝ₒ (r5E.toO ⬝ₒ .var 2)
def sp5Gen : Term := toTerm (absN [0, 1, 2] sp5GenBody)
def sp5 : Term := fixY ⬝ sp5Gen

/-- `rb51 f h x xs = f (App5 h x) xs`. -/
def rb51Body : OTerm := .var 0 ⬝ₒ (app5.toO ⬝ₒ .var 1 ⬝ₒ .var 2) ⬝ₒ .var 3
def rb51 : Term := toTerm (absN [0, 1, 2, 3] rb51Body)

/-- `rb5Gen f h args = args h (rb51 f h)`. -/
def rb5GenBody : OTerm := .var 2 ⬝ₒ .var 1 ⬝ₒ (rb51.toO ⬝ₒ .var 0 ⬝ₒ .var 1)
def rb5Gen : Term := toTerm (absN [0, 1, 2] rb5GenBody)
def rb5 : Term := fixY ⬝ rb5Gen

/-- The step protocol: `stepped t = λ c1 c2 c3. c1 t`, `done = λ c1 c2 c3. c2`,
    `errd = λ c1 c2 c3. c3`. -/
def steppedBody : OTerm := .var 1 ⬝ₒ .var 0
def tag2Body : OTerm := .var 1
def tag3Body : OTerm := .var 2
def steppedT : Term := toTerm (absN [0, 1, 2, 3] steppedBody)
def doneT : Term := toTerm (absN [0, 1, 2] tag2Body)
def errdT : Term := toTerm (absN [0, 1, 2] tag3Body)

/-- The result protocol: `rVal x = λ c1 c2 c3. c1 x`, `rErr = λ c1 c2 c3. c2`,
    `rTime = λ c1 c2 c3. c3`. -/
def rVal : Term := toTerm (absN [0, 1, 2, 3] steppedBody)
def rErr : Term := toTerm (absN [0, 1, 2] tag2Body)
def rTime : Term := toTerm (absN [0, 1, 2] tag3Body)

def q5I1Body : OTerm := steppedT.toO ⬝ₒ (rb5.toO ⬝ₒ .var 0 ⬝ₒ .var 1)
def q5I1 : Term := toTerm (absN [0, 1] q5I1Body)
def q5IBody : OTerm := .var 0 ⬝ₒ doneT.toO ⬝ₒ q5I1.toO
def q5I : Term := toTerm (absN [0] q5IBody)

def q5K2Body : OTerm := steppedT.toO ⬝ₒ (rb5.toO ⬝ₒ .var 0 ⬝ₒ .var 2)
def q5K2 : Term := toTerm (absN [0, 1, 2] q5K2Body)
def q5K1Body : OTerm := .var 1 ⬝ₒ doneT.toO ⬝ₒ (q5K2.toO ⬝ₒ .var 0)
def q5K1 : Term := toTerm (absN [0, 1] q5K1Body)
def q5KBody : OTerm := .var 0 ⬝ₒ doneT.toO ⬝ₒ q5K1.toO
def q5K : Term := toTerm (absN [0] q5KBody)

def q5S3Body : OTerm :=
  steppedT.toO ⬝ₒ (rb5.toO
    ⬝ₒ (app5.toO ⬝ₒ (app5.toO ⬝ₒ .var 0 ⬝ₒ .var 2) ⬝ₒ (app5.toO ⬝ₒ .var 1 ⬝ₒ .var 2))
    ⬝ₒ .var 3)
def q5S3 : Term := toTerm (absN [0, 1, 2, 3] q5S3Body)
def q5S2Body : OTerm := .var 2 ⬝ₒ doneT.toO ⬝ₒ (q5S3.toO ⬝ₒ .var 0 ⬝ₒ .var 1)
def q5S2 : Term := toTerm (absN [0, 1, 2] q5S2Body)
def q5S1Body : OTerm := .var 1 ⬝ₒ doneT.toO ⬝ₒ (q5S2.toO ⬝ₒ .var 0)
def q5S1 : Term := toTerm (absN [0, 1] q5S1Body)
def q5SBody : OTerm := .var 0 ⬝ₒ doneT.toO ⬝ₒ q5S1.toO
def q5S : Term := toTerm (absN [0] q5SBody)

/-- `st5 m = sp5 m nil q5S q5K q5I arm`, with the arm `e` a parameter. -/
def st5Body (e : Term) : OTerm :=
  sp5.toO ⬝ₒ .var 0 ⬝ₒ nilT.toO ⬝ₒ q5S.toO ⬝ₒ q5K.toO ⬝ₒ q5I.toO ⬝ₒ e.toO
def st5 (e : Term) : Term := toTerm (absN [0] (st5Body e))

/-- `wf51 w m n2 = st5 m (w n2) (rVal m) rErr`. -/
def wf51Body (e : Term) : OTerm :=
  (st5 e).toO ⬝ₒ .var 1 ⬝ₒ (.var 0 ⬝ₒ .var 2) ⬝ₒ (rVal.toO ⬝ₒ .var 1) ⬝ₒ rErr.toO
def wf51 (e : Term) : Term := toTerm (absN [0, 1, 2] (wf51Body e))

/-- `wf5Gen w n m = n rTime (wf51 w m)`. -/
def wf5GenBody (e : Term) : OTerm :=
  .var 1 ⬝ₒ rTime.toO ⬝ₒ ((wf51 e).toO ⬝ₒ .var 0 ⬝ₒ .var 2)
def wf5Gen (e : Term) : Term := toTerm (absN [0, 1, 2] (wf5GenBody e))

/-- **The five-symbol interpreter with arm `e` at the `Err` site.** -/
def wf5 (e : Term) : Term := fixY ⬝ wf5Gen e

/-- The exposing arm, `errArmAbs acc = errd`: `K (K (K I))`. -/
def errArmAbs : Term := K ⬝ errdT

/-- The hiding arm, `errArmOmg acc = Ω`: `K (S I I (S I I))`. -/
def errArmOmg : Term := K ⬝ (S ⬝ I ⬝ I ⬝ (S ⬝ I ⬝ I))

/-- The two arms are the paper's (§5.2). -/
theorem errArm_eq_paper : errArmAbs = K ⬝ (K ⬝ (K ⬝ I)) ∧
    toTerm (absN [0] errdT.toO) = errArmAbs ∧
    toTerm (absN [0] (S ⬝ I ⬝ I ⬝ (S ⬝ I ⬝ I)).toO) = errArmOmg := by decide

/-- The two interpreters have the paper's sizes: 768 and 771 atoms. -/
theorem wf5_atoms : atoms (wf5 errArmAbs) = 768 ∧ atoms (wf5 errArmOmg) = 771 := by
  decide +kernel

-- ---------------------------------------------------------------------------
-- β for each definition
-- ---------------------------------------------------------------------------

theorem r5S_elim (acc s k i e : Term) : WSteps (r5S ⬝ acc ⬝ s ⬝ k ⬝ i ⬝ e) (s ⬝ acc) := by
  beta_close [0, 1, 2, 3, 4] r5SBody [acc, s, k, i, e]

theorem r5K_elim (acc s k i e : Term) : WSteps (r5K ⬝ acc ⬝ s ⬝ k ⬝ i ⬝ e) (k ⬝ acc) := by
  beta_close [0, 1, 2, 3, 4] r5KBody [acc, s, k, i, e]

theorem r5I_elim (acc s k i e : Term) : WSteps (r5I ⬝ acc ⬝ s ⬝ k ⬝ i ⬝ e) (i ⬝ acc) := by
  beta_close [0, 1, 2, 3, 4] r5IBody [acc, s, k, i, e]

theorem r5E_elim (acc s k i e : Term) : WSteps (r5E ⬝ acc ⬝ s ⬝ k ⬝ i ⬝ e) (e ⬝ acc) := by
  beta_close [0, 1, 2, 3, 4] r5EBody [acc, s, k, i, e]

theorem sp5Gen_beta (f m acc : Term) :
    WSteps (sp5Gen ⬝ f ⬝ m ⬝ acc)
      (m ⬝ (r5S ⬝ acc) ⬝ (r5K ⬝ acc) ⬝ (r5I ⬝ acc) ⬝ (spApp ⬝ f ⬝ acc) ⬝ (r5E ⬝ acc)) := by
  beta_close [0, 1, 2] sp5GenBody [f, m, acc]

theorem rb51_beta (f h x xs : Term) :
    WSteps (rb51 ⬝ f ⬝ h ⬝ x ⬝ xs) (f ⬝ (app5 ⬝ h ⬝ x) ⬝ xs) := by
  beta_close [0, 1, 2, 3] rb51Body [f, h, x, xs]

theorem rb5Gen_beta (f h args : Term) :
    WSteps (rb5Gen ⬝ f ⬝ h ⬝ args) (args ⬝ h ⬝ (rb51 ⬝ f ⬝ h)) := by
  beta_close [0, 1, 2] rb5GenBody [f, h, args]

theorem stepped_elim (t c1 c2 c3 : Term) : WSteps (steppedT ⬝ t ⬝ c1 ⬝ c2 ⬝ c3) (c1 ⬝ t) := by
  beta_close [0, 1, 2, 3] steppedBody [t, c1, c2, c3]

theorem done_elim (c1 c2 c3 : Term) : WSteps (doneT ⬝ c1 ⬝ c2 ⬝ c3) c2 := by
  beta_close [0, 1, 2] tag2Body [c1, c2, c3]

theorem errd_elim (c1 c2 c3 : Term) : WSteps (errdT ⬝ c1 ⬝ c2 ⬝ c3) c3 := by
  beta_close [0, 1, 2] tag3Body [c1, c2, c3]

theorem q5I1_beta (x rest : Term) :
    WSteps (q5I1 ⬝ x ⬝ rest) (steppedT ⬝ (rb5 ⬝ x ⬝ rest)) := by
  beta_close [0, 1] q5I1Body [x, rest]

theorem q5I_beta (args : Term) : WSteps (q5I ⬝ args) (args ⬝ doneT ⬝ q5I1) := by
  beta_close [0] q5IBody [args]

theorem q5K2_beta (x y rest : Term) :
    WSteps (q5K2 ⬝ x ⬝ y ⬝ rest) (steppedT ⬝ (rb5 ⬝ x ⬝ rest)) := by
  beta_close [0, 1, 2] q5K2Body [x, y, rest]

theorem q5K1_beta (x r : Term) : WSteps (q5K1 ⬝ x ⬝ r) (r ⬝ doneT ⬝ (q5K2 ⬝ x)) := by
  beta_close [0, 1] q5K1Body [x, r]

theorem q5K_beta (args : Term) : WSteps (q5K ⬝ args) (args ⬝ doneT ⬝ q5K1) := by
  beta_close [0] q5KBody [args]

theorem q5S3_beta (x y z rest : Term) :
    WSteps (q5S3 ⬝ x ⬝ y ⬝ z ⬝ rest)
      (steppedT ⬝ (rb5 ⬝ (app5 ⬝ (app5 ⬝ x ⬝ z) ⬝ (app5 ⬝ y ⬝ z)) ⬝ rest)) := by
  beta_close [0, 1, 2, 3] q5S3Body [x, y, z, rest]

theorem q5S2_beta (x y r2 : Term) :
    WSteps (q5S2 ⬝ x ⬝ y ⬝ r2) (r2 ⬝ doneT ⬝ (q5S3 ⬝ x ⬝ y)) := by
  beta_close [0, 1, 2] q5S2Body [x, y, r2]

theorem q5S1_beta (x r : Term) : WSteps (q5S1 ⬝ x ⬝ r) (r ⬝ doneT ⬝ (q5S2 ⬝ x)) := by
  beta_close [0, 1] q5S1Body [x, r]

theorem q5S_beta (args : Term) : WSteps (q5S ⬝ args) (args ⬝ doneT ⬝ q5S1) := by
  beta_close [0] q5SBody [args]

theorem st5_beta (e m : Term) :
    WSteps (st5 e ⬝ m) (sp5 ⬝ m ⬝ nilT ⬝ q5S ⬝ q5K ⬝ q5I ⬝ e) := by
  have h := absN_beta_close [0] (st5Body e) (fun _ => K) [m] rfl
  simp only [st5Body, OTerm.close, close_toO] at h
  exact h

theorem wf51_beta (e w m n2 : Term) :
    WSteps (wf51 e ⬝ w ⬝ m ⬝ n2) (st5 e ⬝ m ⬝ (w ⬝ n2) ⬝ (rVal ⬝ m) ⬝ rErr) := by
  have h := absN_beta_close [0, 1, 2] (wf51Body e) (fun _ => K) [w, m, n2] rfl
  simp only [wf51Body, OTerm.close, close_toO] at h
  exact h

theorem wf5Gen_beta (e w n m : Term) :
    WSteps (wf5Gen e ⬝ w ⬝ n ⬝ m) (n ⬝ rTime ⬝ (wf51 e ⬝ w ⬝ m)) := by
  have h := absN_beta_close [0, 1, 2] (wf5GenBody e) (fun _ => K) [w, n, m] rfl
  simp only [wf5GenBody, OTerm.close, close_toO] at h
  exact h

-- ---------------------------------------------------------------------------
-- Recursion, the rebuilder, the arms
-- ---------------------------------------------------------------------------

def sp5X : Term := selfT sp5Gen
def rb5X : Term := selfT rb5Gen
def wf5X (e : Term) : Term := selfT (wf5Gen e)

theorem sp5X_case (m acc : Term) :
    WSteps (sp5X ⬝ m ⬝ acc)
      (m ⬝ (r5S ⬝ acc) ⬝ (r5K ⬝ acc) ⬝ (r5I ⬝ acc) ⬝ (spApp ⬝ sp5X ⬝ acc) ⬝ (r5E ⬝ acc)) :=
  (WSteps.left acc (WSteps.left m (selfT_unroll sp5Gen))).trans (sp5Gen_beta sp5X m acc)

theorem rb5X_case (h args : Term) :
    WSteps (rb5X ⬝ h ⬝ args) (args ⬝ h ⬝ (rb51 ⬝ rb5X ⬝ h)) :=
  (WSteps.left args (WSteps.left h (selfT_unroll rb5Gen))).trans (rb5Gen_beta rb5X h args)

theorem wf5X_case (e n m : Term) :
    WSteps (wf5X e ⬝ n ⬝ m) (n ⬝ rTime ⬝ (wf51 e ⬝ wf5X e ⬝ m)) :=
  (WSteps.left m (WSteps.left n (selfT_unroll (wf5Gen e)))).trans (wf5Gen_beta e (wf5X e) n m)

theorem rb5X_spec : ∀ (xs : List T5) (H : T5),
    WSteps (rb5X ⬝ quote5 H ⬝ qlist5 xs) (quote5 (appT5 H xs))
  | [], _ => (rb5X_case _ _).trans (nil_elim _ _)
  | a :: as, H =>
    ((rb5X_case _ _).trans (cons_elim _ _ _ _)).trans
      ((rb51_beta _ _ _ _).trans (rb5X_spec as (H ⬝₅ a)))

/-- A contracted spine, rebuilt under `stepped`. -/
theorem stepped_rb5 (xs : List T5) (H : T5) :
    WSteps (steppedT ⬝ (rb5 ⬝ quote5 H ⬝ qlist5 xs)) (steppedT ⬝ quote5 (appT5 H xs)) :=
  WSteps.right _ ((WSteps.left _ (WSteps.left _ (fixY_self rb5Gen))).trans (rb5X_spec xs H))

theorem q5I_nil : WSteps (q5I ⬝ nilT) doneT := (q5I_beta _).trans (nil_elim _ _)

theorem q5I_one (x r : Term) :
    WSteps (q5I ⬝ (consT ⬝ x ⬝ r)) (steppedT ⬝ (rb5 ⬝ x ⬝ r)) :=
  ((q5I_beta _).trans (cons_elim _ _ _ _)).trans (q5I1_beta _ _)

theorem q5K_nil : WSteps (q5K ⬝ nilT) doneT := (q5K_beta _).trans (nil_elim _ _)

theorem q5K_cons (x r : Term) :
    WSteps (q5K ⬝ (consT ⬝ x ⬝ r)) (r ⬝ doneT ⬝ (q5K2 ⬝ x)) :=
  ((q5K_beta _).trans (cons_elim _ _ _ _)).trans (q5K1_beta _ _)

theorem q5K_one (x : Term) : WSteps (q5K ⬝ (consT ⬝ x ⬝ nilT)) doneT :=
  (q5K_cons _ _).trans (nil_elim _ _)

theorem q5K_two (x y r : Term) :
    WSteps (q5K ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ r))) (steppedT ⬝ (rb5 ⬝ x ⬝ r)) :=
  ((q5K_cons _ _).trans (cons_elim _ _ _ _)).trans (q5K2_beta _ _ _)

theorem q5S_nil : WSteps (q5S ⬝ nilT) doneT := (q5S_beta _).trans (nil_elim _ _)

theorem q5S_cons (x r : Term) :
    WSteps (q5S ⬝ (consT ⬝ x ⬝ r)) (r ⬝ doneT ⬝ (q5S2 ⬝ x)) :=
  ((q5S_beta _).trans (cons_elim _ _ _ _)).trans (q5S1_beta _ _)

theorem q5S_one (x : Term) : WSteps (q5S ⬝ (consT ⬝ x ⬝ nilT)) doneT :=
  (q5S_cons _ _).trans (nil_elim _ _)

theorem q5S_cons2 (x y r : Term) :
    WSteps (q5S ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ r))) (r ⬝ doneT ⬝ (q5S3 ⬝ x ⬝ y)) :=
  ((q5S_cons _ _).trans (cons_elim _ _ _ _)).trans (q5S2_beta _ _ _)

theorem q5S_two (x y : Term) :
    WSteps (q5S ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ nilT))) doneT :=
  (q5S_cons2 _ _ _).trans (nil_elim _ _)

theorem q5S_three (x y z r : Term) :
    WSteps (q5S ⬝ (consT ⬝ x ⬝ (consT ⬝ y ⬝ (consT ⬝ z ⬝ r))))
      (steppedT ⬝ (rb5 ⬝ (app5 ⬝ (app5 ⬝ x ⬝ z) ⬝ (app5 ⬝ y ⬝ z)) ⬝ r)) :=
  ((q5S_cons2 _ _ _).trans (cons_elim _ _ _ _)).trans (q5S3_beta _ _ _ _)

-- ---------------------------------------------------------------------------
-- The walk and dispatch, with the arm a parameter
-- ---------------------------------------------------------------------------

/-- A walker's answer handed the three arms and the site's arm `e`. -/
def disp5 (e t : Term) : Term := t ⬝ q5S ⬝ q5K ⬝ q5I ⬝ e

theorem disp5_mono (e : Term) {t u : Term} (h : WSteps t u) : WSteps (disp5 e t) (disp5 e u) :=
  WSteps.left _ (WSteps.left _ (WSteps.left _ (WSteps.left _ h)))

theorem sp5X_app (f a : T5) (acc : Term) :
    WSteps (sp5X ⬝ quote5 (f ⬝₅ a) ⬝ acc) (sp5X ⬝ quote5 f ⬝ (consT ⬝ quote5 a ⬝ acc)) :=
  ((sp5X_case _ _).trans (quote5App_elim f a _ _ _ _ _)).trans (spApp_beta _ _ _ _)

theorem walk5_S (e acc : Term) : WSteps (disp5 e (sp5X ⬝ quote5 .S ⬝ acc)) (q5S ⬝ acc) :=
  (disp5_mono e ((sp5X_case _ _).trans (quote5S_elim _ _ _ _ _))).trans (r5S_elim _ _ _ _ _)

theorem walk5_K (e acc : Term) : WSteps (disp5 e (sp5X ⬝ quote5 .K ⬝ acc)) (q5K ⬝ acc) :=
  (disp5_mono e ((sp5X_case _ _).trans (quote5K_elim _ _ _ _ _))).trans (r5K_elim _ _ _ _ _)

theorem walk5_I (e acc : Term) : WSteps (disp5 e (sp5X ⬝ quote5 .I ⬝ acc)) (q5I ⬝ acc) :=
  (disp5_mono e ((sp5X_case _ _).trans (quote5I_elim _ _ _ _ _))).trans (r5I_elim _ _ _ _ _)

theorem walk5_E (e acc : Term) : WSteps (disp5 e (sp5X ⬝ quote5 .Err ⬝ acc)) (e ⬝ acc) :=
  (disp5_mono e ((sp5X_case _ _).trans (quote5E_elim _ _ _ _ _))).trans (r5E_elim _ _ _ _ _)

/-- **The walk over five symbols.**  The dispatch answers `done` on a weak
    head normal form, `stepped` of the head contraction's encoding when there
    is one, and otherwise `Err` is at the head and the answer is the site's
    arm applied to the accumulated argument list: the only use of `e`. -/
theorem walk5 (e : Term) (M : T5) : ∀ xs : List T5,
    (Whnf5 (appT5 M xs) ∧ WSteps (disp5 e (sp5X ⬝ quote5 M ⬝ qlist5 xs)) doneT) ∨
      (∃ N, Step5 (appT5 M xs) N ∧
        WSteps (disp5 e (sp5X ⬝ quote5 M ⬝ qlist5 xs)) (steppedT ⬝ quote5 N)) ∨
      (head5 (appT5 M xs) = .Err ∧
        ∃ acc, WSteps (disp5 e (sp5X ⬝ quote5 M ⬝ qlist5 xs)) (e ⬝ acc)) := by
  induction M with
  | S =>
    intro xs
    match xs with
    | [] => exact .inl ⟨.S, (walk5_S _ _).trans q5S_nil⟩
    | [x] => exact .inl ⟨.S1 x, (walk5_S _ _).trans (q5S_one _)⟩
    | [x, y] => exact .inl ⟨.S2 x y, (walk5_S _ _).trans (q5S_two _ _)⟩
    | x :: y :: z :: rest =>
      exact .inr (.inl ⟨appT5 (x ⬝₅ z ⬝₅ (y ⬝₅ z)) rest, step5_appT (.S x y z) rest,
        ((walk5_S _ _).trans (q5S_three _ _ _ _)).trans
          (stepped_rb5 rest (x ⬝₅ z ⬝₅ (y ⬝₅ z)))⟩)
  | K =>
    intro xs
    match xs with
    | [] => exact .inl ⟨.K, (walk5_K _ _).trans q5K_nil⟩
    | [x] => exact .inl ⟨.K1 x, (walk5_K _ _).trans (q5K_one _)⟩
    | x :: y :: rest =>
      exact .inr (.inl ⟨appT5 x rest, step5_appT (.K x y) rest,
        ((walk5_K _ _).trans (q5K_two _ _ _)).trans (stepped_rb5 rest x)⟩)
  | I =>
    intro xs
    match xs with
    | [] => exact .inl ⟨.I, (walk5_I _ _).trans q5I_nil⟩
    | x :: rest =>
      exact .inr (.inl ⟨appT5 x rest, step5_appT (.I x) rest,
        ((walk5_I _ _).trans (q5I_one _ _)).trans (stepped_rb5 rest x)⟩)
  | Err =>
    intro xs
    exact .inr (.inr ⟨head5_appT .Err xs, _, walk5_E _ _⟩)
  | app f a ihf _ =>
    intro xs
    have hw := disp5_mono e (sp5X_app f a (qlist5 xs))
    cases ihf (a :: xs) with
    | inl h => exact .inl ⟨h.1, hw.trans h.2⟩
    | inr h =>
      cases h with
      | inl h =>
        cases h with
        | intro N hN => exact .inr (.inl ⟨N, hN.1, hw.trans hN.2⟩)
      | inr h =>
        cases h.2 with
        | intro acc hacc => exact .inr (.inr ⟨h.1, acc, hw.trans hacc⟩)

theorem st5_walk (e : Term) (M : T5) :
    WSteps (st5 e ⬝ quote5 M) (disp5 e (sp5X ⬝ quote5 M ⬝ qlist5 [])) :=
  (st5_beta e _).trans (disp5_mono e (WSteps.left _ (WSteps.left _ (fixY_self sp5Gen))))

/-- Step adequacy over five symbols, for every arm: weak head normal form. -/
theorem st5_whnf (e : Term) {M : T5} (hw : Whnf5 M) : WSteps (st5 e ⬝ quote5 M) doneT := by
  cases walk5 e M [] with
  | inl h => exact (st5_walk e M).trans h.2
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro N hN => exact (hw.no_step hN.1).elim
    | inr h => exact (hw.head h.1).elim

/-- Step adequacy over five symbols, for every arm: a head contraction. -/
theorem st5_step (e : Term) {M M' : T5} (hs : Step5 M M') :
    WSteps (st5 e ⬝ quote5 M) (steppedT ⬝ quote5 M') := by
  cases walk5 e M [] with
  | inl h => exact (h.1.no_step hs).elim
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro N hN =>
        rw [Step5.det hs hN.1]
        exact (st5_walk e M).trans hN.2
    | inr h => exact (hs.head h.1).elim

/-- With `Err` at the head, `step` is the arm applied to the argument list. -/
theorem st5_err (e : Term) {M : T5} (hh : head5 M = .Err) :
    ∃ acc, WSteps (st5 e ⬝ quote5 M) (e ⬝ acc) := by
  cases walk5 e M [] with
  | inl h => exact (h.1.head hh).elim
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro N hN => exact (hN.1.head hh).elim
    | inr h =>
      cases h.2 with
      | intro acc hacc => exact ⟨acc, (st5_walk e M).trans hacc⟩

/-- Every term is a weak head normal form, has a head contraction, or has
    `Err` at its head. -/
theorem trichotomy5 (M : T5) : Whnf5 M ∨ (∃ N, Step5 M N) ∨ head5 M = .Err := by
  cases walk5 K M [] with
  | inl h => exact .inl h.1
  | inr h =>
    cases h with
    | inl h =>
      cases h with
      | intro N hN => exact .inr (.inl ⟨N, hN.1⟩)
    | inr h => exact .inr (.inr h.1)

-- ---------------------------------------------------------------------------
-- Runs, and Lemma 5.3
-- ---------------------------------------------------------------------------

/-- An object-level outcome: a value, a timeout, or `Err` reached the head. -/
inductive Out5
  | val (N : T5)
  | time
  | crash

/-- `Run5 k t o`: the outcome of at most `k` step-attempts of head reduction
    on `t`.  `crash` is `Err` in head position within the budget. -/
inductive Run5 : Nat → T5 → Out5 → Prop
  | time (t : T5) : Run5 0 t .time
  | val {k : Nat} {t : T5} (h : Whnf5 t) : Run5 (k + 1) t (.val t)
  | crash {k : Nat} {t : T5} (h : head5 t = .Err) : Run5 (k + 1) t .crash
  | step {k : Nat} {t t' : T5} {o : Out5} (h : Step5 t t') (hs : Run5 k t' o) : Run5 (k + 1) t o

/-- The interpreter's answer for an outcome. -/
def res5 : Out5 → Term
  | .val N => rVal ⬝ quote5 N
  | .time => rTime
  | .crash => rErr

theorem run5_total : ∀ (k : Nat) (t : T5), ∃ o, Run5 k t o
  | 0, t => ⟨.time, .time t⟩
  | k + 1, t => by
    cases trichotomy5 t with
    | inl h => exact ⟨.val t, .val h⟩
    | inr h =>
      cases h with
      | inl h =>
        cases h with
        | intro t' ht =>
          cases run5_total k t' with
          | intro o ho => exact ⟨o, .step ht ho⟩
      | inr h => exact ⟨.crash, .crash h⟩

theorem wf5X_suc (e n m : Term) :
    WSteps (wf5X e ⬝ (sucT ⬝ n) ⬝ m) (st5 e ⬝ m ⬝ (wf5X e ⬝ n) ⬝ (rVal ⬝ m) ⬝ rErr) :=
  ((wf5X_case _ _ _).trans (suc_elim _ _ _)).trans (wf51_beta _ _ _ _)

/-- Fuel adequacy over five symbols.  For any arm, off the site; and on the
    site for an arm that answers `errd`. -/
theorem wf5X_run (e : Term) {k : Nat} {t : T5} {o : Out5} (h : Run5 k t o)
    (he : o = .crash → ∀ acc, WSteps (e ⬝ acc) errdT) :
    WSteps (wf5X e ⬝ natT k ⬝ quote5 t) (res5 o) := by
  induction h with
  | time t => exact (wf5X_case _ _ _).trans (zero_elim _ _)
  | val hw =>
    exact (wf5X_suc _ _ _).trans
      ((WSteps.left _ (WSteps.left _ (WSteps.left _ (st5_whnf e hw)))).trans (done_elim _ _ _))
  | crash hh =>
    cases st5_err e hh with
    | intro acc hacc =>
      exact (wf5X_suc _ _ _).trans
        ((WSteps.left _ (WSteps.left _ (WSteps.left _ (hacc.trans (he rfl acc))))).trans
          (errd_elim _ _ _))
  | step hs _ ih =>
    exact (wf5X_suc _ _ _).trans
      ((WSteps.left _ (WSteps.left _ (WSteps.left _ (st5_step e hs)))).trans
        ((stepped_elim _ _ _ _).trans (ih he)))

theorem wf5_run (e : Term) {k : Nat} {t : T5} {o : Out5} (h : Run5 k t o)
    (he : o = .crash → ∀ acc, WSteps (e ⬝ acc) errdT) :
    WSteps (wf5 e ⬝ natT k ⬝ quote5 t) (res5 o) :=
  (WSteps.left _ (WSteps.left _ (fixY_self (wf5Gen e)))).trans (wf5X_run e h he)

/-- **Faithfulness at a site, within the budget** (the paper's Lemma 5.3,
    sharpened): if the run of `t` at budget `k` does not bring `Err` into
    head position, the interpreters with any two arms `e₁`, `e₂` at the site
    reduce to the same answer, `rVal ⟨N⟩` or `rTime`. -/
theorem faithful_run (e₁ e₂ : Term) {k : Nat} {t : T5} {o : Out5} (h : Run5 k t o)
    (ho : o ≠ .crash) :
    WSteps (wf5 e₁ ⬝ natT k ⬝ quote5 t) (res5 o) ∧
      WSteps (wf5 e₂ ⬝ natT k ⬝ quote5 t) (res5 o) :=
  ⟨wf5_run e₁ h fun hc => (ho hc).elim, wf5_run e₂ h fun hc => (ho hc).elim⟩

theorem run5_crash {k : Nat} {t : T5} {o : Out5} (h : Run5 k t o) (ho : o = .crash) :
    ∃ t', Steps5 t t' ∧ head5 t' = .Err := by
  induction h with
  | time t => cases ho
  | val _ => cases ho
  | crash hh => exact ⟨_, .refl _, hh⟩
  | step hs _ ih =>
    cases ih ho with
    | intro t' ht => exact ⟨t', .step hs ht.1, ht.2⟩

/-- **Faithfulness at a site** (the paper's Lemma 5.3 at ℓ = `Err`, for the family `wf5 e`; the
    paper's lemma is for any leaf ℓ and any two interpreters): let two interpreters
    be identical except in the step arm selected for `Err`.  For every object
    term whose reduction never brings `Err` into head position, and every
    budget, they produce the same result. -/
theorem faithful_site (e₁ e₂ : Term) (t : T5)
    (hn : ∀ t', Steps5 t t' → head5 t' ≠ .Err) (k : Nat) :
    ∃ o, o ≠ .crash ∧ WSteps (wf5 e₁ ⬝ natT k ⬝ quote5 t) (res5 o) ∧
      WSteps (wf5 e₂ ⬝ natT k ⬝ quote5 t) (res5 o) := by
  cases run5_total k t with
  | intro o ho =>
    have hc : o ≠ .crash := fun hc =>
      match run5_crash ho hc with
      | ⟨t', ht⟩ => hn t' ht.1 ht.2
    exact ⟨o, hc, faithful_run e₁ e₂ ho hc⟩

/-- **The exposing interpreter** (Table 1, first column): with the arm
    `errArmAbs`, every run reduces to its outcome's answer, `rErr` when `Err`
    reaches the head. -/
theorem wf5Abs_run {k : Nat} {t : T5} {o : Out5} (h : Run5 k t o) :
    WSteps (wf5 errArmAbs ⬝ natT k ⬝ quote5 t) (res5 o) :=
  wf5_run errArmAbs h fun _ acc => .single (.K errdT acc)

end SelfInterp
