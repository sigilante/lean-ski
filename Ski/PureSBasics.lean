import Ski.NoImp
open Term

/-!
# Facts about pure S: leaf count, no fixed-point combinator (both known), PEEL

Three facts about the combinator S alone, for the S16 paper (`notes/LOCK1-RELCOMP.md`, with
the Wizard repairs W1–W16 at its end).  Leaf count and the absence of a fixed-point combinator are known (W16: Zachos 1978,
Waldmann 2000, *Dance of the Starlings* 2017); no published statement of PEEL is known to us. All are mechanized
here so that the paper can cite them from the gate.

**1. Leaf count** (`wstep_leaves`, `wsteps_leaves`; RELCOMP W4).  A weak step of a pure-S term
never decreases the number of leaves: `|a c (b c)| = |a| + |b| + 2|c| ≥ 1 + |a| + |b| + |c|`
(`leaves_contract`).  Hence no pure-S `t` applied to pure-S arguments reduces to a term built
from (a sub-multiset of) those arguments, each used at most once (`no_rearrangement`): `t`
itself contributes at least one leaf that cannot be recovered.  The concrete instances are no
relative `I`, `K`, `T`, `C`, `B` and no relative permutation, the identity included, with any
spare arguments (`no_rel_I`, `no_rel_K`, `no_rel_T`, `no_rel_C`, `no_rel_B`, `no_rel_perm`).
`Term` has no variables, so these are stated for every closed pure-S instance of the
arguments; the arguments need not be distinct, so they hold in particular at distinct ones.
The open forms, over the variable calculus `Open.VTerm` below, are `Open.no_rel_I` … .

**2. No fixed-point combinator** (`no_fixed_point`; RELCOMP Cor. RC (e) as repaired by W3).
No pure-S `Y` has `Y f` convertible to `f (Y f)` for every pure-S `f`.  The proof uses only
`f = S` (`no_fixed_point_S`): a head step of a pure-S term never yields a one-item frame
`S a` (`NoImp.no_step_S1`), so a pure-S term convertible to `S N` is literally `S a`
(`conv_one_item`), by Church–Rosser and standardization (`eval_back`).  Then `Y S = S a` forces
`Y = S`, and `S S`, `S (S S)` are distinct normal forms.  This is G2 (RELCOMP §1.2) at a closed head: `S`
with one argument plays the variable.  `no_fixed_point` has the same statement as `Ncfp.no_fpc`,
and `no_fixed_point_S` as `Ncfp.no_fixed_point_combinator`; these are independent short proofs
via `conv_one_item`, without NCFP.

**3. PEEL** (`Open.peel`; RELCOMP Theorem PEEL, W2).  `Term` has no variables, and no closed
term can stand in for a fresh one: a closed atom other than `S` is `K` or `I`, which vanish
when they reach the head (`S I x y → I y (x y)`), and occurrences of a pure-S subterm are not
conserved.  So PEEL is stated over `Open.VTerm`, pure S with variables, whose step is the
S-rule at any position (`Open.emb_wstep` maps pure-S weak steps onto it).  For distinct
variables `w₁ … w_r` occurring in neither `M` nor `N`, `M w₁ ⋯ w_r ↠ N w₁ ⋯ w_r` iff `M ↠ N`.
`M` is arbitrary, so it may be `M′ x⃗`.  The proof is RELCOMP's for the root position only:
the last variable occurs once at the end, occurrences never decrease (`vsteps_occ`), so no step
fired the root, and every step lay inside the left child (`peel_one`).  Lemma ARG in general
(a linear argument at any depth) is not mechanized.
-/

namespace PureSBasics
open HnfS Conv

/-! ## 1. Leaf count -/

/-- The number of leaves of a term. -/
def leaves : Term → Nat
  | .S => 1
  | .K => 1
  | .I => 1
  | .app f x => leaves f + leaves x

theorem leaves_pos : ∀ t : Term, 0 < leaves t
  | .S => Nat.zero_lt_one
  | .K => Nat.zero_lt_one
  | .I => Nat.zero_lt_one
  | .app f x => by
    have := leaves_pos f
    show 0 < leaves f + leaves x
    omega

/-- The contractum of `S f g x` has at least as many leaves as the redex. -/
theorem leaves_contract (f g x : Term) :
    1 + leaves f + leaves g + leaves x ≤ leaves (f ⬝ x ⬝ (g ⬝ x)) := by
  have := leaves_pos x
  simp only [leaves]
  omega

/-- **Leaf-count monotonicity.**  A weak step of a pure-S term never decreases the leaf count. -/
theorem wstep_leaves {t u : Term} (h : WStep t u) (ht : PureS t) : leaves t ≤ leaves u := by
  induction h with
  | S f g x =>
    have := leaves_pos x
    simp only [leaves]
    omega
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih =>
    have := ih ht.app_inv.1
    simp only [leaves]
    omega
  | right f _ ih =>
    have := ih ht.app_inv.2
    simp only [leaves]
    omega

theorem wsteps_pure {t u : Term} (h : WSteps t u) (ht : PureS t) : PureS u := by
  induction h with
  | refl => exact ht
  | step s _ ih => exact ih (wstep_pure s ht).1

theorem wsteps_leaves {t u : Term} (h : WSteps t u) (ht : PureS t) : leaves t ≤ leaves u := by
  induction h with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans (wstep_leaves s ht) (ih (wstep_pure s ht).1)

/-- A pure-S term does not weakly reduce to a term with fewer leaves. -/
theorem no_wsteps_of_lt {s u : Term} (hs : PureS s) (h : leaves u < leaves s) : ¬ WSteps s u :=
  fun hw => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (wsteps_leaves hw hs))

/-! ### Spines and rearrangements -/

/-- `apps t [x₁, …, x_k] = t x₁ ⋯ x_k`. -/
def apps (t : Term) : List Term → Term
  | [] => t
  | x :: xs => apps (t ⬝ x) xs

/-- The total leaf count of a list of terms. -/
def lsum : List Term → Nat
  | [] => 0
  | x :: xs => leaves x + lsum xs

theorem leaves_apps : ∀ (t : Term) (xs : List Term), leaves (apps t xs) = leaves t + lsum xs
  | t, [] => by simp only [apps, lsum]; omega
  | t, x :: xs => by
    simp only [apps, lsum]
    rw [leaves_apps (t ⬝ x) xs]
    simp only [leaves]
    omega

theorem apps_pure : ∀ {t : Term} {xs : List Term}, PureS t → (∀ x ∈ xs, PureS x) →
    PureS (apps t xs)
  | _, [], ht, _ => ht
  | _, x :: xs, ht, hx =>
    apps_pure (xs := xs) (.app ht (hx x (List.mem_cons_self ..)))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem lsum_append : ∀ (l₁ l₂ : List Term), lsum (l₁ ++ l₂) = lsum l₁ + lsum l₂
  | [], l₂ => by simp only [List.nil_append, lsum]; omega
  | x :: l₁, l₂ => by
    simp only [List.cons_append, lsum]
    rw [lsum_append l₁ l₂]
    omega

theorem lsum_perm {l l' : List Term} (h : l.Perm l') : lsum l = lsum l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [lsum]; omega
  | swap x y l => simp only [lsum]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem lsum_sublist {l l' : List Term} (h : l.Sublist l') : lsum l ≤ lsum l' := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a _ ih => simp only [lsum]; omega
  | cons_cons a _ ih => simp only [lsum]; omega

/-- `Linear l u`: `u` is built by application from the terms of `l`, each used once, in the
    order of `l` (left to right).  Reordering and dropping are allowed by the hypothesis of
    `no_rearrangement`, which asks only that a permutation of `l` be a sublist of the
    arguments. -/
inductive Linear : List Term → Term → Prop
  | atom (x : Term) : Linear [x] x
  | app {l₁ l₂ : List Term} {f g : Term} : Linear l₁ f → Linear l₂ g → Linear (l₁ ++ l₂) (f ⬝ g)

theorem Linear.leaves_eq {l : List Term} {u : Term} (h : Linear l u) : leaves u = lsum l := by
  induction h with
  | atom x => simp only [lsum]; omega
  | app _ _ ih1 ih2 => rw [lsum_append]; simp only [leaves]; omega

theorem Linear.apps {l : List Term} {f : Term} (h : Linear l f) :
    ∀ ys : List Term, Linear (l ++ ys) (PureSBasics.apps f ys)
  | [] => by simpa [PureSBasics.apps] using h
  | y :: ys => by
    have := Linear.apps (Linear.app h (Linear.atom y)) ys
    simpa [PureSBasics.apps, List.append_assoc] using this

/-- **No rearrangement.**  A pure-S `t` applied to pure-S arguments `xs` does not weakly reduce
    to any term built from a sub-multiset of `xs`, each element used at most once.  (Leaf count:
    the target has at most `lsum xs` leaves, the source `leaves t + lsum xs > lsum xs`.) -/
theorem no_rearrangement {t u : Term} {xs l : List Term} (ht : PureS t)
    (hx : ∀ x ∈ xs, PureS x) (hu : Linear l u) (hl : ∃ l' : List Term, l'.Perm l ∧ l'.Sublist xs) :
    ¬ WSteps (apps t xs) u := by
  obtain ⟨l', hp, hs⟩ := hl
  apply no_wsteps_of_lt (apps_pure ht hx)
  rw [hu.leaves_eq, leaves_apps, ← lsum_perm hp]
  have := lsum_sublist hs
  have := leaves_pos t
  omega

/-- No relative permutation, the identity included: `t x₁ ⋯ x_k ↠ y y₁ ⋯ y_{k-1}` is impossible
    whenever `y :: ys` is a permutation of `xs`. -/
theorem no_rel_perm {t y : Term} {xs ys : List Term} (ht : PureS t) (hx : ∀ x ∈ xs, PureS x)
    (hp : (y :: ys).Perm xs) : ¬ WSteps (apps t xs) (apps y ys) :=
  no_rearrangement ht hx (by simpa using (Linear.atom y).apps ys) ⟨xs, hp.symm, .refl _⟩

/-- No relative `I`: `t x w⃗ ↠ x w⃗` is impossible. -/
theorem no_rel_I {t x : Term} {ws : List Term} (ht : PureS t) (hx : PureS x)
    (hw : ∀ w ∈ ws, PureS w) : ¬ WSteps (apps (t ⬝ x) ws) (apps x ws) := by
  apply no_wsteps_of_lt (apps_pure (.app ht hx) hw)
  rw [leaves_apps, leaves_apps]
  have := leaves_pos t
  simp only [leaves]
  omega

/-- No relative `K`: `t x y w⃗ ↠ x w⃗` is impossible. -/
theorem no_rel_K {t x y : Term} {ws : List Term} (ht : PureS t) (hx : PureS x) (hy : PureS y)
    (hw : ∀ w ∈ ws, PureS w) : ¬ WSteps (apps (t ⬝ x ⬝ y) ws) (apps x ws) := by
  apply no_wsteps_of_lt (apps_pure (.app (.app ht hx) hy) hw)
  rw [leaves_apps, leaves_apps]
  have := leaves_pos t
  have := leaves_pos y
  simp only [leaves]
  omega

/-- No relative `T`: `t x y w⃗ ↠ y x w⃗` is impossible. -/
theorem no_rel_T {t x y : Term} {ws : List Term} (ht : PureS t) (hx : PureS x) (hy : PureS y)
    (hw : ∀ w ∈ ws, PureS w) : ¬ WSteps (apps (t ⬝ x ⬝ y) ws) (apps (y ⬝ x) ws) := by
  apply no_wsteps_of_lt (apps_pure (.app (.app ht hx) hy) hw)
  rw [leaves_apps, leaves_apps]
  have := leaves_pos t
  simp only [leaves]
  omega

/-- No relative `C`: `t x y z w⃗ ↠ x z y w⃗` is impossible. -/
theorem no_rel_C {t x y z : Term} {ws : List Term} (ht : PureS t) (hx : PureS x) (hy : PureS y)
    (hz : PureS z) (hw : ∀ w ∈ ws, PureS w) :
    ¬ WSteps (apps (t ⬝ x ⬝ y ⬝ z) ws) (apps (x ⬝ z ⬝ y) ws) := by
  apply no_wsteps_of_lt (apps_pure (.app (.app (.app ht hx) hy) hz) hw)
  rw [leaves_apps, leaves_apps]
  have := leaves_pos t
  simp only [leaves]
  omega

/-- No relative `B`: `t x y z w⃗ ↠ x (y z) w⃗` is impossible. -/
theorem no_rel_B {t x y z : Term} {ws : List Term} (ht : PureS t) (hx : PureS x) (hy : PureS y)
    (hz : PureS z) (hw : ∀ w ∈ ws, PureS w) :
    ¬ WSteps (apps (t ⬝ x ⬝ y ⬝ z) ws) (apps (x ⬝ (y ⬝ z)) ws) := by
  apply no_wsteps_of_lt (apps_pure (.app (.app (.app ht hx) hy) hz) hw)
  rw [leaves_apps, leaves_apps]
  have := leaves_pos t
  simp only [leaves]
  omega

/-! ## 2. No fixed-point combinator -/

theorem wsteps_S {w : Term} (h : WSteps S w) : w = S := NoImp.normal_wsteps NoImp.normal_S h

/-- Every weak reduct of `S N` is `S N'`. -/
theorem wsteps_S1 {N w : Term} (h : WSteps (S ⬝ N) w) : ∃ N', w = S ⬝ N' := by
  generalize he : S ⬝ N = s at h
  induction h generalizing N with
  | refl => exact ⟨N, he.symm⟩
  | step s _ ih =>
    subst he
    cases s with
    | left _ h => cases h
    | right _ _ => exact ih rfl

/-- Every weak reduct of `S a b` is `S a' b'`. -/
theorem wsteps_S2 {a b w : Term} (h : WSteps (S ⬝ a ⬝ b) w) : ∃ a' b', w = S ⬝ a' ⬝ b' := by
  generalize he : S ⬝ a ⬝ b = s at h
  induction h generalizing a b with
  | refl => exact ⟨a, b, he.symm⟩
  | step s _ ih =>
    subst he
    cases s with
    | left _ h =>
      cases h with
      | left _ h => cases h
      | right _ _ => exact ih rfl
    | right _ _ => exact ih rfl

/-- A head run of a pure-S term that ends in `S a` is empty. -/
theorem steps_to_S1 {t a : Term} (ht : PureS t) (h : Steps t (S ⬝ a)) : t = S ⬝ a := by
  have key : ∀ {t v : Term}, Steps t v → PureS t → v = S ⬝ a → t = S ⬝ a := by
    intro t v h
    induction h with
    | refl => intro _ e; exact e
    | step s _ ih =>
      intro ht e
      have e' := ih (wstep_pure s.weak ht).1 e
      subst e'
      exact absurd s (NoImp.no_step_S1 ht)
  exact key h ht rfl

/-- A pure-S term convertible to a one-item frame `S N` is, as written, a one-item frame `S a`.
    `N` is arbitrary.  For pure-S `N`, `Ncfp.hnf1_conv` (NcfpTheta.lean) gives more: also
    `a` convertible to `N`. -/
theorem conv_one_item {t N : Term} (ht : PureS t) (h : Convertible t (S ⬝ N)) :
    ∃ a, t = S ⬝ a := by
  obtain ⟨w, htw, hNw⟩ := conv_iff_join.mp h
  obtain ⟨N', rfl⟩ := wsteps_S1 hNw
  obtain ⟨v, ⟨hs, hv⟩, hvw⟩ := eval_back htw ⟨.refl _, .S1 N'⟩
  have hp : PureS v := InfNF.steps_pure ht hs
  cases hv with
  | S => cases wsteps_S hvw
  | K => exact absurd hp PureS.not_K
  | I => exact absurd hp PureS.not_I
  | S1 x => exact ⟨x, steps_to_S1 ht hs⟩
  | S2 x y =>
    obtain ⟨a', b', he⟩ := wsteps_S2 hvw
    cases he
  | K1 x => exact absurd hp.app_inv.1 PureS.not_K

theorem not_conv_SS : ¬ Convertible (S ⬝ S) (S ⬝ (S ⬝ S)) := by
  intro h
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  have e1 := NoImp.normal_wsteps (NoImp.normal_S1 NoImp.normal_S) h1
  have e2 := NoImp.normal_wsteps (NoImp.normal_S1 (NoImp.normal_S1 NoImp.normal_S)) h2
  rw [e1] at e2
  cases e2

/-- A pure-S `Y` with `Y S` convertible to a one-item frame `S N` is `S` itself. -/
theorem conv_YS_one_item {Y N : Term} (hY : PureS Y) (h : Convertible (Y ⬝ S) (S ⬝ N)) :
    Y = S := by
  obtain ⟨a, ha⟩ := conv_one_item (.app hY .S) h
  injection ha

/-- No pure-S `Y` has `Y S` convertible to `S (Y S)`.  Same statement as
    `Ncfp.no_fixed_point_combinator`; an independent short proof via `conv_one_item`, without NCFP. -/
theorem no_fixed_point_S {Y : Term} (hY : PureS Y) : ¬ Convertible (Y ⬝ S) (S ⬝ (Y ⬝ S)) := by
  intro h
  have e := conv_YS_one_item hY h
  subst e
  exact not_conv_SS h

/-- **Pure S has no fixed-point combinator**, even for weak convertibility: no pure-S `Y` has
    `Y f` convertible to `f (Y f)` for every pure-S `f`.  (Only `f = S` is used.)
    Same statement as `Ncfp.no_fpc`; an independent short proof via `conv_one_item`, without NCFP. -/
theorem no_fixed_point :
    ¬ ∃ Y, PureS Y ∧ ∀ f, PureS f → Convertible (Y ⬝ f) (f ⬝ (Y ⬝ f)) :=
  fun ⟨_, hY, h⟩ => no_fixed_point_S hY (h S .S)

/-! ## 3. Pure S with variables, and PEEL -/

namespace Open

/-- Pure-S terms over variables `var n`. -/
inductive VTerm
  | S
  | var (n : Nat)
  | app (f x : VTerm)
  deriving DecidableEq

local infixl:70 " ∙ " => VTerm.app

/-- The S-rule at any position. -/
inductive VStep : VTerm → VTerm → Prop
  | S (f g x : VTerm) : VStep (.S ∙ f ∙ g ∙ x) (f ∙ x ∙ (g ∙ x))
  | left {f f' : VTerm} (x : VTerm) (h : VStep f f') : VStep (f ∙ x) (f' ∙ x)
  | right (f : VTerm) {x x' : VTerm} (h : VStep x x') : VStep (f ∙ x) (f ∙ x')

inductive VSteps : VTerm → VTerm → Prop
  | refl (t : VTerm) : VSteps t t
  | step {t t' u : VTerm} (h : VStep t t') (hs : VSteps t' u) : VSteps t u

theorem VSteps.left {f f' : VTerm} (x : VTerm) (h : VSteps f f') : VSteps (f ∙ x) (f' ∙ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

/-- The embedding of terms; on pure-S terms it is the identity on structure. -/
def emb : Term → VTerm
  | .S => .S
  | .K => .var 0
  | .I => .var 1
  | .app f x => emb f ∙ emb x

/-- A weak step of a pure-S term is a `VStep` of its embedding. -/
theorem emb_wstep {t u : Term} (h : WStep t u) (ht : PureS t) : VStep (emb t) (emb u) := by
  induction h with
  | S f g x => exact .S (emb f) (emb g) (emb x)
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih => exact .left (emb x) (ih ht.app_inv.1)
  | right f _ ih => exact .right (emb f) (ih ht.app_inv.2)

theorem emb_wsteps {t u : Term} (h : WSteps t u) (ht : PureS t) : VSteps (emb t) (emb u) := by
  induction h with
  | refl t => exact .refl _
  | step s _ ih => exact .step (emb_wstep s ht) (ih (wstep_pure s ht).1)

/-- The number of occurrences of the variable `n`. -/
def occ (n : Nat) : VTerm → Nat
  | .S => 0
  | .var m => if m = n then 1 else 0
  | .app f x => occ n f + occ n x

/-- The number of leaves. -/
def vleaves : VTerm → Nat
  | .S => 1
  | .var _ => 1
  | .app f x => vleaves f + vleaves x

theorem vleaves_pos : ∀ t : VTerm, 0 < vleaves t
  | .S => Nat.zero_lt_one
  | .var _ => Nat.zero_lt_one
  | .app f x => by
    have := vleaves_pos f
    show 0 < vleaves f + vleaves x
    omega

/-- Occurrences of a variable never decrease along a step (S is non-erasing). -/
theorem vstep_occ {t u : VTerm} (h : VStep t u) (n : Nat) : occ n t ≤ occ n u := by
  induction h with
  | S f g x => simp only [occ]; omega
  | left x _ ih => simp only [occ]; omega
  | right f _ ih => simp only [occ]; omega

/-- A step creates no variable. -/
theorem vstep_occ_zero {t u : VTerm} {n : Nat} (h : VStep t u) (ht : occ n t = 0) :
    occ n u = 0 := by
  induction h with
  | S f g x => simp only [occ] at *; omega
  | left x _ ih => simp only [occ] at *; have := ih (by omega); omega
  | right f _ ih => simp only [occ] at *; have := ih (by omega); omega

theorem vsteps_occ {t u : VTerm} (h : VSteps t u) (n : Nat) : occ n t ≤ occ n u := by
  induction h with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans (vstep_occ s n) ih

theorem vstep_leaves {t u : VTerm} (h : VStep t u) : vleaves t ≤ vleaves u := by
  induction h with
  | S f g x => have := vleaves_pos x; simp only [vleaves]; omega
  | left x _ ih => simp only [vleaves]; omega
  | right f _ ih => simp only [vleaves]; omega

theorem vsteps_leaves {t u : VTerm} (h : VSteps t u) : vleaves t ≤ vleaves u := by
  induction h with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans (vstep_leaves s) ih

/-- `vapps M [w₁, …, w_r] = M w₁ ⋯ w_r` (variables). -/
def vapps (M : VTerm) : List Nat → VTerm
  | [] => M
  | w :: ws => vapps (M ∙ .var w) ws

theorem vleaves_vapps : ∀ (M : VTerm) (ws : List Nat), vleaves (vapps M ws) = vleaves M + ws.length
  | M, [] => by simp only [vapps, List.length_nil]; omega
  | M, w :: ws => by
    rw [vapps, vleaves_vapps _ ws]
    simp only [vleaves, List.length_cons]
    omega

theorem vsteps_vapps : ∀ {M N : VTerm} (ws : List Nat), VSteps M N → VSteps (vapps M ws) (vapps N ws)
  | _, _, [], h => h
  | _, _, w :: ws, h => vsteps_vapps ws (h.left (.var w))

/-- Copying a variable gives it two occurrences. -/
theorem occ_two (w : Nat) (f g : VTerm) : 2 ≤ occ w (f ∙ .var w ∙ (g ∙ .var w)) := by
  show 2 ≤ occ w f + (if w = w then 1 else 0) + (occ w g + (if w = w then 1 else 0))
  rw [if_pos rfl]
  omega

/-- **PEEL at the root.**  If `w` does not occur in `P` and `P w ↠ N` with `w` occurring at
    most once in `N`, then `N = P' w` with `P ↠ P'`. -/
theorem peel_one {w : Nat} {N : VTerm} (hN : occ w N ≤ 1) :
    ∀ {P : VTerm}, occ w P = 0 → VSteps (P ∙ .var w) N → ∃ P', N = P' ∙ .var w ∧ VSteps P P' := by
  intro P hP h
  generalize he : P ∙ .var w = s at h
  induction h generalizing P with
  | refl => exact ⟨P, he.symm, .refl _⟩
  | step st rest ih =>
    subst he
    cases st with
    | S f g x =>
      exact absurd (Nat.le_trans (occ_two w f g) (Nat.le_trans (vsteps_occ rest w) hN)) (by decide)
    | left _ h' =>
      obtain ⟨P', e, hs⟩ := ih hN (vstep_occ_zero h' hP) rfl
      exact ⟨P', e, .step h' hs⟩
    | right _ h' => cases h'

/-- **Theorem PEEL.**  For distinct variables `w₁ … w_r` occurring in neither `M` nor `N`,
    `M w₁ ⋯ w_r ↠ N w₁ ⋯ w_r` iff `M ↠ N`.  (`M` is arbitrary, e.g. `M′ x⃗`.) -/
theorem peel : ∀ {M N : VTerm} {ws : List Nat}, ws.Nodup → (∀ w ∈ ws, occ w M = 0) →
    (∀ w ∈ ws, occ w N = 0) → (VSteps (vapps M ws) (vapps N ws) ↔ VSteps M N)
  | _, _, [], _, _, _ => Iff.rfl
  | M, N, w :: ws, hd, hM, hN => by
    obtain ⟨hw, hd'⟩ := List.nodup_cons.mp hd
    have fresh : ∀ {Q : VTerm}, (∀ v ∈ w :: ws, occ v Q = 0) → ∀ v ∈ ws, occ v (Q ∙ .var w) = 0 := by
      intro Q hQ v hv
      have hne : w ≠ v := fun e => hw (e ▸ hv)
      have := hQ v (List.mem_cons_of_mem _ hv)
      simp only [occ, hne, if_false]
      omega
    rw [vapps, vapps, peel hd' (fresh hM) (fresh hN)]
    constructor
    · intro h
      have hP := hM w (List.mem_cons_self ..)
      have hle : occ w (N ∙ .var w) ≤ 1 := by
        have := hN w (List.mem_cons_self ..)
        simp only [occ, if_true]
        omega
      obtain ⟨P', e, hs⟩ := peel_one hle hP h
      injection e with e1
      subst e1
      exact hs
    · exact fun h => h.left (.var w)

/-! ### Open forms of the leaf-count corollaries

Here `M` is any `VTerm` (closed or not) and `x, y, z, w⃗` are variables, not necessarily
distinct. -/

theorem no_vsteps_of_lt {s u : VTerm} (h : vleaves u < vleaves s) : ¬ VSteps s u :=
  fun hv => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (vsteps_leaves hv))

/-- No relative `I` over open terms: `M x w⃗ ↠ x w⃗` is impossible. -/
theorem no_rel_I (M : VTerm) (x : Nat) (ws : List Nat) :
    ¬ VSteps (vapps (M ∙ .var x) ws) (vapps (.var x) ws) := by
  apply no_vsteps_of_lt
  rw [vleaves_vapps, vleaves_vapps]
  have := vleaves_pos M
  simp only [vleaves]
  omega

/-- No relative `K` over open terms: `M x y w⃗ ↠ x w⃗` is impossible. -/
theorem no_rel_K (M : VTerm) (x y : Nat) (ws : List Nat) :
    ¬ VSteps (vapps (M ∙ .var x ∙ .var y) ws) (vapps (.var x) ws) := by
  apply no_vsteps_of_lt
  rw [vleaves_vapps, vleaves_vapps]
  have := vleaves_pos M
  simp only [vleaves]
  omega

/-- No relative `T` over open terms: `M x y w⃗ ↠ y x w⃗` is impossible. -/
theorem no_rel_T (M : VTerm) (x y : Nat) (ws : List Nat) :
    ¬ VSteps (vapps (M ∙ .var x ∙ .var y) ws) (vapps (.var y ∙ .var x) ws) := by
  apply no_vsteps_of_lt
  rw [vleaves_vapps, vleaves_vapps]
  have := vleaves_pos M
  simp only [vleaves]
  omega

/-- No relative `C` over open terms: `M x y z w⃗ ↠ x z y w⃗` is impossible. -/
theorem no_rel_C (M : VTerm) (x y z : Nat) (ws : List Nat) :
    ¬ VSteps (vapps (M ∙ .var x ∙ .var y ∙ .var z) ws) (vapps (.var x ∙ .var z ∙ .var y) ws) := by
  apply no_vsteps_of_lt
  rw [vleaves_vapps, vleaves_vapps]
  have := vleaves_pos M
  simp only [vleaves]
  omega

/-- No relative `B` over open terms: `M x y z w⃗ ↠ x (y z) w⃗` is impossible. -/
theorem no_rel_B (M : VTerm) (x y z : Nat) (ws : List Nat) :
    ¬ VSteps (vapps (M ∙ .var x ∙ .var y ∙ .var z) ws) (vapps (.var x ∙ (.var y ∙ .var z)) ws) := by
  apply no_vsteps_of_lt
  rw [vleaves_vapps, vleaves_vapps]
  have := vleaves_pos M
  simp only [vleaves]
  omega

/-- No term applied to `r` variables reduces to a term with at most `r` leaves. -/
theorem no_short (M N : VTerm) (ws : List Nat) (h : vleaves N ≤ ws.length) :
    ¬ VSteps (vapps M ws) N := by
  apply no_vsteps_of_lt
  rw [vleaves_vapps]
  have := vleaves_pos M
  omega

/-- No relative permutation over open terms, the identity included: `M x⃗ ↠ y y⃗` is impossible
    whenever `y :: y⃗` is a permutation of `x⃗` (variables, not assumed distinct). -/
theorem no_rel_perm (M : VTerm) {y : Nat} {xs ys : List Nat} (hp : (y :: ys).Perm xs) :
    ¬ VSteps (vapps M xs) (vapps (.var y) ys) := by
  apply no_short
  rw [vleaves_vapps, ← hp.length_eq]
  simp only [vleaves, List.length_cons]
  omega

end Open

end PureSBasics
