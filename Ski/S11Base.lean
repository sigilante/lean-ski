import Ski.HnfS
open Term

/-!
# S11: the families of `p_K`, their head runs, and their blocks

Paper S11, *An S-Term Determined by Its Teeth Among Terms Without a Head Normal Form*, §3.
This module is the base of the S11 mechanization (plan `notes/S11-MECH-PLAN.md`, milestone
M1a).

* **The families.** `Q = S (S S)`, `G = S Q Q`, `c 0 = G`, `c (j+1) = Q (c j)`, and
  `pK = Q c₀ c₂ S`.  The terms `a_m` are indexed by a *state* `(i, n) : Nat × Nat` with
  `aT (i, n) = c i ⬝ c n`: the paper's `Q c_j c_n` is `c (j+1) ⬝ c n` and its `G c_n` is
  `c 0 ⬝ c n`, so the paper's "`a_m` is `Q c_j c_n` or `G c_n`" holds by definition.  The
  transition `next (j+1, n) = (j, n)`, `next (0, n) = (n, n+1)` is the paper's
  `a_m ↦ a_{m+1}`; `st m` is the state of `a_m` (`st 0 = (1, 2)`, so `am 0 = Q c₀ c₂`).  In
  both cases the paper's `b_{m+1}` is `c n' ⬝ a_{m+1}` with `n'` the second component of the
  new state, so `bT s = c s.2 ⬝ aT s`.  The index `i_m` is `(st m).2 - 1`, `x_m = c_{i_m} a_m`,
  and `v_m = a_m (Q a_m)` is the paper's `v`.
* **Head runs** (equations (1)–(3)): `run_Q`, `run_G`, `run_am`, `run_bm`, with the
  intermediate frames as separate `Step` facts.
* **Spines with passive arguments.** `apps T Us = T U₁ ⋯ U_r` (a left fold), `nargs` (the
  number of arguments on the spine), and the generic facts that a head step of `T` is a head
  step of `apps T Us` (`step_apps`), and that a step from `apps (S g₁ g₂) Us` consumes the
  first passive argument (`step_apps_S2`).
* **Blocks** (S1's 38-block table, kernel-checked by `decide +kernel`): `fold Q = 2`,
  `fold (c 0) = 22`, `fold (c (j+1)) = 30`, `fold (am m) = 31`, `fold (c j ⬝ am m) = 31`,
  `fold (Q ⬝ am m) = 30`, `fold (vm m) = 36`, `fold (Q ⬝ am m ⬝ vm m) = 31`, and blocks `31`
  and `36` absorb every block on the right.  Hence the hnf-less facts of Lemma 6(b) and
  `v_m` (`nohnf_am_apps`, `nohnf_cam_apps`, `nohnf_Qav_apps`, `nohnf_vm`) follow from
  `HnfS.no_hnf_of_bot`.  The paper derives these from head runs; here they come from the block
  model (plan §0).
-/

namespace S11

/-! ## The families -/

/-- `Q = S (S S)`. -/
def Q : Term := S ⬝ (S ⬝ S)

/-- `G = S Q Q`. -/
def G : Term := S ⬝ Q ⬝ Q

/-- `c 0 = G`, `c (j+1) = Q (c j)`. -/
def c : Nat → Term
  | 0 => G
  | j + 1 => Q ⬝ c j

/-- The term `p_K = S (S S) G (Q (Q G)) S`. -/
def pK : Term := S ⬝ (S ⬝ S) ⬝ G ⬝ (Q ⬝ (Q ⬝ G)) ⬝ S

theorem pK_eq : pK = Q ⬝ c 0 ⬝ c 2 ⬝ S := rfl

/-- The state transition `a_m ↦ a_{m+1}`: `Q c_j c_n ↦ c_j c_n`, `G c_n ↦ c_n c_{n+1}`. -/
def next : Nat × Nat → Nat × Nat
  | (j + 1, n) => (j, n)
  | (0, n) => (n, n + 1)

/-- The state of `a_m`. -/
def st : Nat → Nat × Nat
  | 0 => (1, 2)
  | m + 1 => next (st m)

/-- The term of a state: `aT (i, n) = c i ⬝ c n`. -/
def aT (s : Nat × Nat) : Term := c s.1 ⬝ c s.2

/-- `bT s = c s.2 ⬝ aT s`. -/
def bT (s : Nat × Nat) : Term := c s.2 ⬝ aT s

/-- `a_m`. -/
def am (m : Nat) : Term := aT (st m)

/-- `b_m` (the paper uses it for `m ≥ 1`). -/
def bm (m : Nat) : Term := bT (st m)

/-- `i_m`. -/
def im (m : Nat) : Nat := (st m).2 - 1

/-- `x_m = c_{i_m} a_m`. -/
def xm (m : Nat) : Term := c (im m) ⬝ am m

/-- `v_m = a_m (Q a_m)`. -/
def vm (m : Nat) : Term := am m ⬝ (Q ⬝ am m)

/-- `Y_n = b_n S`. -/
def Y (n : Nat) : Term := bm n ⬝ S

theorem st_succ (m : Nat) : st (m + 1) = next (st m) := rfl

theorem am_zero : am 0 = Q ⬝ c 0 ⬝ c 2 := rfl

theorem am_of_q {m j n : Nat} (hs : st m = (j + 1, n)) : am m = Q ⬝ c j ⬝ c n := by
  unfold am aT; rw [hs]; rfl

theorem am_of_g {m n : Nat} (hs : st m = (0, n)) : am m = G ⬝ c n := by
  unfold am aT; rw [hs]; rfl

theorem st_succ_q {m j n : Nat} (hs : st m = (j + 1, n)) : st (m + 1) = (j, n) := by
  rw [st_succ, hs]; rfl

theorem st_succ_g {m n : Nat} (hs : st m = (0, n)) : st (m + 1) = (n, n + 1) := by
  rw [st_succ, hs]; rfl

/-- The paper's `b_{m+1}`: `c_n a_{m+1}` after `Q c_j c_n`, `c_{n+1} a_{m+1}` after `G c_n`. -/
theorem bm_succ (m : Nat) : bm (m + 1) = c (st (m + 1)).2 ⬝ am (m + 1) := rfl

/-- The second index never falls below `2`. -/
theorem st_snd_ge (m : Nat) : 2 ≤ (st m).2 := by
  induction m with
  | zero => exact Nat.le_refl 2
  | succ m ih =>
    rw [st_succ]
    rcases h : st m with ⟨i, n⟩
    rw [h] at ih
    cases i with
    | zero => exact Nat.le_succ_of_le ih
    | succ j => exact ih

/-- `b_m = Q c_{i_m} a_m`. -/
theorem bm_eq (m : Nat) : bm m = Q ⬝ c (im m) ⬝ am m := by
  have h := st_snd_ge m
  unfold bm bT im
  obtain ⟨k, hk⟩ : ∃ k, (st m).2 = k + 1 := ⟨(st m).2 - 1, by omega⟩
  rw [hk]; rfl

/-! ## Spines with passive arguments -/

/-- `apps T [U₁, …, U_r] = T U₁ ⋯ U_r`. -/
def apps (T : Term) : List Term → Term
  | [] => T
  | U :: Us => apps (T ⬝ U) Us

/-- The number of arguments on the spine. -/
def nargs : Term → Nat
  | .app f _ => nargs f + 1
  | _ => 0

theorem apps_nil (T : Term) : apps T [] = T := rfl

theorem apps_cons (T U : Term) (Us : List Term) : apps T (U :: Us) = apps (T ⬝ U) Us := rfl

theorem apps_append (T : Term) (Us Vs : List Term) :
    apps T (Us ++ Vs) = apps (apps T Us) Vs := by
  induction Us generalizing T with
  | nil => rfl
  | cons U Us ih => exact ih (T ⬝ U)

theorem nargs_apps (T : Term) (Us : List Term) : nargs (apps T Us) = nargs T + Us.length := by
  induction Us generalizing T with
  | nil => rfl
  | cons U Us ih =>
    rw [apps_cons, ih, List.length_cons]
    show nargs T + 1 + Us.length = nargs T + (Us.length + 1); omega

/-- An application `apps T Us` splits as the function part and the last passive argument, or
`Us` is empty. -/
theorem apps_eq_app {T f x : Term} {Us : List Term} (h : apps T Us = f ⬝ x) :
    (Us = [] ∧ T = f ⬝ x) ∨ ∃ Vs, Us = Vs ++ [x] ∧ f = apps T Vs := by
  induction Us generalizing T with
  | nil => exact .inl ⟨rfl, h⟩
  | cons U Us ih =>
    rcases ih h with ⟨rfl, he⟩ | ⟨Vs, rfl, rfl⟩
    · injection he with h1 h2
      subst h1; subst h2
      exact .inr ⟨[], rfl, rfl⟩
    · exact .inr ⟨U :: Vs, rfl, rfl⟩

/-- Injectivity of a three-item frame. -/
theorem S3_inj {p q r x y z : Term} (h : S ⬝ p ⬝ q ⬝ r = S ⬝ x ⬝ y ⬝ z) :
    p = x ∧ q = y ∧ r = z := by
  injection h with h1 h2
  injection h1 with h3 h4
  injection h3 with _ h5
  exact ⟨h5, h4, h2⟩

/-- A spine with three arguments in its head part takes no passive argument in a three-item
frame. -/
theorem apps_eq3 {T x y z : Term} {Us : List Term} (hT : nargs T = 3)
    (h : apps T Us = S ⬝ x ⬝ y ⬝ z) : Us = [] ∧ T = S ⬝ x ⬝ y ⬝ z := by
  cases Us with
  | nil => exact ⟨rfl, h⟩
  | cons U Us =>
    have := congrArg nargs h
    rw [nargs_apps, hT, List.length_cons] at this
    exact absurd this (by simp only [nargs]; omega)

/-- A three-item frame `apps (S g₁ g₂) Us` has exactly one passive argument. -/
theorem apps_S2_eq3 {g₁ g₂ x y z : Term} {Us : List Term}
    (h : apps (S ⬝ g₁ ⬝ g₂) Us = S ⬝ x ⬝ y ⬝ z) : Us = [z] ∧ g₁ = x ∧ g₂ = y := by
  cases Us with
  | nil => injection h with h1 h2; injection h1 with h3 h4; injection h3
  | cons U Us =>
    cases Us with
    | nil =>
      obtain ⟨h1, h2, h3⟩ := S3_inj h
      exact ⟨by rw [h3], h1, h2⟩
    | cons U' Us =>
      have := congrArg nargs h
      rw [nargs_apps] at this
      exact absurd this (by simp only [nargs, List.length_cons]; omega)

/-- A head step of `T` is a head step of `T U₁ ⋯ U_r`. -/
theorem step_apps {T T' : Term} (h : Step T T') (Us : List Term) :
    Step (apps T Us) (apps T' Us) := by
  induction Us generalizing T T' with
  | nil => exact h
  | cons U Us ih => exact ih (.left U h)

theorem steps_apps {T T' : Term} (h : Steps T T') (Us : List Term) :
    Steps (apps T Us) (apps T' Us) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (step_apps h Us) ih

/-- The step from `T U₁ ⋯ U_r` is the step of `T`. -/
theorem step_apps_det {T T' t : Term} {Us : List Term} (h : Step T T')
    (ht : Step (apps T Us) t) : t = apps T' Us :=
  Step.det ht (step_apps h Us)

/-- A step from `S g₁ g₂ U₁ ⋯ U_r` consumes `U₁`. -/
theorem step_apps_S2 {g₁ g₂ t : Term} {Us : List Term} (h : Step (apps (S ⬝ g₁ ⬝ g₂) Us) t) :
    ∃ U Vs, Us = U :: Vs ∧ t = apps (g₁ ⬝ U ⬝ (g₂ ⬝ U)) Vs := by
  cases Us with
  | nil => exact absurd h (fun h => Whnf.no_step (.S2 g₁ g₂) h)
  | cons U Vs => exact ⟨U, Vs, rfl, step_apps_det (.S g₁ g₂ U) h⟩

/-! ## Head runs: equations (1)–(3) -/

theorem step_Q (u v : Term) : Step (Q ⬝ u ⬝ v) (S ⬝ S ⬝ v ⬝ (u ⬝ v)) := .S (S ⬝ S) u v

theorem step_SS (v w : Term) : Step (S ⬝ S ⬝ v ⬝ w) (S ⬝ w ⬝ (v ⬝ w)) := .S S v w

theorem step_G (u : Term) : Step (G ⬝ u) (Q ⬝ u ⬝ (Q ⬝ u)) := .S Q Q u

/-- Equation (1), first line: `Q u v → S S v (u v) → S (u v) (v (u v))`. -/
theorem run_Q (u v : Term) : Steps (Q ⬝ u ⬝ v) (S ⬝ (u ⬝ v) ⬝ (v ⬝ (u ⬝ v))) :=
  .step (step_Q u v) (.step (step_SS v (u ⬝ v)) (.refl _))

/-- Equation (1), second line: `G u → Q u (Q u) ↠ S (u (Q u)) (Q u (u (Q u)))`. -/
theorem run_G (u : Term) :
    Steps (G ⬝ u) (S ⬝ (u ⬝ (Q ⬝ u)) ⬝ (Q ⬝ u ⬝ (u ⬝ (Q ⬝ u)))) :=
  .step (step_G u) (run_Q u (Q ⬝ u))

/-- The first frames of `a_m`: `a_m ↠ S S c a_{m+1}` with `c = c (st (m+1)).2`. -/
theorem run_am_SS (m : Nat) : Steps (am m) (S ⬝ S ⬝ c (st (m + 1)).2 ⬝ am (m + 1)) := by
  rcases hs : st m with ⟨i, n⟩
  cases i with
  | succ j =>
    have h1 : st (m + 1) = (j, n) := st_succ_q hs
    have h2 : am (m + 1) = c j ⬝ c n := by unfold am aT; rw [h1]
    rw [am_of_q hs, h2, h1]
    exact .single (step_Q (c j) (c n))
  | zero =>
    rw [am_of_g hs]
    have h1 : st (m + 1) = (n, n + 1) := st_succ_g hs
    have h2 : am (m + 1) = c n ⬝ c (n + 1) := by unfold am aT; rw [h1]
    rw [h2, h1]
    exact .step (step_G (c n)) (.single (step_Q (c n) (Q ⬝ c n)))

/-- Equation (2): `a_m ↠ S S c a_{m+1} → S a_{m+1} b_{m+1}`. -/
theorem run_am (m : Nat) : Steps (am m) (S ⬝ am (m + 1) ⬝ bm (m + 1)) :=
  (run_am_SS m).trans (.single (step_SS _ _))

/-- Equation (3): `b_m = Q c_{i_m} a_m ↠ S x_m (a_m x_m)`. -/
theorem run_bm (m : Nat) : Steps (bm m) (S ⬝ xm m ⬝ (am m ⬝ xm m)) := by
  rw [bm_eq]; exact run_Q _ _

/-! ## Purity -/

open HnfS in
theorem pure_Q : PureS Q := .app .S (.app .S .S)

open HnfS in
theorem pure_G : PureS G := .app (.app .S pure_Q) pure_Q

open HnfS in
theorem pure_c (j : Nat) : PureS (c j) := by
  induction j with
  | zero => exact pure_G
  | succ j ih => exact .app pure_Q ih

open HnfS in
theorem pure_am (m : Nat) : PureS (am m) := .app (pure_c _) (pure_c _)

open HnfS in
theorem pure_apps {T : Term} {Us : List Term} (hT : PureS T) (hU : ∀ U ∈ Us, PureS U) :
    PureS (apps T Us) := by
  induction Us generalizing T with
  | nil => exact hT
  | cons U Us ih =>
    exact ih (.app hT (hU U (.head _))) (fun V hV => hU V (.tail _ hV))

/-! ## Blocks (S1's 38-block table) -/

/-- The table facts used here, by kernel evaluation. -/
theorem T_S11 :
    HnfS.fold Q = 2 ∧ HnfS.fold G = 22 ∧ HnfS.β 2 22 = 30 ∧ HnfS.β 2 30 = 30 ∧
    HnfS.β 22 22 = 31 ∧ HnfS.β 22 30 = 31 ∧ HnfS.β 30 22 = 31 ∧ HnfS.β 30 30 = 31 ∧
    HnfS.β 22 31 = 31 ∧ HnfS.β 30 31 = 31 ∧ HnfS.β 2 31 = 30 ∧ HnfS.β 31 30 = 36 ∧
    HnfS.β 30 36 = 31 := by
  decide +kernel

/-- Block `31` absorbs every block on the right. -/
theorem T_S11_31 : ∀ u, u < 38 → HnfS.β 31 u = 36 := by decide +kernel

/-- Block `36` absorbs every block on the right. -/
theorem T_S11_36 : ∀ u, u < 38 → HnfS.β 36 u = 36 := by decide +kernel

theorem fold_Q : HnfS.fold Q = 2 := T_S11.1

theorem fold_c_zero : HnfS.fold (c 0) = 22 := T_S11.2.1

theorem fold_c_succ (j : Nat) : HnfS.fold (c (j + 1)) = 30 := by
  induction j with
  | zero =>
    show HnfS.β (HnfS.fold Q) (HnfS.fold (c 0)) = 30
    rw [fold_Q, fold_c_zero]; exact T_S11.2.2.1
  | succ j ih =>
    show HnfS.β (HnfS.fold Q) (HnfS.fold (c (j + 1))) = 30; rw [fold_Q, ih]; exact T_S11.2.2.2.1

theorem fold_c (j : Nat) : HnfS.fold (c j) = 22 ∨ HnfS.fold (c j) = 30 := by
  cases j with
  | zero => exact .inl fold_c_zero
  | succ j => exact .inr (fold_c_succ j)

/-- Every `aT s`, in particular every `a_m`, has block `31`. -/
theorem fold_aT (s : Nat × Nat) : HnfS.fold (aT s) = 31 := by
  show HnfS.β (HnfS.fold (c s.1)) (HnfS.fold (c s.2)) = 31
  obtain ⟨-, -, -, -, h1, h2, h3, h4, -⟩ := T_S11
  rcases fold_c s.1 with e1 | e1 <;> rcases fold_c s.2 with e2 | e2 <;> rw [e1, e2] <;>
    first | exact h1 | exact h2 | exact h3 | exact h4

theorem fold_am (m : Nat) : HnfS.fold (am m) = 31 := fold_aT _

/-- `c_j a_m` has block `31`. -/
theorem fold_cam (j m : Nat) : HnfS.fold (c j ⬝ am m) = 31 := by
  show HnfS.β (HnfS.fold (c j)) (HnfS.fold (am m)) = 31
  rw [fold_am]
  rcases fold_c j with e | e <;> rw [e]
  · exact T_S11.2.2.2.2.2.2.2.2.1
  · exact T_S11.2.2.2.2.2.2.2.2.2.1

/-- `Q a_m` has block `30`. -/
theorem fold_Qam (m : Nat) : HnfS.fold (Q ⬝ am m) = 30 := by
  show HnfS.β (HnfS.fold Q) (HnfS.fold (am m)) = 30
  rw [fold_Q, fold_am]; exact T_S11.2.2.2.2.2.2.2.2.2.2.1

/-- `v_m = a_m (Q a_m)` has block `36`. -/
theorem fold_vm (m : Nat) : HnfS.fold (vm m) = 36 := by
  show HnfS.β (HnfS.fold (am m)) (HnfS.fold (Q ⬝ am m)) = 36
  rw [fold_am, fold_Qam]; exact T_S11.2.2.2.2.2.2.2.2.2.2.2.1

/-- `Q a_m v_m` has block `31`. -/
theorem fold_Qav (m : Nat) : HnfS.fold (Q ⬝ am m ⬝ vm m) = 31 := by
  show HnfS.β (HnfS.fold (Q ⬝ am m)) (HnfS.fold (vm m)) = 31
  rw [fold_Qam, fold_vm]; exact T_S11.2.2.2.2.2.2.2.2.2.2.2.2

/-- A spine whose head part has block `36` has block `36`. -/
theorem fold_apps_36 {T : Term} {Us : List Term} (hT : HnfS.fold T = 36)
    (hU : ∀ U ∈ Us, HnfS.PureS U) : HnfS.fold (apps T Us) = 36 := by
  induction Us generalizing T with
  | nil => exact hT
  | cons U Us ih =>
    refine ih ?_ (fun V hV => hU V (.tail _ hV))
    show HnfS.β (HnfS.fold T) (HnfS.fold U) = 36
    rw [hT]; exact T_S11_36 _ (HnfS.fold_lt (hU U (.head _)))

/-- A spine whose head part has block `31` and at least one argument has block `36`. -/
theorem fold_apps_31 {T U : Term} {Us : List Term} (hT : HnfS.fold T = 31)
    (hU : ∀ V ∈ U :: Us, HnfS.PureS V) : HnfS.fold (apps T (U :: Us)) = 36 := by
  rw [apps_cons]
  refine fold_apps_36 ?_ (fun V hV => hU V (.tail _ hV))
  show HnfS.β (HnfS.fold T) (HnfS.fold U) = 36
  rw [hT]; exact T_S11_31 _ (HnfS.fold_lt (hU U (.head _)))

/-! ## Lemma 6(b) and `v_m`, by blocks -/

/-- Lemma 6(b), first family: `a_m U₁ ⋯ U_r` (`r ≥ 1`) has no hnf. -/
theorem nohnf_am_apps (m : Nat) {U : Term} {Us : List Term}
    (hU : ∀ V ∈ U :: Us, HnfS.PureS V) : ¬ HnfS.HasHnf (apps (am m) (U :: Us)) :=
  HnfS.no_hnf_of_bot (pure_apps (pure_am m) hU) (fold_apps_31 (fold_am m) hU)

/-- Lemma 6(b), second family: `c_j a_m U₁ ⋯ U_r` (`r ≥ 1`) has no hnf. -/
theorem nohnf_cam_apps (j m : Nat) {U : Term} {Us : List Term}
    (hU : ∀ V ∈ U :: Us, HnfS.PureS V) : ¬ HnfS.HasHnf (apps (c j ⬝ am m) (U :: Us)) :=
  HnfS.no_hnf_of_bot (pure_apps (.app (pure_c j) (pure_am m)) hU) (fold_apps_31 (fold_cam j m) hU)

/-- `v_m = a_m (Q a_m)` has no hnf. -/
theorem nohnf_vm (m : Nat) : ¬ HnfS.HasHnf (vm m) :=
  HnfS.no_hnf_of_bot (.app (pure_am m) (.app pure_Q (pure_am m))) (fold_vm m)

/-- Lemma 6(b), third family: `Q a_m v_m U₁ ⋯ U_r` (`r ≥ 1`) has no hnf. -/
theorem nohnf_Qav_apps (m : Nat) {U : Term} {Us : List Term}
    (hU : ∀ V ∈ U :: Us, HnfS.PureS V) : ¬ HnfS.HasHnf (apps (Q ⬝ am m ⬝ vm m) (U :: Us)) := by
  have hp : HnfS.PureS (Q ⬝ am m ⬝ vm m) :=
    .app (.app pure_Q (pure_am m)) (.app (pure_am m) (.app pure_Q (pure_am m)))
  exact HnfS.no_hnf_of_bot (pure_apps hp hU) (fold_apps_31 (fold_Qav m) hU)

end S11
