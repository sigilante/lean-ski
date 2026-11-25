import Ski.S11Second

open Term

/-!
# S11: solutions in 𝔅; Theorem 1 (CT(p_K)) and Corollary 2

Paper S11, *An S-Term Determined by Its Teeth Among Terms Without a Head Normal Form*, §5 and
the proofs of Theorem 1 and Corollary 2.  Milestone M5 of `notes/S11-MECH-PLAN.md`.  Lemma
numbers follow the compiled paper (`lem:persist` = Lemma 15, `lem:closure` = Lemma 16 (Lean
`lemma15`), `lem:typing` = Lemma 17 (Lean `lemma16_i`/`lemma16_ii`), `lem:sol` = Lemma 18).

* **Definition 14** (`SolFrom k s`, "`s` is a solution from `k`").  Coinductive: some predicate
  `R` holds of `(k, s)` and is closed under "the head run reaches a two-item hnf `S s' t'` with
  `t' =β b_{k+1}`, and `R (k+1) s'`".  No sequence is ever chosen.  `SolFrom.unfold` is the
  paper's reading (one step of the spine equations), `solFrom_of_seq` builds a solution from an
  explicit sequence `s_j, t_j`, and `SolFrom.step` uses the uniqueness of the hnf (the paper's
  "`s_j`, `t_j` are determined by `s₀`").
* **Lemma 15(a), (b)**: `sol_conv`; `sol_am` (`a_k`) and `sol_aq` (`a′_k`, `k ≥ n₀`).
  Lemma 15(c) is `lemma10c` (S11Closure); Theorem 1 instantiates it with the explicit spine
  `P j s := s = a′_{n₀+j}` (`spine_aq`), as the M1b review requires.
* **Lemma 18** (`lemma18`): a member of `𝔅` that is a solution from `k` is `a_k`, by cases on
  `InB`; the final step `m = k` is `im_shift_inj` with `im_eq_of_xm_conv`.
* **Theorem 1** (`ct_pK`) and **Corollary 2** (`ct_pK_rest`).
-/

namespace S11
open HnfS Conv
open HeadRec (Sub)

/-! ## Definition 14: solutions -/

/-- **Definition 14.**  `s` is a *solution from `k`*: for every `j`, `s_j` has a two-item hnf
`S s_{j+1} t_{j+1}` with `t_{j+1} =β b_{k+j+1}` (`s₀ = s`).  Stated coinductively, as the
existence of a predicate `R` that contains `(k, s)` and is closed under one spine equation. -/
def SolFrom (k : Nat) (s : Term) : Prop :=
  ∃ R : Nat → Term → Prop, R k s ∧
    ∀ k s, R k s → ∃ s' t', Steps s (S ⬝ s' ⬝ t') ∧ Convertible t' (bm (k + 1)) ∧ R (k + 1) s'

/-- The coinduction principle for `SolFrom`. -/
theorem SolFrom.coind (R : Nat → Term → Prop)
    (hc : ∀ k s, R k s → ∃ s' t', Steps s (S ⬝ s' ⬝ t') ∧ Convertible t' (bm (k + 1)) ∧
      R (k + 1) s')
    {k : Nat} {s : Term} (h : R k s) : SolFrom k s :=
  ⟨R, h, hc⟩

/-- One spine equation: a solution from `k` has a two-item hnf `S s' t'` with
`t' =β b_{k+1}`, and `s'` is a solution from `k + 1`. -/
theorem SolFrom.unfold {k : Nat} {s : Term} (h : SolFrom k s) :
    ∃ s' t', Steps s (S ⬝ s' ⬝ t') ∧ Convertible t' (bm (k + 1)) ∧ SolFrom (k + 1) s' := by
  obtain ⟨R, hR, hc⟩ := h
  obtain ⟨s', t', h1, h2, h3⟩ := hc k s hR
  exact ⟨s', t', h1, h2, R, h3, hc⟩

/-- A solution from an explicit sequence: if `s_j ↠_h S s_{j+1} t_{j+1}` and
`t_{j+1} =β b_{k+j+1}` for every `j`, then `s₀` is a solution from `k`. -/
theorem solFrom_of_seq (k : Nat) (ss ts : Nat → Term)
    (h : ∀ j, Steps (ss j) (S ⬝ ss (j + 1) ⬝ ts (j + 1)) ∧
      Convertible (ts (j + 1)) (bm (k + j + 1))) :
    SolFrom k (ss 0) := by
  refine SolFrom.coind (fun k' s => ∃ j, k' = k + j ∧ s = ss j) ?_ ⟨0, rfl, rfl⟩
  rintro k' s ⟨j, rfl, rfl⟩
  exact ⟨ss (j + 1), ts (j + 1), (h j).1, (h j).2, j + 1, rfl, rfl⟩

/-- The hnf of a solution is unique: if `s ↠_h S a b`, then `a` is a solution from `k + 1` and
`b =β b_{k+1}`. -/
theorem SolFrom.step {k : Nat} {s a b : Term} (h : SolFrom k s) (hs : Steps s (S ⬝ a ⬝ b)) :
    SolFrom (k + 1) a ∧ Convertible b (bm (k + 1)) := by
  obtain ⟨s', t', h1, h2, h3⟩ := h.unfold
  have e := hnf_eq hs (isHnf_S2 a b) h1 (isHnf_S2 s' t')
  cases e
  exact ⟨h3, h2⟩

/-- A solution has an hnf. -/
theorem SolFrom.hasHnf {k : Nat} {s : Term} (h : SolFrom k s) : HasHnf s :=
  let ⟨s', t', h1, _⟩ := h.unfold
  ⟨_, h1.weak, isHnf_S2 s' t'⟩

/-- A solution is not `S` and not `S y`. -/
theorem SolFrom.not_short {k : Nat} {s : Term} (h : SolFrom k s)
    (hs : s = S ∨ ∃ y, s = S ⬝ y) : False := by
  obtain ⟨s', t', h1, -⟩ := h.unfold
  rcases hs with rfl | ⟨y, rfl⟩
  · have e := InfNF.steps_from_hnf (.inl rfl) h1
    cases e
  · have e := InfNF.steps_from_hnf (.inr (.inl ⟨y, rfl⟩)) h1
    cases e

/-- If `S x y` is a solution from `k`, then `x` is one from `k + 1`. -/
theorem SolFrom.first {k : Nat} {x y : Term} (h : SolFrom k (S ⬝ x ⬝ y)) : SolFrom (k + 1) x :=
  (h.step (.refl _)).1

/-! ## Lemma 15(a), (b) -/

/-- **Lemma 15(a).**  A closed S-term convertible with a solution from `k` is one. -/
theorem sol_conv {k : Nat} {s s' : Term} (h : SolFrom k s) (hp : PureS s) (hp' : PureS s')
    (hc : Convertible s s') : SolFrom k s' := by
  refine SolFrom.coind
    (fun k x => ∃ y, SolFrom k y ∧ PureS y ∧ PureS x ∧ Convertible y x) ?_ ⟨s, h, hp, hp', hc⟩
  rintro k x ⟨y, hy, py, px, hyx⟩
  obtain ⟨y1, z1, h1, hz, hy1⟩ := hy.unfold
  obtain ⟨x1, x2, h2, c1, c2⟩ := inv_hnf2 py px hyx h1
  exact ⟨x1, x2, h2, c2.symm.trans hz, y1, hy1,
    (InfNF.steps_pure py h1).app_inv.1.app_inv.2, (InfNF.steps_pure px h2).app_inv.1.app_inv.2, c1⟩

/-- **Lemma 15(b)**, first half: `a_k` is a solution from `k` (equation (2)), with
`s_j = a_{k+j}`, `t_j = b_{k+j}`. -/
theorem sol_am (k : Nat) : SolFrom k (am k) :=
  SolFrom.coind (fun k s => s = am k)
    (fun k s hs => by subst hs; exact ⟨_, _, run_am k, .refl _, rfl⟩) rfl

/-- **Lemma 15(b)**, second half, from the explicit run of `q` (Lemmas 11, 13 as in
`second_run`): `a′_k` is a solution from `k` for every `k ≥ n₀`. -/
theorem sol_aq {q : Term} {n₀ : Nat}
    (hR : ∀ n, n₀ ≤ n → Steps (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1)) ∧
      Convertible (bq q (n + 1)) (bm (n + 1)))
    {k : Nat} (hk : n₀ ≤ k) : SolFrom k (aq q k) := by
  refine SolFrom.coind (fun k s => n₀ ≤ k ∧ s = aq q k) ?_ ⟨hk, rfl⟩
  rintro k s ⟨hk, rfl⟩
  obtain ⟨h1, h2⟩ := hR k hk
  exact ⟨_, _, h1, h2, Nat.le_succ_of_le hk, rfl⟩

/-- **Lemma 15(b)** for `q` with the teeth of `p_K`: from some `n₀` on, `a′_k` is a solution
from `k`. -/
theorem lemma15b {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) :
    ∃ n₀, ∀ k, n₀ ≤ k → SolFrom k (aq q k) := by
  obtain ⟨n₀, h⟩ := second_run hq hnq hY
  exact ⟨n₀, fun k hk =>
    sol_aq (fun n hn => ⟨(h n hn).2.1, (h n hn).2.2.2⟩) hk⟩

/-- The explicit spine of `q` (the M1b review's instantiation of Lemma 15(c)):
`P j s := s = a′_{n₀+j}` is a spine predicate. -/
theorem spine_aq {q : Term} {n₀ : Nat}
    (hR : ∀ n, n₀ ≤ n → Steps (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1))) :
    Spine (fun j s => s = aq q (n₀ + j)) := by
  intro j s hs
  subst hs
  exact ⟨_, _, hR (n₀ + j) (Nat.le_add_right _ _), rfl⟩

/-! ## Lemma 18 -/

/-- Along `a_m` and a solution from `k`, the spines stay in step. -/
theorem sol_am_shift {k m : Nat} (h : SolFrom k (am m)) : ∀ j, SolFrom (k + j) (am (m + j))
  | 0 => h
  | j + 1 => ((sol_am_shift h j).step (run_am (m + j))).1

/-- If `a_m` is a solution from `k`, then `m = k`: `b_{m+j} =β b_{k+j}` gives
`x_{m+j} =β x_{k+j}`, so `i_{m+j} = i_{k+j}` for all `j ≥ 1`, and `i` is not eventually
periodic. -/
theorem sol_am_eq {k m : Nat} (h : SolFrom k (am m)) : m = k := by
  apply im_shift_inj
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hc := ((sol_am_shift h i).step (run_am (m + i))).2
  obtain ⟨a', b', h1, c1, -⟩ := inv_hnf2 (pure_bm _) (pure_bm _) hc (run_bm (m + i + 1))
  have e := hnf_eq h1 (isHnf_S2 a' b') (run_bm (k + i + 1)) (isHnf_S2 _ _)
  cases e
  exact im_eq_of_xm_conv c1

/-- `b_m` has an hnf. -/
theorem hasHnf_bm (m : Nat) : HasHnf (bm m) := ⟨_, (run_bm m).weak, isHnf_S2 _ _⟩

/-- **Lemma 18** (`lem:sol`).  If `β ∈ 𝔅` is a solution from `k`, then `β = a_k`. -/
theorem lemma18 {k : Nat} {β : Term} (hb : InB β) (hs : SolFrom k β) : β = am k := by
  cases hb with
  | pS => exact (hs.not_short (.inl rfl)).elim
  | pSS => exact (hs.not_short (.inr ⟨S, rfl⟩)).elim
  | pQ => exact (hs.not_short (.inr ⟨S ⬝ S, rfl⟩)).elim
  | pSQ => exact (hs.not_short (.inr ⟨Q, rfl⟩)).elim
  | pc j =>
    cases j with
    | zero =>
      have h1 : SolFrom (k + 1) Q := SolFrom.first (x := Q) (y := Q) hs
      exact (h1.not_short (.inr ⟨S ⬝ S, rfl⟩)).elim
    | succ j =>
      have h1 : SolFrom (k + 1) (S ⬝ S) := SolFrom.first (x := S ⬝ S) (y := c j) hs
      exact (h1.not_short (.inr ⟨S, rfl⟩)).elim
  | Fa m Us hU =>
    cases Us with
    | nil =>
      have hs' : SolFrom k (am m) := hs
      show am m = am k
      rw [sol_am_eq hs']
    | cons U Us =>
      exact (nohnf_am_apps m (fun V hV => (hU V hV).pure) hs.hasHnf).elim
  | Fx j m Us hU =>
    cases Us with
    | nil =>
      cases j with
      | zero =>
        have hs' : SolFrom k (G ⬝ am m) := hs
        have h1 := (hs'.step (run_G (am m))).1
        exact (nohnf_vm m h1.hasHnf).elim
      | succ j =>
        have hs' : SolFrom k (Q ⬝ c j ⬝ am m) := hs
        have h2 := (hs'.step (run_Q (c j) (am m))).2
        have pa := pure_am m
        have pca : PureS (c j ⬝ am m) := .app (pure_c j) pa
        have nv : ¬ HasHnf (am m ⬝ (c j ⬝ am m)) := nohnf_am_apps m (Us := []) (pure_one pca)
        exact (inv_nohnf (.app pa pca) (pure_bm _) h2 nv (hasHnf_bm _)).elim
    | cons U Us =>
      exact (nohnf_cam_apps j m (fun V hV => (hU V hV).pure) hs.hasHnf).elim
  | FQa m =>
    have h1 : SolFrom (k + 1) (S ⬝ S) := SolFrom.first (x := S ⬝ S) (y := am m) hs
    exact (h1.not_short (.inr ⟨S, rfl⟩)).elim
  | FQa2 m Us hU =>
    cases Us with
    | nil =>
      have hs' : SolFrom k (Q ⬝ am m ⬝ vm m) := hs
      have h1 := (hs'.step (run_Q (am m) (vm m))).1
      have pv : PureS (vm m) := .app (pure_am m) (.app pure_Q (pure_am m))
      exact (nohnf_am_apps m (Us := []) (pure_one pv) h1.hasHnf).elim
    | cons U Us =>
      exact (nohnf_Qav_apps m (fun V hV => (hU V hV).pure) hs.hasHnf).elim
  | FSSc j => exact ((SolFrom.first hs).not_short (.inl rfl)).elim
  | FSSa m => exact ((SolFrom.first hs).not_short (.inl rfl)).elim
  | FSSQa m => exact ((SolFrom.first hs).not_short (.inl rfl)).elim
  | FSSv m => exact ((SolFrom.first hs).not_short (.inl rfl)).elim
  | FSa m => exact (hs.not_short (.inr ⟨_, rfl⟩)).elim
  | FSca j m => exact (hs.not_short (.inr ⟨_, rfl⟩)).elim
  | FSv m => exact (hs.not_short (.inr ⟨_, rfl⟩)).elim
  | FSav m => exact (hs.not_short (.inr ⟨_, rfl⟩)).elim

/-! ## Theorem 1 -/

/-- One head run to `S a b`: either literal (`t = S a b`) or at least one step. -/
theorem steps_cases {t u : Term} (h : Steps t u) : t = u ∨ ∃ t₁, Step t t₁ ∧ Steps t₁ u := by
  cases h with
  | refl => exact .inl rfl
  | step s r => exact .inr ⟨_, s, r⟩

/-- **A non-literal step** (proof of Theorem 1, first sentence): from every `n ≥ n₀` on, some
`a′_{n'}` is not literally `S a′_{n'+1} b′_{n'+1}`, since a literal step shrinks the size.
Strong induction on `sz (a′_n)`; equality of terms is decidable. -/
theorem exists_nonliteral {q : Term} {n₀ : Nat}
    (hR : ∀ n, n₀ ≤ n → Steps (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1))) :
    ∀ s n, n₀ ≤ n → HeadRec.sz (aq q n) ≤ s →
      ∃ n', n ≤ n' ∧ aq q n' ≠ S ⬝ aq q (n' + 1) ⬝ bq q (n' + 1)
  | 0, n, _, h => absurd h (Nat.not_le_of_gt (HeadRec.sz_pos _))
  | s + 1, n, hn, h => by
    cases decEq (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1)) with
    | isFalse hne => exact ⟨n, Nat.le_refl n, hne⟩
    | isTrue e =>
      have hlt : HeadRec.sz (aq q (n + 1)) < HeadRec.sz (aq q n) := by
        rw [e]
        exact Nat.lt_of_lt_of_le (HeadRec.sz_arg_lt S _) (Nat.le_of_lt (HeadRec.sz_fun_lt _ _))
      obtain ⟨n', h1, h2⟩ :=
        exists_nonliteral hR s (n + 1) (Nat.le_succ_of_le hn) (by omega)
      exact ⟨n', by omega, h2⟩

/-- **Theorem 1 (CT(p_K)).**  Every closed S-term `q` without an hnf such that
`τ_n(q) =β τ_n(p_K)` for all `n ≥ 1` satisfies `q =β p_K`. -/
theorem ct_pK {q : Term} (hq : PureS q) (hn : ¬ HasHnf q)
    (ht : ∀ n, 1 ≤ n → Convertible (tooth n q) (tooth n pK)) : Convertible q pK := by
  have hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n) := fun n h => by
    have := ht n h
    rw [tooth_pK h] at this
    exact this
  -- Lemmas 11 and 13: the explicit run `a′_n ↠_h S a′_{n+1} b′_{n+1}` from `n₀` on.
  obtain ⟨n₀, hR⟩ := second_run hq hn hY
  have hst : ∀ n, n₀ ≤ n → Steps (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1)) :=
    fun n h => (hR n h).2.1
  -- A non-literal step `n = n₀ + j₀`: `b′_{n+1} = y a′_{n+1}` (Lemma 3(a)).
  obtain ⟨n, hn₀, hne⟩ :=
    exists_nonliteral hst (HeadRec.sz (aq q n₀)) n₀ (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨j₀, rfl⟩ : ∃ j₀, n = n₀ + j₀ := ⟨n - n₀, by omega⟩
  have hpa : PureS (aq q (n₀ + j₀)) := aq_pure hq hn (n₀ + j₀)
  obtain ⟨y, hby⟩ : ∃ y, bq q (n₀ + j₀ + 1) = y ⬝ aq q (n₀ + j₀ + 1) := by
    rcases steps_cases (hst _ hn₀) with e | ⟨t₁, s, r⟩
    · exact absurd e hne
    · obtain ⟨y, -, e⟩ := run_to_S2 hpa s r
      exact ⟨y, e⟩
  have hsub : Sub (aq q (n₀ + (j₀ + 1))) (bq q (n₀ + j₀ + 1)) := by
    rw [hby]; exact .right y .refl
  have hpb : PureS (bq q (n₀ + j₀ + 1)) := by
    have hp := tooth_pure hq hn (n₀ + j₀ + 1)
    rw [(hR _ hn₀).2.2.1] at hp
    exact hp.app_inv.1
  -- (CR): a common reduct `R` of `b′_{n+1}` and `b_{n+1}` (Lemma 13).
  obtain ⟨R, hbR, hbmR⟩ := conv_iff_join.1 (hR _ hn₀).2.2.2
  -- Lemma 15(c) on the explicit spine `P j s := s = a′_{n₀+j}`.
  obtain ⟨j', -, s', u', rfl, hsu, hu⟩ :=
    lemma10c (spine_aq hst) (j := j₀ + 1) hpb rfl (.refl _) hsub hbR
  -- Lemmas 16, 17: `u' ∈ Red(𝔅)`.
  obtain ⟨β, hβ, hβu⟩ := lemma15 ⟨bm (n₀ + j₀ + 1), InB.ofBm _, hbmR⟩ hu
  -- Lemma 15(a), (b): `u'` and `β` are solutions from `k = n₀ + j'`; Lemma 18: `β = a_k`.
  have hk : n₀ ≤ n₀ + j' := Nat.le_add_right _ _
  have hsol := sol_aq (fun n h => ⟨(hR n h).2.1, (hR n h).2.2.2⟩) hk
  have hpa' := aq_pure hq hn (n₀ + j')
  have hpu : PureS u' := (fold_wsteps hsu hpa').1
  have hsolu := sol_conv hsol hpa' hpu (Convertible.of_wsteps hsu)
  have hsolβ := sol_conv hsolu hpu hβ.pure (Convertible.of_wsteps hβu).symm
  have e := lemma18 hβ hsolβ
  subst e
  -- `a′_k =β u' =β a_k`, so `rest^k(q) = a′_k S =β a_k S = rest^k(p_K)`; Lemma 6.
  have hconv : Convertible (aq q (n₀ + j')) (am (n₀ + j')) :=
    (Convertible.of_wsteps hsu).trans (Convertible.of_wsteps hβu).symm
  have hrest : Convertible (restN (n₀ + j') q) (restN (n₀ + j') pK) := by
    rw [(hR _ hk).1, restN_pK]
    exact conv_appL S hconv
  exact lemma6 hq pure_pK hn nohnf_pK (n₀ + j') hrest (fun i h1 _ => ht i h1)

/-! ## Corollary 2 -/

/-- `pre n t = t Y_n ⋯ Y_1`. -/
def pre : Nat → Term → Term
  | 0, t => t
  | n + 1, t => pre n (t ⬝ Y (n + 1))

theorem restN_add (n : Nat) (t : Term) : ∀ i, restN (i + n) t = restN i (restN n t)
  | 0 => by rw [Nat.zero_add]; rfl
  | i + 1 => by rw [Nat.succ_add, restN_succ, restN_add n t i]; rfl

/-- `τ_{n+i}(t) = τ_i(rest^n(t))` for `i ≥ 1`. -/
theorem tooth_add (n : Nat) (t : Term) (i : Nat) :
    tooth (n + (i + 1)) t = tooth (i + 1) (restN n t) := by
  show tooth1 (restN (n + i) t) = tooth1 (restN i (restN n t))
  rw [Nat.add_comm n i, restN_add]

/-- For hnf-less `t`, `t Y_n ⋯ Y_1` has no hnf, its `n`-th rest is `t`, and its teeth
`τ_1, …, τ_n` are `Y_1, …, Y_n`: each prefix `t Y_n ⋯ Y_{j+1}` is its own first stable
frame. -/
theorem pre_spec : ∀ (n : Nat) {t : Term}, PureS t → ¬ HasHnf t →
    PureS (pre n t) ∧ ¬ HasHnf (pre n t) ∧ restN n (pre n t) = t ∧
      ∀ i, 1 ≤ i → i ≤ n → tooth i (pre n t) = Y i
  | 0, t, hp, hn => ⟨hp, hn, rfl, fun i h1 h2 => absurd h1 (by omega)⟩
  | n + 1, t, hp, hn => by
    have hp' : PureS (t ⬝ Y (n + 1)) := .app hp (pure_Y _)
    have hn' : ¬ HasHnf (t ⬝ Y (n + 1)) := nohnf_app hp (pure_Y _) hn
    obtain ⟨h1, h2, h3, h4⟩ := pre_spec n hp' hn'
    obtain ⟨e1, e2⟩ := moves_A hp (pure_Y (n + 1)) hn
    refine ⟨h1, h2, ?_, fun i hi1 hi2 => ?_⟩
    · show rest1 (restN n (pre n (t ⬝ Y (n + 1)))) = t
      rw [h3, e1]
    · rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · exact h4 i hi1 (by omega)
      · obtain rfl : i = n + 1 := by omega
        show tooth1 (restN n (pre n (t ⬝ Y (n + 1)))) = Y (n + 1)
        rw [h3, e2]

/-- **Corollary 2.**  Let `n ≥ 0`.  Every closed S-term `q` without an hnf such that
`τ_i(q) =β τ_{n+i}(p_K)` for all `i ≥ 1` satisfies `q =β rest^n(p_K)`. -/
theorem ct_pK_rest (n : Nat) {q : Term} (hq : PureS q) (hn : ¬ HasHnf q)
    (ht : ∀ i, 1 ≤ i → Convertible (tooth i q) (tooth (n + i) pK)) :
    Convertible q (restN n pK) := by
  obtain ⟨hp', hn', hr', ht'⟩ := pre_spec n hq hn
  have hc : Convertible (pre n q) pK := by
    refine ct_pK hp' hn' (fun i hi => ?_)
    rcases Nat.lt_or_ge n i with hlt | hle
    · obtain ⟨i', rfl⟩ : ∃ i', i = n + (i' + 1) := ⟨i - n - 1, by omega⟩
      rw [tooth_add, hr']
      exact ht (i' + 1) (Nat.succ_pos i')
    · rw [ht' i hi hle, tooth_pK hi]
      exact .refl _
  have h := inv_restN hp' pure_pK hc hn' n
  rw [hr'] at h
  exact h

end S11
