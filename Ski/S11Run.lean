import Ski.S11Teeth

open Term

/-!
# S11: the run of `p_K`; Lemmas 8, 9, 10

Paper S11, *An S-Term Determined by Its Teeth Among Terms Without a Head Normal Form*, §3.
Milestone M2 of the plan `notes/S11-MECH-PLAN.md`.  Lemma numbers follow the compiled paper
(`lem:pk` = Lemma 8, `lem:teeth` = Lemma 9, `lem:index` = Lemma 10).

* **Lemma 8** (`lem:pk`).  (a) `lemma8a`: for every `m` and closed S-term `u`, `a_m u` has no
  hnf and its first stable frame is `a_{m+1} u (b_{m+1} u)`, i.e. `rest(a_m u) = a_{m+1} u` and
  `τ₁(a_m u) = b_{m+1} u`.  The hnf-less claim comes from S1's block model (`nohnf_am_apps`,
  M1a), the first stable frame from Lemma 4(B) with `k = 0` (`moves_B0`).  (b) is M1a's
  `nohnf_am_apps`, `nohnf_cam_apps`, `nohnf_Qav_apps`, restated as `lemma8b`.
* **Lemma 9** (`lem:teeth`).  The run of `p_K` in closed form: `restN_pK : restN n pK = am n ⬝ S`
  for every `n` (also `n = 0`, since `p_K = a_0 S` by definition), and `tooth_pK : tooth n pK =
  Y n` for `n ≥ 1`.  The teeth: `Y_n`, `x_n S`, `a_n x_n`, `a_n x_n S` have no hnf,
  `rest(Y_n) = x_n S`, `τ₁(Y_n) = a_n x_n S`, `rest(τ₁ Y_n) = a_n x_n`, `τ₁(τ₁ Y_n) = S`
  (`lemma9`), so Lemma 7(d) applies to every `t =β Y_n` and Lemma 7(c) to every `t =β τ₁(Y_n)`
  (`lemma9_suffix_Y`, `lemma9_suffix_tY`).  No move on these terms is exposed: each is `(A)` or
  `(B)` with `k = 0`.
* **Lemma 10** (`lem:index`).  `κ` as a relation `Kappa x k` ("`x·1^j` has an hnf for `j < k`
  and `x·1^k` has none"), which is functional (`kappa_unique`).  (a) `kappa_conv`,
  `kappa_conv_iff`; (b) `kappa_xm : Kappa (xm n) (im n + 1)`; (c) `im_of_conv`: if
  `τ₁(Y_n) =β τ₁(Y_{n'})`, then `i_n = i_{n'}`.  The index is read off any `t =β τ₁(Y_n)` by
  `κ(τ₁ τ₁ τ₁ (rest t))` (`index_read`).
* **The counter.**  `im` is non-decreasing (`im_mono`), unbounded (`im_unbounded`, with the
  constructive witness `st (m + j + 1) = (n, n+1)` from `st m = (j, n)`), and not eventually
  periodic (`im_not_periodic`, the form used by Lemma 18).
-/

namespace S11
open HnfS Conv

/-! ## Lemma 4(B) with `k = 0` -/

/-- **Lemma 4(B), `k = 0`.**  If `f⁻ ↠_h S a b` and `a u` has no hnf, then `f⁻ u` has no hnf,
`rest(f⁻ u) = a u` and `τ₁(f⁻ u) = b u`. -/
theorem moves_B0 {fm u a b : Term} (hf : PureS fm) (hu : PureS u) (h0 : Steps fm (S ⬝ a ⬝ b))
    (hn : ¬ HasHnf (a ⬝ u)) :
    ¬ HasHnf (fm ⬝ u) ∧ rest1 (fm ⬝ u) = a ⬝ u ∧ tooth1 (fm ⬝ u) = b ⬝ u := by
  have hs : Steps (fm ⬝ u) (a ⬝ u ⬝ (b ⬝ u)) := (steps_left h0 u).trans (.single (.S a b u))
  have hp : PureS (a ⬝ u ⬝ (b ⬝ u)) := InfNF.steps_pure (.app hf hu) hs
  have hn' : ¬ HasHnf (a ⬝ u ⬝ (b ⬝ u)) := nohnf_app hp.app_inv.1 hp.app_inv.2 hn
  have hfu : ¬ HasHnf (fm ⬝ u) := by
    refine (Conv.stable_iff (.app hf hu)).1 ?_
    rw [← Phi.steps_fold (.app hf hu) hs]
    exact (Conv.stable_iff hp).2 hn'
  obtain ⟨k, a', b', w', hc, h1, h2, h3⟩ := moves_B hf hu hfu h0
  cases hc with
  | zero => exact ⟨hfu, h2, h3⟩
  | succ hs' _ => exact absurd ⟨_, hs'.weak, .inr (.inr ⟨_, _, rfl⟩)⟩ hn

/-! ## Purity of the families -/

theorem pure_xm (m : Nat) : PureS (xm m) := .app (pure_c _) (pure_am m)

theorem pure_bm (m : Nat) : PureS (bm m) := .app (pure_c _) (pure_am m)

theorem pure_Y (m : Nat) : PureS (Y m) := .app (pure_bm m) .S

theorem bm_eq_cam (m : Nat) : bm m = c (st m).2 ⬝ am m := rfl

/-! ## Lemma 8 -/

/-- **Lemma 8(a).**  For every `m` and closed S-term `u`, `a_m u` has no hnf, and its first stable
frame is `a_{m+1} u (b_{m+1} u)`. -/
theorem lemma8a (m : Nat) {u : Term} (hu : PureS u) :
    ¬ HasHnf (am m ⬝ u) ∧ rest1 (am m ⬝ u) = am (m + 1) ⬝ u ∧
      tooth1 (am m ⬝ u) = bm (m + 1) ⬝ u :=
  moves_B0 (pure_am m) hu (run_am m)
    (nohnf_am_apps (m + 1) (Us := []) (fun V hV => by
      cases hV with
      | head => exact hu
      | tail _ h => cases h))

/-- **Lemma 8(a)**, as `Conv.FirstStable`. -/
theorem lemma8a_first (m : Nat) {u : Term} (hu : PureS u) :
    FirstStable (am m ⬝ u) (am (m + 1) ⬝ u) (bm (m + 1) ⬝ u) := by
  obtain ⟨hn, h1, h2⟩ := lemma8a m hu
  have h := first_stable_spec (.app (pure_am m) hu) hn
  rw [h1, h2] at h
  exact h

/-- **Lemma 8(b).**  For `r ≥ 1`, `a_m U⃗`, `c_j a_m U⃗` and `Q a_m (a_m (Q a_m)) U⃗` have no hnf
(closed S-terms `U_i`). -/
theorem lemma8b (j m : Nat) {U : Term} {Us : List Term} (hU : ∀ V ∈ U :: Us, PureS V) :
    ¬ HasHnf (apps (am m) (U :: Us)) ∧ ¬ HasHnf (apps (c j ⬝ am m) (U :: Us)) ∧
      ¬ HasHnf (apps (Q ⬝ am m ⬝ (am m ⬝ (Q ⬝ am m))) (U :: Us)) :=
  ⟨nohnf_am_apps m hU, nohnf_cam_apps j m hU, nohnf_Qav_apps m hU⟩

/-! ## Lemma 9: the run of `p_K` -/

/-- One closed S-term, as a list hypothesis. -/
theorem pure_one {u : Term} (hu : PureS u) : ∀ V ∈ [u], PureS V := by
  intro V hV
  cases hV with
  | head => exact hu
  | tail _ h => cases h

theorem pure_two {u v : Term} (hu : PureS u) (hv : PureS v) : ∀ V ∈ [u, v], PureS V := by
  intro V hV
  cases hV with
  | head => exact hu
  | tail _ h => exact pure_one hv V h

/-- **Lemma 9**, states: `rest^n(p_K) = a_n S` for every `n` (`p_K = a_0 S`). -/
theorem restN_pK : ∀ n, restN n pK = am n ⬝ S
  | 0 => rfl
  | n + 1 => by
    rw [restN_succ, restN_pK n]
    exact (lemma8a n .S).2.1

/-- **Lemma 9**, teeth: `τ_{n+1}(p_K) = Y_{n+1}`. -/
theorem tooth_pK_succ (n : Nat) : tooth (n + 1) pK = Y (n + 1) := by
  rw [tooth_succ, restN_pK n]
  exact (lemma8a n .S).2.2

/-- **Lemma 9**, teeth: `τ_n(p_K) = Y_n` for `n ≥ 1`. -/
theorem tooth_pK {n : Nat} (hn : 1 ≤ n) : tooth n pK = Y n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact tooth_pK_succ k

theorem pure_pK : PureS pK := .app (pure_am 0) .S

/-- `p_K` has no hnf. -/
theorem nohnf_pK : ¬ HasHnf pK := (lemma8a 0 .S).1

/-- **Lemma 9**, the teeth `Y_n` (for every `n`; the paper needs `n ≥ 1`): `Y_n`, `x_n S`,
`a_n x_n`, `a_n x_n S` have no hnf; `rest(Y_n) = x_n S`, `τ₁(Y_n) = a_n x_n S`,
`rest(τ₁ Y_n) = a_n x_n`, `τ₁(τ₁ Y_n) = S`. -/
theorem lemma9 (n : Nat) :
    ¬ HasHnf (Y n) ∧ ¬ HasHnf (xm n ⬝ S) ∧ ¬ HasHnf (am n ⬝ xm n) ∧
      ¬ HasHnf (am n ⬝ xm n ⬝ S) ∧
      rest1 (Y n) = xm n ⬝ S ∧ tooth1 (Y n) = am n ⬝ xm n ⬝ S ∧
      rest1 (tooth1 (Y n)) = am n ⬝ xm n ∧ tooth1 (tooth1 (Y n)) = S := by
  have hY : ¬ HasHnf (Y n) := nohnf_cam_apps _ n (Us := []) (pure_one .S)
  have hxS : ¬ HasHnf (xm n ⬝ S) := nohnf_cam_apps _ n (Us := []) (pure_one .S)
  have hax : ¬ HasHnf (am n ⬝ xm n) := nohnf_am_apps n (Us := []) (pure_one (pure_xm n))
  have haxS : ¬ HasHnf (am n ⬝ xm n ⬝ S) :=
    nohnf_am_apps n (Us := [S]) (pure_two (pure_xm n) .S)
  obtain ⟨-, h1, h2⟩ := moves_B0 (pure_bm n) .S (run_bm n) hxS
  have hY1 : tooth1 (Y n) = am n ⬝ xm n ⬝ S := h2
  obtain ⟨h3, h4⟩ := moves_A (.app (pure_am n) (pure_xm n)) .S hax
  refine ⟨hY, hxS, hax, haxS, h1, hY1, ?_, ?_⟩
  · rw [hY1]; exact h3
  · rw [hY1]; exact h4

/-- **Lemma 9**: Lemma 7(d) applies to every `t =β Y_n`. -/
theorem lemma9_suffix_Y (n : Nat) {t : Term} (ht : PureS t) (hc : Convertible t (Y n)) {d : Nat}
    {e : Term} (h : RSuf d e t) (hd : 1 ≤ d) :
    e = S ∨ (d = 1 ∧ Convertible e (tooth1 (Y n))) := by
  obtain ⟨hY, -, -, haxS, -, hY1, -, hY2⟩ := lemma9 n
  exact lemma7d ht (pure_Y n) hc hY (by rw [hY1]; exact haxS) hY2 h hd

/-- **Lemma 9**: Lemma 7(c) applies to every `t =β τ₁(Y_n)`. -/
theorem lemma9_suffix_tY (n : Nat) {t : Term} (ht : PureS t)
    (hc : Convertible t (tooth1 (Y n))) {d : Nat} {e : Term} (h : RSuf d e t) (hd : 1 ≤ d) :
    e = S := by
  obtain ⟨hY, -, -, haxS, -, hY1, -, hY2⟩ := lemma9 n
  have hp : PureS (tooth1 (Y n)) := tooth1_pure (pure_Y n) hY
  exact lemma7c ht hp hc (by rw [hY1]; exact haxS) hY2 h hd

/-! ## Lemma 10: the index `κ` -/

/-- `Dot1 x y`: `x` has an hnf `S u₁ ⋯ u_m` with `m ≥ 1` and `u₁ = y` (the paper's `x·1 = y`). -/
def Dot1 (x y : Term) : Prop := Steps x (S ⬝ y) ∨ ∃ z, Steps x (S ⬝ y ⬝ z)

/-- `Kappa x k`: `x·1^j` is defined for `j ≤ k`, has an hnf for `j < k`, and `x·1^k` (closed)
has none; i.e. the paper's `κ(x) = k`. -/
inductive Kappa : Term → Nat → Prop
  | zero {x : Term} : PureS x → ¬ HasHnf x → Kappa x 0
  | succ {x y : Term} {k : Nat} : Dot1 x y → Kappa y k → Kappa x (k + 1)

theorem dot1_hasHnf {x y : Term} (h : Dot1 x y) : HasHnf x := by
  rcases h with h | ⟨z, h⟩
  · exact ⟨_, h.weak, .inr (.inl ⟨y, rfl⟩)⟩
  · exact ⟨_, h.weak, .inr (.inr ⟨y, z, rfl⟩)⟩

/-- `x·1` is unique. -/
theorem dot1_unique {x y y' : Term} (h : Dot1 x y) (h' : Dot1 x y') : y = y' := by
  have key : ∀ {X X' : Term}, IsHnf X → IsHnf X' → Steps x X → Steps x X' → X = X' :=
    fun hX hX' s s' => Phi.hnf_unique s hX s' hX'
  rcases h with h | ⟨z, h⟩ <;> rcases h' with h' | ⟨z', h'⟩
  · have e := key (.inr (.inl ⟨_, rfl⟩)) (.inr (.inl ⟨_, rfl⟩)) h h'
    injection e
  · have e := key (.inr (.inl ⟨_, rfl⟩)) (.inr (.inr ⟨_, _, rfl⟩)) h h'
    injection e with e1 e2
    cases e1
  · have e := key (.inr (.inr ⟨_, _, rfl⟩)) (.inr (.inl ⟨_, rfl⟩)) h h'
    injection e with e1 e2
    cases e1
  · have e := key (.inr (.inr ⟨_, _, rfl⟩)) (.inr (.inr ⟨_, _, rfl⟩)) h h'
    injection e with e1 _
    injection e1

/-- `κ` is a function. -/
theorem kappa_unique {x : Term} {k k' : Nat} (h : Kappa x k) (h' : Kappa x k') : k = k' := by
  induction h generalizing k' with
  | zero _ hn =>
    cases h' with
    | zero => rfl
    | succ hd _ => exact absurd (dot1_hasHnf hd) hn
  | succ hd _ ih =>
    cases h' with
    | zero _ hn => exact absurd (dot1_hasHnf hd) hn
    | succ hd' hk' =>
      have e := dot1_unique hd hd'
      subst e
      rw [ih hk']

/-- **Lemma 10(a).**  If `x =β x'` (closed S-terms) and `κ(x) = k`, then `κ(x') = k`. -/
theorem kappa_conv {x x' : Term} {k : Nat} (h : Kappa x k) (hx : PureS x) (hx' : PureS x')
    (hc : Convertible x x') : Kappa x' k := by
  induction h generalizing x' with
  | zero _ hn => exact .zero hx' (inv_nohnf hx hx' hc hn)
  | @succ x y k hd _ ih =>
    rcases hd with h1 | ⟨z, h2⟩
    · obtain ⟨y', s', hy⟩ := inv_hnf1 hx hx' hc h1
      have hy0 : PureS y := (InfNF.steps_pure hx h1).app_inv.2
      have hy1 : PureS y' := (InfNF.steps_pure hx' s').app_inv.2
      exact .succ (.inl s') (ih hy0 hy1 hy)
    · obtain ⟨y', z', s', hy, _⟩ := inv_hnf2 hx hx' hc h2
      have hy0 : PureS y := (InfNF.steps_pure hx h2).app_inv.1.app_inv.2
      have hy1 : PureS y' := (InfNF.steps_pure hx' s').app_inv.1.app_inv.2
      exact .succ (.inr ⟨z', s'⟩) (ih hy0 hy1 hy)

/-- **Lemma 10(a)**, both sides defined or not. -/
theorem kappa_conv_iff {x x' : Term} {k : Nat} (hx : PureS x) (hx' : PureS x')
    (hc : Convertible x x') : Kappa x k ↔ Kappa x' k :=
  ⟨fun h => kappa_conv h hx hx' hc, fun h => kappa_conv h hx' hx hc.symm⟩

/-- `κ(c_j a_m) = j + 1`. -/
theorem kappa_cam (m : Nat) : ∀ j, Kappa (c j ⬝ am m) (j + 1)
  | 0 =>
    .succ (.inr ⟨_, run_G (am m)⟩) (.zero (.app (pure_am m) (.app pure_Q (pure_am m)))
      (nohnf_vm m))
  | j + 1 => .succ (.inr ⟨_, run_Q (c j) (am m)⟩) (kappa_cam m j)

/-- **Lemma 10(b).**  `κ(x_n) = i_n + 1`. -/
theorem kappa_xm (n : Nat) : Kappa (xm n) (im n + 1) := kappa_cam n (im n)

/-- `τ₁(a_n x_n) = b_{n+1} x_n`, `τ₁(b_{n+1} x_n) = a_{n+1} x_{n+1} x_n`, `τ₁` of that is `x_n`;
all three terms have no hnf. -/
theorem teeth_chain (n : Nat) :
    ¬ HasHnf (am n ⬝ xm n) ∧ tooth1 (am n ⬝ xm n) = bm (n + 1) ⬝ xm n ∧
      ¬ HasHnf (bm (n + 1) ⬝ xm n) ∧
      tooth1 (bm (n + 1) ⬝ xm n) = am (n + 1) ⬝ xm (n + 1) ⬝ xm n ∧
      ¬ HasHnf (am (n + 1) ⬝ xm (n + 1) ⬝ xm n) ∧
      tooth1 (am (n + 1) ⬝ xm (n + 1) ⬝ xm n) = xm n := by
  obtain ⟨h1, -, h2⟩ := lemma8a n (pure_xm n)
  have hxx : ¬ HasHnf (xm (n + 1) ⬝ xm n) :=
    nohnf_cam_apps _ (n + 1) (Us := []) (pure_one (pure_xm n))
  obtain ⟨h3, -, h4⟩ := moves_B0 (pure_bm (n + 1)) (pure_xm n) (run_bm (n + 1)) hxx
  have hax : ¬ HasHnf (am (n + 1) ⬝ xm (n + 1)) :=
    nohnf_am_apps (n + 1) (Us := []) (pure_one (pure_xm (n + 1)))
  have h5 : ¬ HasHnf (am (n + 1) ⬝ xm (n + 1) ⬝ xm n) :=
    nohnf_am_apps (n + 1) (Us := [xm n]) (pure_two (pure_xm (n + 1)) (pure_xm n))
  exact ⟨h1, h2, h3, h4, h5, (moves_A (.app (pure_am _) (pure_xm _)) (pure_xm n) hax).2⟩

/-- `x_n = τ₁ τ₁ τ₁ (rest (τ₁ Y_n))`. -/
theorem xm_read (n : Nat) : tooth1 (tooth1 (tooth1 (rest1 (tooth1 (Y n))))) = xm n := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := lemma9 n
  obtain ⟨-, h1, -, h2, -, h3⟩ := teeth_chain n
  rw [h, h1, h2, h3]

/-- **The index is read off the teeth.**  For every closed S-term `t =β τ₁(Y_n)`,
`κ(τ₁ τ₁ τ₁ (rest t)) = i_n + 1`. -/
theorem index_read (n : Nat) {t : Term} (ht : PureS t) (hc : Convertible (tooth1 (Y n)) t) :
    Kappa (tooth1 (tooth1 (tooth1 (rest1 t)))) (im n + 1) := by
  obtain ⟨hY, -, -, haxS, -, hY1, hr, -⟩ := lemma9 n
  obtain ⟨hax, h1, hbx, h2, haxx, h3⟩ := teeth_chain n
  have p0 : PureS (tooth1 (Y n)) := tooth1_pure (pure_Y n) hY
  have n0 : ¬ HasHnf (tooth1 (Y n)) := by rw [hY1]; exact haxS
  -- step 1: rest
  obtain ⟨n0', -, c1⟩ := inv_first p0 ht hc n0
  have p1 : PureS (rest1 (tooth1 (Y n))) := rest1_pure p0 n0
  have p1' : PureS (rest1 t) := rest1_pure ht n0'
  have n1 : ¬ HasHnf (rest1 (tooth1 (Y n))) := by rw [hr]; exact hax
  -- step 2: τ₁
  obtain ⟨n1', c2, -⟩ := inv_first p1 p1' c1 n1
  have p2 : PureS (tooth1 (rest1 (tooth1 (Y n)))) := tooth1_pure p1 n1
  have p2' : PureS (tooth1 (rest1 t)) := tooth1_pure p1' n1'
  have n2 : ¬ HasHnf (tooth1 (rest1 (tooth1 (Y n)))) := by rw [hr, h1]; exact hbx
  -- step 3: τ₁
  obtain ⟨n2', c3, -⟩ := inv_first p2 p2' c2 n2
  have p3 : PureS (tooth1 (tooth1 (rest1 (tooth1 (Y n))))) := tooth1_pure p2 n2
  have p3' : PureS (tooth1 (tooth1 (rest1 t))) := tooth1_pure p2' n2'
  have n3 : ¬ HasHnf (tooth1 (tooth1 (rest1 (tooth1 (Y n))))) := by rw [hr, h1, h2]; exact haxx
  -- step 4: τ₁
  obtain ⟨n3', c4, -⟩ := inv_first p3 p3' c3 n3
  have p4' : PureS (tooth1 (tooth1 (tooth1 (rest1 t)))) := tooth1_pure p3' n3'
  rw [xm_read n] at c4
  exact kappa_conv (kappa_xm n) (pure_xm n) p4' c4

/-- **Lemma 10(c).**  If `τ₁(Y_n) =β τ₁(Y_{n'})`, then `i_n = i_{n'}`. -/
theorem im_of_conv {n n' : Nat} (hc : Convertible (tooth1 (Y n)) (tooth1 (Y n'))) :
    im n = im n' := by
  have hY' := (lemma9 n').1
  have h := index_read n (tooth1_pure (pure_Y n') hY') hc
  rw [xm_read n'] at h
  have e := kappa_unique h (kappa_xm n')
  omega

/-! ## The counter `i_m`: monotone, unbounded, not eventually periodic -/

theorem st_snd_le_succ (m : Nat) : (st m).2 ≤ (st (m + 1)).2 := by
  rw [st_succ]
  rcases st m with ⟨i, n⟩
  cases i with
  | zero => exact Nat.le_succ n
  | succ j => exact Nat.le_refl n

/-- The second index never decreases. -/
theorem st_snd_mono {m m' : Nat} (h : m ≤ m') : (st m).2 ≤ (st m').2 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (st_snd_le_succ _)

/-- `i_m` is non-decreasing. -/
theorem im_mono {m m' : Nat} (h : m ≤ m') : im m ≤ im m' := by
  have := st_snd_mono h
  unfold im; omega

/-- From the state `(j, n)` the first index counts down to `0` in `j` steps. -/
theorem st_down : ∀ (j : Nat) {m n : Nat}, st m = (j, n) → st (m + j) = (0, n)
  | 0, _, _, h => h
  | j + 1, m, n, h => by
    have h1 := st_succ_q h
    have := st_down j h1
    rw [show m + (j + 1) = m + 1 + j by omega]
    exact this

/-- From the state `(j, n)`, the state `(n, n + 1)` is reached after `j + 1` steps: the second
index grows. -/
theorem st_grow {j m n : Nat} (h : st m = (j, n)) : st (m + j + 1) = (n, n + 1) :=
  st_succ_g (st_down j h)

/-- The second index is unbounded, with an explicit witness. -/
theorem st_unbounded : ∀ N, ∃ m, N ≤ (st m).2
  | 0 => ⟨0, Nat.zero_le _⟩
  | N + 1 => by
    obtain ⟨m, hm⟩ := st_unbounded N
    rcases hs : st m with ⟨j, n⟩
    rw [hs] at hm
    refine ⟨m + j + 1, ?_⟩
    rw [st_grow hs]
    exact Nat.succ_le_succ hm

/-- **`i_m` is unbounded.** -/
theorem im_unbounded (N : Nat) : ∃ m, N ≤ im m := by
  obtain ⟨m, hm⟩ := st_unbounded (N + 1)
  exact ⟨m, by unfold im; omega⟩

/-- `i_m` is eventually above every bound. -/
theorem im_unbounded' (N : Nat) : ∃ m, ∀ m', m ≤ m' → N ≤ im m' := by
  obtain ⟨m, hm⟩ := im_unbounded N
  exact ⟨m, fun m' h => Nat.le_trans hm (im_mono h)⟩

/-- **`i_m` is not eventually periodic**: if `i_{m+j} = i_{m+p+j}` for all `j ≥ 1`, then
`p = 0`. -/
theorem im_not_periodic {m p : Nat} (hp : 1 ≤ p)
    (h : ∀ j, 1 ≤ j → im (m + j) = im (m + p + j)) : False := by
  have hs : ∀ s, im (m + 1 + p * s) = im (m + 1) := by
    intro s
    induction s with
    | zero => rw [Nat.mul_zero, Nat.add_zero]
    | succ s ih =>
      have e : m + 1 + p * (s + 1) = m + p + (1 + p * s) := by
        rw [Nat.mul_succ]; generalize p * s = q; omega
      have e' : m + 1 + p * s = m + (1 + p * s) := by generalize p * s = q; omega
      rw [e, ← h (1 + p * s) (by omega), ← e', ih]
  obtain ⟨m₀, hm₀⟩ := im_unbounded' (im (m + 1) + 1)
  have h1 := hm₀ (m + 1 + m₀) (by omega)
  have h2 : im (m + 1 + m₀) ≤ im (m + 1 + p * m₀) :=
    im_mono (Nat.add_le_add_left (Nat.le_mul_of_pos_left m₀ hp) _)
  rw [hs] at h2
  omega

/-- The form used by Lemma 18: if `i_{m+j} = i_{k+j}` for all `j ≥ 1`, then `m = k`. -/
theorem im_shift_inj {m k : Nat} (h : ∀ j, 1 ≤ j → im (m + j) = im (k + j)) : m = k := by
  rcases Nat.lt_trichotomy m k with hlt | heq | hgt
  · exfalso
    refine im_not_periodic (m := m) (p := k - m) (by omega) (fun j hj => ?_)
    rw [show m + (k - m) = k by omega]
    exact h j hj
  · exact heq
  · exfalso
    refine im_not_periodic (m := k) (p := m - k) (by omega) (fun j hj => ?_)
    rw [show k + (m - k) = m by omega]
    exact (h j hj).symm

end S11
