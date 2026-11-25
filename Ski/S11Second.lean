import Ski.S11Run
import Ski.S11Closure

open Term

/-!
# S11: runs with the teeth of `p_K`; Lemmas 11, 12, 13

Paper S11, *An S-Term Determined by Its Teeth Among Terms Without a Head Normal Form*, §4.
Milestone M4 of the plan `notes/S11-MECH-PLAN.md`.  Lemma numbers follow the compiled paper
(`lem:srun` = Lemma 11, `lem:cancel` = Lemma 12, `lem:left` = Lemma 13).

Throughout, `q` is a closed S-term without an hnf whose teeth are those of `p_K`:
`τ_n(q) =β Y_n` for every `n ≥ 1` (hypothesis `hY`; `tooth_pK` turns it into `τ_n(q) =β τ_n(p_K)`).

* **The run of `q`, explicitly.**  `aq q n = a′_n` is the function part of `rest^n(q)` and
  `bq q n = b′_n` the function part of `τ_n(q)` (`lhs`).  Both are functions of `n`, so a spine
  predicate `P j s := (s = aq q (n₀ + j))` is available to Lemma 15(c) (`srun_spine`).
* **The moves of `q`.**  `moveY` classifies a move whose tooth is `=β Y_m`: kind (A); kind (B)
  with `k = 0` and `u = S`; or the "second case" (`w_k =β τ₁(Y_m)`).  `bad_step` and
  `bad_forever` propagate the second case to every later move, and `no_bad` refutes it through
  Lemma 10(c) (`im_of_conv`) and the unboundedness of `i` (`im_unbounded`).  `move_q`: every move
  of `q` is of kind (A), or of kind (B) in the form of Lemma 11 (`KindB`).
* **Lemma 11** (`lem:srun`).  `exists_kindB` finds a move of kind (B) by strong induction on
  `HeadRec.sz (rest^n q)` (a move of kind (A) shrinks the state), `kindB_succ` shows that every
  later move is again of kind (B), `srun` packages this, and `lemma11` is the paper's statement.
  No choice: every case split is `decHasHnf` (inside `lemma4`) or a Prop-valued `Or`.
* **Lemma 12** (`lem:cancel`).  `lemma12a`, `lemma12b`.
* **Lemma 13** (`lem:left`).  `cancel_cam` (the inner induction peeling `c_{i−k}`, with the
  `G a` and `Q a v` steps), `lemma13_core` (`b′ S =β Y_n ⟹ b′ =β b_n`), `lemma13`, and the
  package `second_run` for M5.
-/

namespace S11
open HnfS Conv

/-! ## Small facts -/

/-- The function part of an application (`S` otherwise). -/
def lhs : Term → Term
  | .app f _ => f
  | _ => S

theorem hasHnf_S : HasHnf S := ⟨S, .refl S, .inl rfl⟩

/-- A closed S-application is not convertible with `S`. -/
theorem app_not_conv_S {f x : Term} (h : PureS (f ⬝ x)) (hc : Convertible (f ⬝ x) S) : False := by
  have e := conv_S h hc
  cases e

/-- For M5's Lemma 18: `x_m =β x_k` implies `i_m = i_k` (Lemma 10(a), (b) and `κ` functional). -/
theorem im_eq_of_xm_conv {m k : Nat} (hc : Convertible (xm m) (xm k)) : im m = im k := by
  have h := kappa_conv (kappa_xm m) (pure_xm m) (pure_xm k) hc
  have e := kappa_unique h (kappa_xm k)
  omega

/-- A chain of length `0` is trivial. -/
theorem chain_zero {a b w a' b' w' : Term} (h : Chain a b w 0 a' b' w') :
    a' = a ∧ b' = b ∧ w' = w := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-! ## Lemma 12: S-cancellation -/

/-- **Lemma 12(a).**  If `t` has no hnf and `e S =β t S`, then `e =β t`. -/
theorem lemma12a {e t : Term} (he : PureS e) (ht : PureS t) (hn : ¬ HasHnf t)
    (hc : Convertible (e ⬝ S) (t ⬝ S)) : Convertible e t := by
  obtain ⟨hr, hτ⟩ := moves_A ht .S hn
  have hpe : PureS (e ⬝ S) := .app he .S
  have hnt : ¬ HasHnf (t ⬝ S) := nohnf_app ht .S hn
  have hne : ¬ HasHnf (e ⬝ S) := inv_nohnf (.app ht .S) hpe hc.symm hnt
  obtain ⟨-, c1, c2⟩ := inv_first hpe (.app ht .S) hc hne
  cases decHasHnf he with
  | isFalse h =>
    rw [(moves_A he .S h).1, hr] at c2
    exact c2
  | isTrue h =>
    exfalso
    obtain ⟨a₀, b₀, h0⟩ := two_item he h hne
    obtain ⟨k, a, b, w, -, -, -, h3⟩ := moves_B he .S hne h0
    have hp := tooth1_pure hpe hne
    rw [h3] at hp c1
    rw [hτ] at c1
    exact app_not_conv_S hp c1

/-- **Lemma 12(b).**  Let `h ↠_h S u v`, where `u S` has no hnf and `u` or `v` has no hnf.  If
`e S =β h S`, then `e ↠_h S e₁ e₂` with `e₁ S =β u S` and `e₂ S =β v S`. -/
theorem lemma12b {e h u v : Term} (he : PureS e) (hh : PureS h) (hs : Steps h (S ⬝ u ⬝ v))
    (hnu : ¬ HasHnf (u ⬝ S)) (huv : ¬ HasHnf u ∨ ¬ HasHnf v)
    (hc : Convertible (e ⬝ S) (h ⬝ S)) :
    ∃ e₁ e₂, Steps e (S ⬝ e₁ ⬝ e₂) ∧ Convertible (e₁ ⬝ S) (u ⬝ S) ∧
      Convertible (e₂ ⬝ S) (v ⬝ S) := by
  obtain ⟨hnh, hr, hτ⟩ := moves_B0 hh .S hs hnu
  have hpuv := InfNF.steps_pure hh hs
  have hu : PureS u := hpuv.app_inv.1.app_inv.2
  have hv : PureS v := hpuv.app_inv.2
  have hpe : PureS (e ⬝ S) := .app he .S
  have hph : PureS (h ⬝ S) := .app hh .S
  have hne : ¬ HasHnf (e ⬝ S) := inv_nohnf hph hpe hc.symm hnh
  obtain ⟨-, c1, c2⟩ := inv_first hpe hph hc hne
  rw [hr] at c2
  rw [hτ] at c1
  cases decHasHnf he with
  | isFalse h0 =>
    exfalso
    rw [(moves_A he .S h0).2] at c1
    exact app_not_conv_S (.app hv .S) c1.symm
  | isTrue h0 =>
    obtain ⟨e₁, e₂, h1⟩ := two_item he h0 hne
    obtain ⟨k, a, b, w, hch, hnaw, h3, h4⟩ := moves_B he .S hne h1
    cases k with
    | zero =>
      obtain ⟨ea, eb, ew⟩ := chain_zero hch
      rw [h3, ea, ew] at c2
      rw [h4, eb, ew] at c1
      exact ⟨e₁, e₂, h1, c2, c1⟩
    | succ k =>
      exfalso
      rcases huv with hu0 | hv0
      · -- `rest(e S) = a_k w_k =β u S`, whose `τ₁` is `S`; but `τ₁(a_k w_k)` is an application.
        have hpaw : PureS (a ⬝ w) := by
          have := rest1_pure hpe hne
          rw [h3] at this
          exact this
        rw [h3] at c2
        obtain ⟨-, c3, -⟩ := inv_first hpaw (.app hu .S) c2 hnaw
        rw [(moves_A hu .S hu0).2] at c3
        rcases lemma4 hpaw.app_inv.1 hpaw.app_inv.2 hnaw with
          ⟨-, -, hτ'⟩ | ⟨-, -, -, k', a', b', w', -, -, -, hτ'⟩
        · rw [hτ'] at c3
          rcases chain_last hch with ⟨hk, -⟩ | ⟨x, y, hxy⟩
          · exact Nat.succ_ne_zero _ hk
          · subst hxy
            exact app_not_conv_S hpaw.app_inv.2 c3
        · have hp := tooth1_pure hpaw hnaw
          rw [hτ'] at c3 hp
          exact app_not_conv_S hp c3
      · -- `τ₁(v S) = S`, and the application `w₁ = e₂ S` is a right suffix of `τ₁(e S)`.
        have hpt := tooth1_pure hpe hne
        have hs : RSuf (k + 1) (e₂ ⬝ S) (tooth1 (e ⬝ S)) := by
          rw [h4]; exact chain_rsuf_w1 hch
        have e' := lemma7c hpt (.app hv .S) c1 (nohnf_app hv .S hv0) (moves_A hv .S hv0).2 hs
          (Nat.succ_pos k)
        cases e'

/-! ## Lemma 13: the left parts `b′_n` -/

/-- The inner induction of Lemma 13: `e S =β c_j a_m S` implies `e =β c_j a_m`. -/
theorem cancel_cam (m : Nat) : ∀ (j : Nat) {e : Term}, PureS e →
    Convertible (e ⬝ S) (c j ⬝ am m ⬝ S) → Convertible e (c j ⬝ am m)
  | 0, e, he, hc => by
    have pa := pure_am m
    have pQa : PureS (Q ⬝ am m) := .app pure_Q pa
    have pv : PureS (vm m) := .app pa pQa
    have pav : PureS (am m ⬝ vm m) := .app pa pv
    have pQav : PureS (Q ⬝ am m ⬝ vm m) := .app (.app pure_Q pa) pv
    have nvS : ¬ HasHnf (vm m ⬝ S) := nohnf_am_apps m (Us := [S]) (pure_two pQa .S)
    obtain ⟨ζ, η, h1, cζ, cη⟩ := lemma12b (h := G ⬝ am m) (u := vm m)
      (v := Q ⬝ am m ⬝ vm m) he (.app pure_G pa) (run_G (am m)) nvS (.inl (nohnf_vm m)) hc
    have p1 := InfNF.steps_pure he h1
    have cζ' : Convertible ζ (vm m) := lemma12a p1.app_inv.1.app_inv.2 pv (nohnf_vm m) cζ
    have nav : ¬ HasHnf (am m ⬝ vm m) := nohnf_am_apps m (Us := []) (pure_one pv)
    have navS : ¬ HasHnf (am m ⬝ vm m ⬝ S) := nohnf_am_apps m (Us := [S]) (pure_two pv .S)
    obtain ⟨η₁, η₂, h2, c1, c2⟩ := lemma12b (h := Q ⬝ am m ⬝ vm m) (u := am m ⬝ vm m)
      (v := vm m ⬝ (am m ⬝ vm m)) p1.app_inv.2 pQav (run_Q (am m) (vm m)) navS (.inl nav) cη
    have p2 := InfNF.steps_pure p1.app_inv.2 h2
    have c1' : Convertible η₁ (am m ⬝ vm m) := lemma12a p2.app_inv.1.app_inv.2 pav nav c1
    have nvav : ¬ HasHnf (vm m ⬝ (am m ⬝ vm m)) := nohnf_app pv pav (nohnf_vm m)
    have c2' : Convertible η₂ (vm m ⬝ (am m ⬝ vm m)) :=
      lemma12a p2.app_inv.2 (.app pv pav) nvav c2
    have cη' : Convertible η (Q ⬝ am m ⬝ vm m) :=
      (Convertible.of_wsteps h2.weak).trans ((conv_app (conv_appR S c1') c2').trans
        (Convertible.of_wsteps (run_Q (am m) (vm m)).weak).symm)
    exact (Convertible.of_wsteps h1.weak).trans ((conv_app (conv_appR S cζ') cη').trans
      (Convertible.of_wsteps (run_G (am m)).weak).symm)
  | j + 1, e, he, hc => by
    have pa := pure_am m
    have pca : PureS (c j ⬝ am m) := .app (pure_c j) pa
    have nu : ¬ HasHnf (c j ⬝ am m ⬝ S) := nohnf_cam_apps j m (Us := []) (pure_one .S)
    have nv : ¬ HasHnf (am m ⬝ (c j ⬝ am m)) := nohnf_am_apps m (Us := []) (pure_one pca)
    obtain ⟨e₁, e₂, h1, c1, c2⟩ := lemma12b (h := Q ⬝ c j ⬝ am m) (u := c j ⬝ am m)
      (v := am m ⬝ (c j ⬝ am m)) he (.app (.app pure_Q (pure_c j)) pa) (run_Q (c j) (am m))
      nu (.inr nv) hc
    have p1 := InfNF.steps_pure he h1
    have c1' : Convertible e₁ (c j ⬝ am m) := cancel_cam m j p1.app_inv.1.app_inv.2 c1
    have c2' : Convertible e₂ (am m ⬝ (c j ⬝ am m)) := lemma12a p1.app_inv.2 (.app pa pca) nv c2
    exact (Convertible.of_wsteps h1.weak).trans ((conv_app (conv_appR S c1') c2').trans
      (Convertible.of_wsteps (run_Q (c j) (am m)).weak).symm)

/-- **Lemma 13**, for one tooth: if `b′ S =β Y_n`, then `b′ =β b_n`. -/
theorem lemma13_core (n : Nat) {b' : Term} (hb : PureS b') (hc : Convertible (b' ⬝ S) (Y n)) :
    Convertible b' (bm n) := by
  obtain ⟨hY, -, hax, haxS, hr, hτ, -, -⟩ := lemma9 n
  have hpb : PureS (b' ⬝ S) := .app hb .S
  have hnb : ¬ HasHnf (b' ⬝ S) := inv_nohnf (pure_Y n) hpb hc.symm hY
  obtain ⟨-, c1, c2⟩ := inv_first hpb (pure_Y n) hc hnb
  have hp1 : PureS (tooth1 (b' ⬝ S)) := tooth1_pure hpb hnb
  cases decHasHnf hb with
  | isFalse h0 =>
    exfalso
    rw [(moves_A hb .S h0).2, hτ] at c1
    exact inv_nohnf (.app (.app (pure_am n) (pure_xm n)) .S) .S c1.symm haxS hasHnf_S
  | isTrue h0 =>
    obtain ⟨α, β, h1⟩ := two_item hb h0 hnb
    obtain ⟨k, a, b, w, hch, -, h3, h4⟩ := moves_B hb .S hnb h1
    cases k with
    | succ k =>
      exfalso
      have hs : RSuf 1 w (tooth1 (b' ⬝ S)) := by rw [h4]; exact .app b (.zero w)
      have hwS := lemma9_suffix_tY n hp1 c1 hs (Nat.le_refl 1)
      rcases chain_last hch with ⟨hk, -⟩ | ⟨x, y, hxy⟩
      · exact Nat.succ_ne_zero _ hk
      · rw [hxy] at hwS
        cases hwS
    | zero =>
      obtain ⟨ea, eb, ew⟩ := chain_zero hch
      rw [h3, hr, ea, ew] at c2
      rw [h4, hτ, eb, ew] at c1
      have p1 := InfNF.steps_pure hb h1
      have cβ : Convertible β (am n ⬝ xm n) :=
        lemma12a p1.app_inv.2 (.app (pure_am n) (pure_xm n)) hax c1
      have cα : Convertible α (xm n) := cancel_cam n (im n) p1.app_inv.1.app_inv.2 c2
      exact (Convertible.of_wsteps h1.weak).trans ((conv_app (conv_appR S cα) cβ).trans
        (Convertible.of_wsteps (run_bm n).weak).symm)

/-! ## The moves of a term with the teeth of `p_K` -/

/-- **A move whose tooth is `=β Y_m`.**  It is of kind (A); or of kind (B) with `k = 0` and
`u = S`; or of kind (B) with last argument `w_k =β τ₁(Y_m)` (the paper's "second case"). -/
theorem moveY (m : Nat) {fm u : Term} (hf : PureS fm) (hu : PureS u) (hn : ¬ HasHnf (fm ⬝ u))
    (hc : Convertible (tooth1 (fm ⬝ u)) (Y m)) :
    (¬ HasHnf fm ∧ rest1 (fm ⬝ u) = fm ∧ tooth1 (fm ⬝ u) = u) ∨
    (u = S ∧ ∃ a b, Steps fm (S ⬝ a ⬝ b) ∧ rest1 (fm ⬝ u) = a ⬝ S ∧
      tooth1 (fm ⬝ u) = b ⬝ S) ∨
    (∃ a w, rest1 (fm ⬝ u) = a ⬝ w ∧ Convertible w (tooth1 (Y m))) := by
  rcases lemma4 hf hu hn with hA | ⟨a₀, b₀, h0, k, a, b, w, hch, -, hr, hτ⟩
  · exact .inl hA
  · have hpt : PureS (tooth1 (fm ⬝ u)) := tooth1_pure (.app hf hu) hn
    have hs : RSuf 1 w (tooth1 (fm ⬝ u)) := by rw [hτ]; exact .app b (.zero w)
    rcases lemma9_suffix_Y m hpt hc hs (Nat.le_refl 1) with hw | ⟨-, hw⟩
    · cases k with
      | zero =>
        obtain ⟨ea, eb, ew⟩ := chain_zero hch
        rw [ea, ew] at hr
        rw [eb, ew] at hτ
        rw [ew] at hw
        subst hw
        exact .inr (.inl ⟨rfl, a₀, b₀, h0, hr, hτ⟩)
      | succ k =>
        exfalso
        rcases chain_last hch with ⟨hk, -⟩ | ⟨x, y, hxy⟩
        · exact Nat.succ_ne_zero _ hk
        · rw [hxy] at hw
          cases hw
    · exact .inr (.inr ⟨a, w, hr, hw⟩)

/-- **The second case propagates.**  If the state is `f⁻ w` with `w =β τ₁(Y_m)` and the next
tooth is `=β Y_{m+1}`, then the next state is `a w` (the move is of kind (B) with `k = 0` and
`u = w`) and `w =β τ₁(Y_{m+1})`. -/
theorem bad_step (m : Nat) {fm w : Term} (hf : PureS fm) (hw : PureS w) (hn : ¬ HasHnf (fm ⬝ w))
    (h2 : Convertible w (tooth1 (Y m))) (hc : Convertible (tooth1 (fm ⬝ w)) (Y (m + 1))) :
    ∃ a, rest1 (fm ⬝ w) = a ⬝ w ∧ Convertible w (tooth1 (Y (m + 1))) := by
  obtain ⟨hY, -, -, haxS, -, hY1, -, hY2⟩ := lemma9 m
  obtain ⟨hY', -, -, haxS', -, hY1', -, -⟩ := lemma9 (m + 1)
  have p1 : PureS (tooth1 (Y m)) := tooth1_pure (pure_Y m) hY
  have n1 : ¬ HasHnf (tooth1 (Y m)) := by rw [hY1]; exact haxS
  have p1' : PureS (tooth1 (Y (m + 1))) := tooth1_pure (pure_Y _) hY'
  have n1' : ¬ HasHnf (tooth1 (Y (m + 1))) := by rw [hY1']; exact haxS'
  have hnw : ¬ HasHnf w := inv_nohnf p1 hw h2.symm n1
  rcases lemma4 hf hw hn with ⟨-, -, hτ⟩ | ⟨a₀, b₀, h0, k, a, b, w', hch, -, hr, hτ⟩
  · -- kind (A): `τ_{m+1} = w`, so `τ₁(w) =β τ₁(τ₁(Y_m)) = S` and `τ₁(w) =β τ₁(Y_{m+1})`
    exfalso
    rw [hτ] at hc
    have c1 := (inv_first hw p1 h2 hnw).2.1
    rw [hY2] at c1
    have e1 := conv_S (tooth1_pure hw hnw) c1
    have c2 := (inv_first hw (pure_Y _) hc hnw).2.1
    rw [e1] at c2
    exact inv_nohnf p1' .S c2.symm n1' hasHnf_S
  · have hpt : PureS (tooth1 (fm ⬝ w)) := tooth1_pure (.app hf hw) hn
    have hs : RSuf (k + 1) w (tooth1 (fm ⬝ w)) := by rw [hτ]; exact chain_rsuf hch
    rcases lemma9_suffix_Y (m + 1) hpt hc hs (Nat.succ_pos k) with hS | ⟨hk, hw1⟩
    · exact absurd (by rw [hS]; exact hasHnf_S) hnw
    · have hk0 : k = 0 := by omega
      subst hk0
      obtain ⟨ea, -, ew⟩ := chain_zero hch
      rw [ea, ew] at hr
      exact ⟨a₀, hr, hw1⟩

/-! ## Lemma 11: `q` is eventually an S-run -/

/-- `a′_n`: the function part of `rest^n(q)`. -/
def aq (q : Term) (n : Nat) : Term := lhs (restN n q)

/-- `b′_n`: the function part of `τ_n(q)`. -/
def bq (q : Term) (n : Nat) : Term := lhs (tooth n q)

/-- Every state of `q` is an application of closed S-terms without an hnf. -/
theorem restN_split {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q) (n : Nat) :
    ∃ fm u, restN n q = fm ⬝ u ∧ PureS fm ∧ PureS u ∧ ¬ HasHnf (fm ⬝ u) := by
  have hp := restN_pure hq hnq n
  have hnn := restN_nohnf hq hnq n
  revert hp hnn
  generalize restN n q = t
  intro hp hnn
  cases hp with
  | S => exact absurd hasHnf_S hnn
  | app hf hx => exact ⟨_, _, rfl, hf, hx, hnn⟩

theorem aq_pure {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q) (n : Nat) : PureS (aq q n) := by
  obtain ⟨fm, u, e, hf, -, -⟩ := restN_split hq hnq n
  have ha : aq q n = fm := congrArg lhs e
  rw [ha]; exact hf

/-- If the state `rest^n(q) = a w` has `w =β τ₁(Y_n)`, then so does every later state, with the
same `w`. -/
theorem bad_forever {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) (n : Nat) {w : Term}
    (h0 : ∃ a, restN n q = a ⬝ w) (hw : Convertible w (tooth1 (Y n))) :
    ∀ j, (∃ a, restN (n + j) q = a ⬝ w) ∧ Convertible w (tooth1 (Y (n + j)))
  | 0 => ⟨h0, hw⟩
  | j + 1 => by
    obtain ⟨⟨a, e⟩, hwj⟩ := bad_forever hq hnq hY n h0 hw j
    have hp := restN_pure hq hnq (n + j)
    have hnn := restN_nohnf hq hnq (n + j)
    rw [e] at hp hnn
    have hc := hY (n + j + 1) (Nat.succ_pos _)
    rw [tooth_succ, e] at hc
    obtain ⟨a', e', hw'⟩ := bad_step (n + j) hp.app_inv.1 hp.app_inv.2 hnn hwj hc
    refine ⟨⟨a', ?_⟩, hw'⟩
    show rest1 (restN (n + j) q) = a' ⬝ w
    rw [e]; exact e'

/-- **The second case never occurs** (proof of Lemma 11, first paragraph): otherwise
`τ₁(Y_{n'}) =β τ₁(Y_n)` for all `n' ≥ n`, so `i_{n'} = i_n` (Lemma 10(c)), against the
unboundedness of `i`. -/
theorem no_bad {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) (n : Nat) {a w : Term}
    (e : restN n q = a ⬝ w) (hw : Convertible w (tooth1 (Y n))) : False := by
  have hall := bad_forever hq hnq hY n ⟨a, e⟩ hw
  have him : ∀ j, im n = im (n + j) := fun j => im_of_conv (hw.symm.trans (hall j).2)
  obtain ⟨m, hm⟩ := im_unbounded (im n + 1)
  have h1 := im_mono (Nat.le_add_left m n)
  rw [← him m] at h1
  omega

/-- Move `n + 1` of `q` is of kind (B) with `k = 0` and `u = S`, in the form of Lemma 11:
`rest^n(q) = a′_n S`, `a′_n ↠_h S a′_{n+1} b′_{n+1}`, `rest^{n+1}(q) = a′_{n+1} S` and
`τ_{n+1}(q) = b′_{n+1} S`. -/
def KindB (q : Term) (n : Nat) : Prop :=
  restN n q = aq q n ⬝ S ∧ Steps (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1)) ∧
    restN (n + 1) q = aq q (n + 1) ⬝ S ∧ tooth (n + 1) q = bq q (n + 1) ⬝ S

/-- **Every move of `q`** is of kind (A) (`rest^n(q) = rest^{n+1}(q) τ_{n+1}(q)` with
`rest^{n+1}(q) = a′_n` hnf-less) or `KindB`. -/
theorem move_q {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) (n : Nat) :
    (¬ HasHnf (aq q n) ∧ restN (n + 1) q = aq q n ∧
      restN n q = aq q n ⬝ tooth (n + 1) q) ∨ KindB q n := by
  obtain ⟨fm, u, e, hf, hu, hnn⟩ := restN_split hq hnq n
  have hc := hY (n + 1) (Nat.succ_pos n)
  rw [tooth_succ, e] at hc
  have ha : aq q n = fm := congrArg lhs e
  have hr : restN (n + 1) q = rest1 (fm ⬝ u) := congrArg rest1 e
  have ht : tooth (n + 1) q = tooth1 (fm ⬝ u) := congrArg tooth1 e
  rcases moveY (n + 1) hf hu hnn hc with ⟨h1, h2, h3⟩ | ⟨hu, a, b, h0, h1, h2⟩ | ⟨a, w, h1, hw⟩
  · left
    rw [ha, hr, h2, ht, h3, e]
    exact ⟨h1, rfl, rfl⟩
  · right
    subst hu
    have ha' : aq q (n + 1) = a := congrArg lhs (hr.trans h1)
    have hb' : bq q (n + 1) = b := congrArg lhs (ht.trans h2)
    unfold KindB
    rw [ha, ha', hb', hr, ht, e]
    exact ⟨rfl, h0, h1, h2⟩
  · exact (no_bad hq hnq hY (n + 1) (hr.trans h1) hw).elim

/-- After a move of kind (B), the state is `a′ S`; a move of kind (A) from it would make `S` a
tooth, which has an hnf.  So the next move is again `KindB`. -/
theorem kindB_succ {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) {n : Nat} (h : KindB q n) :
    KindB q (n + 1) := by
  rcases move_q hq hnq hY (n + 1) with ⟨-, -, h3⟩ | hB
  · exfalso
    have e := h.2.2.1.symm.trans h3
    injection e with _ e2
    have hc := hY (n + 1 + 1) (Nat.succ_pos _)
    rw [← e2] at hc
    exact inv_nohnf (pure_Y _) .S hc.symm (lemma9 _).1 hasHnf_S
  · exact hB

/-- **Some move of `q` is of kind (B)**, found by strong induction on the size of the state: a
move of kind (A) replaces the state `f⁻ u` by `f⁻`. -/
theorem exists_kindB {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) :
    ∀ s n, HeadRec.sz (restN n q) ≤ s → ∃ n', n ≤ n' ∧ KindB q n'
  | 0, n, h => absurd h (Nat.not_le_of_gt (HeadRec.sz_pos _))
  | s + 1, n, h => by
    rcases move_q hq hnq hY n with ⟨-, h1, h2⟩ | hB
    · have hlt : HeadRec.sz (restN (n + 1) q) < HeadRec.sz (restN n q) := by
        rw [h1, h2]; exact HeadRec.sz_fun_lt _ _
      obtain ⟨n', h3, h4⟩ := exists_kindB hq hnq hY s (n + 1) (by omega)
      exact ⟨n', by omega, h4⟩
    · exact ⟨n, Nat.le_refl n, hB⟩

/-- **Lemma 11**, in the form used later: there is `n₀` such that every move `n + 1` with
`n ≥ n₀` is `KindB`. -/
theorem srun {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) :
    ∃ n₀, ∀ n, n₀ ≤ n → KindB q n := by
  obtain ⟨n₀, -, h⟩ := exists_kindB hq hnq hY (HeadRec.sz q) 0 (Nat.le_refl _)
  refine ⟨n₀, fun n hn₀ => ?_⟩
  induction hn₀ with
  | refl => exact h
  | step _ ih => exact kindB_succ hq hnq hY ih

/-- **Lemma 11** (`lem:srun`), the paper's statement.  There is `n₁ ≥ 1` such that, for every
`n ≥ n₁`, `f_{n−1} = a′_{n−1} S` with `a′_{n−1} ↠_h S a′_n b′_n`, `τ_n(q) = b′_n S` and
`f_n = a′_n S`. -/
theorem lemma11 {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) :
    ∃ n₁, 1 ≤ n₁ ∧ ∀ n, n₁ ≤ n →
      restN (n - 1) q = aq q (n - 1) ⬝ S ∧ Steps (aq q (n - 1)) (S ⬝ aq q n ⬝ bq q n) ∧
        tooth n q = bq q n ⬝ S ∧ restN n q = aq q n ⬝ S := by
  obtain ⟨n₀, h⟩ := srun hq hnq hY
  refine ⟨n₀ + 1, Nat.succ_pos _, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨h1, h2, h3, h4⟩ := h k (by omega)
  rw [Nat.add_sub_cancel]
  exact ⟨h1, h2, h4, h3⟩

/-- **Lemma 13** (`lem:left`): if `τ_n(q) = b′_n S` and `τ_n(q) =β Y_n`, then `b′_n =β b_n`. -/
theorem lemma13 {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q) {n : Nat}
    (hc : Convertible (tooth n q) (Y n)) (e : tooth n q = bq q n ⬝ S) :
    Convertible (bq q n) (bm n) := by
  have hp := tooth_pure hq hnq n
  rw [e] at hp hc
  exact lemma13_core n hp.app_inv.1 hc

/-- **Lemmas 11 and 13**, packaged for M5: from `n₀` on, `rest^n(q) = a′_n S`,
`a′_n ↠_h S a′_{n+1} b′_{n+1}`, `τ_{n+1}(q) = b′_{n+1} S` and `b′_{n+1} =β b_{n+1}`. -/
theorem second_run {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      restN n q = aq q n ⬝ S ∧ Steps (aq q n) (S ⬝ aq q (n + 1) ⬝ bq q (n + 1)) ∧
        tooth (n + 1) q = bq q (n + 1) ⬝ S ∧ Convertible (bq q (n + 1)) (bm (n + 1)) := by
  obtain ⟨n₀, h⟩ := srun hq hnq hY
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2, -, h4⟩ := h n hn
  exact ⟨h1, h2, h4, lemma13 hq hnq (hY (n + 1) (Nat.succ_pos n)) h4⟩

/-- The explicit spine of `q` from `n₀` on (for Lemma 15(c) in M5): `P j s := s = a′_{n₀+j}` is a
spine predicate, with `b′_{n₀+j+1} =β b_{n₀+j+1}` and `rest^{n₀+j}(q) = a′_{n₀+j} S`. -/
theorem srun_spine {q : Term} (hq : PureS q) (hnq : ¬ HasHnf q)
    (hY : ∀ n, 1 ≤ n → Convertible (tooth n q) (Y n)) :
    ∃ n₀, Spine (fun j s => s = aq q (n₀ + j)) ∧
      ∀ j, restN (n₀ + j) q = aq q (n₀ + j) ⬝ S ∧
        Convertible (bq q (n₀ + j + 1)) (bm (n₀ + j + 1)) := by
  obtain ⟨n₀, h⟩ := second_run hq hnq hY
  refine ⟨n₀, fun j s hs => ?_, fun j => ?_⟩
  · obtain ⟨-, h2, -, -⟩ := h (n₀ + j) (Nat.le_add_right _ _)
    subst hs
    exact ⟨_, _, h2, rfl⟩
  · obtain ⟨h1, -, -, h4⟩ := h (n₀ + j) (Nat.le_add_right _ _)
    exact ⟨h1, h4⟩

end S11
