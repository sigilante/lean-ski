import Ski.FFBlock
import Ski.Conv
open Term

/-!
# Run rigidity: Theorem NOIMP, and Lock 1 on the b-family (Lock 1, `notes/LOCK1-FFALL.md` §T5)

Notation of §T4–§T5: `e = S S`, `Q = S e e`, `G 0 = Q`, `G (i + 1) = e (G i)` (all normal forms),
and the b-family nodes `N n j = G j (G (n + 1))`.  `Eqv` is `Congruence.Eqv` (tree equality:
equal `NF` prefixes at every depth); `fold` is S1's 38-block fold `HnfS.fold`.

* `comb` (Lemma C, §T3.1 with the repair WT3.1): if `t ↠h S S c`, then `t = S S q S^k` as written
  (`appS (S ⬝ S ⬝ q) k`, `k ≥ 0`) and `c = q S^k`.
* `last_step` (Lemma L′, §T3.1): a head run to `S a c` is empty or ends with `S S y a → S a (y a)`.
* `nf_reduces` ((NF), §T4.1): a pure-S term `≈` a pure-S normal form reduces to it;
  `G_eqv_inj`: distinct `G`s are not `≈`.
* Table facts by kernel evaluation (`decide +kernel`): `B3`, `B4` (§T5.2 with WT5.2) and the
  rigidity of block `13` (`rig13`, WT4.6: `fold u = 13` gives `u = Q` as written).
* `noimp` (Theorem NOIMP, §T5.2): `Y (G m) ≈ G i (G m)` with `m ≥ 1` gives `Y = G i` as written.
  `eqv_G` (WT5.7, Corollary′): `[G i]_≈ = {G i}`.
* `lock1_G` (§T5.3 with WT5.7, WT5.8): `u ≈ G i (G m)`, `m ≥ 1`, gives a common reduct of `u` and
  `G i (G m)`; `lock1_N`: `u ≈ N n j` gives `Conv.Convertible u (N n j)`.  The coalescence argument
  of §T4.1 is an induction on `u`: a literal node passes to its right subterm, a reduced node is
  closed by `noimp`.  The b-family bound `j ≤ n` is not needed.

Case splits are on decidable block values (`Nat` equalities); no `Classical.choice`.
-/

namespace NoImp
open HnfS HnfSound TopTerm InfNF Congruence FFBlock

/-! ## The terms -/

/-- `G 0 = Q = S (S S) (S S)`, `G (i + 1) = S S (G i)`. -/
def G : Nat → Term
  | 0 => S ⬝ (S ⬝ S) ⬝ (S ⬝ S)
  | i + 1 => S ⬝ S ⬝ G i

/-- The b-family node `N(n, j) = G_j G_{n+1}` (§T5.1). -/
def N (n j : Nat) : Term := G j ⬝ G (n + 1)

/-- `appS x k = x S ⋯ S` (`k` trailing arguments `S`). -/
def appS : Term → Nat → Term
  | x, 0 => x
  | x, k + 1 => appS x k ⬝ S

theorem appS_cons (y : Term) : ∀ k, appS (y ⬝ S) k = appS y (k + 1)
  | 0 => rfl
  | k + 1 => by rw [appS, appS_cons y k]; rfl

theorem G_pure : ∀ i, PureS (G i)
  | 0 => .app (.app .S (.app .S .S)) (.app .S .S)
  | i + 1 => .app (.app .S .S) (G_pure i)

theorem G_inj : ∀ {a b : Nat}, G a = G b → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => by injection h with h1; injection h1 with _ h2; cases h2
  | _ + 1, 0, h => by injection h with h1; injection h1 with _ h2; cases h2
  | _ + 1, _ + 1, h => by injection h with _ h2; rw [G_inj h2]

/-- The last argument of `G i` as written is not `S`. -/
theorem G_ne_appS : ∀ (i : Nat) (X : Term), G i ≠ X ⬝ S
  | 0, _, h => by injection h with _ h2; cases h2
  | i + 1, _, h => by
    injection h with _ h2
    cases i <;> cases h2

/-! ## Normal forms and (NF) -/

theorem normal_S : Normal S := fun _ h => by cases h

theorem normal_S1 {a : Term} (ha : Normal a) : Normal (S ⬝ a) := fun _ h => by
  cases h with
  | left _ h => cases h
  | right _ h => exact ha _ h

theorem normal_S2 {a b : Term} (ha : Normal a) (hb : Normal b) : Normal (S ⬝ a ⬝ b) :=
  fun _ h => by
    cases h with
    | left _ h => exact normal_S1 ha _ h
    | right _ h => exact hb _ h

theorem G_normal : ∀ i, Normal (G i)
  | 0 => normal_S2 (normal_S1 normal_S) (normal_S1 normal_S)
  | i + 1 => normal_S2 normal_S (G_normal i)

theorem normal_wsteps {a b : Term} (ha : Normal a) (h : WSteps a b) : b = a := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (ha _)

/-- **(NF)** (§T4.1).  A pure-S term `≈` a pure-S normal form `A` reduces to `A`. -/
theorem nf_reduces {A : Term} (hA : PureS A) (hN : Normal A) :
    ∀ {a : Term}, PureS a → Eqv a A → WSteps a A := by
  induction hA with
  | S =>
    intro a ha h
    obtain ⟨u', hs, hm⟩ := factK .S ha h.symm (.refl _) (.inl rfl)
    rcases hm with ⟨_, rfl⟩ | ⟨_, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩
    · exact hs.weak
    · cases h1
    · cases h1
  | @app f x hf hx ihf ihx =>
    intro a ha h
    obtain ⟨u', hs, hm⟩ := factK (.app hf hx) ha h.symm (.refl _) (normal_hnf (.app hf hx) hN)
    have hu := steps_pure ha hs
    rcases hm with ⟨h1, _⟩ | ⟨A1, a1, h1, rfl, e1⟩ | ⟨A1, A2, a1, a2, h1, rfl, e1, e2⟩
    · cases h1
    · injection h1 with h2 h3
      subst h2 h3
      exact hs.weak.trans (WSteps.right S (ihx (normal_right hN) hu.app_inv.2 e1.symm))
    · injection h1 with h2 h3
      subst h2 h3
      have e1' : Eqv (S ⬝ a1) (S ⬝ A1) :=
        eqv_app .S .S hu.app_inv.1.app_inv.2 hf.app_inv.2 (Eqv.refl _) e1.symm
      exact hs.weak.trans (WSteps.app (ihf (normal_left hN) hu.app_inv.1 e1')
        (ihx (normal_right hN) hu.app_inv.2 e2.symm))

/-- Distinct `G`s are not `≈` (distinct normal forms). -/
theorem G_eqv_inj {a b : Nat} (h : Eqv (G a) (G b)) : a = b :=
  (G_inj (normal_wsteps (G_normal a) (nf_reduces (G_pure b) (G_normal b) (G_pure a) h))).symm

/-! ## Head-step shapes: Lemmas L′ and C -/

theorem no_step_S {w : Term} (hw : PureS w) : ¬ Step w S := fun h => by
  cases h with
  | K => exact PureS.not_K hw.app_inv.1.app_inv.1
  | I => exact PureS.not_I hw.app_inv.1

theorem no_step_S1 {w a : Term} (hw : PureS w) : ¬ Step w (S ⬝ a) := fun h => by
  cases h with
  | K => exact PureS.not_K hw.app_inv.1.app_inv.1
  | I => exact PureS.not_I hw.app_inv.1
  | left _ h => exact no_step_S hw.app_inv.1 h

/-- A head step into `S a c` is `S S y a → S a (y a)`. -/
theorem step_into_S2 {u v : Term} (hu : PureS u) (h : Step u v) :
    ∀ {a c : Term}, v = S ⬝ a ⬝ c → ∃ y, u = S ⬝ S ⬝ y ⬝ a ∧ c = y ⬝ a := by
  intro a c he
  cases h with
  | S f g x =>
    injection he with h1 h2
    injection h1 with h3 h4
    subst h3 h4 h2
    exact ⟨g, rfl, rfl⟩
  | K => exact absurd hu.app_inv.1.app_inv.1 PureS.not_K
  | I => exact absurd hu.app_inv.1 PureS.not_I
  | left _ h =>
    injection he with h1 _
    subst h1
    exact absurd h (no_step_S1 hu.app_inv.1)

/-- **Lemma L′** (§T3.1).  A head run of a pure S-term to `S a c` is empty, or its last step is
`S S y a → S a (y a)`. -/
theorem last_step {u v : Term} (h : Steps u v) (hu : PureS u) :
    ∀ {a c : Term}, v = S ⬝ a ⬝ c →
      u = S ⬝ a ⬝ c ∨ ∃ y, Steps u (S ⬝ S ⬝ y ⬝ a) ∧ c = y ⬝ a := by
  induction h with
  | refl => intro a c he; exact .inl he
  | step s _ ih =>
    intro a c he
    rcases ih (HnfS.wstep_pure s.weak hu).1 he with h1 | ⟨y, hs, hc⟩
    · obtain ⟨y, rfl, hc⟩ := step_into_S2 hu s h1
      exact .inr ⟨y, .refl _, hc⟩
    · exact .inr ⟨y, .step s hs, hc⟩

/-- A head step into `S S A S^k` comes from `S S y S^(k+1)` with `A = y S`. -/
theorem step_comb {u v : Term} (h : Step u v) (hu : PureS u) :
    ∀ (k : Nat) (A : Term), v = appS (S ⬝ S ⬝ A) k →
      ∃ y, u = appS (S ⬝ S ⬝ y) (k + 1) ∧ A = y ⬝ S := by
  induction h with
  | S f g x =>
    intro k A he
    cases k with
    | zero =>
      injection he with h1 h2
      injection h1 with h3 h4
      subst h3 h4 h2
      exact ⟨g, rfl, rfl⟩
    | succ k =>
      injection he with _ h2
      cases h2
  | K => exact absurd hu.app_inv.1.app_inv.1 PureS.not_K
  | I => exact absurd hu.app_inv.1 PureS.not_I
  | @left f f' x h ih =>
    intro k A he
    cases k with
    | zero =>
      injection he with h1 _
      subst h1
      exact absurd h (no_step_S1 hu.app_inv.1)
    | succ k =>
      injection he with h1 h2
      subst h2
      obtain ⟨y, hf, hA⟩ := ih hu.app_inv.1 k A h1
      exact ⟨y, by rw [hf]; rfl, hA⟩

theorem comb_gen {t v : Term} (h : Steps t v) (ht : PureS t) :
    ∀ (k : Nat) (A : Term), v = appS (S ⬝ S ⬝ A) k →
      ∃ q k', t = appS (S ⬝ S ⬝ q) k' ∧ appS q k' = appS A k := by
  induction h with
  | refl => intro k A he; exact ⟨A, k, he, rfl⟩
  | step s _ ih =>
    intro k A he
    obtain ⟨q, k', h1, h2⟩ := ih (HnfS.wstep_pure s.weak ht).1 k A he
    obtain ⟨y, hy, hq⟩ := step_comb s ht k' q h1
    exact ⟨y, k' + 1, hy, by rw [← h2, hq, appS_cons]⟩

/-- **Lemma C** (comb; §T3.1 with WT3.1).  If a pure S-term `t` head-reduces to `S S c`, then
`t = S S q S^k` as written, for some `k ≥ 0`, and `c = q S^k`. -/
theorem comb {t c : Term} (ht : PureS t) (h : Steps t (S ⬝ S ⬝ c)) :
    ∃ q k, t = appS (S ⬝ S ⬝ q) k ∧ c = appS q k := by
  obtain ⟨q, k, h1, h2⟩ := comb_gen h ht 0 c rfl
  exact ⟨q, k, h1, h2.symm⟩

/-! ## Table facts (kernel evaluation) -/

/-- **B3.** `{y : β y 12 = 25} = {11, 12, 13}`. -/
theorem B3 : ∀ y, y < 38 → (β y 12 = 25 ↔ y = 11 ∨ y = 12 ∨ y = 13) := by decide +kernel

/-- **B4, kind 1.** A block `β 0 α` is never `12` or `13`.  (Stated for B4 as written; `noimp` excludes kind 1 by the block of the c-child, case 1.) -/
theorem B4_one : ∀ a, a < 38 → β 0 a ≠ 12 ∧ β 0 a ≠ 13 := by decide +kernel

/-- **B4, kind 2.** A block `β (β 0 α) γ` is never `11`; it is `12` only with `α = 0`, and `13`
only with `α = γ = 1` (the `13` clause is not used: `noimp` uses `rig13`). -/
theorem B4_two : ∀ a, a < 38 → ∀ c, c < 38 →
    β (β 0 a) c ≠ 11 ∧ (β (β 0 a) c = 12 → a = 0) ∧ (β (β 0 a) c = 13 → a = 1 ∧ c = 1) := by
  decide +kernel

/-- The preimages of `13`, `2` and `1` (WT4.6): `β⁻¹(13) = {(2,1)}`, `β⁻¹(2) = {(0,1)}`,
`β⁻¹(1) = {(0,0)}`. -/
theorem pre13 : ∀ a, a < 38 → ∀ b, b < 38 → (β a b = 13 ↔ a = 2 ∧ b = 1) := by decide +kernel
theorem pre2 : ∀ a, a < 38 → ∀ b, b < 38 → (β a b = 2 ↔ a = 0 ∧ b = 1) := by decide +kernel
theorem pre1 : ∀ a, a < 38 → ∀ b, b < 38 → (β a b = 1 ↔ a = 0 ∧ b = 0) := by decide +kernel

theorem eq_SS_of_fold {t : Term} (ht : PureS t) (h : fold t = 1) : t = S ⬝ S := by
  cases ht with
  | S => exact absurd h (by decide)
  | app hf hx =>
    obtain ⟨h0, h0'⟩ := (pre1 _ (fold_lt hf) _ (fold_lt hx)).1 h
    rw [eq_S_of_fold hf h0, eq_S_of_fold hx h0']

/-- **Rigidity of block 13** (WT4.6).  A pure S-term of block `13` is `Q` as written. -/
theorem rig13 {t : Term} (ht : PureS t) (h : fold t = 13) : t = G 0 := by
  cases ht with
  | S => exact absurd h (by decide)
  | @app f x hf hx =>
    obtain ⟨h2, h1⟩ := (pre13 _ (fold_lt hf) _ (fold_lt hx)).1 h
    rw [eq_SS_of_fold hx h1]
    cases hf with
    | S => exact absurd h2 (by decide)
    | @app g w hg hw =>
      obtain ⟨h0, h1'⟩ := (pre2 _ (fold_lt hg) _ (fold_lt hw)).1 h2
      rw [eq_S_of_fold hg h0, eq_SS_of_fold hw h1']
      rfl

/-! ## Blocks and hnfs of `G i (G m)` -/

theorem fold_G_succ : ∀ i, fold (G (i + 1)) = 12
  | 0 => by decide
  | i + 1 => by
    show β (β 0 0) (fold (G (i + 1))) = 12
    rw [fold_G_succ i]
    decide

/-- **B1–B2.** `b(G i (G m)) = 25` for `m ≥ 1`. -/
theorem fold_GG (i : Nat) {m : Nat} (hm : 1 ≤ m) : fold (G i ⬝ G m) = 25 := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
  show β (fold (G i)) (fold (G (m + 1))) = 25
  rw [fold_G_succ m]
  cases i with
  | zero => decide
  | succ i => rw [fold_G_succ i]; decide

/-- The index of the a-child of `G i (G m)`'s hnf. -/
def tA : Nat → Nat → Nat
  | 0, m => m + 1
  | _ + 1, m => m

/-- The index of the generator of the c-child of `G i (G m)`'s hnf. -/
def tG : Nat → Nat → Nat
  | 0, m => m
  | i + 1, _ => i

theorem tA_ge (i m : Nat) : m ≤ tA i m := by
  cases i with
  | zero => exact Nat.le_succ m
  | succ i => exact Nat.le_refl m

/-- The hnf of `G i (G m)`: `S (G (m+1)) (G m (G (m+1)))` if `i = 0`, `S (G m) (G (i-1) (G m))`
otherwise. -/
theorem G_hnf (i m : Nat) :
    Steps (G i ⬝ G m) (S ⬝ G (tA i m) ⬝ (G (tG i m) ⬝ G (tA i m))) := by
  cases i with
  | zero => exact .step (.S _ _ _) (.single (.S _ _ _))
  | succ i => exact .single (.S _ _ _)

theorem hnf_det {t u v : Term} (hu : Steps t u) (hu' : IsHnf u) (hv : Steps t v)
    (hv' : IsHnf v) : u = v := by
  rcases steps_cmp hu hv with h | h
  · exact (steps_from_hnf hu' h).symm
  · exact steps_from_hnf hv' h

/-- A kind-2 hnf of a term `≈ G i (G m)` has `≈` items to the target's. -/
theorem match_target {x a c : Term} {i m : Nat} (hx : PureS x) (h : Eqv x (G i ⬝ G m))
    (hs : Steps x (S ⬝ a ⬝ c)) :
    Eqv a (G (tA i m)) ∧ Eqv c (G (tG i m) ⬝ G (tA i m)) := by
  obtain ⟨u', hs', hm⟩ := factK hx (.app (G_pure i) (G_pure m)) h hs (.inr (.inr ⟨a, c, rfl⟩))
  have hd := hnf_det hs' ?_ (G_hnf i m) (.inr (.inr ⟨_, _, rfl⟩))
  · rcases hm with ⟨h1, _⟩ | ⟨_, _, h1, _⟩ | ⟨a1, c1, a', c', h1, rfl, ea, ec⟩
    · cases h1
    · cases h1
    · injection h1 with h2 h3
      injection h2 with _ h4
      subst h3 h4
      injection hd with h5 h6
      injection h5 with _ h7
      rw [← h6, ← h7]
      exact ⟨ea, ec⟩
  · rcases hm with ⟨_, rfl⟩ | ⟨_, a', _, rfl, _⟩ | ⟨_, _, a', c', _, rfl, _⟩
    · exact .inl rfl
    · exact .inr (.inl ⟨a', rfl⟩)
    · exact .inr (.inr ⟨a', c', rfl⟩)

/-! ## Theorem NOIMP -/

/-- **Theorem NOIMP** (§T5.2 with WT5.1–WT5.6).  For `m ≥ 1`, if `Y (G m) ≈ G i (G m)`, then
`Y = G i` as written.  In particular no `(i, m)`-impostor exists for any pair with `m ≥ 1`. -/
theorem noimp : ∀ (i : Nat) {Y : Term} {m : Nat}, 1 ≤ m → PureS Y →
    Eqv (Y ⬝ G m) (G i ⬝ G m) → Y = G i := by
  intro i
  induction i with
  | zero => ?_
  | succ i ih => ?_
  all_goals
    intro Y m hm hY h
    have hYG : PureS (Y ⬝ G m) := .app hY (G_pure m)
    have hf := fold_eqv hYG (.app (G_pure _) (G_pure m)) h
    rw [fold_GG _ hm] at hf
    obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel hm).symm⟩
    have hb : β (fold Y) 12 = 25 := by
      have : β (fold Y) (fold (G (m' + 1))) = 25 := hf
      rwa [fold_G_succ m'] at this
    have hY3 := (B3 _ (fold_lt hY)).1 hb
  -- the kind-1 case (block 11) is impossible
  all_goals
    have k1 : ∀ p, Steps Y (S ⬝ p) → False := by
      intro p hs
      have hs2 : Steps (Y ⬝ G (m' + 1)) (S ⬝ p ⬝ G (m' + 1)) := Steps.left _ hs
      have e := (match_target hYG h hs2).2
      have := fold_eqv (G_pure _) (.app (G_pure _) (G_pure _)) e
      rw [fold_G_succ m', fold_GG _ (Nat.le_trans hm (tA_ge _ _))] at this
      exact absurd this (by decide)
  · -- i = 0
    rcases hY3 with h11 | h12 | h13
    · obtain ⟨H, hc, _, hH⟩ := sound_head Y hY (by rw [h11]; decide)
      have hs := headChain_steps hc
      have hfH := (steps_fold hY hs).trans h11
      have hHp := steps_pure hY hs
      rcases hH with rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩
      · exact absurd hfH (by decide)
      · exact (k1 p hs).elim
      · exact absurd hfH (B4_two _ (fold_lt hHp.app_inv.1.app_inv.2) _ (fold_lt hHp.app_inv.2)).1
    · obtain ⟨H, hc, _, hH⟩ := sound_head Y hY (by rw [h12]; decide)
      have hs := headChain_steps hc
      have hfH := (steps_fold hY hs).trans h12
      have hHp := steps_pure hY hs
      rcases hH with rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩
      · exact absurd hfH (by decide)
      · exact (k1 p hs).elim
      · have hp0 := (B4_two _ (fold_lt hHp.app_inv.1.app_inv.2) _ (fold_lt hHp.app_inv.2)).2.1 hfH
        rw [eq_S_of_fold hHp.app_inv.1.app_inv.2 hp0] at hs
        have hs2 : Steps (Y ⬝ G (m' + 1)) (S ⬝ G (m' + 1) ⬝ (q ⬝ G (m' + 1))) :=
          (Steps.left _ hs).trans (.single (.S _ _ _))
        have := G_eqv_inj (match_target hYG h hs2).1
        exact absurd this (Nat.succ_ne_self _).symm
    · exact rig13 hY h13
  · -- i + 1
    rcases hY3 with h11 | h12 | h13
    · obtain ⟨H, hc, _, hH⟩ := sound_head Y hY (by rw [h11]; decide)
      have hs := headChain_steps hc
      have hfH := (steps_fold hY hs).trans h11
      have hHp := steps_pure hY hs
      rcases hH with rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩
      · exact absurd hfH (by decide)
      · exact (k1 p hs).elim
      · exact absurd hfH (B4_two _ (fold_lt hHp.app_inv.1.app_inv.2) _ (fold_lt hHp.app_inv.2)).1
    · obtain ⟨H, hc, _, hH⟩ := sound_head Y hY (by rw [h12]; decide)
      have hs := headChain_steps hc
      have hfH := (steps_fold hY hs).trans h12
      have hHp := steps_pure hY hs
      rcases hH with rfl | ⟨p, rfl⟩ | ⟨p, q, rfl⟩
      · exact absurd hfH (by decide)
      · exact (k1 p hs).elim
      · have hp0 := (B4_two _ (fold_lt hHp.app_inv.1.app_inv.2) _ (fold_lt hHp.app_inv.2)).2.1 hfH
        have hq := hHp.app_inv.2
        rw [eq_S_of_fold hHp.app_inv.1.app_inv.2 hp0] at hs
        have hs2 : Steps (Y ⬝ G (m' + 1)) (S ⬝ G (m' + 1) ⬝ (q ⬝ G (m' + 1))) :=
          (Steps.left _ hs).trans (.single (.S _ _ _))
        have e := (match_target hYG h hs2).2
        have hqi : q = G i := ih hm hq e
        obtain ⟨q₀, k, hY', hq'⟩ := comb hY hs
        cases k with
        | zero =>
          rw [hY']
          show S ⬝ S ⬝ q₀ = S ⬝ S ⬝ G i
          rw [← hqi, hq']
          rfl
        | succ k => exact absurd (hqi.symm.trans hq') (G_ne_appS i _)
    · -- block 13: `Y = Q`, and `Q (G m) ≉ G (i+1) (G m)` (WT4.10(b) with k = 0)
      have hQ := rig13 hY h13
      subst hQ
      have hs0 := G_hnf 0 (m' + 1)
      have := G_eqv_inj (match_target hYG h hs0).1
      exact absurd this (Nat.succ_ne_self _)

/-- **Corollary′** (WT5.7).  `[G i]_≈ = {G i}`: a pure S-term `≈ G i` is `G i` as written. -/
theorem eqv_G {Y : Term} {i : Nat} (hY : PureS Y) (h : Eqv Y (G i)) : Y = G i :=
  noimp i (Nat.le_refl 1) hY (eqv_app hY (G_pure i) (G_pure 1) (G_pure 1) h (Eqv.refl _))

/-! ## Lock 1 on the b-family (coalescence, §T4.1 + §T5.3) -/

/-- **Corollary** (§T5.3 with WT5.7, WT5.8), joinability form.  For `m ≥ 1`, every pure S-term
`u ≈ G i (G m)` has a common reduct with `G i (G m)`. -/
theorem lock1_G {u : Term} (hu : PureS u) :
    ∀ {i m : Nat}, 1 ≤ m → Eqv u (G i ⬝ G m) → ∃ v, WSteps u v ∧ WSteps (G i ⬝ G m) v := by
  induction hu with
  | S =>
    intro i m _ h
    obtain ⟨u', hs, hm⟩ := factK (.app (G_pure i) (G_pure m)) .S h.symm (G_hnf i m)
      (.inr (.inr ⟨_, _, rfl⟩))
    rcases hm with ⟨h1, _⟩ | ⟨_, _, h1, _⟩ | ⟨_, _, a', c', _, rfl, _⟩
    · cases h1
    · cases h1
    · exact absurd (steps_from_S hs) (by intro h; cases h)
  | @app f x hf hx _ ihx =>
    intro i m hm h
    have hfx : PureS (f ⬝ x) := .app hf hx
    have hm' : 1 ≤ tA i m := Nat.le_trans hm (tA_ge i m)
    obtain ⟨u', hs, hmt⟩ := factK (.app (G_pure i) (G_pure m)) hfx h.symm (G_hnf i m)
      (.inr (.inr ⟨_, _, rfl⟩))
    rcases hmt with ⟨h1, _⟩ | ⟨_, _, h1, _⟩ | ⟨_, _, a', c', h1, rfl, ea, ec⟩
    · cases h1
    · cases h1
    · injection h1 with h2 h3
      injection h2 with _ h4
      subst h3 h4
      have hu' := steps_pure hfx hs
      have ha' := hu'.app_inv.1.app_inv.2
      have hred : WSteps a' (G (tA i m)) :=
        nf_reduces (G_pure _) (G_normal _) ha' ea.symm
      have hT := (G_hnf i m).weak
      rcases last_step hs hfx rfl with hlit | ⟨y, hsy, hc⟩
      · -- literal node: pass to the right subterm `x = c'`
        injection hlit with hfa h5
        subst h5
        obtain ⟨v, h6, h7⟩ := ihx hm' ec.symm
        refine ⟨S ⬝ G (tA i m) ⬝ v, ?_, hT.trans (WSteps.right _ h7)⟩
        rw [hfa]
        exact WSteps.app (WSteps.right S hred) h6
      · -- reduced node: the generator `y` is closed by `noimp`
        subst hc
        have hy := (steps_pure hfx hsy).app_inv.1.app_inv.2
        have e1 : Eqv (y ⬝ G (tA i m)) (y ⬝ a') :=
          eqv_app hy hy (G_pure _) ha' (Eqv.refl _) ea
        have hyG := noimp (tG i m) hm' hy (e1.trans ec.symm)
        subst hyG
        exact ⟨_, hs.weak.trans (WSteps.app (WSteps.right S hred) (WSteps.right _ hred)), hT⟩

/-- **Lock 1 on `G i (G m)`** (WT5.8), conversion form. -/
theorem lock1_G_conv {u : Term} {i m : Nat} (hu : PureS u) (hm : 1 ≤ m)
    (h : Eqv u (G i ⬝ G m)) : Conv.Convertible u (G i ⬝ G m) := by
  obtain ⟨v, h1, h2⟩ := lock1_G hu hm h
  exact (Conv.Convertible.of_wsteps h1).trans (Conv.Convertible.of_wsteps h2).symm

/-- **Corollary: Lock 1 on the b-family** (§T5.3).  A pure S-term `≈ N n j` is convertible to
`N n j`.  (The b-family has `j ≤ n`; the theorem holds for all `n`, `j`.) -/
theorem lock1_N {u : Term} {n j : Nat} (hu : PureS u) (h : Eqv u (N n j)) :
    Conv.Convertible u (N n j) :=
  lock1_G_conv hu (Nat.succ_pos n) h

end NoImp
