import Ski.Requote
import Ski.Compose

open Term

/-!
# No behavioural lift at `Nat → Bool`

`no_quote` (Proposition 3.1) forbids *syntactic* quotation: no closed `Q`
has `Q M ↠ ⟨M⟩` for every `M`.  A behavioural lift asks less: from a live
function `f`, a code `⟨c⟩` whose term `c` *behaves* as `f` does.  B2's
working note conjectures, and checks numerically (`notes/checks/cantor.py`;
not in Lean), that such lifts exist at data types, where they canonicalize,
and at some function types, `(Nat → Bool) → Bool` by Berger's search, for
functionals total on all points.  This module proves the lift does not exist
at `Nat → Bool`: no closed `L` sends every function that is total on the
numerals to a term convertible with a code that agrees with it on the
numerals (`no_lift_conv`, and `no_lift` for reduction to the code).

The proof is a stuttering simulation, not a general continuity theorem.

- `num m`: Scott numerals, `num 0 = K`, `num (m+1) = succS ⬝ num m`.
- An *infinite numeral* `ω`: any `fixSelf succS z` with `z ↠ fixB succS`
  (lean-ski's `fixSelf`; each unrolling adds an `I`, `fixSelf_step`).  With
  two arguments it head-reduces to `s ⬝ (K ⬝ ω' ⬝ s)`, `ω'` again such a
  term, exactly as `num (m+1)` reduces to `s ⬝ (K ⬝ num m ⬝ s)`.
- `Rel b t t'`: `t'` is `t` with some infinite numerals replaced by numerals
  `num m`, `m ≥ b`.  If `t` head-reduces to `K` in `n < b` steps, then `t'`
  head-reduces to `K` too, in some number of steps (`sim`): a combinator head steps in lockstep; an infinite numeral at
  the head with two arguments takes one macro step on each side, and the
  numeral's count drops by one while the run drops by at least one step; with
  fewer arguments the run would stop at a weak head normal form other than
  `K`.
- `G c n` decides `n > c` by walking down both numerals: `G ω` is constant
  false, `G (num k)` is false up to `k` and true above.
- `eqT c`: a per-code equality test, by recursion on `c` in Lean.

If `L` lifted, take `f = G ω` and its code `c`: `eqT c (L f)` head-reduces
to `K` in some `n` steps, so by `sim` so does `eqT c (L (G (num (n+1))))`,
so `L` gives `G (num (n+1))` the code `c` as well; but the two functions
differ at `n + 2`, and Church–Rosser refutes `c` agreeing with both.
-/

namespace NoLift

-- ---------------------------------------------------------------------------
-- Head steps, counted
-- ---------------------------------------------------------------------------

/-- `n` head steps. -/
inductive StepsN : Nat → Term → Term → Prop
  | refl (t : Term) : StepsN 0 t t
  | step {t u v : Term} {n : Nat} (h : Step t u) (hs : StepsN n u v) : StepsN (n + 1) t v

theorem StepsN.steps {n : Nat} {t u : Term} : StepsN n t u → Steps t u
  | .refl _ => .refl _
  | .step h hs => .step h hs.steps

theorem counted {t u : Term} : Steps t u → ∃ n, StepsN n t u
  | .refl _ => ⟨0, .refl _⟩
  | .step h hs => let ⟨n, hn⟩ := counted hs; ⟨n + 1, .step h hn⟩

/-- A run to a weak head normal form passes through every head step. -/
theorem stepsN_after {n : Nat} {t u v : Term} (hn : StepsN n t v) (hv : Whnf v) (h : Step t u) :
    ∃ m, n = m + 1 ∧ StepsN m u v := by
  cases hn with
  | refl => exact (hv.no_step h).elim
  | step h' hs => rw [Step.det h h']; exact ⟨_, rfl, hs⟩

/-- ... and through every head reduct, strictly when the reduction takes a step. -/
theorem stepsN_through {u : Term} : ∀ {n : Nat} {t v : Term}, StepsN n t v → Whnf v → Steps t u →
    ∃ m, m ≤ n ∧ StepsN m u v := by
  intro n t v hn hv h
  induction h generalizing n with
  | refl => exact ⟨n, Nat.le_refl _, hn⟩
  | step h1 _ ih =>
    obtain ⟨m, rfl, hm⟩ := stepsN_after hn hv h1
    obtain ⟨k, hk, hk'⟩ := ih hm
    exact ⟨k, by omega, hk'⟩

theorem stepsN_through_lt {n : Nat} {t t1 u v : Term} (hn : StepsN n t v) (hv : Whnf v)
    (h1 : Step t t1) (h : Steps t1 u) : ∃ m, m < n ∧ StepsN m u v := by
  obtain ⟨m, rfl, hm⟩ := stepsN_after hn hv h1
  obtain ⟨k, hk, hk'⟩ := stepsN_through hm hv h
  exact ⟨k, by omega, hk'⟩

/-- A run to `K` from a weak head normal form is empty. -/
theorem stepsN_K_whnf {n : Nat} {t : Term} (hn : StepsN n t K) (ht : Whnf t) : t = K := by
  cases hn with
  | refl => rfl
  | step h _ => exact (ht.no_step h).elim

-- ---------------------------------------------------------------------------
-- Spines
-- ---------------------------------------------------------------------------

/-- A term applied to arguments, first argument innermost. -/
def spineApp : Term → List Term → Term
  | t, [] => t
  | t, a :: r => spineApp (t ⬝ a) r

theorem spineApp_append (h : Term) : ∀ (r : List Term) (x : Term),
    spineApp h (r ++ [x]) = spineApp h r ⬝ x
  | [], _ => rfl
  | a :: r, x => spineApp_append (h ⬝ a) r x

theorem step_spine {u v : Term} (h : Step u v) : ∀ r, Step (spineApp u r) (spineApp v r)
  | [] => h
  | a :: r => step_spine (.left a h) r

theorem steps_spine {u v : Term} (h : Steps u v) : ∀ r, Steps (spineApp u r) (spineApp v r)
  | [] => h
  | a :: r => steps_spine (Steps.left a h) r

/-- Every term is a combinator applied to arguments. -/
theorem leaf_spine : ∀ t : Term, ∃ h r, (h = S ∨ h = K ∨ h = I) ∧ t = spineApp h r
  | .S => ⟨S, [], .inl rfl, rfl⟩
  | .K => ⟨K, [], .inr (.inl rfl), rfl⟩
  | .I => ⟨I, [], .inr (.inr rfl), rfl⟩
  | .app f x => by
    obtain ⟨h, r, hh, rfl⟩ := leaf_spine f
    exact ⟨h, r ++ [x], hh, (spineApp_append h r x).symm⟩

-- ---------------------------------------------------------------------------
-- Numerals and the infinite numeral
-- ---------------------------------------------------------------------------

/-- Scott successor, `λ x z s. s x`, by bracket abstraction with η. -/
def succS : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K)

/-- Scott numerals: `num 0 = λ z s. z`. -/
def num : Nat → Term
  | 0 => K
  | m + 1 => succS ⬝ num m

/-- `succS x z s` head-reduces to `s (K x s)`. -/
theorem succS_steps (x z s : Term) : Steps (succS ⬝ x ⬝ z ⬝ s) (s ⬝ (K ⬝ x ⬝ s)) :=
  iter_sound (k := 7) rfl

/-- The infinite numeral, as a class: a self-reference of `fixY succS`. -/
def omegaT (z : Term) : Term := fixSelf succS z

/-- The first one. -/
def omega0 : Term := omegaT (fixB succS)

/-- With two arguments, an infinite numeral reduces as a successor does, to
    the next infinite numeral, the first step explicit. -/
theorem omega_steps {z : Term} (hz : Steps z (fixB succS)) (a s : Term) :
    Step (omegaT z ⬝ a ⬝ s) (S ⬝ I ⬝ I ⬝ z ⬝ a ⬝ s) ∧
    Steps (S ⬝ I ⬝ I ⬝ z ⬝ a ⬝ s) (s ⬝ (K ⬝ omegaT (I ⬝ z) ⬝ s)) := by
  refine ⟨.left s (.left a (.left z (.K _ _))), ?_⟩
  have h1 : Steps (S ⬝ I ⬝ I ⬝ z ⬝ a ⬝ s) (z ⬝ (I ⬝ z) ⬝ a ⬝ s) := iter_sound (k := 2) rfl
  have h2 := Steps.left s (Steps.left a (Steps.left (I ⬝ z) hz))
  have h3 : Steps (fixB succS ⬝ (I ⬝ z) ⬝ a ⬝ s) (succS ⬝ omegaT (I ⬝ z) ⬝ a ⬝ s) :=
    Steps.left s (Steps.left a (iter_sound (k := 5) rfl))
  exact h1.trans (h2.trans (h3.trans (succS_steps _ _ _)))

/-- With no argument, it stops at `K ⬝ _`. -/
theorem omega_whnf0 {z : Term} (hz : Steps z (fixB succS)) :
    ∃ w, Steps (omegaT z) (K ⬝ w) := by
  have h := fixSelf_unroll (F := succS) hz
  exact ⟨_, h.trans (iter_sound (k := 2) rfl)⟩

/-- With one argument, it stops at `S ⬝ I ⬝ _`. -/
theorem omega_whnf1 {z : Term} (hz : Steps z (fixB succS)) (a : Term) :
    ∃ w, Steps (omegaT z ⬝ a) (S ⬝ I ⬝ w) := by
  have h := Steps.left a (fixSelf_unroll (F := succS) hz)
  exact ⟨_, h.trans (iter_sound (k := 5) rfl)⟩

-- ---------------------------------------------------------------------------
-- The relation and the simulation
-- ---------------------------------------------------------------------------

/-- Two lists related pointwise. -/
inductive Pairs (R : Term → Term → Prop) : List Term → List Term → Prop
  | nil : Pairs R [] []
  | cons {a a' : Term} {r r' : List Term} : R a a' → Pairs R r r' → Pairs R (a :: r) (a' :: r')

/-- `Rel b t t'`: `t'` is `t` with some infinite numerals replaced by
    numerals of at least `b`. -/
inductive Rel (b : Nat) : Term → Term → Prop
  | refl (t : Term) : Rel b t t
  | omega {z : Term} (hz : Steps z (fixB succS)) {m : Nat} (hm : b ≤ m) : Rel b (omegaT z) (num m)
  | app {f f' x x' : Term} : Rel b f f' → Rel b x x' → Rel b (f ⬝ x) (f' ⬝ x')

theorem Rel.mono {b b' : Nat} (hb : b' ≤ b) {t t' : Term} : Rel b t t' → Rel b' t t'
  | .refl t => .refl t
  | .omega hz hm => .omega hz (Nat.le_trans hb hm)
  | .app hf hx => .app (hf.mono hb) (hx.mono hb)

/-- The head of a related pair: the same combinator, or an infinite numeral
    against a numeral. -/
inductive Head (b : Nat) : Term → Term → Prop
  | leaf {h : Term} (hl : h = S ∨ h = K ∨ h = I) : Head b h h
  | omega {z : Term} (hz : Steps z (fixB succS)) {m : Nat} (hm : b ≤ m) : Head b (omegaT z) (num m)

theorem rel_spineApp {b : Nat} {u u' : Term} (hu : Rel b u u') :
    ∀ {r r' : List Term}, Pairs (Rel b) r r' → Rel b (spineApp u r) (spineApp u' r')
  | [], [], .nil => hu
  | _ :: _, _ :: _, .cons ha hr => rel_spineApp (.app hu ha) hr

theorem forall₂_refl {b : Nat} : ∀ r : List Term, Pairs (Rel b) r r
  | [] => .nil
  | a :: r => .cons (.refl a) (forall₂_refl r)

theorem forall₂_append {b : Nat} {r r' : List Term} (hr : Pairs (Rel b) r r')
    {x x' : Term} (hx : Rel b x x') : Pairs (Rel b) (r ++ [x]) (r' ++ [x']) := by
  induction hr with
  | nil => exact .cons hx .nil
  | cons ha _ ih => exact .cons ha ih

theorem forall₂_mono {b b' : Nat} (hb : b' ≤ b) {r r' : List Term}
    (hr : Pairs (Rel b) r r') : Pairs (Rel b') r r' := by
  induction hr with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (ha.mono hb) ih

/-- **The spine view** of a related pair. -/
theorem Rel.spine {b : Nat} {t t' : Term} (h : Rel b t t') :
    ∃ hd hd' r r', Head b hd hd' ∧ Pairs (Rel b) r r' ∧
      t = spineApp hd r ∧ t' = spineApp hd' r' := by
  induction h with
  | refl t =>
    obtain ⟨hd, r, hl, rfl⟩ := leaf_spine t
    exact ⟨hd, hd, r, r, .leaf hl, forall₂_refl r, rfl, rfl⟩
  | omega hz hm => exact ⟨_, _, [], [], .omega hz hm, .nil, rfl, rfl⟩
  | app _ hx ih _ =>
    obtain ⟨hd, hd', r, r', hh, hr, rfl, rfl⟩ := ih
    exact ⟨hd, hd', r ++ [_], r' ++ [_], hh, forall₂_append hr hx,
      (spineApp_append _ _ _).symm, (spineApp_append _ _ _).symm⟩

/-- A spine with an application at its head is not `K`. -/
theorem spineApp_app_ne_K (f x : Term) : ∀ r, spineApp (f ⬝ x) r ≠ K
  | [] => fun h => Term.noConfusion h
  | a :: r => spineApp_app_ne_K (f ⬝ x) a r

/-- **The simulation.**  If `t` head-reduces to `K` in fewer than `b` steps,
    every `t'` related to it at `b` head-reduces to `K`. -/
theorem sim_fuel : ∀ (fuel n : Nat) {t t' : Term} {b : Nat}, n ≤ fuel →
    Rel b t t' → StepsN n t K → n < b → Steps t' K := by
  intro fuel
  induction fuel with
  | zero =>
    intro n t t' b hf hrel hn _
    obtain rfl : n = 0 := by omega
    cases hn
    obtain ⟨hd, hd', r, r', hh, hr, he, rfl⟩ := hrel.spine
    cases hh with
    | leaf hl =>
      rcases hl with rfl | rfl | rfl
      · cases hr with
        | nil => exact absurd he (fun h => Term.noConfusion h)
        | cons _ hr => exact absurd he.symm (spineApp_app_ne_K _ _ _)
      · cases hr with
        | nil => exact .refl _
        | cons _ hr => exact absurd he.symm (spineApp_app_ne_K _ _ _)
      · cases hr with
        | nil => exact absurd he (fun h => Term.noConfusion h)
        | cons _ hr => exact absurd he.symm (spineApp_app_ne_K _ _ _)
    | omega hz hm => exact absurd he.symm (spineApp_app_ne_K _ _ _)
  | succ fuel ihf =>
  have ih : ∀ m, m < fuel + 1 → ∀ {t t' : Term} {b : Nat}, Rel b t t' → StepsN m t K → m < b → Steps t' K :=
    fun m hm _ _ _ hr hs hb => ihf m (by omega) hr hs hb
  intro n t t' b hf hrel hn hb
  obtain ⟨hd, hd', r, r', hh, hr, rfl, rfl⟩ := hrel.spine
  cases hh with
  | leaf hl =>
    rcases hl with rfl | rfl | rfl
    · -- `S`
      cases hr with
      | nil => exact absurd (stepsN_K_whnf hn .S) (fun h => Term.noConfusion h)
      | cons ha hr =>
        cases hr with
        | nil => exact absurd (stepsN_K_whnf hn (.S1 _)) (fun h => Term.noConfusion h)
        | cons hb' hr =>
          cases hr with
          | nil => exact absurd (stepsN_K_whnf hn (.S2 _ _)) (fun h => Term.noConfusion h)
          | cons hc hrest =>
            obtain ⟨m, rfl, hm⟩ := stepsN_after hn .K (step_spine (.S _ _ _) _)
            exact .step (step_spine (.S _ _ _) _)
              (ih m (by omega) (rel_spineApp (.app (.app ha hc) (.app hb' hc)) hrest) hm (by omega))
    · -- `K`
      cases hr with
      | nil => exact .refl _
      | cons ha hr =>
        cases hr with
        | nil => exact absurd (stepsN_K_whnf hn (.K1 _)) (fun h => Term.noConfusion h)
        | cons _ hrest =>
          obtain ⟨m, rfl, hm⟩ := stepsN_after hn .K (step_spine (.K _ _) _)
          exact .step (step_spine (.K _ _) _) (ih m (by omega) (rel_spineApp ha hrest) hm (by omega))
    · -- `I`
      cases hr with
      | nil => exact absurd (stepsN_K_whnf hn .I) (fun h => Term.noConfusion h)
      | cons ha hrest =>
        obtain ⟨m, rfl, hm⟩ := stepsN_after hn .K (step_spine (.I _) _)
        exact .step (step_spine (.I _) _) (ih m (by omega) (rel_spineApp ha hrest) hm (by omega))
  | @omega z hz m hm =>
    cases hr with
    | nil =>
      obtain ⟨w, hw⟩ := omega_whnf0 hz
      exact absurd (steps_whnf_det hn.steps .K hw (.K1 w)) (fun h => Term.noConfusion h)
    | cons ha hr =>
      cases hr with
      | nil =>
        obtain ⟨w, hw⟩ := omega_whnf1 hz _
        exact absurd (steps_whnf_det hn.steps .K hw (.S2 I w)) (fun h => Term.noConfusion h)
      | cons hs hrest =>
        rename_i a a' s s' rest rest'
        obtain ⟨h1, h2⟩ := omega_steps hz a s
        obtain ⟨n', hn', hrun⟩ := stepsN_through_lt hn .K (step_spine h1 rest) (steps_spine h2 rest)
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hnum : Steps (spineApp (num (k + 1)) (a' :: s' :: rest'))
            (spineApp (s' ⬝ (K ⬝ num k ⬝ s')) rest') := steps_spine (succS_steps _ _ _) rest'
        have hrel : Rel (b - 1) (spineApp (s ⬝ (K ⬝ omegaT (I ⬝ z) ⬝ s)) rest)
            (spineApp (s' ⬝ (K ⬝ num k ⬝ s')) rest') :=
          rel_spineApp (.app (hs.mono (Nat.sub_le _ _))
              (.app (.app (.refl K) (.omega (.step (.I _) hz) (by omega))) (hs.mono (Nat.sub_le _ _))))
            (forall₂_mono (Nat.sub_le _ _) hrest)
        exact hnum.trans (ih n' (by omega) hrel hrun (by omega))

theorem sim (n : Nat) {t t' : Term} {b : Nat} (hrel : Rel b t t') (hn : StepsN n t K) (hb : n < b) :
    Steps t' K :=
  sim_fuel n n (Nat.le_refl _) hrel hn hb

-- ---------------------------------------------------------------------------
-- Booleans
-- ---------------------------------------------------------------------------

/-- `true` is `K`, `false` is `K I`. -/
def boolT : Bool → Term
  | true => K
  | false => K ⬝ I

theorem K_wsteps {u : Term} (h : WSteps K u) : u = K := by
  cases h with
  | refl => rfl
  | step h _ => cases h

/-- Nothing reduces to both `K` and `K I`. -/
theorem K_KI_disjoint {t : Term} (h1 : WSteps t K) (h2 : WSteps t (K ⬝ I)) : False := by
  obtain ⟨w, hw1, hw2⟩ := church_rosser h1 h2
  rw [K_wsteps hw1] at hw2
  exact Compose.F_not_K hw2

theorem bool_disjoint {t : Term} (h1 : WSteps t (boolT false)) (h2 : WSteps t (boolT true)) : False :=
  K_KI_disjoint h2 h1

/-- A weak reduction to `K` is a head reduction to `K`. -/
theorem steps_of_wsteps_K {t : Term} (h : WSteps t K) : Steps t K :=
  (Compose.eval_K_iff.2 h).1

-- ---------------------------------------------------------------------------
-- Weak behaviour of numerals and of the infinite numeral
-- ---------------------------------------------------------------------------

theorem succS_wsteps (x z s : Term) : WSteps (succS ⬝ x ⬝ z ⬝ s) (s ⬝ x) :=
  (succS_steps x z s).weak.trans (WSteps.right s (.single (.K x s)))

theorem omega_wsteps {z : Term} (hz : Steps z (fixB succS)) (a s : Term) :
    WSteps (omegaT z ⬝ a ⬝ s) (s ⬝ omegaT (I ⬝ z)) := by
  obtain ⟨h1, h2⟩ := omega_steps hz a s
  exact (Steps.step h1 h2).weak.trans (WSteps.right s (.single (.K _ s)))

-- ---------------------------------------------------------------------------
-- `G c n`: is `n > c`?
-- ---------------------------------------------------------------------------

/-- `λ c'. g c' n'`, over `g` (0), `n'` (3), `c'` (4). -/
def gIn2 : OTerm := absN [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 3)

/-- `λ n'. c true (λ c'. g c' n')`, over `g` (0), `c` (1), `n'` (3). -/
def gIn1 : OTerm := absN [3] (.var 1 ⬝ₒ .K ⬝ₒ gIn2)

/-- The step function's body, over `g` (0), `c` (1), `n` (2):
    `n false (λ n'. c true (λ c'. g c' n'))`. -/
def gBody : OTerm := .var 2 ⬝ₒ (K ⬝ I).toO ⬝ₒ gIn1

def gStep : Term := toTerm (absN [0, 1, 2] gBody)

/-- **`G`**, the fixpoint of `gStep`. -/
def G : Term := fixSelf gStep (fixB gStep)

theorem G_unroll : WSteps G (gStep ⬝ G) := by
  have h := (fixSelf_unroll (F := gStep) (Steps.refl (fixB gStep))).weak
  have hI : WSteps (fixSelf gStep (I ⬝ fixB gStep)) G := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem G_zero (c : Term) : WSteps (G ⬝ c ⬝ num 0) (boolT false) := by
  have h := absN_beta_close [0, 1, 2] gBody (fun _ => K) [G, c, num 0] rfl
  simp only [gBody, OTerm.close, close_toO] at h
  exact ((WSteps.left _ (WSteps.left _ G_unroll)).trans h).trans (.single (.K _ _))

/-- `G c (k+1)` asks `c`, and on a successor recurses with `k`. -/
theorem G_succ (c : Term) (k : Nat) : ∃ X, WSteps (G ⬝ c ⬝ num (k + 1)) (c ⬝ K ⬝ X) ∧
    ∀ c', WSteps (X ⬝ c') (G ⬝ c' ⬝ num k) := by
  have h := absN_beta_close [0, 1, 2] gBody (fun _ => K) [G, c, num (k + 1)] rfl
  simp only [gBody, OTerm.close, close_toO] at h
  let σ := overrideC (fun _ => K) [0, 1, 2] [G, c, num (k + 1)]
  have h1 := absN_beta_close [3] (.var 1 ⬝ₒ .K ⬝ₒ gIn2) σ [num k] rfl
  simp only [OTerm.close] at h1
  refine ⟨gIn2.close (overrideC σ [3] [num k]), ?_, fun c' => ?_⟩
  · have h0 := (WSteps.left _ (WSteps.left _ G_unroll)).trans h
    have hs := succS_wsteps (num k) (K ⬝ I) (gIn1.close σ)
    exact (h0.trans hs).trans h1
  · have h2 := absN_beta_close [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 3) (overrideC σ [3] [num k]) [c'] rfl
    simp only [OTerm.close] at h2
    exact h2

/-- `G` on numerals decides `j < n`. -/
theorem G_num : ∀ (n j : Nat), WSteps (G ⬝ num j ⬝ num n) (boolT (decide (j < n)))
  | 0, j => by simpa using G_zero (num j)
  | n + 1, 0 => by
    obtain ⟨X, hX, _⟩ := G_succ (num 0) n
    simpa [boolT] using hX.trans (.single (.K _ _))
  | n + 1, j + 1 => by
    obtain ⟨X, hX, hrec⟩ := G_succ (num (j + 1)) n
    have h := (hX.trans (succS_wsteps (num j) K X)).trans ((hrec (num j)).trans (G_num n j))
    simpa [Nat.add_lt_add_iff_right] using h

/-- `G` on the infinite numeral is constantly false. -/
theorem G_omega : ∀ (n : Nat) {z : Term}, Steps z (fixB succS) →
    WSteps (G ⬝ omegaT z ⬝ num n) (boolT false)
  | 0, _, _ => G_zero _
  | n + 1, z, hz => by
    obtain ⟨X, hX, hrec⟩ := G_succ (omegaT z) n
    exact (hX.trans (omega_wsteps hz K X)).trans
      ((hrec _).trans (G_omega n (.step (.I _) hz)))

-- ---------------------------------------------------------------------------
-- Equality with a fixed code
-- ---------------------------------------------------------------------------

/-- `λ _ _. false`. -/
def kkF : Term := K ⬝ (K ⬝ (K ⬝ I))

theorem kkF_wsteps (a b : Term) : WSteps (kkF ⬝ a ⬝ b) (K ⬝ I) :=
  (WSteps.left b (.single (.K _ a))).trans (.single (.K _ b))

/-- **`eqT c`**: is the code `⟨c⟩`?  By recursion on `c`, over the code's
    four continuations (`S`, `K`, `I`, `App`). -/
def eqT : Term → Term
  | .S => toTerm (absN [0] (.var 0 ⬝ₒ .K ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ kkF.toO))
  | .K => toTerm (absN [0] (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ .K ⬝ₒ (K ⬝ I).toO ⬝ₒ kkF.toO))
  | .I => toTerm (absN [0] (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ .K ⬝ₒ kkF.toO))
  | .app f x => toTerm (absN [0] (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ
      absN [1, 2] ((eqT f).toO ⬝ₒ .var 1 ⬝ₒ ((eqT x).toO ⬝ₒ .var 2) ⬝ₒ (K ⬝ I).toO)))

theorem and_wsteps (b : Bool) (q : Term) :
    WSteps (boolT b ⬝ q ⬝ (K ⬝ I)) (if b then q else K ⬝ I) := by
  cases b with
  | true => exact .single (.K _ _)
  | false => exact (WSteps.left _ (.single (.K _ _))).trans (.single (.I _))

/-- **`eqT_spec`**: `eqT c ⟨d⟩ ↠ true` exactly when `c = d`. -/
theorem eqT_spec : ∀ c d : Term, WSteps (eqT c ⬝ quoteT d) (boolT (decide (c = d))) := by
  intro c
  induction c with
  | S =>
    intro d
    have h := absN_beta_close [0] (.var 0 ⬝ₒ .K ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ kkF.toO)
      (fun _ => K) [quoteT d] rfl
    simp only [OTerm.close, close_toO] at h
    refine h.trans ?_
    cases d with
    | S => exact Requote.quoteS_elim _ _ _ _
    | K => exact Requote.quoteK_elim _ _ _ _
    | I => exact Requote.quoteI_elim _ _ _ _
    | app f x => exact (Requote.quoteApp_elim f x _ _ _ _).trans (kkF_wsteps _ _)
  | K =>
    intro d
    have h := absN_beta_close [0] (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ .K ⬝ₒ (K ⬝ I).toO ⬝ₒ kkF.toO)
      (fun _ => K) [quoteT d] rfl
    simp only [OTerm.close, close_toO] at h
    refine h.trans ?_
    cases d with
    | S => exact Requote.quoteS_elim _ _ _ _
    | K => exact Requote.quoteK_elim _ _ _ _
    | I => exact Requote.quoteI_elim _ _ _ _
    | app f x => exact (Requote.quoteApp_elim f x _ _ _ _).trans (kkF_wsteps _ _)
  | I =>
    intro d
    have h := absN_beta_close [0] (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ .K ⬝ₒ kkF.toO)
      (fun _ => K) [quoteT d] rfl
    simp only [OTerm.close, close_toO] at h
    refine h.trans ?_
    cases d with
    | S => exact Requote.quoteS_elim _ _ _ _
    | K => exact Requote.quoteK_elim _ _ _ _
    | I => exact Requote.quoteI_elim _ _ _ _
    | app f x => exact (Requote.quoteApp_elim f x _ _ _ _).trans (kkF_wsteps _ _)
  | app f x ihf ihx =>
    intro d
    let inner : OTerm := absN [1, 2] ((eqT f).toO ⬝ₒ .var 1 ⬝ₒ ((eqT x).toO ⬝ₒ .var 2) ⬝ₒ (K ⬝ I).toO)
    have h := absN_beta_close [0] (.var 0 ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ (K ⬝ I).toO ⬝ₒ inner)
      (fun _ => K) [quoteT d] rfl
    simp only [OTerm.close, close_toO] at h
    refine h.trans ?_
    cases d with
    | S => exact Requote.quoteS_elim _ _ _ _
    | K => exact Requote.quoteK_elim _ _ _ _
    | I => exact Requote.quoteI_elim _ _ _ _
    | app f' x' =>
      refine (Requote.quoteApp_elim f' x' _ _ _ _).trans ?_
      have h2 := absN_beta_close [1, 2] ((eqT f).toO ⬝ₒ .var 1 ⬝ₒ ((eqT x).toO ⬝ₒ .var 2) ⬝ₒ (K ⬝ I).toO)
        (overrideC (fun _ => K) [0] [quoteT (f' ⬝ x')]) [quoteT f', quoteT x'] rfl
      simp only [OTerm.close, close_toO] at h2
      refine h2.trans ?_
      refine ((WSteps.left (K ⬝ I) (WSteps.app (ihf f') (ihx x'))).trans (and_wsteps _ _)).trans ?_
      by_cases hf : f = f'
      · by_cases hx : x = x'
        · subst hf; subst hx; simpa using WSteps.refl _
        · subst hf; simpa [hx, boolT] using WSteps.refl _
      · simpa [hf, boolT] using WSteps.refl _

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- `f` is total on the numerals: a boolean at each. -/
def Total (f : Term) : Prop := ∀ n, ∃ b : Bool, WSteps (f ⬝ num n) (boolT b)

/-- `L` lifts at `Nat → Bool`: every total function gets a code whose term
    agrees with it on the numerals. -/
def LiftNB (L : Term) : Prop :=
  ∀ f, Total f → ∃ c, WSteps (L ⬝ f) (quoteT c) ∧
    ∀ (n : Nat) (b : Bool), WSteps (f ⬝ num n) (boolT b) → WSteps (c ⬝ num n) (boolT b)

theorem KI_wsteps {u : Term} (h : WSteps (K ⬝ I) u) : u = K ⬝ I := by
  cases h with
  | refl => rfl
  | step h _ =>
    cases h with
    | left _ h => cases h
    | right _ h => cases h

theorem bool_wsteps {b : Bool} {u : Term} (h : WSteps (boolT b) u) : u = boolT b := by
  cases b with
  | true => exact K_wsteps h
  | false => exact KI_wsteps h

/-- A reduct of something that reaches a boolean reaches that boolean. -/
theorem to_bool_of_join {t w : Term} {b : Bool} (ht : WSteps t (boolT b)) (hw : WSteps t w) :
    WSteps w (boolT b) := by
  obtain ⟨v, h1, h2⟩ := church_rosser ht hw
  rw [bool_wsteps h1] at h2
  exact h2

/-- `L` lifts at `Nat → Bool` up to conversion: `L f` and some code agreeing
    with `f` have a common reduct. -/
def LiftNBc (L : Term) : Prop :=
  ∀ f, Total f → ∃ c w, WSteps (L ⬝ f) w ∧ WSteps (quoteT c) w ∧
    ∀ (n : Nat) (b : Bool), WSteps (f ⬝ num n) (boolT b) → WSteps (c ⬝ num n) (boolT b)

/-- `eqT c` on a term convertible with `⟨d⟩`. -/
theorem eqT_conv {c d w x : Term} (hx : WSteps x w) (hd : WSteps (quoteT d) w) :
    WSteps (eqT c ⬝ x) (boolT (decide (c = d))) :=
  (WSteps.right _ hx).trans
    (to_bool_of_join (eqT_spec c d) (WSteps.right _ hd))

/-- **No behavioural lift at `Nat → Bool`, up to conversion.** -/
theorem no_lift_conv (L : Term) : ¬ LiftNBc L := by
  intro hL
  have hf : Total (G ⬝ omega0) := fun n => ⟨false, G_omega n (.refl _)⟩
  obtain ⟨c, w, hw, hcw, hag⟩ := hL _ hf
  have h1 : WSteps (eqT c ⬝ (L ⬝ (G ⬝ omega0))) K := by
    simpa [boolT] using eqT_conv (c := c) hw hcw
  obtain ⟨n, hn⟩ := counted (steps_of_wsteps_K h1)
  have hrel : Rel (n + 1) (eqT c ⬝ (L ⬝ (G ⬝ omega0))) (eqT c ⬝ (L ⬝ (G ⬝ num (n + 1)))) :=
    .app (.refl _) (.app (.refl _) (.app (.refl _) (.omega (.refl _) (Nat.le_refl _))))
  have h2 := (sim n hrel hn (Nat.lt_succ_self n)).weak
  have hg : Total (G ⬝ num (n + 1)) := fun m => ⟨_, G_num m (n + 1)⟩
  obtain ⟨c', w', hw', hcw', hag'⟩ := hL _ hg
  have h3 := eqT_conv (c := c) hw' hcw'
  have hcc : c = c' := by
    by_cases hne : c = c'
    · exact hne
    · simp [hne, boolT] at h3; exact (K_KI_disjoint h2 h3).elim
  subst hcc
  have e1 := hag (n + 2) false (G_omega (n + 2) (.refl _))
  have e2 := hag' (n + 2) true (by simpa using G_num (n + 2) (n + 1))
  exact bool_disjoint e1 e2

/-- **No behavioural lift at `Nat → Bool`** (the code reached by reduction). -/
theorem no_lift (L : Term) : ¬ LiftNB L := fun hL =>
  no_lift_conv L fun f hf =>
    let ⟨c, hc, hag⟩ := hL f hf
    ⟨c, quoteT c, hc, .refl _, hag⟩

end NoLift
