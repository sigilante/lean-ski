import Ski.InfNF
import Ski.Fuel
open Term

/-!
# The word problem for S: the floor theorems (S3, phase 1)

**The problem.**  Is convertibility of closed S-terms decidable?  Open since Barendregt
(1975, LNCS 37); RTA open problem #97.  Waldmann (2000, "The combinator S", Inf. & Comput. 159,
§5) conjectures that it is, and names the route: limits of reductions.  Smullyan's *Dance of the
Starlings* asks it as Question 30, and as Question 31 asks whether two S-terms with the same
(infinite) normal form are convertible.  This module calls the latter statement `Lock1`; it is
*not* proved here.  What is proved is what holds around it.

`Conv` is the equivalence closure of weak reduction; by Church–Rosser (`Weak.church_rosser`) it
is joinability (`conv_iff_join`).  `InfEq t u` says `t^∞ = u^∞`: the two terms have the same
prefix (`InfNF.NF`) at every depth.

* (a) `infEq_of_conv`: convertible pure terms have equal `t^∞` (the free direction).
* (b) `lock1_normalizing`: if `t` normalizes and `t^∞ = u^∞`, then `u` reduces to the same normal
  form, so `Conv t u`.  Lock 1 holds whenever one side normalizes.
* (c) `pre n d t`: a computable, fuel-indexed function for the depth-`d` prefix of `t^∞`.  It is
  sound (`pre_sound`), monotone in fuel (`pre_mono`), total (`pre_total`: some fuel suffices,
  constructively from `TopTerm.reach_all`) and so agrees with `NF` (`pre_iff`).
  `joinWithin` and `prefixDiffer` are Boolean searches:
  - `conv_iff_joinWithin`: `Conv t u ↔ ∃ n, joinWithin n t u = true` (all terms, no hypothesis);
  - `not_conv_of_differ`: `prefixDiffer k t u = true` refutes `Conv t u` (pure terms);
  - `lock1_conv_iff`: under `Lock1`, `Conv t u ↔ ∀ k, prefixDiffer k t u = false`, so
    convertibility is both an `∃` and a `∀` over a computable Boolean;
  - `lock1_not_conv_iff`: under `Lock1`, `¬ Conv t u ↔ ¬¬ ∃ k, prefixDiffer k t u = true`.
  Removing that double negation is an instance of Markov's principle for the search; no proof without it is known.  It is not assumed: it
  appears as the explicit hypothesis `MP` in `lock1_mp_not_conv_iff` and `lock1_mp_decides`
  (the interleaved search halts, so `Conv t u ∨ ¬ Conv t u`).  The form `Lock1Sep` (inconvertible
  terms have a differing prefix), classically the same as `Lock1`, gives
  `¬ Conv t u ↔ ∃ k, prefixDiffer k t u = true` with no `MP` (`lock1Sep_not_conv_iff`).
* (d) `infEq_hnf`, `hnf_decomp`: if `t^∞ = u^∞` and both have head normal forms `S a⃗`, `S b⃗`,
  then the two have the same length and `aᵢ^∞ = bᵢ^∞`; `conv_of_children`: if the `aᵢ`, `bᵢ` are
  pairwise convertible then so are `t`, `u`.  `lock1_hnf_children` combines them: Lock 1 at the
  children gives Lock 1 at the parents.  The recursion this suggests need not end (productive
  terms), so this is a reduction step and not a proof.

Everything here is constructive: the axiom gate (`Ski/Audit.lean`) admits `propext` and
`Quot.sound` only.
-/

namespace WordProblem
open HnfS HnfSound InfNF TopTerm

/-! ## Conversion -/

/-- Convertibility: the equivalence closure of weak reduction. -/
inductive Conv : Term → Term → Prop
  | refl (t : Term) : Conv t t
  | step {t u : Term} : WStep t u → Conv t u
  | symm {t u : Term} : Conv t u → Conv u t
  | trans {t u v : Term} : Conv t u → Conv u v → Conv t v

theorem Conv.of_wsteps {t u : Term} (h : WSteps t u) : Conv t u := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .trans (.step s) ih

/-- **Church–Rosser, in its conversion form.**  Convertible terms have a common reduct. -/
theorem conv_iff_join {t u : Term} : Conv t u ↔ ∃ w, WSteps t w ∧ WSteps u w := by
  constructor
  · intro h
    induction h with
    | refl t => exact ⟨t, .refl _, .refl _⟩
    | step s => exact ⟨_, .single s, .refl _⟩
    | symm _ ih => obtain ⟨w, h1, h2⟩ := ih; exact ⟨w, h2, h1⟩
    | trans _ _ ih1 ih2 =>
      obtain ⟨w1, a, b⟩ := ih1
      obtain ⟨w2, c, d⟩ := ih2
      obtain ⟨w, e, f⟩ := church_rosser b c
      exact ⟨w, a.trans e, d.trans f⟩
  · rintro ⟨w, h1, h2⟩
    exact .trans (.of_wsteps h1) (.symm (.of_wsteps h2))

theorem Conv.appL {f g : Term} (x : Term) (h : Conv f g) : Conv (f ⬝ x) (g ⬝ x) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.left x s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem Conv.appR (f : Term) {x y : Term} (h : Conv x y) : Conv (f ⬝ x) (f ⬝ y) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.right f s)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

theorem Conv.app {f g x y : Term} (h1 : Conv f g) (h2 : Conv x y) : Conv (f ⬝ x) (g ⬝ y) :=
  .trans (.appL x h1) (.appR g h2)

/-! ## Equality of infinitary normal forms -/

/-- `t^∞ = u^∞`: the same prefix at every depth. -/
def InfEq (t u : Term) : Prop := ∀ d P, NF d t P ↔ NF d u P

/-- `t^∞ ≠ u^∞`, positively: at some depth the prefixes differ. -/
def InfApart (t u : Term) : Prop := ∃ d P Q, NF d t P ∧ NF d u Q ∧ P ≠ Q

/-- **Lock 1** (*Dance of the Starlings*, Question 31, for `t^∞`): equal infinitary normal forms
imply convertibility.  Open. -/
def Lock1 : Prop := ∀ t u, PureS t → PureS u → InfEq t u → Conv t u

theorem InfEq.refl (t : Term) : InfEq t t := fun _ _ => Iff.rfl

theorem InfEq.symm {t u : Term} (h : InfEq t u) : InfEq u t := fun d P => (h d P).symm

theorem InfEq.trans {t u v : Term} (h1 : InfEq t u) (h2 : InfEq u v) : InfEq t v :=
  fun d P => (h1 d P).trans (h2 d P)

/-- For pure terms one inclusion is enough: prefixes exist and are unique. -/
theorem infEq_of_imp {t u : Term} (ht : PureS t) (hu : PureS u)
    (h : ∀ d P, NF d t P → NF d u P) : InfEq t u := by
  intro d P
  refine ⟨h d P, fun hP => ?_⟩
  obtain ⟨Q, hQ⟩ := nf_exists d ht
  rw [nf_unique hu hP (h d Q hQ)]
  exact hQ

/-- For pure terms, `t^∞ = u^∞` iff at each depth some prefix is common. -/
theorem infEq_iff_common {t u : Term} (ht : PureS t) (hu : PureS u) :
    InfEq t u ↔ ∀ d, ∃ P, NF d t P ∧ NF d u P := by
  constructor
  · intro h d
    obtain ⟨P, hP⟩ := nf_exists d ht
    exact ⟨P, hP, (h d P).mp hP⟩
  · intro h
    refine infEq_of_imp ht hu fun d P hP => ?_
    obtain ⟨Q, h1, h2⟩ := h d
    rw [nf_unique ht hP h1]
    exact h2

theorem infApart_not_infEq {t u : Term} (hu : PureS u) (h : InfApart t u) : ¬ InfEq t u := by
  obtain ⟨d, P, Q, hP, hQ, hne⟩ := h
  intro e
  exact hne (nf_unique hu ((e d P).mp hP) hQ)

/-- For pure terms, equality of `t^∞` is the negation of apartness (prefixes are decidable
data). -/
theorem infEq_iff_not_apart {t u : Term} (ht : PureS t) (hu : PureS u) :
    InfEq t u ↔ ¬ InfApart t u := by
  constructor
  · exact fun e a => infApart_not_infEq hu a e
  · intro hn
    refine infEq_of_imp ht hu fun d P hP => ?_
    obtain ⟨Q, hQ⟩ := nf_exists d hu
    if e : P = Q then exact e ▸ hQ
    else exact absurd ⟨d, P, Q, hP, hQ, e⟩ hn

/-! ## (a) The free direction -/

theorem infEq_of_wsteps {t u : Term} (ht : PureS t) (h : WSteps t u) : InfEq t u :=
  fun _ _ => ⟨fun hP => nf_wsteps ht hP h, fun hP => nf_wsteps_back ht h hP⟩

/-- **Convertible pure terms have the same infinitary normal form.** -/
theorem infEq_of_conv {t u : Term} (ht : PureS t) (hu : PureS u) (h : Conv t u) : InfEq t u := by
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  exact (infEq_of_wsteps ht h1).trans (infEq_of_wsteps hu h2).symm

/-! ## (b) Lock 1 for normalizing terms -/

/-- A full cut determines the term. -/
theorem cut_inj : ∀ {d : Nat} {a b : Term}, (cut d a).full = true → cut d a = cut d b → a = b := by
  intro d
  induction d with
  | zero => intro a b h _; simp [cut, PT.full] at h
  | succ d ih =>
    intro a b h e
    cases a with
    | S =>
      cases b with
      | S => rfl
      | K => simp [cut] at e
      | I => simp [cut] at e
      | app _ _ => simp [cut] at e
    | K => simp [cut, PT.full] at h
    | I => simp [cut, PT.full] at h
    | app l r =>
      simp only [cut, PT.full, Bool.and_eq_true] at h
      cases b with
      | S => simp [cut] at e
      | K => simp [cut] at e
      | I => simp [cut] at e
      | app l' r' =>
        simp only [cut] at e
        injection e with e1 e2
        rw [ih h.1 e1, ih h.2 e2]

/-- **Lock 1 when one side normalizes.**  If `t` has the normal form `n` and `t^∞ = u^∞`, then
`u` reduces to `n` too, and `t`, `u` are convertible. -/
theorem lock1_normalizing {t u n : Term} (ht : PureS t) (hn : WSteps t n) (hN : Normal n)
    (h : InfEq t u) : WSteps u n ∧ Conv t u := by
  have hnp := (fold_wsteps hn ht).1
  have h1 : NF (height n) u (cut (height n) n) :=
    (h _ _).mp (nf_wsteps_back ht hn (nf_normal _ hnp hN))
  obtain ⟨m, hm, hc⟩ := nf_approx h1
  have e : n = m := cut_inj (cut_full hnp _ (Nat.le_refl _)) hc.symm
  subst e
  exact ⟨hm, conv_iff_join.mpr ⟨n, hn, hm⟩⟩

/-! ## (c) A computable prefix function -/

def isHnfB : Term → Bool
  | .S => true
  | .app .S _ => true
  | .app (.app .S _) _ => true
  | _ => false

theorem isHnfB_iff {t : Term} : isHnfB t = true ↔ IsHnf t := by
  constructor
  · intro h
    unfold isHnfB at h
    split at h
    · exact .inl rfl
    · exact .inr (.inl ⟨_, rfl⟩)
    · exact .inr (.inr ⟨_, _, rfl⟩)
    · cases h
  · rintro (rfl | ⟨x, rfl⟩ | ⟨x, y, rfl⟩) <;> rfl

/-- The Boolean form of `InfNF.Stable`. -/
def stableB (f w : Term) : Bool := fold f == 36 || isHnfB (f ⬝ w)

theorem stableB_iff {f w : Term} : stableB f w = true ↔ Stable f w := by
  unfold stableB Stable
  rw [Bool.or_eq_true, beq_iff_eq, isHnfB_iff]

def mkApp : Option PT → Option PT → Option PT
  | some a, some b => some (.app a b)
  | _, _ => none

theorem mkApp_some {x y : Option PT} {P : PT} (h : mkApp x y = some P) :
    ∃ a b, x = some a ∧ y = some b ∧ P = .app a b := by
  cases x with
  | none => cases h
  | some a =>
    cases y with
    | none => cases h
    | some b => injection h with h; exact ⟨a, b, rfl, rfl, h.symm⟩

/-- **The depth-`d` prefix of `t^∞`, with fuel `n`.**  Head-reduce until the root is stable,
then recurse into both parts one level down.  Each head step and each level costs one unit. -/
def pre : Nat → Nat → Term → Option PT
  | _, 0, _ => some .hole
  | _, _ + 1, .S => some .S
  | n + 1, d + 1, .app f w =>
    if stableB f w then mkApp (pre n d f) (pre n d w)
    else
      match step? (f ⬝ w) with
      | some t' => pre n (d + 1) t'
      | none => none
  | _, _, _ => none

theorem pre_zero (n : Nat) (t : Term) : pre n 0 t = some .hole := by
  cases n <;> rfl

theorem pre_S (n d : Nat) : pre n (d + 1) S = some .S := by
  cases n <;> rfl

theorem pre_app (n d : Nat) (f w : Term) : pre (n + 1) (d + 1) (f ⬝ w) =
    if stableB f w then mkApp (pre n d f) (pre n d w)
    else
      match step? (f ⬝ w) with
      | some t' => pre n (d + 1) t'
      | none => none := rfl

theorem pre_K (n d : Nat) : pre n (d + 1) K = none := by
  cases n <;> rfl

theorem pre_I (n d : Nat) : pre n (d + 1) I = none := by
  cases n <;> rfl

theorem pre_app_zero (d : Nat) (f w : Term) : pre 0 (d + 1) (f ⬝ w) = none := rfl

/-- Soundness: what `pre` returns is a prefix of `t^∞`. -/
theorem pre_sound : ∀ {n d : Nat} {t : Term} {P : PT}, PureS t → pre n d t = some P → NF d t P := by
  intro n
  induction n with
  | zero =>
    intro d t P ht h
    cases d with
    | zero => rw [pre_zero] at h; injection h with h; subst h; exact .zero t
    | succ d =>
      cases ht with
      | S => rw [pre_S] at h; injection h with h; subst h; exact .leaf d
      | app _ _ => rw [pre_app_zero] at h; cases h
  | succ n ih =>
    intro d t P ht h
    cases d with
    | zero => rw [pre_zero] at h; injection h with h; subst h; exact .zero t
    | succ d =>
      cases ht with
      | S => rw [pre_S] at h; injection h with h; subst h; exact .leaf d
      | @app f w hf hw =>
        rw [pre_app] at h
        cases hst : stableB f w with
        | true =>
          rw [hst, if_pos rfl] at h
          obtain ⟨a, b, h1, h2, rfl⟩ := mkApp_some h
          exact .node (.refl _) (stableB_iff.mp hst) (ih hf h1) (ih hw h2)
        | false =>
          rw [hst, if_neg Bool.false_ne_true] at h
          cases hs : step? (f ⬝ w) with
          | none => rw [hs] at h; cases h
          | some t' =>
            rw [hs] at h
            have s := step?_sound hs
            have hp := PureS.app hf hw
            exact nf_bwd hp (.single s) (ih (wstep_pure s.weak hp).1 h)

/-- More fuel does not change the answer. -/
theorem pre_mono : ∀ {n d : Nat} {t : Term} {P : PT}, pre n d t = some P →
    pre (n + 1) d t = some P := by
  intro n
  induction n with
  | zero =>
    intro d t P h
    cases d with
    | zero => rw [pre_zero] at h ⊢; exact h
    | succ d =>
      cases t with
      | S => rw [pre_S] at h ⊢; exact h
      | K => rw [pre_K] at h; cases h
      | I => rw [pre_I] at h; cases h
      | app f w => rw [pre_app_zero] at h; cases h
  | succ n ih =>
    intro d t P h
    cases d with
    | zero => rw [pre_zero] at h ⊢; exact h
    | succ d =>
      cases t with
      | S => rw [pre_S] at h ⊢; exact h
      | K => rw [pre_K] at h; cases h
      | I => rw [pre_I] at h; cases h
      | app f w =>
        rw [pre_app] at h ⊢
        cases hst : stableB f w with
        | true =>
          rw [hst] at h
          rw [if_pos rfl] at h ⊢
          obtain ⟨a, b, h1, h2, rfl⟩ := mkApp_some h
          rw [ih h1, ih h2]
          rfl
        | false =>
          rw [hst] at h
          rw [if_neg Bool.false_ne_true] at h ⊢
          cases hs : step? (f ⬝ w) with
          | none => rw [hs] at h; cases h
          | some t' =>
            rw [hs] at h
            exact ih h

theorem pre_mono_add {n d : Nat} {t : Term} {P : PT} (h : pre n d t = some P) (k : Nat) :
    pre (n + k) d t = some P := by
  induction k with
  | zero => exact h
  | succ k ih => exact pre_mono ih

theorem pre_mono_le {n m d : Nat} {t : Term} {P : PT} (h : pre n d t = some P) (hnm : n ≤ m) :
    pre m d t = some P := by
  have := pre_mono_add h (m - n)
  rwa [Nat.add_sub_cancel' hnm] at this

/-- A stable root: recurse into both parts. -/
theorem pre_stable {d : Nat} {f w : Term} (hst : stableB f w = true)
    (hf : ∃ n P, pre n d f = some P) (hw : ∃ n P, pre n d w = some P) :
    ∃ n P, pre n (d + 1) (f ⬝ w) = some P := by
  obtain ⟨n1, Pf, h1⟩ := hf
  obtain ⟨n2, Pw, h2⟩ := hw
  refine ⟨n1 + n2 + 1, .app Pf Pw, ?_⟩
  rw [pre_app, hst, if_pos rfl, pre_mono_le h1 (Nat.le_add_right n1 n2),
    pre_mono_le h2 (Nat.le_add_left n2 n1)]
  rfl

/-- **Totality.**  For every depth some fuel suffices.  Constructive: the fuel is read off the
derivation `TopTerm.reach_all` that the head path reaches a stable root. -/
theorem pre_total : ∀ (d : Nat) {t : Term}, PureS t → ∃ n P, pre n d t = some P := by
  intro d
  induction d with
  | zero => intro t _; exact ⟨0, .hole, pre_zero 0 t⟩
  | succ d ih =>
    intro t ht
    have hr := reach_all ht
    induction hr with
    | @hnf u hu =>
      cases ht with
      | S => exact ⟨0, .S, pre_S 0 d⟩
      | @app f w hf hw =>
        exact pre_stable (stableB_iff.mpr (.inr hu)) (ih hf) (ih hw)
    | @bot f w hf hb =>
      exact pre_stable (stableB_iff.mpr (.inl hb)) (ih hf) (ih ht.app_inv.2)
    | @step t t' s _ ih' =>
      cases ht with
      | S => cases s
      | @app f w hf hw =>
        cases hst : stableB f w with
        | true => exact pre_stable hst (ih hf) (ih hw)
        | false =>
          obtain ⟨n, P, h⟩ := ih' (wstep_pure s.weak (.app hf hw)).1
          refine ⟨n + 1, P, ?_⟩
          rw [pre_app, hst, if_neg Bool.false_ne_true, step?_complete s]
          exact h

/-- **`pre` computes `NF`.** -/
theorem pre_iff {d : Nat} {t : Term} {P : PT} (ht : PureS t) :
    NF d t P ↔ ∃ n, pre n d t = some P := by
  constructor
  · intro h
    obtain ⟨n, Q, hQ⟩ := pre_total d ht
    exact ⟨n, by rw [nf_unique ht h (pre_sound ht hQ)]; exact hQ⟩
  · rintro ⟨n, h⟩
    exact pre_sound ht h

/-! ## (c) Two searches -/

/-- The contraction at the root, if there is one. -/
def rootRed : Term → List Term
  | .app (.app (.app .S f) g) x => [f ⬝ x ⬝ (g ⬝ x)]
  | .app (.app .K x) _ => [x]
  | .app .I x => [x]
  | _ => []

/-- All one-step reducts. -/
def reducts : Term → List Term
  | .app f x => rootRed (f ⬝ x) ++ ((reducts f).map (· ⬝ x) ++ (reducts x).map (f ⬝ ·))
  | _ => []

theorem rootRed_sound {t u : Term} (h : u ∈ rootRed t) : WStep t u := by
  unfold rootRed at h
  split at h
  · rw [List.mem_singleton] at h; subst h; exact .S _ _ _
  · rw [List.mem_singleton] at h; subst h; exact .K _ _
  · rw [List.mem_singleton] at h; subst h; exact .I _
  · cases h

theorem mem_reducts : ∀ {t u : Term}, u ∈ reducts t ↔ WStep t u := by
  intro t u
  constructor
  · intro h
    induction t generalizing u with
    | S => cases h
    | K => cases h
    | I => cases h
    | app f x ihf ihx =>
      unfold reducts at h
      rw [List.mem_append, List.mem_append, List.mem_map, List.mem_map] at h
      rcases h with h | ⟨f', hf', rfl⟩ | ⟨x', hx', rfl⟩
      · exact rootRed_sound h
      · exact .left x (ihf hf')
      · exact .right f (ihx hx')
  · intro h
    induction h with
    | S f g x => unfold reducts; exact List.mem_append.mpr (.inl (List.mem_singleton.mpr rfl))
    | K x y => unfold reducts; exact List.mem_append.mpr (.inl (List.mem_singleton.mpr rfl))
    | I x => unfold reducts; exact List.mem_append.mpr (.inl (List.mem_singleton.mpr rfl))
    | @left f f' x _ ih =>
      unfold reducts
      exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨f', ih, rfl⟩))))
    | @right f x x' _ ih =>
      unfold reducts
      exact List.mem_append.mpr (.inr (List.mem_append.mpr (.inr (List.mem_map.mpr ⟨x', ih, rfl⟩))))

/-- All reducts within `n` steps. -/
def reachN : Nat → Term → List Term
  | 0, t => [t]
  | n + 1, t => t :: (reducts t).flatMap (reachN n)

theorem reachN_sound : ∀ {n : Nat} {t a : Term}, a ∈ reachN n t → WSteps t a := by
  intro n
  induction n with
  | zero => intro t a h; rw [reachN, List.mem_singleton] at h; subst h; exact .refl _
  | succ n ih =>
    intro t a h
    rw [reachN, List.mem_cons, List.mem_flatMap] at h
    rcases h with rfl | ⟨r, hr, ha⟩
    · exact .refl _
    · exact .step (mem_reducts.mp hr) (ih ha)

theorem reachN_self (n : Nat) (t : Term) : t ∈ reachN n t := by
  cases n with
  | zero => exact List.mem_singleton.mpr rfl
  | succ n => exact List.mem_cons_self

theorem reachN_succ : ∀ {n : Nat} {t a : Term}, a ∈ reachN n t → a ∈ reachN (n + 1) t := by
  intro n
  induction n with
  | zero => intro t a h; rw [reachN, List.mem_singleton] at h; subst h; exact reachN_self _ _
  | succ n ih =>
    intro t a h
    rw [reachN, List.mem_cons, List.mem_flatMap] at h
    rw [reachN, List.mem_cons, List.mem_flatMap]
    rcases h with rfl | ⟨r, hr, ha⟩
    · exact .inl rfl
    · exact .inr ⟨r, hr, ih ha⟩

theorem reachN_le {n m : Nat} {t a : Term} (h : a ∈ reachN n t) (hnm : n ≤ m) : a ∈ reachN m t := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact reachN_succ ih

theorem reachN_complete {t a : Term} (h : WSteps t a) : ∃ n, a ∈ reachN n t := by
  induction h with
  | refl t => exact ⟨0, reachN_self 0 t⟩
  | @step t t' a s _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [reachN, List.mem_cons, List.mem_flatMap]
    exact .inr ⟨t', mem_reducts.mpr s, hn⟩

/-- Do `t` and `u` have a common reduct within `n` steps each? -/
def joinWithin (n : Nat) (t u : Term) : Bool :=
  (reachN n t).any fun a => decide (a ∈ reachN n u)

theorem joinWithin_iff {n : Nat} {t u : Term} :
    joinWithin n t u = true ↔ ∃ a, a ∈ reachN n t ∧ a ∈ reachN n u := by
  unfold joinWithin
  rw [List.any_eq_true]
  constructor
  · rintro ⟨a, h1, h2⟩; exact ⟨a, h1, of_decide_eq_true h2⟩
  · rintro ⟨a, h1, h2⟩; exact ⟨a, h1, decide_eq_true h2⟩

/-- **Conversion is semi-decided by the join search.**  No hypothesis on the terms. -/
theorem conv_iff_joinWithin {t u : Term} : Conv t u ↔ ∃ n, joinWithin n t u = true := by
  constructor
  · intro h
    obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
    obtain ⟨n1, a1⟩ := reachN_complete h1
    obtain ⟨n2, a2⟩ := reachN_complete h2
    exact ⟨n1 + n2, joinWithin_iff.mpr
      ⟨w, reachN_le a1 (Nat.le_add_right n1 n2), reachN_le a2 (Nat.le_add_left n2 n1)⟩⟩
  · rintro ⟨n, h⟩
    obtain ⟨a, h1, h2⟩ := joinWithin_iff.mp h
    exact conv_iff_join.mpr ⟨a, reachN_sound h1, reachN_sound h2⟩

/-- With fuel `n`, both depth-`d` prefixes are computed and differ. -/
def prefixDifferAt (n d : Nat) (t u : Term) : Bool :=
  match pre n d t, pre n d u with
  | some P, some Q => decide (P ≠ Q)
  | _, _ => false

theorem prefixDifferAt_iff {n d : Nat} {t u : Term} :
    prefixDifferAt n d t u = true ↔ ∃ P Q, pre n d t = some P ∧ pre n d u = some Q ∧ P ≠ Q := by
  unfold prefixDifferAt
  constructor
  · intro h
    split at h
    · next P Q h1 h2 => exact ⟨P, Q, h1, h2, of_decide_eq_true h⟩
    · cases h
  · rintro ⟨P, Q, h1, h2, hne⟩
    rw [h1, h2]
    exact decide_eq_true hne

/-- With fuel `k`, the prefixes at some depth `≤ k` are computed and differ. -/
def prefixDiffer (k : Nat) (t u : Term) : Bool :=
  (List.range (k + 1)).any fun d => prefixDifferAt k d t u

/-- **Apartness of `t^∞`, `u^∞` is semi-decided by the prefix search.** -/
theorem differ_iff_apart {t u : Term} (ht : PureS t) (hu : PureS u) :
    (∃ k, prefixDiffer k t u = true) ↔ InfApart t u := by
  constructor
  · rintro ⟨k, h⟩
    unfold prefixDiffer at h
    rw [List.any_eq_true] at h
    obtain ⟨d, _, hd⟩ := h
    obtain ⟨P, Q, h1, h2, hne⟩ := prefixDifferAt_iff.mp hd
    exact ⟨d, P, Q, pre_sound ht h1, pre_sound hu h2, hne⟩
  · rintro ⟨d, P, Q, hP, hQ, hne⟩
    obtain ⟨n1, h1⟩ := (pre_iff ht).mp hP
    obtain ⟨n2, h2⟩ := (pre_iff hu).mp hQ
    refine ⟨n1 + n2 + d, ?_⟩
    unfold prefixDiffer
    rw [List.any_eq_true]
    refine ⟨d, List.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_left d _)), ?_⟩
    exact prefixDifferAt_iff.mpr ⟨P, Q,
      pre_mono_le h1 (Nat.le_trans (Nat.le_add_right n1 n2) (Nat.le_add_right _ d)),
      pre_mono_le h2 (Nat.le_trans (Nat.le_add_left n2 n1) (Nat.le_add_right _ d)), hne⟩

/-- **A differing prefix refutes conversion.**  No use of `Lock1`. -/
theorem not_conv_of_differ {t u : Term} (ht : PureS t) (hu : PureS u)
    (h : ∃ k, prefixDiffer k t u = true) : ¬ Conv t u :=
  fun hc => infApart_not_infEq hu ((differ_iff_apart ht hu).mp h) (infEq_of_conv ht hu hc)

/-- **Lock 1 makes conversion co-semi-decidable.**  Under `Lock1`, pure `t`, `u` are convertible
iff the prefix search never finds a difference. -/
theorem lock1_conv_iff (L : Lock1) {t u : Term} (ht : PureS t) (hu : PureS u) :
    Conv t u ↔ ∀ k, prefixDiffer k t u = false := by
  constructor
  · intro hc k
    cases h : prefixDiffer k t u with
    | false => rfl
    | true => exact absurd hc (not_conv_of_differ ht hu ⟨k, h⟩)
  · intro h
    refine L t u ht hu ((infEq_iff_not_apart ht hu).mpr fun a => ?_)
    obtain ⟨k, hk⟩ := (differ_iff_apart ht hu).mpr a
    rw [h k] at hk
    cases hk

/-- Under `Lock1`, inconvertibility is the double negation of "the prefix search succeeds". -/
theorem lock1_not_conv_iff (L : Lock1) {t u : Term} (ht : PureS t) (hu : PureS u) :
    ¬ Conv t u ↔ ¬¬ ∃ k, prefixDiffer k t u = true := by
  constructor
  · intro hn hne
    refine hn ((lock1_conv_iff L ht hu).mpr fun k => ?_)
    cases h : prefixDiffer k t u with
    | false => rfl
    | true => exact absurd ⟨k, h⟩ hne
  · exact fun hnn hc => hnn fun hd => not_conv_of_differ ht hu hd hc

/-- Lock 1 in separated form: inconvertible terms have a differing prefix.  Classically the
same statement as `Lock1`. -/
def Lock1Sep : Prop := ∀ t u, PureS t → PureS u → ¬ Conv t u → InfApart t u

/-- Under `Lock1Sep`, inconvertibility is semi-decided by the prefix search. -/
theorem lock1Sep_not_conv_iff (L : Lock1Sep) {t u : Term} (ht : PureS t) (hu : PureS u) :
    ¬ Conv t u ↔ ∃ k, prefixDiffer k t u = true :=
  ⟨fun hn => (differ_iff_apart ht hu).mpr (L t u ht hu hn), not_conv_of_differ ht hu⟩

/-- Markov's principle, as a hypothesis: an unbounded Boolean search that cannot fail halts. -/
def MP : Prop := ∀ f : Nat → Bool, ¬¬ (∃ n, f n = true) → ∃ n, f n = true

theorem lock1Sep_of_lock1 (mp : MP) (L : Lock1) : Lock1Sep := fun _ _ ht hu hn =>
  (differ_iff_apart ht hu).mp (mp _ ((lock1_not_conv_iff L ht hu).mp hn))

theorem lock1_of_lock1Sep (mp : MP) (L : Lock1Sep) : Lock1 := fun t u ht hu e =>
  conv_iff_joinWithin.mpr (mp _ fun hne =>
    infApart_not_infEq hu (L t u ht hu fun hc => hne (conv_iff_joinWithin.mp hc)) e)

/-- Under `Lock1` and Markov's principle, inconvertibility is semi-decided by the prefix
search. -/
theorem lock1_mp_not_conv_iff (mp : MP) (L : Lock1) {t u : Term} (ht : PureS t) (hu : PureS u) :
    ¬ Conv t u ↔ ∃ k, prefixDiffer k t u = true :=
  lock1Sep_not_conv_iff (lock1Sep_of_lock1 mp L) ht hu

/-- **Lock 1 ⟹ the word problem is decidable, given Markov's principle.**  The interleaved
search halts: for pure `t`, `u` some `k` finds a common reduct or a differing prefix. -/
theorem lock1_mp_decides (mp : MP) (L : Lock1) {t u : Term} (ht : PureS t) (hu : PureS u) :
    ∃ k, joinWithin k t u = true ∨ prefixDiffer k t u = true := by
  have key : ∃ k, (joinWithin k t u || prefixDiffer k t u) = true := by
    refine mp _ fun hne => ?_
    have h1 : ¬ Conv t u := fun hc => by
      obtain ⟨n, hn⟩ := conv_iff_joinWithin.mp hc
      exact hne ⟨n, by rw [hn]; rfl⟩
    refine (lock1_not_conv_iff L ht hu).mp h1 ?_
    rintro ⟨k, hk⟩
    exact hne ⟨k, by rw [hk, Bool.or_true]⟩
  obtain ⟨k, hk⟩ := key
  exact ⟨k, Bool.or_eq_true _ _ ▸ hk⟩

theorem lock1_mp_em (mp : MP) (L : Lock1) {t u : Term} (ht : PureS t) (hu : PureS u) :
    Conv t u ∨ ¬ Conv t u := by
  obtain ⟨k, h | h⟩ := lock1_mp_decides mp L ht hu
  · exact .inl (conv_iff_joinWithin.mpr ⟨k, h⟩)
  · exact .inr (not_conv_of_differ ht hu ⟨k, h⟩)

/-! ## (d) Head normal forms: Lock 1 reduces to the children -/

theorem nf_hnf_app {d : Nat} {f w : Term} {Pf Pw : PT} (hh : IsHnf (f ⬝ w)) (hf : NF d f Pf)
    (hw : NF d w Pw) : NF (d + 1) (f ⬝ w) (.app Pf Pw) :=
  .node (.refl _) (.inr hh) hf hw

theorem nf_hnf_app_inv {d : Nat} {f w : Term} {P : PT} (hh : IsHnf (f ⬝ w))
    (h : NF (d + 1) (f ⬝ w) P) : ∃ Pf Pw, P = .app Pf Pw ∧ NF d f Pf ∧ NF d w Pw := by
  cases h with
  | node hs _ hf hw =>
    have e := steps_from_hnf hh hs
    injection e with e1 e2
    subst e1 e2
    exact ⟨_, _, rfl, hf, hw⟩

theorem not_infEq_S_app {g x : Term} : ¬ InfEq S (g ⬝ x) := by
  intro e
  have h := (e 1 .S).mp (.leaf 0)
  cases h

/-- For head normal forms `f w`, `g x`: equal `^∞` gives equal `^∞` of both parts. -/
theorem infEq_hnf_app {f w g x : Term} (hp : PureS (f ⬝ w)) (hq : PureS (g ⬝ x))
    (hh : IsHnf (f ⬝ w)) (hk : IsHnf (g ⬝ x)) (e : InfEq (f ⬝ w) (g ⬝ x)) :
    InfEq f g ∧ InfEq w x := by
  have key : ∀ {f w g x : Term}, PureS (f ⬝ w) → IsHnf (f ⬝ w) → IsHnf (g ⬝ x) →
      InfEq (f ⬝ w) (g ⬝ x) → (∀ d P, NF d f P → NF d g P) ∧ (∀ d P, NF d w P → NF d x P) := by
    intro f w g x hp hh hk e
    constructor
    · intro d P hP
      obtain ⟨Pw, hw⟩ := nf_exists d hp.app_inv.2
      obtain ⟨Pf', Pw', e', h1, _⟩ := nf_hnf_app_inv hk ((e (d + 1) _).mp (nf_hnf_app hh hP hw))
      injection e' with e1 e2
      subst e1 e2
      exact h1
    · intro d P hP
      obtain ⟨Pf, hf⟩ := nf_exists d hp.app_inv.1
      obtain ⟨Pf', Pw', e', _, h2⟩ := nf_hnf_app_inv hk ((e (d + 1) _).mp (nf_hnf_app hh hf hP))
      injection e' with e1 e2
      subst e1 e2
      exact h2
  have k1 := key hp hh hk e
  have k2 := key hq hk hh e.symm
  exact ⟨fun d P => ⟨k1.1 d P, k2.1 d P⟩, fun d P => ⟨k1.2 d P, k2.2 d P⟩⟩

/-- Two head normal forms of the same length whose arguments are pairwise `R`-related. -/
inductive HnfMatch (R : Term → Term → Prop) : Term → Term → Prop
  | S : HnfMatch R S S
  | S1 {a b : Term} : R a b → HnfMatch R (S ⬝ a) (S ⬝ b)
  | S2 {a a' b b' : Term} : R a b → R a' b' → HnfMatch R (S ⬝ a ⬝ a') (S ⬝ b ⬝ b')

/-- **Head normal forms with equal `^∞` match.**  Same number of arguments, and the arguments
have pairwise equal `^∞`. -/
theorem infEq_hnf {h k : Term} (hp : PureS h) (hq : PureS k) (hh : IsHnf h) (hk : IsHnf k)
    (e : InfEq h k) : HnfMatch InfEq h k := by
  rcases hh with rfl | ⟨a, rfl⟩ | ⟨a, a', rfl⟩ <;> rcases hk with rfl | ⟨b, rfl⟩ | ⟨b, b', rfl⟩
  · exact .S
  · exact absurd e not_infEq_S_app
  · exact absurd e not_infEq_S_app
  · exact absurd e.symm not_infEq_S_app
  · exact .S1 (infEq_hnf_app hp hq (.inr (.inl ⟨a, rfl⟩)) (.inr (.inl ⟨b, rfl⟩)) e).2
  · exact absurd (infEq_hnf_app hp hq (.inr (.inl ⟨a, rfl⟩)) (.inr (.inr ⟨b, b', rfl⟩)) e).1
      not_infEq_S_app
  · exact absurd e.symm not_infEq_S_app
  · exact absurd (infEq_hnf_app hp hq (.inr (.inr ⟨a, a', rfl⟩)) (.inr (.inl ⟨b, rfl⟩)) e).1.symm
      not_infEq_S_app
  · obtain ⟨e1, e2⟩ := infEq_hnf_app hp hq (.inr (.inr ⟨a, a', rfl⟩)) (.inr (.inr ⟨b, b', rfl⟩)) e
    exact .S2 (infEq_hnf_app hp.app_inv.1 hq.app_inv.1 (.inr (.inl ⟨a, rfl⟩))
      (.inr (.inl ⟨b, rfl⟩)) e1).2 e2

/-- **The hnf decomposition.**  If `t^∞ = u^∞` and `t`, `u` reduce to head normal forms `h`,
`k`, then `h` and `k` match with arguments of pairwise equal `^∞`. -/
theorem hnf_decomp {t u h k : Term} (ht : PureS t) (hu : PureS u) (h1 : WSteps t h)
    (hh : IsHnf h) (h2 : WSteps u k) (hk : IsHnf k) (e : InfEq t u) : HnfMatch InfEq h k :=
  infEq_hnf (fold_wsteps h1 ht).1 (fold_wsteps h2 hu).1 hh hk
    ((infEq_of_wsteps ht h1).symm.trans (e.trans (infEq_of_wsteps hu h2)))

/-- Equal `^∞` preserves having a head normal form (`fold t = 36` iff `t` has none). -/
theorem infEq_fold {t u : Term} (ht : PureS t) (hu : PureS u) (e : InfEq t u) :
    fold t = 36 ↔ fold u = 36 := by
  rw [← leftInf_iff ht, ← leftInf_iff hu]
  exact ⟨fun h d P hP => h d P ((e d P).mpr hP), fun h d P hP => h d P ((e d P).mp hP)⟩

/-- The decomposition with the head normal forms supplied: if `t` has one and `t^∞ = u^∞`, both
head-reduce to matching head normal forms. -/
theorem hnf_decomp_ex {t u : Term} (ht : PureS t) (hu : PureS u) (hb : fold t ≠ 36)
    (e : InfEq t u) :
    ∃ h k, Steps t h ∧ Steps u k ∧ IsHnf h ∧ IsHnf k ∧ HnfMatch InfEq h k := by
  obtain ⟨h, c1, _, hh⟩ := sound_head t ht hb
  obtain ⟨k, c2, _, hk⟩ := sound_head u hu fun hb' => hb ((infEq_fold ht hu e).mpr hb')
  have s1 := headChain_steps c1
  have s2 := headChain_steps c2
  exact ⟨h, k, s1, s2, hh, hk, hnf_decomp ht hu s1.weak hh s2.weak hk e⟩

theorem HnfMatch.conv {h k : Term} (m : HnfMatch Conv h k) : Conv h k := by
  cases m with
  | S => exact .refl _
  | S1 r => exact .app (.refl _) r
  | S2 r r' => exact .app (.app (.refl _) r) r'

/-- **Convertible children give convertible parents.** -/
theorem conv_of_children {t u h k : Term} (h1 : WSteps t h) (h2 : WSteps u k)
    (m : HnfMatch Conv h k) : Conv t u :=
  .trans (.of_wsteps h1) (.trans m.conv (.symm (.of_wsteps h2)))

/-- **Lock 1 reduces to the children of head normal forms.**  If `t^∞ = u^∞`, `t` and `u`
reduce to head normal forms `h`, `k`, and Lock 1 holds at each pair of corresponding arguments
of `h`, `k`, then `t` and `u` are convertible. -/
theorem lock1_hnf_children {t u h k : Term} (ht : PureS t) (hu : PureS u) (h1 : WSteps t h)
    (hh : IsHnf h) (h2 : WSteps u k) (hk : IsHnf k) (e : InfEq t u)
    (L : HnfMatch (fun a b => InfEq a b → Conv a b) h k) : Conv t u := by
  refine conv_of_children h1 h2 ?_
  have m := hnf_decomp ht hu h1 hh h2 hk e
  cases L with
  | S => exact .S
  | S1 l => cases m with | S1 r => exact .S1 (l r)
  | S2 l l' => cases m with | S2 r r' => exact .S2 (l r) (l' r')

end WordProblem
