import Ski.NatFan

open Term

/-!
# The fan step at Cantor space, in an oracle semantics

`CantorTotal.no_lift_cantor_total`: over closed terms, totality on the
definable streams does not give a lift, given a Kleene tree.  The fan step
needs *all* points of Cantor space, so it needs points that are not terms.
This module supplies them.

**The oracle calculus.** `TermO` is SKI with a constant `ora α` for every
`α : ℕ → Bool`.  It is a stream cell: `ora α ⬝ k → k (α 0) (ora (α ∘ succ))`.
A closed CL functional `F` is *oracle-total* when `F ⬝ ora α` head-reduces to a
boolean for every `α`, computable or not (`OracleTotal`).

**Sequentiality.** The concern is that a term may apply a stream to arbitrary
continuations, not just the head and tail selectors.  The simulation absorbs
it: the oracle answers any continuation `k` as a cons cell would.  So a run of
`n` head steps of `F ⬝ ora α` is mirrored, by weak reduction, on every CL term
whose first `n + 1` bits are `α`'s, with arbitrary tails (`simO`).  Hence every
`α` has its own modulus (`oracle_local`).

**Compactness.** The fan theorem (`fan`, by König's lemma, classical) turns the
per-`α` moduli into one `m`.  So an oracle-total `F` is m-local (`cantor_fan`),
and `CantorLift.cantorL` lifts it (`cantor_lift_oracle`).

`fan` and what depends on it use `Classical.choice`: the fan theorem is not
constructive.  The simulation itself uses only `propext` and `Quot.sound`.
-/

namespace OracleFan

open NoLift LiftBool Search CantorLift CantorTotal

-- ---------------------------------------------------------------------------
-- The oracle calculus
-- ---------------------------------------------------------------------------

inductive TermO
  | S | K | I
  | ora (α : Nat → Bool)
  | app (f x : TermO)

infixl:70 " ⬝ₚ " => TermO.app

def emb : Term → TermO
  | .S => .S
  | .K => .K
  | .I => .I
  | .app f x => emb f ⬝ₚ emb x

theorem emb_inj : ∀ {t u : Term}, emb t = emb u → t = u
  | .S, .S, _ => rfl
  | .K, .K, _ => rfl
  | .I, .I, _ => rfl
  | .app f x, .app g y, h => by
    simp only [emb, TermO.app.injEq] at h
    rw [emb_inj h.1, emb_inj h.2]
  | .S, .K, h | .S, .I, h | .S, .app _ _, h | .K, .S, h | .K, .I, h | .K, .app _ _, h
  | .I, .S, h | .I, .K, h | .I, .app _ _, h | .app _ _, .S, h | .app _ _, .K, h
  | .app _ _, .I, h => by simp [emb] at h

def shift (α : Nat → Bool) : Nat → Bool := fun i => α (i + 1)

/-- Head steps of the oracle calculus. -/
inductive StepO : TermO → TermO → Prop
  | S (f g x : TermO) : StepO (.S ⬝ₚ f ⬝ₚ g ⬝ₚ x) (f ⬝ₚ x ⬝ₚ (g ⬝ₚ x))
  | K (x y : TermO) : StepO (.K ⬝ₚ x ⬝ₚ y) x
  | I (x : TermO) : StepO (.I ⬝ₚ x) x
  | ora (α : Nat → Bool) (k : TermO) :
      StepO (.ora α ⬝ₚ k) (k ⬝ₚ emb (boolT (α 0)) ⬝ₚ .ora (shift α))
  | left {f f' : TermO} (x : TermO) (h : StepO f f') : StepO (f ⬝ₚ x) (f' ⬝ₚ x)

inductive WhnfO : TermO → Prop
  | S : WhnfO .S
  | K : WhnfO .K
  | I : WhnfO .I
  | S1 (x : TermO) : WhnfO (.S ⬝ₚ x)
  | S2 (x y : TermO) : WhnfO (.S ⬝ₚ x ⬝ₚ y)
  | K1 (x : TermO) : WhnfO (.K ⬝ₚ x)
  | ora (α : Nat → Bool) : WhnfO (.ora α)

theorem WhnfO.no_step {t u : TermO} (hw : WhnfO t) (hs : StepO t u) : False := by
  cases hw with
  | S => cases hs
  | K => cases hs
  | I => cases hs
  | ora => cases hs
  | S1 => cases hs with | left _ h => cases h
  | K1 => cases hs with | left _ h => cases h
  | S2 => cases hs with | left _ h => cases h with | left _ h => cases h

theorem StepO.det {t u v : TermO} (h₁ : StepO t u) (h₂ : StepO t v) : u = v := by
  induction h₁ generalizing v with
  | S f g x =>
    cases h₂ with
    | S => rfl
    | left _ h => exact (WhnfO.no_step (.S2 f g) h).elim
  | K x y =>
    cases h₂ with
    | K => rfl
    | left _ h => exact (WhnfO.no_step (.K1 x) h).elim
  | I x =>
    cases h₂ with
    | I => rfl
    | left _ h => exact (WhnfO.no_step .I h).elim
  | ora α k =>
    cases h₂ with
    | ora => rfl
    | left _ h => exact (WhnfO.no_step (.ora α) h).elim
  | left x h ih =>
    cases h₂ with
    | S => exact (WhnfO.no_step (.S2 _ _) h).elim
    | K => exact (WhnfO.no_step (.K1 _) h).elim
    | I => exact (WhnfO.no_step .I h).elim
    | ora => exact (WhnfO.no_step (.ora _) h).elim
    | left _ h' => rw [ih h']

inductive StepsNO : Nat → TermO → TermO → Prop
  | refl (t : TermO) : StepsNO 0 t t
  | step {t u v : TermO} {n : Nat} (h : StepO t u) (hs : StepsNO n u v) : StepsNO (n + 1) t v

theorem stepsNO_after {n : Nat} {t u v : TermO} (hn : StepsNO n t v) (hv : WhnfO v) (h : StepO t u) :
    ∃ m, n = m + 1 ∧ StepsNO m u v := by
  cases hn with
  | refl => exact (hv.no_step h).elim
  | step h' hs => rw [StepO.det h h']; exact ⟨_, rfl, hs⟩

/-- **Oracle totality**: `F ⬝ ora α` head-reduces to a boolean for every `α`. -/
def OracleTotal (F : Term) : Prop :=
  ∀ α : Nat → Bool, ∃ n b, StepsNO n (emb F ⬝ₚ .ora α) (emb (boolT b))

-- ---------------------------------------------------------------------------
-- Spines
-- ---------------------------------------------------------------------------

def spineO : TermO → List TermO → TermO
  | t, [] => t
  | t, a :: r => spineO (t ⬝ₚ a) r

theorem spineO_append (h : TermO) : ∀ (r : List TermO) (x : TermO), spineO h (r ++ [x]) = spineO h r ⬝ₚ x
  | [], _ => rfl
  | a :: r, x => spineO_append (h ⬝ₚ a) r x

theorem stepO_spine {u v : TermO} (h : StepO u v) : ∀ r, StepO (spineO u r) (spineO v r)
  | [] => h
  | a :: r => stepO_spine (.left a h) r

-- ---------------------------------------------------------------------------
-- The relation and the simulation
-- ---------------------------------------------------------------------------

/-- `RelO b t t'`: `t` is `t'` embedded, with some CL terms replaced by oracles
    whose first `b` bits they share. -/
inductive RelO (b : Nat) : TermO → Term → Prop
  | refl (t : Term) : RelO b (emb t) t
  | ora (α : Nat → Bool) {u : Term} (hu : HasPrefix (pre α b) u) : RelO b (.ora α) u
  | app {f : TermO} {f' : Term} {x : TermO} {x' : Term} :
      RelO b f f' → RelO b x x' → RelO b (f ⬝ₚ x) (f' ⬝ x')

theorem prefix_pre_mono : ∀ {b b' : Nat} (α : Nat → Bool) {u : Term}, b' ≤ b →
    HasPrefix (pre α b) u → HasPrefix (pre α b') u
  | _, 0, _, _, _, _ => trivial
  | b + 1, b' + 1, α, u, h, ⟨u', h1, h2⟩ => ⟨u', h1, prefix_pre_mono (shift α) (by omega) h2⟩
  | 0, _ + 1, _, _, h, _ => absurd h (by omega)

theorem RelO.mono {b b' : Nat} (hb : b' ≤ b) {t : TermO} {t' : Term} : RelO b t t' → RelO b' t t'
  | .refl t => .refl t
  | .ora α hu => .ora α (prefix_pre_mono α hb hu)
  | .app hf hx => .app (hf.mono hb) (hx.mono hb)

inductive PairsO (R : TermO → Term → Prop) : List TermO → List Term → Prop
  | nil : PairsO R [] []
  | cons {a : TermO} {a' : Term} {r : List TermO} {r' : List Term} :
      R a a' → PairsO R r r' → PairsO R (a :: r) (a' :: r')

theorem pairsO_append {b : Nat} {r : List TermO} {r' : List Term} (hr : PairsO (RelO b) r r')
    {x : TermO} {x' : Term} (hx : RelO b x x') : PairsO (RelO b) (r ++ [x]) (r' ++ [x']) := by
  induction hr with
  | nil => exact .cons hx .nil
  | cons ha _ ih => exact .cons ha ih

theorem pairsO_mono {b b' : Nat} (hb : b' ≤ b) {r : List TermO} {r' : List Term}
    (hr : PairsO (RelO b) r r') : PairsO (RelO b') r r' := by
  induction hr with
  | nil => exact .nil
  | cons ha _ ih => exact .cons (ha.mono hb) ih

theorem relO_spine {b : Nat} {u : TermO} {u' : Term} (hu : RelO b u u') :
    ∀ {r : List TermO} {r' : List Term}, PairsO (RelO b) r r' → RelO b (spineO u r) (spineApp u' r')
  | [], [], .nil => hu
  | _ :: _, _ :: _, .cons ha hr => relO_spine (.app hu ha) hr

inductive HeadO (b : Nat) : TermO → Term → Prop
  | leaf {h : Term} (hl : h = S ∨ h = K ∨ h = I) : HeadO b (emb h) h
  | ora (α : Nat → Bool) {u : Term} (hu : HasPrefix (pre α b) u) : HeadO b (.ora α) u

theorem RelO.spine {b : Nat} {t : TermO} {t' : Term} (h : RelO b t t') :
    ∃ hd hd' r r', HeadO b hd hd' ∧ PairsO (RelO b) r r' ∧ t = spineO hd r ∧ t' = spineApp hd' r' := by
  induction h with
  | refl t =>
    obtain ⟨hd, r, hl, rfl⟩ := leaf_spine t
    refine ⟨emb hd, hd, r.map emb, r, .leaf hl, ?_, ?_, rfl⟩
    · clear hl
      induction r with
      | nil => exact .nil
      | cons a r ih => exact .cons (.refl a) ih
    · clear hl
      induction r generalizing hd with
      | nil => rfl
      | cons a r ih => exact ih (hd ⬝ a)
  | ora α hu => exact ⟨_, _, [], [], .ora α hu, .nil, rfl, rfl⟩
  | app _ hx ih _ =>
    obtain ⟨hd, hd', r, r', hh, hr, rfl, rfl⟩ := ih
    exact ⟨hd, hd', r ++ [_], r' ++ [_], hh, pairsO_append hr hx,
      (spineO_append _ _ _).symm, (spineApp_append _ _ _).symm⟩

/-- **The oracle simulation.**  A head run of `t` to a whnf `v` in `n < b`
    steps is mirrored on every related CL term `t'`, by weak reduction, to a `v'`
    related to `v`. -/
theorem simO : ∀ (fuel n : Nat) {t : TermO} {t' : Term} {v : TermO} {b : Nat}, n ≤ fuel →
    RelO b t t' → StepsNO n t v → WhnfO v → n < b → ∃ v', WSteps t' v' ∧ RelO (b - n) v v' := by
  intro fuel
  induction fuel with
  | zero =>
    intro n t t' v b hf hrel hn _ _
    obtain rfl : n = 0 := by omega
    cases hn
    exact ⟨t', .refl _, by simpa using hrel⟩
  | succ fuel ihf =>
  intro n t t' v b hf hrel hn hv hb
  have stop : WhnfO t → ∃ v', WSteps t' v' ∧ RelO (b - n) v v' := fun ht => by
    cases hn with
    | refl => exact ⟨t', .refl _, by simpa using hrel⟩
    | step h _ => exact (ht.no_step h).elim
  obtain ⟨hd, hd', r, r', hh, hr, rfl, rfl⟩ := hrel.spine
  have lock : ∀ {u : TermO} {u' : Term}, StepO (spineO hd r) u → WSteps (spineApp hd' r') u' →
      RelO (b - 1) u u' → ∃ v', WSteps (spineApp hd' r') v' ∧ RelO (b - n) v v' := by
    intro u u' h h' hu
    obtain ⟨m, rfl, hm⟩ := stepsNO_after hn hv h
    obtain ⟨v', hv', hrel'⟩ := ihf m (by omega) hu hm hv (by omega)
    exact ⟨v', h'.trans hv', hrel'.mono (by omega)⟩
  cases hh with
  | leaf hl =>
    rcases hl with rfl | rfl | rfl
    · cases hr with
      | nil => exact stop .S
      | cons ha hr =>
        cases hr with
        | nil => exact stop (.S1 _)
        | cons hb' hr =>
          cases hr with
          | nil => exact stop (.S2 _ _)
          | cons hc hrest =>
            exact lock (stepO_spine (.S _ _ _) _) (steps_spine (.single (.S _ _ _)) _).weak
              (relO_spine (.app (.app (ha.mono (Nat.sub_le _ _)) (hc.mono (Nat.sub_le _ _)))
                (.app (hb'.mono (Nat.sub_le _ _)) (hc.mono (Nat.sub_le _ _)))) (pairsO_mono (Nat.sub_le _ _) hrest))
    · cases hr with
      | nil => exact stop .K
      | cons ha hr =>
        cases hr with
        | nil => exact stop (.K1 _)
        | cons _ hrest =>
          exact lock (stepO_spine (.K _ _) _) (steps_spine (.single (.K _ _)) _).weak
            (relO_spine (ha.mono (Nat.sub_le _ _)) (pairsO_mono (Nat.sub_le _ _) hrest))
    · cases hr with
      | nil => exact stop .I
      | cons ha hrest =>
        exact lock (stepO_spine (.I _) _) (steps_spine (.single (.I _)) _).weak
          (relO_spine (ha.mono (Nat.sub_le _ _)) (pairsO_mono (Nat.sub_le _ _) hrest))
  | ora α hu =>
    cases hr with
    | nil => exact stop (.ora α)
    | cons hk hrest =>
      rename_i k k' rest rest'
      -- `b ≥ 1`, so the CL side has the oracle's first bit
      obtain ⟨b1, rfl⟩ : ∃ b1, b = b1 + 1 := ⟨b - 1, by omega⟩
      obtain ⟨u1, h1, h2⟩ := hu
      have hright : WSteps (spineApp hd' (k' :: rest'))
          (spineApp (k' ⬝ boolT (α 0) ⬝ u1) rest') :=
        NatFan.wsteps_spine ((WSteps.left _ h1).trans (cons_sel _ _ _)) rest'
      refine lock (stepO_spine (.ora α k) rest) hright ?_
      exact relO_spine (.app (.app (hk.mono (by omega)) (.refl _)) (.ora (shift α) h2))
        (pairsO_mono (by omega) hrest)

theorem relO_emb : ∀ {b : Nat} {x : TermO} {v' : Term}, RelO b x v' → ∀ t : Term, x = emb t → v' = t := by
  intro b x v' h
  induction h with
  | refl t0 => intro t he; exact emb_inj he
  | ora α _ => intro t he; cases t <;> simp [emb] at he
  | app _ _ ihf ihx =>
    intro t he
    cases t with
    | app t1 t2 =>
      simp only [emb, TermO.app.injEq] at he
      rw [ihf t1 he.1, ihx t2 he.2]
    | _ => simp [emb] at he

theorem whnfO_bool (b : Bool) : WhnfO (emb (boolT b)) := by
  cases b
  · exact .K1 _
  · exact .K

/-- **Every point has a modulus**: a run of `F ⬝ ora α` to a boolean in `n`
    steps fixes `F` on every CL term with `α`'s first `n + 1` bits. -/
theorem oracle_local {F : Term} {α : Nat → Bool} {n : Nat} {b : Bool}
    (h : StepsNO n (emb F ⬝ₚ .ora α) (emb (boolT b))) :
    ∀ s, HasPrefix (pre α (n + 1)) s → WSteps (F ⬝ s) (boolT b) := by
  intro s hs
  obtain ⟨v', hv', hrel⟩ := simO n n (Nat.le_refl _) (.app (.refl F) (.ora α hs)) h (whnfO_bool b) (by omega)
  rw [relO_emb hrel _ rfl] at hv'
  exact hv'

-- ---------------------------------------------------------------------------
-- The fan theorem (classical)
-- ---------------------------------------------------------------------------

theorem take_prefix : ∀ (w : List Bool) (j : Nat) {s : Term}, HasPrefix w s → HasPrefix (w.take j) s
  | [], _, _, _ => by simp; trivial
  | _ :: _, 0, _, _ => trivial
  | b :: w, j + 1, s, ⟨s', h1, h2⟩ => ⟨s', h1, take_prefix w j h2⟩

theorem pre_range : ∀ (α : Nat → Bool) (n : Nat), CantorTotal.pre α n = (List.range n).map α
  | _, 0 => rfl
  | α, n + 1 => by
    rw [CantorTotal.pre, pre_range (fun i => α (i + 1)) n, List.range_succ_eq_map]
    simp [Function.comp_def]

theorem take_append_take {β : Type} : ∀ (a v : List β) (k j : Nat), j ≤ a.length + k →
    (a ++ v.take k).take j = (a ++ v).take j
  | [], v, k, j, h => by simp [List.take_take, Nat.min_eq_left (by simpa using h)]
  | x :: a, v, k, 0, _ => rfl
  | x :: a, v, k, j + 1, h => by
    simp only [List.cons_append, List.take_succ_cons]
    rw [take_append_take a v k j (by simp at h; omega)]

open Classical in
/-- **The fan theorem.**  If every path through the binary tree meets the bar `B`
    at a finite prefix, there is one depth `m` by which every word of length `m`
    has met it.  By König's lemma; classical. -/
theorem fan (B : List Bool → Prop) (hB : ∀ α : Nat → Bool, ∃ n, B (pre α n)) :
    ∃ m, ∀ w : List Bool, w.length = m → ∃ j, j ≤ m ∧ B (w.take j) := by
  -- `u` has unbarred extensions of every length
  let Good (u : List Bool) : Prop := ∀ k, ∃ v : List Bool, v.length = k ∧
    ∀ j, j ≤ u.length + k → ¬ B ((u ++ v).take j)
  apply Classical.byContradiction
  intro hno
  have h0 : Good [] := by
    intro k
    have := not_exists.1 hno k
    simp only [not_forall, not_exists, not_and] at this
    obtain ⟨w, hw, hw'⟩ := this
    exact ⟨w, hw, fun j hj hB' => hw' j (by simpa [hw] using hj) hB'⟩
  -- a good word has a good one-bit extension
  have hext : ∀ u, Good u → Good (u ++ [false]) ∨ Good (u ++ [true]) := by
    intro u hu
    apply Classical.byContradiction
    intro hboth
    simp only [not_or] at hboth
    obtain ⟨hf, ht⟩ := hboth
    have bad : ∀ c : Bool, ¬ Good (u ++ [c]) → ∃ k0, ∀ k, k0 ≤ k → ∀ v : List Bool, v.length = k →
        ∃ j, j ≤ (u ++ [c]).length + k ∧ B (((u ++ [c]) ++ v).take j) := by
      intro c hc
      simp only [Good, not_forall, not_exists, not_and] at hc
      obtain ⟨k0, hk0⟩ := hc
      refine ⟨k0, fun k hk v hv => ?_⟩
      have := hk0 (v.take k0) (by simp [hv, hk])
      simp only [Classical.not_not] at this
      obtain ⟨j, hj, hBj⟩ := this
      refine ⟨j, by simp at hj ⊢ <;> omega, ?_⟩
      have : ((u ++ [c]) ++ v.take k0).take j = ((u ++ [c]) ++ v).take j :=
        take_append_take _ v k0 j (by simp at hj ⊢ <;> omega)
      rwa [← this]
    obtain ⟨kf, hkf⟩ := bad false hf
    obtain ⟨kt, hkt⟩ := bad true ht
    obtain ⟨v, hv, hv'⟩ := hu (max kf kt + 1)
    cases v with
    | nil => simp at hv
    | cons c v' =>
      have hv'l : v'.length = max kf kt := by simpa using hv
      cases c
      · obtain ⟨j, hj, hBj⟩ := hkf (max kf kt) (by omega) v' hv'l
        exact hv' j (by simp at hj ⊢ <;> omega) (by simpa using hBj)
      · obtain ⟨j, hj, hBj⟩ := hkt (max kf kt) (by omega) v' hv'l
        exact hv' j (by simp at hj ⊢ <;> omega) (by simpa using hBj)
  -- the path that stays good
  let step (u : List Bool) : List Bool := if Good (u ++ [false]) then u ++ [false] else u ++ [true]
  let path : Nat → List Bool := fun n => Nat.rec [] (fun _ u => step u) n
  have hpath_succ : ∀ n, path (n + 1) = step (path n) := fun _ => rfl
  have hgood : ∀ n, Good (path n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [hpath_succ]
      by_cases hc : Good (path n ++ [false])
      · simp only [step, hc, if_true]
      · simp only [step, hc, if_false]; exact (hext _ ih).resolve_left hc
  have hlen : ∀ n, (path n).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hpath_succ]; simp only [step]; split <;> simp [ih]
  have happ : ∀ n, ∃ c, path (n + 1) = path n ++ [c] := by
    intro n; rw [hpath_succ]; simp only [step]; split
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  let α : Nat → Bool := fun i => (path (i + 1)).getD i false
  have hpre : ∀ n, pre α n = path n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pre_range, List.range_succ, List.map_append, ← pre_range, ih]
      obtain ⟨c, hc⟩ := happ n
      rw [hc]
      simp [α, hc, List.getD_eq_getElem?_getD, hlen n]
  obtain ⟨n, hBn⟩ := hB α
  obtain ⟨v, hv, hv'⟩ := hgood n 0
  rw [List.length_eq_zero_iff.1 hv] at hv'
  have e : (path n ++ []).take n = pre α n := by
    rw [List.append_nil, hpre n, List.take_of_length_le (by rw [hlen n]; exact Nat.le_refl n)]
  exact hv' n (by rw [hlen n]; omega) (by rw [e]; exact hBn)

-- ---------------------------------------------------------------------------
-- The fan step and the lift
-- ---------------------------------------------------------------------------

open Classical in
/-- **The fan step at Cantor space.**  An oracle-total functional is m-local
    for some `m`. -/
theorem cantor_fan {F : Term} (hF : OracleTotal F) : ∃ m φ, Local m φ F := by
  let B (w : List Bool) : Prop := ∃ b : Bool, ∀ s, HasPrefix w s → WSteps (F ⬝ s) (boolT b)
  have hB : ∀ α : Nat → Bool, ∃ n, B (pre α n) := by
    intro α
    obtain ⟨n, b, hrun⟩ := hF α
    exact ⟨n + 1, b, oracle_local hrun⟩
  obtain ⟨m, hm⟩ := fan B hB
  refine ⟨m, fun w => if h : B w then Classical.choose h else false, ?_⟩
  intro w hw s hs
  have hBw : B w := by
    obtain ⟨j, _, b, hb⟩ := hm w hw
    exact ⟨b, fun s' hs' => hb s' (take_prefix w j hs')⟩
  simp only [hBw, dif_pos]
  exact Classical.choose_spec hBw s hs

/-- **`cantorL` lifts every oracle-total functional.** -/
theorem cantor_lift_oracle {F : Term} (hF : OracleTotal F) :
    ∃ m φ, WSteps (cantorL ⬝ F) (quoteT (evalT ⬝ D m φ)) ∧
      ∀ (w : List Bool) (s : Term) (r : Bool), w.length = m → HasPrefix w s →
        WSteps (F ⬝ s) (boolT r) → WSteps (evalT ⬝ D m φ ⬝ s) (boolT r) := by
  obtain ⟨m, φ, hl⟩ := cantor_fan hF
  exact ⟨m, φ, cantor_lift hl⟩

end OracleFan
