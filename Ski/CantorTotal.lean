import Ski.Coalgebra

open Term

/-!
# No lift at Cantor space under totality alone, given a Kleene tree

`CantorLift.cantor_lift` lifts every m-local stream functional.  Under totality
on the streams alone (the frame of `NoLift.no_lift`), Berger's search
diverges on a functional built from a Kleene tree.  This module shows more:
**no** closed term lifts every functional total on the streams, provided a
Kleene tree is definable.  One is: `KleeneTree.kleene`, so the unconditional
form is `KleeneTree.no_lift_cantor_total'`.

The impossibility generalizes (`no_lift_family`).  For any `Ψ`, if `Ψ (num (k+1))`
differs from `Ψ ω` at some test input for every `k`, then no closed `L` lifts
both `Ψ ω` and every `Ψ (num k)` on those inputs.  The proof is
`NoLift.no_lift_core`'s, with the stuttering simulation `NoLift.sim` relating
`Ψ ω` to `Ψ (num (n+1))`.

For Cantor space, take `Ψ` to be a *walker* over a tree `T` of finite words:
`Ψ c s` asks whether the stream `s` leaves `T` within `c` steps.
- `Ψ (num k)` gives up after `k` steps, so it is total (`walk_num`).
- `Ψ ω` never gives up.  If `T` has no definable infinite path, every definable
  stream leaves `T` eventually, so `Ψ ω` is total and constantly true there
  (`walk_omega`).
- If `T` is infinite (it has a word of every length) and prefix-closed, a stream
  that follows a long word of `T` and then continues with zeros separates
  `Ψ ω` from `Ψ (num (k+1))`.

A tree with these properties, decided by a closed term on stream prefixes
(`Kleene`), is a Kleene tree: a computable infinite binary tree with no
computable path.  That one exists is standard recursion theory, and since
weak CL computes every partial recursive function it is definable here.  That
step is the hypothesis of `no_lift_cantor_total`; `Ski/KleeneTree.lean`
discharges it by building the tree inside the calculus.
-/

namespace CantorTotal

open NoLift LiftBool Search CantorLift

-- ---------------------------------------------------------------------------
-- The impossibility, for any family Ψ ω, Ψ (num k)
-- ---------------------------------------------------------------------------

/-- `L` lifts `f` on the test inputs `X`, up to conversion. -/
def LiftsOn (X : Term → Prop) (L f : Term) : Prop :=
  ∃ c w, WSteps (L ⬝ f) w ∧ WSteps (quoteT c) w ∧
    ∀ x, X x → ∀ b : Bool, WSteps (f ⬝ x) (boolT b) → WSteps (c ⬝ x) (boolT b)

/-- **No lift for a separated family.**  If, for every `k`, some test input
    tells `Ψ ω` from `Ψ (num (k+1))`, then no closed `L` lifts `Ψ ω` and every
    `Ψ (num k)`. -/
theorem no_lift_family (X : Term → Prop) (Ψ L : Term)
    (hdiff : ∀ k, ∃ x b, X x ∧ WSteps (Ψ ⬝ omega0 ⬝ x) (boolT b) ∧
      WSteps (Ψ ⬝ num (k + 1) ⬝ x) (boolT (!b)))
    (h0 : LiftsOn X L (Ψ ⬝ omega0)) (hk : ∀ k, LiftsOn X L (Ψ ⬝ num k)) : False := by
  obtain ⟨c, w, hw, hcw, hag⟩ := h0
  have h1 : WSteps (eqT c ⬝ (L ⬝ (Ψ ⬝ omega0))) K := by
    simpa [boolT] using eqT_conv (c := c) hw hcw
  obtain ⟨n, hn⟩ := counted (steps_of_wsteps_K h1)
  have hrel : Rel (n + 1) (eqT c ⬝ (L ⬝ (Ψ ⬝ omega0))) (eqT c ⬝ (L ⬝ (Ψ ⬝ num (n + 1)))) :=
    .app (.refl _) (.app (.refl _) (.app (.refl _) (.omega (.refl _) (Nat.le_refl _))))
  have h2 := (sim n hrel hn (Nat.lt_succ_self n)).weak
  obtain ⟨c', w', hw', hcw', hag'⟩ := hk (n + 1)
  have h3 := eqT_conv (c := c) hw' hcw'
  have hcc : c = c' := by
    by_cases hne : c = c'
    · exact hne
    · simp [hne, boolT] at h3; exact (K_KI_disjoint h2 h3).elim
  subst hcc
  obtain ⟨x, b, hx, hb, hnb⟩ := hdiff n
  have e1 := hag x hx b hb
  have e2 := hag' x hx (!b) hnb
  cases b
  · exact bool_disjoint e1 e2
  · exact bool_disjoint e2 e1

-- ---------------------------------------------------------------------------
-- Streams as bit sequences
-- ---------------------------------------------------------------------------

/-- The first `n` bits. -/
def pre (bits : Nat → Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => bits 0 :: pre (fun i => bits (i + 1)) n

/-- `s` is a stream with these bits. -/
def IsStream (bits : Nat → Bool) (s : Term) : Prop := ∀ n, HasPrefix (pre bits n) s

/-- A finite word, then zeros. -/
def wordStream : List Bool → Term
  | [] => zerosT
  | b :: w => consC ⬝ boolT b ⬝ wordStream w

def wordBits (w : List Bool) (i : Nat) : Bool := w.getD i false

theorem pre_false : ∀ n, pre (fun _ => false) n = List.replicate n false
  | 0 => rfl
  | n + 1 => by simp [pre, pre_false n, List.replicate_succ]

theorem wordStream_isStream : ∀ w : List Bool, IsStream (wordBits w) (wordStream w)
  | [], n => by
    have : (wordBits []) = fun _ => false := by funext i; simp [wordBits]
    rw [this, pre_false]; exact zeros_prefix n
  | b :: w, 0 => trivial
  | b :: w, n + 1 => by
    have hb : wordBits (b :: w) 0 = b := by simp [wordBits]
    have ht : (fun i => wordBits (b :: w) (i + 1)) = wordBits w := by funext i; simp [wordBits]
    simp only [pre, hb, ht]
    exact prefix_cons b (wordStream_isStream w n)

theorem pre_word : ∀ (w : List Bool) (j : Nat), j ≤ w.length → pre (wordBits w) j = w.take j
  | _, 0, _ => rfl
  | [], j + 1, h => by simp at h
  | b :: w, j + 1, h => by
    have ht : (fun i => wordBits (b :: w) (i + 1)) = wordBits w := by funext i; simp [wordBits]
    simp only [pre]
    rw [ht, pre_word w j (by simpa using h)]
    simp [wordBits]

-- ---------------------------------------------------------------------------
-- The walker
-- ---------------------------------------------------------------------------

/-- `τ` decides the tree `T` on stream prefixes. -/
def Decides (τ : Term) (T : List Bool → Bool) : Prop :=
  ∀ bits s, IsStream bits s → ∀ n, WSteps (τ ⬝ s ⬝ num n) (boolT (T (pre bits n)))

/-- `go c s n = τ s n (c false (λ c'. go c' s (succ n))) true`,
    over `r` (0), `c` (1), `s` (2), `n` (3), `c'` (4). -/
def goIn : OTerm := absN [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 2 ⬝ₒ (succS.toO ⬝ₒ .var 3))
def goBody (τ : Term) : OTerm :=
  τ.toO ⬝ₒ .var 2 ⬝ₒ .var 3 ⬝ₒ (.var 1 ⬝ₒ (K ⬝ I).toO ⬝ₒ goIn) ⬝ₒ .K
def goStep (τ : Term) : Term := toTerm (absN [0, 1, 2, 3] (goBody τ))

/-- **The walker** over `τ`'s tree. -/
def goT (τ : Term) : Term := fixSelf (goStep τ) (fixB (goStep τ))

theorem go_unroll (τ : Term) : WSteps (goT τ) (goStep τ ⬝ goT τ) := by
  have h := (fixSelf_unroll (F := goStep τ) (Steps.refl (fixB (goStep τ)))).weak
  have hI : WSteps (fixSelf (goStep τ) (I ⬝ fixB (goStep τ))) (goT τ) := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

theorem go_unfold (τ c s n : Term) : ∃ X,
    WSteps (goT τ ⬝ c ⬝ s ⬝ n) (τ ⬝ s ⬝ n ⬝ (c ⬝ (K ⬝ I) ⬝ X) ⬝ K) ∧
    ∀ c', WSteps (X ⬝ c') (goT τ ⬝ c' ⬝ s ⬝ (succS ⬝ n)) := by
  have h := absN_beta_close [0, 1, 2, 3] (goBody τ) (fun _ => K) [goT τ, c, s, n] rfl
  simp only [goBody, OTerm.close, close_toO, appT] at h
  refine ⟨_, (WSteps.left _ (WSteps.left _ (WSteps.left _ (go_unroll τ)))).trans h, fun c' => ?_⟩
  have h2 := absN_beta_close [4] (.var 0 ⬝ₒ .var 4 ⬝ₒ .var 2 ⬝ₒ (succS.toO ⬝ₒ .var 3))
    (overrideC (fun _ => K) [0, 1, 2, 3] [goT τ, c, s, n]) [c'] rfl
  simp only [OTerm.close, close_toO, appT] at h2
  exact h2

/-- The walk with a budget, in Lean: did the stream leave the tree within `k`
    steps from depth `n`? -/
def walk (T : List Bool → Bool) (bits : Nat → Bool) : Nat → Nat → Bool
  | k, n => if T (pre bits n) then (match k with
      | 0 => false
      | k + 1 => walk T bits k (n + 1)) else true

theorem walk_num {τ : Term} {T : List Bool → Bool} (hτ : Decides τ T) {bits : Nat → Bool} {s : Term}
    (hs : IsStream bits s) : ∀ k n, WSteps (goT τ ⬝ num k ⬝ s ⬝ num n) (boolT (walk T bits k n)) := by
  intro k
  induction k with
  | zero =>
    intro n
    obtain ⟨X, hX, _⟩ := go_unfold τ (num 0) s (num n)
    have h := (hX.trans (WSteps.left _ (WSteps.left _ (hτ bits s hs n)))).trans (sel _ _ _)
    cases hT : T (pre bits n) with
    | false => rw [hT] at h; simpa [walk, hT, boolT] using h
    | true =>
      rw [hT] at h
      have h1 : WSteps (goT τ ⬝ num 0 ⬝ s ⬝ num n) (num 0 ⬝ (K ⬝ I) ⬝ X) := by simpa using h
      simpa [walk, hT, boolT] using h1.trans (.single (.K _ _))
  | succ k ih =>
    intro n
    obtain ⟨X, hX, hrec⟩ := go_unfold τ (num (k + 1)) s (num n)
    have h := (hX.trans (WSteps.left _ (WSteps.left _ (hτ bits s hs n)))).trans (sel _ _ _)
    cases hT : T (pre bits n) with
    | false => rw [hT] at h; simpa [walk, hT, boolT] using h
    | true =>
      rw [hT] at h
      have h1 : WSteps (goT τ ⬝ num (k + 1) ⬝ s ⬝ num n) (num (k + 1) ⬝ (K ⬝ I) ⬝ X) := by simpa using h
      have h' := (h1.trans (succS_wsteps (num k) _ X)).trans ((hrec _).trans (ih (n + 1)))
      simpa [walk, hT] using h'

theorem walk_omega {τ : Term} {T : List Bool → Bool} (hτ : Decides τ T) {bits : Nat → Bool} {s : Term}
    (hs : IsStream bits s) : ∀ (d n : Nat) {z : Term}, Steps z (fixB succS) →
      T (pre bits (n + d)) = false → WSteps (goT τ ⬝ omegaT z ⬝ s ⬝ num n) K := by
  intro d
  induction d with
  | zero =>
    intro n z _ hN
    obtain ⟨X, hX, _⟩ := go_unfold τ (omegaT z) s (num n)
    have h := (hX.trans (WSteps.left _ (WSteps.left _ (hτ bits s hs n)))).trans (sel _ _ _)
    have hN' : T (pre bits n) = false := by simpa using hN
    rw [hN'] at h
    simpa using h
  | succ d ih =>
    intro n z hz hN
    obtain ⟨X, hX, hrec⟩ := go_unfold τ (omegaT z) s (num n)
    have h := (hX.trans (WSteps.left _ (WSteps.left _ (hτ bits s hs n)))).trans (sel _ _ _)
    cases hT : T (pre bits n) with
    | false => rw [hT] at h; simpa using h
    | true =>
      rw [hT] at h
      have h1 : WSteps (goT τ ⬝ omegaT z ⬝ s ⬝ num n) (omegaT z ⬝ (K ⬝ I) ⬝ X) := by simpa using h
      have h' := (h1.trans (omega_wsteps hz _ X)).trans
        ((hrec _).trans (ih (n + 1) (.step (.I _) hz) (by rw [Nat.add_right_comm]; simpa [Nat.add_assoc] using hN)))
      exact h'

/-- `Ψ c s = go c s 0`. -/
def PsiT (τ : Term) : Term := toTerm (absN [0, 1] ((goT τ).toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ (num 0).toO))

theorem psi_go (τ c s : Term) : WSteps (PsiT τ ⬝ c ⬝ s) (goT τ ⬝ c ⬝ s ⬝ num 0) := by
  have h := absN_beta_close [0, 1] ((goT τ).toO ⬝ₒ .var 0 ⬝ₒ .var 1 ⬝ₒ (num 0).toO) (fun _ => K) [c, s] rfl
  simp only [OTerm.close, close_toO, appT] at h
  exact h

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- A Kleene tree, decided by `τ` on stream prefixes: prefix-closed, infinite,
    and with no definable infinite path. -/
structure Kleene (τ : Term) (T : List Bool → Bool) : Prop where
  decides : Decides τ T
  closed : ∀ w v : List Bool, T (w ++ v) = true → T w = true
  infinite : ∀ k, ∃ w : List Bool, w.length = k ∧ T w = true
  noPath : ∀ bits s, IsStream bits s → ∃ N, T (pre bits N) = false

/-- Test inputs: the definable streams. -/
def Streams (s : Term) : Prop := ∃ bits, IsStream bits s

/-- A functional total on the definable streams. -/
def TotalS (f : Term) : Prop := ∀ s, Streams s → ∃ b : Bool, WSteps (f ⬝ s) (boolT b)

/-- **No lift at Cantor space under totality alone.**  Given a Kleene tree, no
    closed `L` lifts every functional that is total on the definable streams. -/
theorem no_lift_cantor_total {τ : Term} {T : List Bool → Bool} (hK : Kleene τ T) (L : Term)
    (hL : ∀ f, TotalS f → LiftsOn Streams L f) : False := by
  have hω : ∀ s, Streams s → WSteps (PsiT τ ⬝ omegaT (fixB succS) ⬝ s) K := by
    rintro s ⟨bits, hs⟩
    obtain ⟨N, hN⟩ := hK.noPath bits s hs
    exact (psi_go _ _ _).trans (walk_omega hK.decides hs N 0 (.refl _) (by simpa using hN))
  have hnum : ∀ k s bits, IsStream bits s →
      WSteps (PsiT τ ⬝ num k ⬝ s) (boolT (walk T bits k 0)) := fun k s bits hs =>
    (psi_go _ _ _).trans (walk_num hK.decides hs k 0)
  refine no_lift_family Streams (PsiT τ) L ?_ (hL _ ?_) (fun k => hL _ ?_)
  · intro k
    obtain ⟨w, hw, hTw⟩ := hK.infinite (k + 1)
    refine ⟨wordStream w, true, ⟨_, wordStream_isStream w⟩, hω _ ⟨_, wordStream_isStream w⟩, ?_⟩
    -- the walk follows `w` for `k + 1` steps without leaving the tree
    have hin : ∀ j, j ≤ k + 1 → T (pre (wordBits w) j) = true := fun j hj => by
      rw [pre_word w j (by omega)]
      exact hK.closed _ (w.drop j) (by rw [List.take_append_drop]; exact hTw)
    have hwalk : ∀ i n, n + i = k + 1 → walk T (wordBits w) i n = false := by
      intro i
      induction i with
      | zero => intro n hn; simp [walk, hin n (by omega)]
      | succ i ih => intro n hn; simp only [walk, hin n (by omega), if_true]; exact ih (n + 1) (by omega)
    simpa [hwalk (k + 1) 0 (by omega)] using hnum (k + 1) _ _ (wordStream_isStream w)
  · rintro s ⟨bits, hs⟩
    exact ⟨true, hω s ⟨bits, hs⟩⟩
  · rintro s ⟨bits, hs⟩
    exact ⟨_, hnum k s bits hs⟩

end CantorTotal
