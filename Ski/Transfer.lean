import Ski.Abs
import Ski.Fuel
open Term

/-!
# The transfer lemmas

Part II proves termination and bounds on a realizer language and carries
them to the compiled `SKI` term.  `simulation` gives weak reduction; the
budget and the circuit count normal-order head contractions.  Two lemmas
bridge the gap, and one of them is false in its obvious counted form.

**Standardization, qualitative.**  A weak reduction to a weak head normal
form gives a normal-order evaluation (`eval_of_wsteps`), whose value weakly
reduces to the target.  This is `eval_back` at a normal form.

**Standardization, counted, is false.**  One would like a term that weakly
reduces to `u` in `n` steps, where `u` normalizes in `m` head steps, to
normalize in at most `n + m` head steps.  `D ⬝ (I ⬝ F)` refutes it, where
`D = S I I` duplicates its argument (`counted_standardization_false`).
One weak step contracts `I ⬝ F` inside the argument, and `D ⬝ F`
normalizes in 8 head steps.  Normal order contracts the redex only after
`D` has copied it, once per copy that reaches the head, and takes 10.
Weak reduction shares work that head reduction repeats.  A bound on the
trace therefore cannot come from a count of weak steps.  It must be
proved of head reduction directly, or through a measure that `S`'s
duplication respects.

**Counted β for the compiler's abstraction.**  `abs` is `skijack`'s
bracket abstraction.  `[x] M ⬝ N` weakly reduces to `M[N/x]` in at most
`vsize M` steps (`abs_beta_count`), where `vsize` counts the nodes of `M`
that contain a variable and counts a closed subterm as one node.
Abstraction at most triples `vsize` (`vsize_abs`), and closed arguments
never raise it (`vsize_subst`).  So β for `k` formals takes at most
`3^k · vsize M` weak steps (`absN_beta_count`): a constant per node of the
body, with a factor exponential in the number of binders, which is the
known cost of abstraction without `B` and `C`.
-/

-- ---------------------------------------------------------------------------
-- Standardization
-- ---------------------------------------------------------------------------

/-- **Standardization, qualitative.**  A weak reduction to a weak head normal
    form yields a normal-order evaluation, whose value weakly reduces to it. -/
theorem eval_of_wsteps {t v : Term} (h : WSteps t v) (hv : Whnf v) :
    ∃ v', Eval t v' ∧ WSteps v' v :=
  eval_back h ⟨.refl v, hv⟩

/-- `S I I`: applies its argument to itself. -/
def dupT : Term := S ⬝ I ⬝ I

/-- `[y] (y K)`: applies its argument to `K`. -/
def appK : Term := S ⬝ I ⬝ (K ⬝ K)

/-- **Counted standardization is false.**  `D ⬝ (I ⬝ F)` weakly reduces to
    `D ⬝ F` in one step; `D ⬝ F` normalizes in 8 head steps, and
    `D ⬝ (I ⬝ F)` in 10, more than `1 + 8`. -/
theorem counted_standardization_false :
    WStep (dupT ⬝ (I ⬝ appK)) (dupT ⬝ appK) ∧
    (runF 20 (dupT ⬝ appK)).map Prod.snd = some 8 ∧
    (runF 20 (dupT ⬝ (I ⬝ appK))).map Prod.snd = some 10 :=
  ⟨.right _ (.I _), by decide, by decide⟩

-- ---------------------------------------------------------------------------
-- Counted weak reduction on open terms
-- ---------------------------------------------------------------------------

/-- Exactly `n` weak steps. -/
inductive OWStepsN : Nat → OTerm → OTerm → Prop
  | refl (t : OTerm) : OWStepsN 0 t t
  | step {n : Nat} {t t' u : OTerm} (h : OWStep t t') (hs : OWStepsN n t' u) :
      OWStepsN (n + 1) t u

theorem OWStepsN.weak {n : Nat} {t u : OTerm} (h : OWStepsN n t u) : OWSteps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h ih

theorem OWStepsN.trans {a b : Nat} {t u v : OTerm} (h₁ : OWStepsN a t u)
    (h₂ : OWStepsN b u v) : OWStepsN (a + b) t v := by
  induction h₁ with
  | refl _ => rw [Nat.zero_add]; exact h₂
  | @step n _ _ _ h _ ih =>
    rw [Nat.add_right_comm]
    exact .step h (ih h₂)

theorem OWStepsN.left {n : Nat} {f f' : OTerm} (x : OTerm) (h : OWStepsN n f f') :
    OWStepsN n (f ⬝ₒ x) (f' ⬝ₒ x) := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.left x h) ih

theorem OWStepsN.right {n : Nat} (f : OTerm) {x x' : OTerm} (h : OWStepsN n x x') :
    OWStepsN n (f ⬝ₒ x) (f ⬝ₒ x') := by
  induction h with
  | refl _ => exact .refl _
  | step h _ ih => exact .step (.right f h) ih

theorem OWStepsN.app {a b : Nat} {f f' x x' : OTerm} (hf : OWStepsN a f f')
    (hx : OWStepsN b x x') : OWStepsN (a + b) (f ⬝ₒ x) (f' ⬝ₒ x') :=
  (hf.left x).trans (hx.right f')

theorem OWStepsN.appL {n : Nat} {t u : OTerm} (h : OWStepsN n t u) :
    ∀ as, OWStepsN n (appL t as) (appL u as)
  | [] => h
  | a :: as => OWStepsN.appL (OWStepsN.left a h) as

-- ---------------------------------------------------------------------------
-- The measure
-- ---------------------------------------------------------------------------

/-- No variable occurs. -/
def OTerm.closedB : OTerm → Bool
  | .var _ => false
  | .app f x => f.closedB && x.closedB
  | _ => true

/-- Nodes that contain a variable, a closed subterm counting as one. -/
def OTerm.vsize : OTerm → Nat
  | .app f x => if (f ⬝ₒ x).closedB then 1 else f.vsize + x.vsize + 1
  | _ => 1

theorem vsize_pos : ∀ t : OTerm, 1 ≤ t.vsize
  | .S => Nat.le_refl 1
  | .K => Nat.le_refl 1
  | .I => Nat.le_refl 1
  | .var _ => Nat.le_refl 1
  | .app f x => by
    simp only [OTerm.vsize]
    split
    · exact Nat.le_refl 1
    · omega

theorem vsize_of_closed : ∀ {t : OTerm}, t.closedB = true → t.vsize = 1
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var _, h => by cases h
  | .app _ _, h => by simp only [OTerm.vsize, h, if_true]

theorem vsize_app_open {f x : OTerm} (h : (f ⬝ₒ x).closedB = false) :
    (f ⬝ₒ x).vsize = f.vsize + x.vsize + 1 := by
  simp only [OTerm.vsize, h, Bool.false_eq_true, if_false]

theorem vsize_app_le (f x : OTerm) : (f ⬝ₒ x).vsize ≤ f.vsize + x.vsize + 1 := by
  cases h : (f ⬝ₒ x).closedB with
  | true => rw [vsize_of_closed h]; omega
  | false => rw [vsize_app_open h]; exact Nat.le_refl _

theorem mem_of_closed {x : Nat} : ∀ {t : OTerm}, t.closedB = true → t.mem x = false
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var _, h => by cases h
  | .app f a, h => by
    simp only [OTerm.closedB, Bool.and_eq_true] at h
    simp only [OTerm.mem, mem_of_closed h.1, mem_of_closed h.2, Bool.or_false]

theorem closed_of_mem {x : Nat} {t : OTerm} (h : t.mem x = true) : t.closedB = false := by
  cases hc : t.closedB with
  | false => rfl
  | true => rw [mem_of_closed hc] at h; cases h

theorem closedB_toO : ∀ t : Term, t.toO.closedB = true
  | .S => rfl
  | .K => rfl
  | .I => rfl
  | .app f a => by
    simp only [Term.toO, OTerm.closedB, closedB_toO f, closedB_toO a, Bool.and_self]

theorem subst_closed {τ : Nat → OTerm} : ∀ {t : OTerm}, t.closedB = true → t.subst τ = t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var _, h => by cases h
  | .app f a, h => by
    simp only [OTerm.closedB, Bool.and_eq_true] at h
    simp only [OTerm.subst, subst_closed h.1, subst_closed h.2]

/-- Substituting a closed term never raises the measure. -/
theorem vsize_subst {x : Nat} {N : OTerm} (hN : N.closedB = true) :
    ∀ t : OTerm, (t.subst (single x N)).vsize ≤ t.vsize
  | .S => Nat.le_refl _
  | .K => Nat.le_refl _
  | .I => Nat.le_refl _
  | .var y => by
    by_cases hy : y = x
    · subst hy
      show (single y N y).vsize ≤ _
      rw [single_self, vsize_of_closed hN]; exact vsize_pos _
    · show (single x N y).vsize ≤ _
      rw [single_ne N hy]; exact Nat.le_refl _
  | .app f a => by
    cases hc : (f ⬝ₒ a).closedB with
    | true => rw [subst_closed hc]; exact Nat.le_refl _
    | false =>
      rw [vsize_app_open hc]
      exact Nat.le_trans (vsize_app_le _ _)
        (Nat.add_le_add_right (Nat.add_le_add (vsize_subst hN f) (vsize_subst hN a)) 1)

theorem closedB_abs_of_closed {x : Nat} : ∀ {t : OTerm}, t.closedB = true →
    abs x t = .K ⬝ₒ t
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var _, h => by cases h
  | .app f a, h => by rw [abs_app, if_pos (mem_of_closed h)]

/-- **Abstraction at most triples the measure.** -/
theorem vsize_abs (x : Nat) : ∀ t : OTerm, (abs x t).vsize ≤ 3 * t.vsize
  | .S => by rw [closedB_abs_of_closed rfl]; decide
  | .K => by rw [closedB_abs_of_closed rfl]; decide
  | .I => by rw [closedB_abs_of_closed rfl]; decide
  | .var y => by
    rw [abs_var]
    by_cases hy : y = x
    · rw [if_pos hy]; simp [OTerm.vsize]
    · rw [if_neg hy]; simp [OTerm.vsize, OTerm.closedB]
  | .app e f => by
    have hpos := vsize_pos (e ⬝ₒ f)
    by_cases hm : (OTerm.app e f).mem x = false
    · rw [abs_app, if_pos hm]
      refine Nat.le_trans (vsize_app_le _ _) ?_
      have : OTerm.K.vsize = 1 := rfl
      omega
    · have hc : (e ⬝ₒ f).closedB = false := closed_of_mem (by simpa using hm)
      rw [vsize_app_open hc] at hpos ⊢
      by_cases he : f = .var x ∧ e.mem x = false
      · rw [abs_app, if_neg hm, if_pos he]; omega
      · rw [abs_app, if_neg hm, if_neg he]
        have h1 := vsize_app_le (.S ⬝ₒ abs x e) (abs x f)
        have h2 := vsize_app_le .S (abs x e)
        have h3 : OTerm.S.vsize = 1 := rfl
        have ie := vsize_abs x e
        have if' := vsize_abs x f
        omega

-- ---------------------------------------------------------------------------
-- Counted β
-- ---------------------------------------------------------------------------

/-- **Counted β.**  `[x] M ⬝ N` weakly reduces to `M[N/x]` in at most
    `vsize M` steps. -/
theorem abs_beta_count (x : Nat) (N : OTerm) : ∀ M : OTerm,
    ∃ n, n ≤ M.vsize ∧ OWStepsN n (abs x M ⬝ₒ N) (M.subst (single x N))
  | .S => ⟨1, Nat.le_refl _, .step (.K _ _) (.refl _)⟩
  | .K => ⟨1, Nat.le_refl _, .step (.K _ _) (.refl _)⟩
  | .I => ⟨1, Nat.le_refl _, .step (.K _ _) (.refl _)⟩
  | .var y => by
    refine ⟨1, vsize_pos _, ?_⟩
    by_cases hy : y = x
    · subst hy
      rw [abs_var, if_pos rfl]
      show OWStepsN 1 (.I ⬝ₒ N) (single y N y)
      rw [single_self]
      exact .step (.I _) (.refl _)
    · rw [abs_var, if_neg hy]
      show OWStepsN 1 (.K ⬝ₒ .var y ⬝ₒ N) (single x N y)
      rw [single_ne N hy]
      exact .step (.K _ _) (.refl _)
  | .app e f => by
    by_cases hm : (OTerm.app e f).mem x = false
    · rw [abs_app, if_pos hm, subst_single_of_not_mem hm]
      exact ⟨1, vsize_pos _, .step (.K _ _) (.refl _)⟩
    · have hc : (e ⬝ₒ f).closedB = false := closed_of_mem (by simpa using hm)
      rw [vsize_app_open hc]
      by_cases he : f = .var x ∧ e.mem x = false
      · rw [abs_app, if_neg hm, if_pos he]
        cases he with
        | intro hf he =>
          subst hf
          refine ⟨0, Nat.zero_le _, ?_⟩
          show OWStepsN 0 (e ⬝ₒ N) (OTerm.app (e.subst (single x N)) (single x N x))
          rw [subst_single_of_not_mem he, single_self]
          exact .refl _
      · rw [abs_app, if_neg hm, if_neg he]
        cases abs_beta_count x N e with
        | intro a ha =>
          cases abs_beta_count x N f with
          | intro b hb =>
            refine ⟨a + b + 1, by omega, ?_⟩
            exact .step (.S _ _ _) (OWStepsN.app ha.2 hb.2)

theorem vsize_absN (xs : List Nat) (M : OTerm) :
    (absN xs M).vsize ≤ 3 ^ xs.length * M.vsize := by
  induction xs with
  | nil => simp [absN]
  | cons y ys ih =>
    show (abs y (absN ys M)).vsize ≤ _
    refine Nat.le_trans (vsize_abs y _) ?_
    rw [List.length_cons, Nat.pow_succ]
    calc 3 * (absN ys M).vsize ≤ 3 * (3 ^ ys.length * M.vsize) := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ ys.length * 3 * M.vsize := by
        rw [Nat.mul_comm 3, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm 3 M.vsize]

theorem vsize_substL : ∀ (xs : List Nat) (Ns : List Term) (M : OTerm),
    (substL xs Ns M).vsize ≤ M.vsize
  | x :: xs, N :: Ns, M =>
    Nat.le_trans (vsize_substL xs Ns _) (vsize_subst (x := x) (closedB_toO N) M)
  | [], _, _ => Nat.le_refl _
  | _ :: _, [], _ => Nat.le_refl _

/-- **Counted β for all the formals.**  `[x1] … [xk] M` applied to closed
    arguments weakly reduces to `M` with the arguments substituted in at
    most `3^k · vsize M` steps. -/
theorem absN_beta_count : ∀ (xs : List Nat) (Ns : List Term) (M : OTerm),
    Distinct xs → xs.length = Ns.length →
      ∃ n, n ≤ 3 ^ xs.length * M.vsize ∧
        OWStepsN n (appL (absN xs M) (Ns.map Term.toO)) (substL xs Ns M)
  | [], [], M, _, _ => ⟨0, Nat.zero_le _, .refl _⟩
  | x :: xs, N :: Ns, M, hd, hl => by
    cases abs_beta_count x N.toO (absN xs M) with
    | intro a ha =>
      have h1 := ha.2
      rw [absN_subst (fun z => mem_toO z N) hd.1 M] at h1
      cases absN_beta_count xs Ns (M.subst (single x N.toO)) hd.2 (Nat.succ.inj hl) with
      | intro b hb =>
        refine ⟨a + b, ?_, (OWStepsN.appL h1 _).trans hb.2⟩
        have e1 := Nat.le_trans ha.1 (vsize_absN xs M)
        have e2 := Nat.le_trans hb.1
          (Nat.mul_le_mul_left (3 ^ xs.length) (vsize_subst (closedB_toO N) M))
        rw [List.length_cons, Nat.pow_succ]
        have e3 : 3 ^ xs.length * M.vsize + 3 ^ xs.length * M.vsize ≤
            3 ^ xs.length * 3 * M.vsize := by
          rw [Nat.mul_assoc, Nat.mul_comm 3 M.vsize, ← Nat.mul_assoc]
          omega
        omega
  | [], _ :: _, _, _, hl => by cases hl
  | _ :: _, [], _, _, hl => by cases hl
