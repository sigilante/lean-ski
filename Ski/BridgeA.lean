import Ski.CostAdd
open Term

/-!
# The threaded compilation converges

The prover runs the threaded compilation `compiledA` (`Ski/CostAdd.lean`),
which bounds the cost of additively affine realizers.  `Ski/Bridge.lean`
proves convergence for the plain compilation `compiled`.  This file proves
it for `compiledA`, so that both theorems speak of the term the prover runs.

**The theorem** (`compiledA_converges`).  Let a realizer be typed and
closed, and let every constant realize its type.  Then its threaded
compiled term converges.  No affinity is assumed: the theorem covers
every stratum-1 and stratum-2 realizer.

**The method** is Tait's reducibility `RS`, as in `Ski/Bridge.lean`.  Only
the case differs.  The threaded case `s (λ a ȳ. F a) (λ a ȳ. G a) ȳ`
selects a continuation, which receives the injected value and the shared
variables' own values.  Its body is then `F a` under the environment
extended at `a` alone (`overrideC_brS`).
-/

namespace Rz

open Tm

variable {β γ : Type} (ι : γ → Term)

/-- The occurrence of a name in `λ ȳ. b`, for a name outside `ȳ`. -/
theorem lamsS_occurs_out {n : Nat} (b : Src) : ∀ zs : List Nat, n ∉ zs →
    (lamsS zs b).occurs n = b.occurs n
  | [], _ => rfl
  | z :: zs, hz => by
    show (z != n && (lamsS zs b).occurs n) = b.occurs n
    rw [lamsS_occurs_out b zs (fun h => hz (.tail _ h)),
      bne_iff_ne.2 (fun e => hz (by rw [← e]; exact .head _)), Bool.true_and]

/-- A name bound by `λ ȳ` does not occur free in `λ ȳ. b`. -/
theorem lamsS_occurs_in {n : Nat} (b : Src) : ∀ zs : List Nat, n ∈ zs →
    (lamsS zs b).occurs n = false
  | [], hz => by cases hz
  | z :: zs, hz => by
    show (z != n && (lamsS zs b).occurs n) = false
    by_cases hzn : z = n
    · rw [hzn, bne_self_eq_false, Bool.false_and]
    · cases hz with
      | head => exact absurd rfl hzn
      | tail _ hz => rw [lamsS_occurs_in b zs hz, Bool.and_false]

/-- **A continuation is closed** when its body's free names below `d` are
    threaded and none lies above `d`. -/
theorem brS_closed {d : Nat} {ys : List Nat} {F : Src} (h1 : ∀ n, d < n → F.cnt n = 0)
    (h2 : ∀ n, n < d → n ∉ ys → F.occurs n = false) : ∀ n, (brS d ys F).occurs n = false := by
  intro n
  show (d != n && (lamsS ys (F ⬝ₛ .var d)).occurs n) = false
  by_cases hn : d = n
  · rw [hn, bne_self_eq_false, Bool.false_and]
  · by_cases hny : n ∈ ys
    · rw [lamsS_occurs_in _ ys hny, Bool.and_false]
    · rw [lamsS_occurs_out _ ys hny]
      show (d != n && (F.occurs n || (d == n))) = false
      have hF : F.occurs n = false := by
        by_cases hlt : n < d
        · exact h2 n hlt hny
        · cases ho : F.occurs n with
          | false => rfl
          | true => have := Src.cnt_pos_of_occurs ho; have := h1 n (by omega); omega
      rw [hF, beq_false_of_ne hn, Bool.false_or, Bool.and_false]

/-- The threaded branch's continuation is closed. -/
theorem brS_trA_closed {d : Nat} {h : Tm γ} {ys : List Nat} (hd : closedAt d h)
    (hocc : ∀ n, n < d → n ∉ ys → (trA ι d h).occurs n = false) :
    ∀ n, (brS d ys (trA ι d h)).occurs n = false :=
  brS_closed (fun n hn => by
    have := Src.cnt_trA ι h d n hd
    rw [if_neg (by omega)] at this
    omega) hocc

/-- The continuation's formals, given the injected value and the shared
    variables' own values, extend the environment at `a` alone. -/
theorem overrideC_brS (γ : Nat → Term) (a : Nat) (N : Term) (ys : List Nat) (hy : a ∉ ys) :
    overrideC γ (a :: ys) (N :: ys.map γ) = updC γ a N := by
  show overrideC (updC γ a N) ys (ys.map γ) = updC γ a N
  have e : ys.map γ = ys.map (updC γ a N) := by
    apply List.map_congr_left
    intro y hy'
    unfold updC
    rw [if_neg (fun e => hy (by rw [← e]; exact hy'))]
  rw [e, overrideC_self]

/-- The environment, changed at the depth, still realizes the context. -/
theorem EnvOK.upd_depth {d : Nat} {Γ : Nat → Ty β} {γ : Nat → Term} (h : EnvOK d Γ γ)
    (N : Term) : EnvOK d Γ (updC γ d N) := by
  intro i hi
  show RS (Γ i) (updC γ d N (d - 1 - i))
  unfold updC
  rw [if_neg (by omega)]
  exact h i hi

/-- A selected continuation, applied to the injected value and the shared
    variables, weakly reduces to the branch applied to the value. -/
theorem brS_beta (sc : List Nat) (d : Nat) (ys : List Nat) (F : Src) (γ : Nat → Term) (N : Term)
    (hc : ∀ n, (brS d ys F).occurs n = false) (hy : d ∉ ys) :
    WSteps (appT ((comp sc (brS d ys F)).close γ ⬝ N) (ys.map γ))
      ((comp (d :: ys) F).close (updC γ d N) ⬝ N) := by
  rw [comp_brS sc d ys F hc]
  have h := absN_beta_close (d :: ys) (comp (d :: ys) F ⬝ₒ .var d) γ (N :: ys.map γ)
    (by rw [List.length_cons, List.length_cons, List.length_map])
  rw [overrideC_brS γ d N ys hy] at h
  have e : (comp (d :: ys) F ⬝ₒ OTerm.var d).close (updC γ d N) =
      (comp (d :: ys) F).close (updC γ d N) ⬝ N := by
    show (comp (d :: ys) F).close (updC γ d N) ⬝ updC γ d N d = _
    unfold updC
    rw [if_pos rfl]
  rw [e] at h
  exact h

/-- The fundamental lemma for the threaded translation. -/
theorem semA {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : ∀ c, RS (sig c) (ι c)) :
    ∀ d, closedAt d t → ∀ γ, EnvOK d Γ γ → ∀ sc,
      RS A ((absN (trA ι d t).peel.1 (comp sc (trA ι d t).peel.2)).close γ) := by
  have usual : ∀ {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β},
      (∀ d, closedAt d t → ∀ γ, EnvOK d Γ γ → ∀ sc,
        RS A ((absN (trA ι d t).peel.1 (comp sc (trA ι d t).peel.2)).close γ)) →
      ∀ d, closedAt d t → ∀ γ, EnvOK d Γ γ → ∀ sc, RS A ((comp sc (trA ι d t)).close γ) := by
    intro Γ t A ih d hd γ hγ sc
    cases t with
    | lam b =>
      cases comp_lam_close sc d (trA ι (d + 1) b) γ with
      | intro sc' hw => exact RS.back A hw (ih d hd γ hγ sc')
    | case s f g =>
      have hi := ih d hd γ hγ sc
      cases appS_app (sharedS d (trA ι d f) (trA ι d g))
        (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f))
        (brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g)) with
      | intro f' h => cases h with
        | intro a' h =>
          have e : trA ι d (.case s f g) = f' ⬝ₛ a' := h
          rw [e] at hi ⊢
          exact hi
    | _ => exact ih d hd γ hγ sc
  induction h with
  | var Γ n =>
    intro d hd γ hγ sc
    exact hγ n hd
  | const Γ c =>
    intro d _ γ _ sc
    show RS (sig c) ((ι c).toO.close γ)
    rw [close_toO]
    exact hc c
  | @lam Γ A B b _ ih =>
    intro d hd γ hγ sc
    show RS (.arr A B) ((abs d (absN (trA ι (d + 1) b).peel.1 (comp sc (trA ι (d + 1) b).peel.2))).close γ)
    intro N hN
    exact RS.back B (abs_beta_close d _ γ N) (ih (d + 1) hd (updC γ d N) (hγ.cons hN) sc)
  | app _ _ ihf iha =>
    intro d hd γ hγ sc
    exact (usual ihf d hd.1 γ hγ sc) _ (usual iha d hd.2 γ hγ sc)
  | pair _ _ iha ihb =>
    intro d hd γ hγ sc
    show RS _ (pairG.toO.close γ ⬝ (comp sc (trA ι d _)).close γ ⬝ (comp sc (trA ι d _)).close γ)
    rw [close_toO]
    exact RS.pair (usual iha d hd.1 γ hγ sc) (usual ihb d hd.2 γ hγ sc)
  | @fst Γ A B t _ ih =>
    intro d hd γ hγ sc
    cases (usual ih d hd γ hγ sc).2 with
    | intro a hp =>
      cases hp with
      | intro b hp =>
        exact RS.back A ((hp.1 _).trans (projS_beta sc d true γ a b)) hp.2.1
  | @snd Γ A B t _ ih =>
    intro d hd γ hγ sc
    cases (usual ih d hd γ hγ sc).2 with
    | intro a hp =>
      cases hp with
      | intro b hp =>
        exact RS.back B ((hp.1 _).trans (projS_beta sc d false γ a b)) hp.2.2
  | inl _ ih =>
    intro d hd γ hγ sc
    show RS _ (inlG.toO.close γ ⬝ (comp sc (trA ι d _)).close γ)
    rw [close_toO]
    exact RS.inl (usual ih d hd γ hγ sc)
  | inr _ ih =>
    intro d hd γ hγ sc
    show RS _ (inrG.toO.close γ ⬝ (comp sc (trA ι d _)).close γ)
    rw [close_toO]
    exact RS.inr (usual ih d hd γ hγ sc)
  | @case Γ A B C s f g _ _ _ ihs ihf ihg =>
    intro d hd γ hγ sc
    have hpeel : (trA ι d (.case s f g)).peel = ([], trA ι d (.case s f g)) := by
      cases appS_app (sharedS d (trA ι d f) (trA ι d g))
        (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f))
        (brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g)) with
      | intro f' h => cases h with
        | intro a' h =>
          have e : trA ι d (.case s f g) = f' ⬝ₛ a' := h
          rw [e]; rfl
    rw [hpeel]
    show RS C ((comp sc (appS (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f)
      ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g))
      (sharedS d (trA ι d f) (trA ι d g)))).close γ)
    have hcF := brS_trA_closed ι (ys := sharedS d (trA ι d f) (trA ι d g)) hd.2.1
      (fun n hn hny => (not_sharedS hn hny).1)
    have hcG := brS_trA_closed ι (ys := sharedS d (trA ι d f) (trA ι d g)) hd.2.2
      (fun n hn hny => (not_sharedS hn hny).2)
    generalize hys : sharedS d (trA ι d f) (trA ι d g) = ys at hcF hcG ⊢
    have hdy : d ∉ ys := fun h => by
      rw [← hys] at h
      have := sharedS_lt h
      omega
    rw [comp_appS, close_appL, List.map_map]
    have ecl : (OTerm.close γ ∘ OTerm.var) = γ := rfl
    rw [ecl]
    show RS C (appT ((comp sc (trA ι d s)).close γ ⬝ (comp sc (brS d ys (trA ι d f))).close γ
      ⬝ (comp sc (brS d ys (trA ι d g))).close γ) (ys.map γ))
    have hf := usual ihf d hd.2.1
    have hg := usual ihg d hd.2.2
    cases (usual ihs d hd.1 γ hγ sc).2 with
    | inl hl =>
      cases hl with
      | intro a ha =>
        exact RS.back C ((WSteps.appT (ha.1 _ _) _).trans
          (brS_beta sc d ys (trA ι d f) γ a hcF hdy))
          (hf (updC γ d a) (hγ.upd_depth a) (d :: ys) a ha.2)
    | inr hr =>
      cases hr with
      | intro b hb =>
        exact RS.back C ((WSteps.appT (hb.1 _ _) _).trans
          (brS_beta sc d ys (trA ι d g) γ b hcG hdy))
          (hg (updC γ d b) (hγ.upd_depth b) (d :: ys) b hb.2)

/-- **A typed closed realizer's threaded compiled term is related to its
    type.** -/
theorem compiledA_RS {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : ∀ c, RS (sig c) (ι c)) (ht : closedAt 0 t) :
    RS A (compiledA ι t) := by
  have hs := semA ι h hc
  cases t with
  | lam b =>
    cases comp_lam_close [] 0 (trA ι 1 b) (fun _ => K) with
    | intro sc' hw =>
      exact RS.back A hw (hs 0 ht (fun _ => K) (fun _ h => absurd h (Nat.not_lt_zero _)) sc')
  | case s f g =>
    have hi := hs 0 ht (fun _ => K) (fun _ h => absurd h (Nat.not_lt_zero _)) []
    cases appS_app (sharedS 0 (trA ι 0 f) (trA ι 0 g))
      (trA ι 0 s ⬝ₛ brS 0 (sharedS 0 (trA ι 0 f) (trA ι 0 g)) (trA ι 0 f))
      (brS 0 (sharedS 0 (trA ι 0 f) (trA ι 0 g)) (trA ι 0 g)) with
    | intro f' h => cases h with
      | intro a' h =>
        have e : trA ι 0 (.case s f g) = f' ⬝ₛ a' := h
        show RS A ((comp [] (trA ι 0 (.case s f g))).close fun _ => K)
        rw [e] at hi ⊢
        exact hi
  | _ => exact hs 0 ht (fun _ => K) (fun _ h => absurd h (Nat.not_lt_zero _)) []

/-- **The threaded compilation converges**: the threaded compiled term of a
    typed closed realizer, whose constants realize their types, reaches a
    weak head normal form in normal order. -/
theorem compiledA_converges {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β}
    (h : Typed sig Γ t A) (hc : ∀ c, RS (sig c) (ι c)) (ht : closedAt 0 t) :
    Converges (compiledA ι t) :=
  (compiledA_RS ι h hc ht).conv

/-- Applied to converging witnesses, a threaded compiled realizer of type
    `W₁ ⇒ … ⇒ Wₖ ⇒ B`, over base types, converges. -/
theorem compiledA_apply_converges {sig : γ → Ty β} {Γ : Nat → Ty β} {t : Tm γ}
    {B : Ty β} (Ws : List β) (h : Typed sig Γ t (Ws.foldr (fun w C => .arr (.base w) C) B))
    (hc : ∀ c, RS (sig c) (ι c)) (ht : closedAt 0 t) (ws : List Term) (hl : ws.length = Ws.length)
    (hw : ∀ w ∈ ws, Converges w) : Converges (appT (compiledA ι t) ws) := by
  have key : ∀ (Ws : List β) (ws : List Term) (r : Term), ws.length = Ws.length →
      (∀ w ∈ ws, Converges w) → RS (Ws.foldr (fun w C => .arr (.base w) C) B) r →
      RS B (appT r ws) := by
    intro Ws
    induction Ws with
    | nil => intro ws r hl _ hr; cases ws with
      | nil => exact hr
      | cons _ _ => cases hl
    | cons W Ws ih =>
      intro ws r hl hw hr
      cases ws with
      | nil => cases hl
      | cons w ws =>
        exact ih ws (r ⬝ w) (Nat.succ.inj hl) (fun v hv => hw v (.tail _ hv))
          (hr w (hw w (.head _)))
  exact (key Ws ws _ hl hw (compiledA_RS ι h hc ht)).conv

/-- **The threaded glue converges**, with no hypothesis left. -/
theorem glueA_converges {Γ : Nat → Ty β} {t : Tm Empty} {A : Ty β}
    (h : Typed Empty.elim Γ t A) (ht : closedAt 0 t) :
    Converges (compiledA Empty.elim t) :=
  compiledA_converges Empty.elim h (fun c => c.elim) ht

end Rz
