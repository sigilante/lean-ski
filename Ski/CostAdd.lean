import Ski.Cost
import Ski.Stratum
open Term

/-!
# Normal-order cost of additively affine realizers

`Ski/Cost.lean` bounds the compiled term of a multiplicatively affine
realizer.  Glue that carries a context through a case shares variables
across the case's two branches: OR distributed over a context (`orDist`,
`Ski/Sigma.lean`) does.  An additively affine realizer (`AffA`,
`Ski/Stratum.lean`) may do so, and there `S` copies the shared argument into
both continuations.

**The translation** (`trA`) is `trS` except at a case.  Every variable that
occurs in either branch is threaded through the case: the case selects a
continuation, and the continuation receives them.

  `case s f g`  ↦  `s (λ a ȳ. f a) (λ a ȳ. g a) ȳ`

`ȳ` lists the variables that occur in `f` or `g`.  Each continuation is a
closed source λ, which `comp` lifts to a closed combinator.  So every
variable occurs at most once in the compiled term (`Src.cnt_trA`), and the
graded typing of `Ski/Cost.lean` applies unchanged: a shared variable is
charged once, as the one argument of the case's result.

**The theorem** (`glue_head_bound_add`).  The compiled term of a closed,
typed, additively affine glue realizer, applied to witnesses that
head-normalize within `mᵢ` steps, head-normalizes within its leaf count
plus `Σ mᵢ` steps.
-/

namespace Rz

variable {β γ : Type} (ι : γ → Term)

open Tm

/-- `λ y₁ … yₖ. b`. -/
def lamsS : List Nat → Src → Src
  | [], b => b
  | y :: ys, b => .lam y (lamsS ys b)

/-- `f y₁ … yₖ`. -/
def appS : Src → List Nat → Src
  | f, [] => f
  | f, y :: ys => appS (f ⬝ₛ .var y) ys

/-- The continuation `λ a ȳ. F a`. -/
def brS (a : Nat) (ys : List Nat) (F : Src) : Src := .lam a (lamsS ys (F ⬝ₛ .var a))

/-- `[d - 1, …, 0]`. -/
def downFrom : Nat → List Nat
  | 0 => []
  | n + 1 => n :: downFrom n

/-- The names below `d` that occur in either branch. -/
def sharedS (d : Nat) (F G : Src) : List Nat :=
  (downFrom d).filter fun n => F.occurs n || G.occurs n

/-- A realizer as SKIjack source, the shared variables of each case threaded
    through its continuations. -/
def trA (d : Nat) : Tm γ → Src
  | .var i => .var (d - 1 - i)
  | .const c => .glob (ι c)
  | .app f a => trA d f ⬝ₛ trA d a
  | .lam b => .lam d (trA (d + 1) b)
  | .pair a b => .glob pairG ⬝ₛ trA d a ⬝ₛ trA d b
  | .fst t => trA d t ⬝ₛ projS d true
  | .snd t => trA d t ⬝ₛ projS d false
  | .inl a => .glob inlG ⬝ₛ trA d a
  | .inr b => .glob inrG ⬝ₛ trA d b
  | .case s f g =>
    appS (trA d s ⬝ₛ brS d (sharedS d (trA d f) (trA d g)) (trA d f)
      ⬝ₛ brS d (sharedS d (trA d f) (trA d g)) (trA d g)) (sharedS d (trA d f) (trA d g))

/-- The compiled term, threaded. -/
def compiledA (t : Tm γ) : Term := toTerm (comp [] (trA ι 0 t))

-- ---------------------------------------------------------------------------
-- Occurrences
-- ---------------------------------------------------------------------------

theorem Src.cnt_zero_of_not_occurs {x : Nat} : ∀ {e : Src}, e.occurs x = false → e.cnt x = 0
  | .glob _, _ => rfl
  | .var y, h => by
    show (if y = x then 1 else 0) = 0
    have h' : (y == x) = false := h
    refine if_neg (fun e => ?_)
    have := (beq_iff_eq (a := y) (b := x)).2 e
    rw [h'] at this
    cases this
  | .app f a, h => by
    have h' := Bool.or_eq_false_iff.1 (show (f.occurs x || a.occurs x) = false from h)
    show f.cnt x + a.cnt x = 0
    rw [Src.cnt_zero_of_not_occurs h'.1, Src.cnt_zero_of_not_occurs h'.2]
  | .lam y b, h => by
    show (if y = x then 0 else b.cnt x) = 0
    by_cases hy : y = x
    · rw [if_pos hy]
    · rw [if_neg hy]
      have h' : (y != x && b.occurs x) = false := h
      rw [bne_iff_ne.2 hy, Bool.true_and] at h'
      exact Src.cnt_zero_of_not_occurs h'

theorem Src.cnt_appS (n : Nat) : ∀ (ys : List Nat) (f : Src),
    (appS f ys).cnt n = f.cnt n + ys.count n
  | [], f => by
    show f.cnt n = f.cnt n + List.count n []
    rw [List.count_nil]; exact (Nat.add_zero _).symm
  | y :: ys, f => by
    show (appS (f ⬝ₛ .var y) ys).cnt n = _
    rw [Src.cnt_appS n ys]
    show f.cnt n + (if y = n then 1 else 0) + ys.count n = f.cnt n + (y :: ys).count n
    by_cases hy : y = n
    · subst hy; rw [if_pos rfl, List.count_cons_self]; omega
    · rw [if_neg hy, List.count_cons_of_ne hy]; omega

theorem Src.cnt_lamsS (n : Nat) (b : Src) : ∀ ys : List Nat,
    (lamsS ys b).cnt n = if n ∈ ys then 0 else b.cnt n
  | [] => by show b.cnt n = if n ∈ ([] : List Nat) then 0 else b.cnt n; rw [if_neg List.not_mem_nil]
  | y :: ys => by
    show (if y = n then 0 else (lamsS ys b).cnt n) = _
    rw [Src.cnt_lamsS n b ys]
    by_cases hy : y = n
    · rw [if_pos hy, if_pos (by rw [hy]; exact .head _)]
    · rw [if_neg hy]
      by_cases hn : n ∈ ys
      · rw [if_pos hn, if_pos (.tail _ hn)]
      · rw [if_neg hn, if_neg (fun h => by cases h with
          | head => exact hy rfl
          | tail _ h => exact hn h)]

theorem Src.cnt_brS (n a : Nat) (ys : List Nat) (F : Src) :
    (brS a ys F).cnt n = if a = n ∨ n ∈ ys then 0 else F.cnt n := by
  show (if a = n then 0 else (lamsS ys (F ⬝ₛ .var a)).cnt n) = _
  rw [Src.cnt_lamsS]
  by_cases ha : a = n
  · rw [if_pos ha, if_pos (.inl ha)]
  · rw [if_neg ha]
    by_cases hn : n ∈ ys
    · rw [if_pos hn, if_pos (.inr hn)]
    · rw [if_neg hn, if_neg (fun h => by cases h with
        | inl h => exact ha h
        | inr h => exact hn h)]
      show F.cnt n + (if a = n then 1 else 0) = F.cnt n
      rw [if_neg ha, Nat.add_zero]

theorem mem_downFrom {m : Nat} : ∀ (n : Nat), m ∈ downFrom n ↔ m < n
  | 0 => ⟨fun h => (by cases h), fun h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    constructor
    · intro h
      cases h with
      | head => exact Nat.lt_succ_self _
      | tail _ h => exact Nat.lt_succ_of_lt ((mem_downFrom _).1 h)
    · intro h
      by_cases e : m = n
      · rw [e]; exact .head _
      · exact .tail _ ((mem_downFrom n).2 (by omega))

theorem nodup_downFrom : ∀ n : Nat, (downFrom n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => List.nodup_cons.2 ⟨fun h => Nat.lt_irrefl n ((mem_downFrom n).1 h), nodup_downFrom n⟩

theorem sharedS_lt {d n : Nat} {F G : Src} (h : n ∈ sharedS d F G) : n < d :=
  (mem_downFrom d).1 (List.mem_filter.1 h).1

theorem sharedS_nodup (d : Nat) (F G : Src) : (sharedS d F G).Nodup :=
  List.Pairwise.sublist List.filter_sublist (nodup_downFrom d)

theorem sharedS_occurs {d n : Nat} {F G : Src} (h : n ∈ sharedS d F G) :
    F.occurs n = true ∨ G.occurs n = true := by
  have := (List.mem_filter.1 h).2
  simp only [Bool.or_eq_true] at this
  exact this

theorem not_sharedS {d n : Nat} {F G : Src} (hn : n < d) (h : n ∉ sharedS d F G) :
    F.occurs n = false ∧ G.occurs n = false := by
  have h' : ¬ ((F.occurs n || G.occurs n) = true) := fun e =>
    h (List.mem_filter.2 ⟨(mem_downFrom d).2 hn, e⟩)
  cases hF : F.occurs n <;> cases hG : G.occurs n <;> simp_all

/-- **Occurrences, threaded**: a name occurs in the threaded source at most
    as often as its variable does in the realizer, under the additive count. -/
theorem Src.cnt_trA : ∀ (t : Tm γ) (d n : Nat), closedAt d t →
    (trA ι d t).cnt n ≤ if n < d then acnt (d - 1 - n) t else 0
  | .var j, d, n, h => by
    show (if d - 1 - j = n then 1 else 0) ≤ if n < d then (if j = d - 1 - n then 1 else 0) else 0
    have hj : j < d := h
    by_cases hn : n < d
    · rw [if_pos hn]
      by_cases e : d - 1 - j = n
      · rw [if_pos e, if_pos (by omega)]; exact Nat.le_refl 1
      · rw [if_neg e]; exact Nat.zero_le _
    · rw [if_neg hn, if_neg (by omega)]; exact Nat.le_refl 0
  | .const _, d, n, _ => by
    show 0 ≤ _
    exact Nat.zero_le _
  | .app f a, d, n, h => by
    have hf := Src.cnt_trA f d n h.1
    have ha := Src.cnt_trA a d n h.2
    show (trA ι d f).cnt n + (trA ι d a).cnt n ≤ _
    by_cases hn : n < d
    · rw [if_pos hn] at hf ha ⊢; show _ ≤ acnt _ f + acnt _ a; omega
    · rw [if_neg hn] at hf ha ⊢; omega
  | .lam b, d, n, h => by
    have hb := Src.cnt_trA b (d + 1) n h
    show (if d = n then 0 else (trA ι (d + 1) b).cnt n) ≤ if n < d then acnt (d - 1 - n + 1) b else 0
    by_cases e : d = n
    · rw [if_pos e]; exact Nat.zero_le _
    · rw [if_neg e]
      by_cases hn : n < d
      · rw [if_pos (by omega), show d + 1 - 1 - n = d - 1 - n + 1 by omega] at hb
        rw [if_pos hn]; exact hb
      · rw [if_neg (by omega)] at hb; rw [if_neg hn]; exact hb
  | .pair a b, d, n, h => by
    have ha := Src.cnt_trA a d n h.1
    have hb := Src.cnt_trA b d n h.2
    show 0 + (trA ι d a).cnt n + (trA ι d b).cnt n ≤ _
    by_cases hn : n < d
    · rw [if_pos hn] at ha hb ⊢; show _ ≤ acnt _ a + acnt _ b; omega
    · rw [if_neg hn] at ha hb ⊢; omega
  | .fst t, d, n, h => by
    have ht := Src.cnt_trA t d n h
    show (trA ι d t).cnt n + (projS d true).cnt n ≤ _
    rw [Src.cnt_projS, Nat.add_zero]; exact ht
  | .snd t, d, n, h => by
    have ht := Src.cnt_trA t d n h
    show (trA ι d t).cnt n + (projS d false).cnt n ≤ _
    rw [Src.cnt_projS, Nat.add_zero]; exact ht
  | .inl a, d, n, h => by
    have ha := Src.cnt_trA a d n h
    show 0 + (trA ι d a).cnt n ≤ _
    rw [Nat.zero_add]; exact ha
  | .inr b, d, n, h => by
    have hb := Src.cnt_trA b d n h
    show 0 + (trA ι d b).cnt n ≤ _
    rw [Nat.zero_add]; exact hb
  | .case s f g, d, n, h => by
    have hs := Src.cnt_trA s d n h.1
    have hf := Src.cnt_trA f d n h.2.1
    have hg := Src.cnt_trA g d n h.2.2
    show (appS (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f)
      ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g))
      (sharedS d (trA ι d f) (trA ι d g))).cnt n ≤ _
    generalize hys : sharedS d (trA ι d f) (trA ι d g) = ys
    rw [Src.cnt_appS]
    show (trA ι d s).cnt n + (brS d ys (trA ι d f)).cnt n + (brS d ys (trA ι d g)).cnt n
      + ys.count n ≤ _
    rw [Src.cnt_brS, Src.cnt_brS]
    by_cases hn : n < d
    · rw [if_pos hn] at hs hf hg ⊢
      show _ ≤ acnt _ s + max (acnt _ f) (acnt _ g)
      by_cases hy : n ∈ ys
      · rw [if_pos (.inr hy), if_pos (.inr hy)]
        have hc : ys.count n = 1 := by
          rw [← hys] at hy ⊢
          rw [List.Nodup.count (sharedS_nodup d _ _), if_pos hy]
        rw [← hys] at hy
        have hpos : 1 ≤ max (acnt (d - 1 - n) f) (acnt (d - 1 - n) g) := by
          cases sharedS_occurs hy with
          | inl h1 => have := Src.cnt_pos_of_occurs h1; omega
          | inr h1 => have := Src.cnt_pos_of_occurs h1; omega
        omega
      · have hno := not_sharedS hn (by rw [hys]; exact hy)
        rw [Src.cnt_zero_of_not_occurs hno.1, Src.cnt_zero_of_not_occurs hno.2,
          List.count_eq_zero_of_not_mem hy]
        have e1 : (if d = n ∨ n ∈ ys then 0 else 0) = 0 := by split <;> rfl
        rw [e1]
        omega
    · rw [if_neg hn] at hs hf hg ⊢
      have hy : n ∉ ys := fun hy => by rw [← hys] at hy; exact hn (sharedS_lt hy)
      rw [List.count_eq_zero_of_not_mem hy]
      have e1 : (if d = n ∨ n ∈ ys then 0 else (trA ι d f).cnt n) = 0 := by split <;> omega
      have e2 : (if d = n ∨ n ∈ ys then 0 else (trA ι d g).cnt n) = 0 := by split <;> omega
      rw [e1, e2]
      omega

-- ---------------------------------------------------------------------------
-- Compiling the threaded forms
-- ---------------------------------------------------------------------------

theorem appS_app : ∀ (ys : List Nat) (f a : Src), ∃ f' a', appS (f ⬝ₛ a) ys = f' ⬝ₛ a'
  | [], f, a => ⟨f, a, rfl⟩
  | y :: ys, f, a => appS_app ys (f ⬝ₛ a) (.var y)

theorem comp_appS (sc : List Nat) : ∀ (ys : List Nat) (X : Src),
    comp sc (appS X ys) = appL (comp sc X) (ys.map OTerm.var)
  | [], _ => rfl
  | y :: ys, X => comp_appS sc ys (X ⬝ₛ .var y)

theorem lamsS_peel (b : Src) (hb : b.peel.1 = []) : ∀ ys : List Nat,
    (lamsS ys b).peel = (ys, b.peel.2)
  | [] => by
    show b.peel = ([], b.peel.2)
    rw [← hb]
  | y :: ys => by
    show (y :: (lamsS ys b).peel.1, (lamsS ys b).peel.2) = (y :: ys, b.peel.2)
    rw [lamsS_peel b hb ys]

/-- A closed continuation compiles to one combinator: `[a ȳ] (F a)`. -/
theorem comp_brS (sc : List Nat) (a : Nat) (ys : List Nat) (F : Src)
    (hc : ∀ n, (brS a ys F).occurs n = false) :
    comp sc (brS a ys F) = absN (a :: ys) (comp (a :: ys) F ⬝ₒ .var a) := by
  show compLam (sc.filter fun s => (brS a ys F).occurs s) [a] (lamsS ys (F ⬝ₛ .var a)) = _
  rw [filter_false_nil hc sc, compLam_chain, lamsS_peel _ rfl]
  rfl

theorem overrideG_ext (Γ : Nat → GTy β) (a : Nat) (A : GTy β) (ys : List Nat) (hy : a ∉ ys) :
    overrideG (extG Γ a A) ys (ys.map Γ) = extG Γ a A := by
  have e : ys.map Γ = ys.map (extG Γ a A) := by
    apply List.map_congr_left
    intro y hy'
    unfold extG
    rw [if_neg (fun e => hy (by rw [← e]; exact hy'))]
  rw [e, overrideG_self]

/-- **A continuation is typed**: `λ a ȳ. F a : A ⊸ Ȳ ⊸ C`, the shared
    variables at their own types. -/
theorem brS_OG {Γc : Nat → GTy β} {sc : List Nat} {a : Nat} {ys : List Nat} {F : Src}
    {A C : GTy β} (hc : ∀ n, (brS a ys F).occurs n = false) (hay : a ∉ ys) (hys : ys.Nodup)
    (hF : OG (extG Γc a A) (comp (a :: ys) F) (.lin A C))
    (hca : (comp (a :: ys) F).count a = 0)
    (hcy : ∀ y ∈ ys, (comp (a :: ys) F).count y ≤ 1) :
    OG Γc (comp sc (brS a ys F)) (.lin A (arrowsG (ys.map Γc) C)) := by
  rw [comp_brS sc a ys F hc]
  refine absN_OG (a :: ys) (A :: ys.map Γc) Γc _ C (by simp) ⟨hay, distinct_of_nodup hys⟩ ?_ ?_
  · show OG (overrideG (extG Γc a A) ys (ys.map Γc)) _ _
    rw [overrideG_ext Γc a A ys hay]
    exact .appL hF (OG.var' (by unfold extG; rw [if_pos rfl]))
  · intro x hx
    show (comp (a :: ys) F).count x + (if a = x then 1 else 0) ≤ 1
    cases hx with
    | head => rw [hca, if_pos rfl]; exact Nat.le_refl 1
    | tail _ hx =>
      rw [if_neg (fun e => hay (by rw [e]; exact hx)), Nat.add_zero]
      exact hcy x hx

theorem trA_peel : ∀ (t : Tm γ) (d : Nat),
    Distinct (trA ι d t).peel.1 ∧ ∀ n ∈ (trA ι d t).peel.1, d ≤ n
  | .lam b, d => by
    have ih := trA_peel b (d + 1)
    refine ⟨⟨fun h => by have := ih.2 d h; omega, ih.1⟩, fun n hn => ?_⟩
    cases hn with
    | head => exact Nat.le_refl d
    | tail _ h => have := ih.2 n h; omega
  | .case s f g, d => by
    show Distinct (appS _ _).peel.1 ∧ ∀ n ∈ (appS _ _).peel.1, d ≤ n
    cases appS_app (sharedS d (trA ι d f) (trA ι d g))
      (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f))
      (brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g)) with
    | intro f' h => cases h with
      | intro a' h => rw [h]; exact ⟨trivial, fun _ h => by cases h⟩
  | .var _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .const _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .app _ _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .pair _ _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .fst _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .snd _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .inl _, _ => ⟨trivial, fun _ h => by cases h⟩
  | .inr _, _ => ⟨trivial, fun _ h => by cases h⟩

/-- Additively, the free variables below `d` occur at most once. -/
def AffAtA (d : Nat) (t : Tm γ) : Prop := ∀ i, i < d → acnt i t ≤ 1

/-- The fundamental statement for the threaded translation. -/
def SemOGA (Γ : Nat → Ty β) (t : Tm γ) (A : Ty β) : Prop :=
  ∀ d (Γc : Nat → GTy β) (sc : List Nat), CtxOK d Γ Γc → closedAt d t → AffAtA d t → AffA t →
    sc.Nodup → OG Γc (absN (trA ι d t).peel.1 (comp sc (trA ι d t).peel.2)) (gty A)

theorem og_usualA {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (hs : SemOGA ι Γ t A) :
    ∀ d (Γc : Nat → GTy β) (sc : List Nat), CtxOK d Γ Γc → closedAt d t → AffAtA d t →
      AffA t → sc.Nodup → OG Γc (comp sc (trA ι d t)) (gty A) := by
  intro d Γc sc hΓ hd ha haff hsc
  cases t with
  | lam b =>
    show OG Γc (compLam (sc.filter fun s => (Src.lam d (trA ι (d + 1) b)).occurs s) [d]
      (trA ι (d + 1) b)) _
    rw [compLam_chain]
    generalize hcaps : sc.filter (fun s => (Src.lam d (trA ι (d + 1) b)).occurs s) = caps
    have hL : [d] ++ (trA ι (d + 1) b).peel.1 = (trA ι d (.lam b)).peel.1 := rfl
    have hB : (trA ι (d + 1) b).peel.2 = (trA ι d (.lam b)).peel.2 := rfl
    rw [hL, hB]
    generalize hLL : (trA ι d (.lam b)).peel.1 = L
    have hcn : caps.Nodup := by rw [← hcaps]; exact List.Pairwise.sublist List.filter_sublist hsc
    have hLn : L.Nodup := by rw [← hLL]; exact nodup_of_distinct (trA_peel ι _ d).1
    have hdisj : ∀ c ∈ caps, c ∉ L := by
      intro c hc hcL
      rw [← hcaps] at hc
      have h1 := (List.mem_filter.1 hc).2
      rw [← hLL] at hcL
      have hcL' : c ∈ (Src.lam d (trA ι (d + 1) b)).peel.1 := hcL
      rw [Src.occurs_peel hcL'] at h1
      cases h1
    have hnd : (caps ++ L).Nodup :=
      List.nodup_append.2 ⟨hcn, hLn, fun a ha b hb e => hdisj a ha (e ▸ hb)⟩
    have hsem := hs d Γc (caps ++ L) hΓ hd ha haff hnd
    rw [hLL] at hsem
    unfold wrapLift
    rw [absN_append]
    refine OG.appL_vars caps (absN_OG caps (caps.map Γc) Γc _ _ (List.length_map _).symm
      (distinct_of_nodup hcn) (by rw [overrideG_self]; exact hsem) ?_)
    intro c hc
    rw [count_absN L _ (hdisj c hc)]
    refine Nat.le_trans (count_comp c _ (caps ++ L) (List.nodup_iff_count.1 hnd c)) ?_
    have hcL : c ∉ (trA ι d (.lam b)).peel.1 := by rw [hLL]; exact hdisj c hc
    rw [Src.cnt_peel c _ hcL]
    refine Nat.le_trans (Src.cnt_trA ι (.lam b) d c hd) ?_
    split
    · exact ha _ (by omega)
    · exact Nat.zero_le 1
  | var _ => exact hs d Γc sc hΓ hd ha haff hsc
  | const _ => exact hs d Γc sc hΓ hd ha haff hsc
  | app _ _ => exact hs d Γc sc hΓ hd ha haff hsc
  | pair _ _ => exact hs d Γc sc hΓ hd ha haff hsc
  | fst _ => exact hs d Γc sc hΓ hd ha haff hsc
  | snd _ => exact hs d Γc sc hΓ hd ha haff hsc
  | inl _ => exact hs d Γc sc hΓ hd ha haff hsc
  | inr _ => exact hs d Γc sc hΓ hd ha haff hsc
  | case s f g =>
    have := hs d Γc sc hΓ hd ha haff hsc
    cases appS_app (sharedS d (trA ι d f) (trA ι d g))
      (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f))
      (brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g)) with
    | intro f' h => cases h with
      | intro a' h =>
        have e : trA ι d (.case s f g) = f' ⬝ₛ a' := h
        rw [e] at this ⊢
        exact this

/-- **Compiled additively affine realizers are typed**, threaded. -/
theorem ogsemA {sig : γ → Ty β} (hq : ∀ c, Q (gty (sig c)) (ι c) (ι c).leaves)
    {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (h : Typed sig Γ t A) : SemOGA ι Γ t A := by
  induction h with
  | var Γ n =>
    intro d Γc sc hΓ hd _ _ _
    exact OG.var' (hΓ n hd)
  | const Γ c =>
    intro d Γc sc _ _ _ _ _
    exact .const (hq c)
  | @lam Γ A B b _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    show OG Γc (abs d (absN (trA ι (d + 1) b).peel.1 (comp sc (trA ι (d + 1) b).peel.2)))
      (.lin (gty A) (gty B))
    have ha' : AffAtA (d + 1) b := by
      intro i hi
      cases i with
      | zero => exact haff.1
      | succ i => exact ha i (by omega)
    have hog := ih (d + 1) (extG Γc d (gty A)) sc (hΓ.cons A) hd ha' haff.2 hsc
    refine abs_OG _ hog ?_
    have hdp : d ∉ (trA ι (d + 1) b).peel.1 := fun h => by
      have := (trA_peel ι b (d + 1)).2 d h; omega
    rw [count_absN _ _ hdp]
    refine Nat.le_trans (count_comp d _ sc (List.nodup_iff_count.1 hsc d)) ?_
    rw [Src.cnt_peel d _ hdp]
    refine Nat.le_trans (Src.cnt_trA ι b (d + 1) d hd) ?_
    rw [if_pos (by omega), show d + 1 - 1 - d = 0 by omega]
    exact haff.1
  | @app Γ A B f a _ _ ihf iha =>
    intro d Γc sc hΓ hd ha haff hsc
    have haf : AffAtA d f := fun i hi => by have := ha i hi; simp only [acnt] at this; omega
    have haa : AffAtA d a := fun i hi => by have := ha i hi; simp only [acnt] at this; omega
    exact .appL (og_usualA ι ihf d Γc sc hΓ hd.1 haf haff.1 hsc)
      (og_usualA ι iha d Γc sc hΓ hd.2 haa haff.2 hsc)
  | @pair Γ A B a b _ _ iha ihb =>
    intro d Γc sc hΓ hd ha haff hsc
    have haa : AffAtA d a := fun i hi => by have := ha i hi; simp only [acnt] at this; omega
    have hab : AffAtA d b := fun i hi => by have := ha i hi; simp only [acnt] at this; omega
    exact .appL (.appL (.const (Q_pairG _ _)) (og_usualA ι iha d Γc sc hΓ hd.1 haa haff.1 hsc))
      (og_usualA ι ihb d Γc sc hΓ hd.2 hab haff.2 hsc)
  | @fst Γ A B t _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.sub (og_usualA ι ih d Γc sc hΓ hd ha haff hsc) (.prodE _ _ _))
      (projS_OG sc d true Γc _ _)
  | @snd Γ A B t _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.sub (og_usualA ι ih d Γc sc hΓ hd ha haff hsc) (.prodE _ _ _))
      (projS_OG sc d false Γc _ _)
  | @inl Γ A B a _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.const (Q_inlG _ _)) (og_usualA ι ih d Γc sc hΓ hd ha haff hsc)
  | @inr Γ A B b _ ih =>
    intro d Γc sc hΓ hd ha haff hsc
    exact .appL (.const (Q_inrG _ _)) (og_usualA ι ih d Γc sc hΓ hd ha haff hsc)
  | @case Γ A B C s f g _ _ _ ihs ihf ihg =>
    intro d Γc sc hΓ hd ha haff hsc
    have has : AffAtA d s := fun i hi => by
      have := ha i hi; simp only [acnt] at this; omega
    have haf : AffAtA d f := fun i hi => by
      have := ha i hi; simp only [acnt] at this; omega
    have hag : AffAtA d g := fun i hi => by
      have := ha i hi; simp only [acnt] at this; omega
    have hpeel : (trA ι d (.case s f g)).peel = ([], trA ι d (.case s f g)) := by
      cases appS_app (sharedS d (trA ι d f) (trA ι d g))
        (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f))
        (brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g)) with
      | intro f' h => cases h with
        | intro a' h =>
          have e : trA ι d (.case s f g) = f' ⬝ₛ a' := h
          rw [e]; rfl
    rw [hpeel]
    show OG Γc (comp sc (appS (trA ι d s ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d f)
      ⬝ₛ brS d (sharedS d (trA ι d f) (trA ι d g)) (trA ι d g))
      (sharedS d (trA ι d f) (trA ι d g)))) (gty C)
    generalize hys : sharedS d (trA ι d f) (trA ι d g) = ys
    have hysn : ys.Nodup := by rw [← hys]; exact sharedS_nodup d _ _
    have hylt : ∀ y ∈ ys, y < d := fun y hy => by rw [← hys] at hy; exact sharedS_lt hy
    have hdy : d ∉ ys := fun h => by have := hylt d h; omega
    rw [comp_appS]
    refine OG.appL_vars ys ?_
    -- the continuations are closed
    have closedBr : ∀ (F : Src), (∀ n, d < n → F.cnt n = 0) →
        (∀ n, n < d → n ∉ ys → F.occurs n = false) → ∀ n, (brS d ys F).occurs n = false := by
      intro F h1 h2 n
      show (d != n && (lamsS ys (F ⬝ₛ .var d)).occurs n) = false
      by_cases hn : d = n
      · rw [hn, bne_self_eq_false, Bool.false_and]
      · have hlam : ∀ (zs : List Nat) (b : Src), n ∉ zs → (lamsS zs b).occurs n = b.occurs n := by
          intro zs b
          induction zs with
          | nil => intro _; rfl
          | cons z zs ih =>
            intro hz
            show (z != n && (lamsS zs b).occurs n) = b.occurs n
            rw [ih (fun h => hz (.tail _ h)), bne_iff_ne.2 (fun e => hz (by rw [← e]; exact .head _)),
              Bool.true_and]
        by_cases hny : n ∈ ys
        · have hlam' : ∀ (zs : List Nat) (b : Src), n ∈ zs → (lamsS zs b).occurs n = false := by
            intro zs b hz
            induction zs with
            | nil => cases hz
            | cons z zs ih =>
              show (z != n && (lamsS zs b).occurs n) = false
              by_cases hzn : z = n
              · rw [hzn, bne_self_eq_false, Bool.false_and]
              · cases hz with
                | head => exact absurd rfl hzn
                | tail _ hz => rw [ih hz, Bool.and_false]
          rw [hlam' ys _ hny, Bool.and_false]
        · rw [hlam ys _ hny]
          show (d != n && (F.occurs n || (d == n))) = false
          have hF : F.occurs n = false := by
            by_cases hlt : n < d
            · exact h2 n hlt hny
            · cases ho : F.occurs n with
              | false => rfl
              | true => have := Src.cnt_pos_of_occurs ho; have := h1 n (by omega); omega
          rw [hF, beq_false_of_ne hn, Bool.false_or, Bool.and_false]
    have brOG : ∀ (h : Tm γ) (H : Ty β), closedAt d h → AffAtA d h → AffA h →
        SemOGA ι Γ h (.arr H C) →
        (∀ y ∈ ys, acnt (d - 1 - y) h ≤ 1) → (∀ n, n < d → n ∉ ys → (trA ι d h).occurs n = false) →
        OG Γc (comp sc (brS d ys (trA ι d h))) (.lin (gty H) (arrowsG (ys.map Γc) (gty C))) := by
      intro h H hdh hah haffh ih hcnt hocc
      have hΓ' : CtxOK d Γ (extG Γc d (gty H)) := by
        intro i hi
        unfold extG
        rw [if_neg (by omega)]
        exact hΓ i hi
      have hsc' : (d :: ys).Nodup := List.nodup_cons.2 ⟨hdy, hysn⟩
      have hF := og_usualA ι ih d (extG Γc d (gty H)) (d :: ys) hΓ' hdh hah haffh hsc'
      refine brS_OG (closedBr _ (fun n hn => ?_) hocc) hdy hysn hF ?_ ?_
      · have := Src.cnt_trA ι h d n hdh
        rw [if_neg (by omega)] at this
        omega
      · have := Nat.le_trans (count_comp d (trA ι d h) (d :: ys) (List.nodup_iff_count.1 hsc' d))
          (Src.cnt_trA ι h d d hdh)
        rw [if_neg (Nat.lt_irrefl d)] at this
        omega
      · intro y hy
        refine Nat.le_trans (count_comp y (trA ι d h) (d :: ys) (List.nodup_iff_count.1 hsc' y)) ?_
        refine Nat.le_trans (Src.cnt_trA ι h d y hdh) ?_
        rw [if_pos (hylt y hy)]
        exact hcnt y hy
    have hcase := ha
    have hF := brOG f A hd.2.1 haf haff.2.1 ihf
      (fun y hy => by
        have := hcase (d - 1 - y) (by have := hylt y hy; omega)
        simp only [acnt] at this; omega)
      (fun n hn hny => (not_sharedS hn (by rw [hys]; exact hny)).1)
    have hG := brOG g B hd.2.2 hag haff.2.2 ihg
      (fun y hy => by
        have := hcase (d - 1 - y) (by have := hylt y hy; omega)
        simp only [acnt] at this; omega)
      (fun n hn hny => (not_sharedS hn (by rw [hys]; exact hny)).2)
    exact .appL (.appL (.sub (og_usualA ι ihs d Γc sc hΓ hd.1 has haff.1 hsc) (.sumE _ _ _)) hF) hG

/-- **A compiled additively affine realizer behaves at its type within its
    leaf count.** -/
theorem compiledA_Q {sig : γ → Ty β} (hq : ∀ c, Q (gty (sig c)) (ι c) (ι c).leaves)
    {Γ : Nat → Ty β} {t : Tm γ} {A : Ty β} (h : Typed sig Γ t A) (ht : closedAt 0 t)
    (haff : AffA t) : Q (gty A) (compiledA ι t) (compiledA ι t).leaves := by
  have hog := og_usualA ι (ogsemA ι hq h) 0 (fun _ => gty A) []
    (fun _ h => absurd h (Nat.not_lt_zero _)) ht (fun _ h => absurd h (Nat.not_lt_zero _)) haff
    List.nodup_nil
  have hclosed : ∀ x, (comp [] (trA ι 0 t)).mem x = false := fun x => by
    have hc := Nat.le_trans (count_comp x (trA ι 0 t) [] (Nat.zero_le 1)) (Src.cnt_trA ι t 0 x ht)
    rw [if_neg (Nat.not_lt_zero _)] at hc
    exact mem_false_of_count (Nat.le_zero.1 hc)
  have hs := hog.sound (γ := fun _ => K) (μ := fun _ => 0) (fun x hx => by rw [hclosed x] at hx; cases hx)
  rw [envsum_zero, Nat.add_zero] at hs
  show Q (gty A) ((comp [] (trA ι 0 t)).close fun _ => K)
    (Term.leaves ((comp [] (trA ι 0 t)).close fun _ => K))
  rw [leaves_close hclosed]
  exact hs

/-- **The glue's normal-order bound, additively.**  A closed, typed,
    additively affine realizer without constants, of type `W₁ ⇒ … ⇒ Wₖ ⇒ W`
    over base types, compiled with its shared variables threaded and applied
    to witnesses that head-normalize within `mᵢ` steps each, head-normalizes
    within its compiled term's leaf count plus `Σ mᵢ` steps. -/
theorem glue_head_bound_add {Γ : Nat → Ty β} {t : Tm Empty} {w : β} (Ws : List β)
    (h : Typed Empty.elim Γ t (Ws.foldr (fun v C => .arr (.base v) C) (.base w)))
    (ht : closedAt 0 t) (haff : AffA t) (wm : List (Term × Nat)) (hl : wm.length = Ws.length)
    (hw : ∀ p ∈ wm, HNB p.1 p.2) :
    HNB (appT (compiledA Empty.elim t) (wm.map Prod.fst))
      ((compiledA Empty.elim t).leaves + (wm.map Prod.snd).sum) := by
  have hQ := compiledA_Q Empty.elim (fun c => c.elim) h ht haff
  have key : ∀ (Ws : List β) (wm : List (Term × Nat)) (r : Term) (n : Nat),
      wm.length = Ws.length → (∀ p ∈ wm, HNB p.1 p.2) →
      Q (gty (Ws.foldr (fun v C => .arr (.base v) C) (.base w))) r n →
      HNB (appT r (wm.map Prod.fst)) (n + (wm.map Prod.snd).sum) := by
    intro Ws
    induction Ws with
    | nil =>
      intro wm r n hl _ hr
      cases wm with
      | nil => exact hr
      | cons _ _ => cases hl
    | cons v Ws ih =>
      intro wm r n hl hw hr
      cases wm with
      | nil => cases hl
      | cons p wm =>
        have h1 := ih wm (r ⬝ p.1) (n + p.2) (Nat.succ.inj hl) (fun q hq => hw q (.tail _ hq))
          (hr p.1 p.2 (hw p (.head _)))
        show HNB (appT (r ⬝ p.1) (wm.map Prod.fst)) (n + (p.2 + (wm.map Prod.snd).sum))
        rw [← Nat.add_assoc]
        exact h1
  exact key Ws wm _ _ hl hw hQ

/-- `λ x y. case (inl y) (λ a. fst (a, x)) (λ b. fst (x, b))`: `x` occurs in
    both branches, so the realizer is additively but not multiplicatively
    affine. -/
def sharedT : Tm Empty :=
  .lam (.lam (.case (.inl (.var 0)) (.lam (.fst (.pair (.var 0) (.var 2))))
    (.lam (.fst (.pair (.var 2) (.var 0))))))

theorem sharedT_not_aff : ¬ Tm.Aff sharedT := fun h => absurd h.1 (by decide)

theorem sharedT_affA : AffA sharedT :=
  ⟨by decide, by decide, trivial, ⟨by decide, trivial, trivial⟩, ⟨by decide, trivial, trivial⟩⟩

theorem sharedT_typed (Γ : Nat → Ty β) (w : β) :
    Typed Empty.elim Γ sharedT (.arr (.base w) (.arr (.base w) (.base w))) :=
  .lam (.lam (.case (A := .base w) (B := .base w) (.inl (.var _ 0))
    (.lam (.fst (B := .base w) (.pair (.var _ 0) (.var _ 2))))
    (.lam (.fst (B := .base w) (.pair (.var _ 2) (.var _ 0))))))

theorem sharedT_leaves : (compiledA Empty.elim sharedT).leaves = 78 := by decide

/-- **The additive bound, instantiated**: with the shared variable threaded,
    the compiled term applied to two witnesses head-normalizes within
    `78 + m₁ + m₂` steps. -/
theorem sharedT_bound (w₁ w₂ : Term) (m₁ m₂ : Nat) (h₁ : HNB w₁ m₁) (h₂ : HNB w₂ m₂) :
    HNB (compiledA Empty.elim sharedT ⬝ w₁ ⬝ w₂) (78 + (m₁ + (m₂ + 0))) := by
  have h := glue_head_bound_add (Γ := fun _ => .base ()) (w := ()) [(), ()] (sharedT_typed _ ())
    ⟨show 0 < 0 + 1 + 1 by decide,
      ⟨show 0 < 0 + 1 + 1 + 1 by decide, show 2 < 0 + 1 + 1 + 1 by decide⟩,
      ⟨show 2 < 0 + 1 + 1 + 1 by decide, show 0 < 0 + 1 + 1 + 1 by decide⟩⟩
    sharedT_affA [(w₁, m₁), (w₂, m₂)] rfl (by
      intro p hp
      cases hp with
      | head => exact h₁
      | tail _ hp => cases hp with
        | head => exact h₂
        | tail _ hp => cases hp)
  rw [sharedT_leaves] at h
  exact h

end Rz
