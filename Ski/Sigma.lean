import Ski.CostAdd
import Ski.Stratum2
open Term

/-!
# The Σ-protocol algebra's glue lies in stratum 1

The Σ-protocol algebra composes proofs of NP statements by AND, OR and
threshold (Cramer–Damgård–Schoenmakers).  Following the paper, only atoms,
AND and OR are primitive, and threshold is a fold over them.

**Formulas** (`SF`): atoms, `top`, `bot`, `and`, `or`.  **Threshold** (`thrF`)
is `k`-of-`φs`:

- `thr 0 φs = top`;
- `thr (k + 1) [] = bot`;
- `thr (k + 1) (φ :: φs) = (φ ∧ thr k φs) ∨ thr (k + 1) φs`: take the first
  component and `k` more, or skip it.

Realizer types (`den`): an atom's witness type is a base type, `∧` is a
product, `∨` a sum, and `top` is `U ⇒ U`, realized by the identity, so the
glue needs no constants.

**Proof plans** (`Plan φ`) record which parts the prover proves.  A plan for
`thr k φs` exists exactly when at least `k` components have plans
(`thrPlan_isSome`, `thrPlan_extract`).

**The glue** is the realizer transformations the algebra uses:
- composition: pairing, injections, threshold's take and skip, and the whole
  prover composition `compose p` of a plan, as a function of its witnesses;
- elimination: projections, split, case, commutation of `∧` and of `∨`, `∨`
  distributed over a context, and threshold weakening
  `thr (k + 1) φs ⇒ thr k φs`, a fold of cases.

**The theorem** (`glue_stratum1`): every glue term is in stratum 1, that is
closed, typed at its type, and additively affine (`Stratum1`).  Stratum 1 is
closed under application (`Stratum1.app`), so glue composed with glue stays
there.  A stratum-1 term's call-by-name reductions are shorter than its
additive size (`Stratum1.source_bound`), and its compiled term behaves at
its type within its combinator count (`Stratum1.compiled_bound`).

**The additive rule.**  Most of this glue is affine even under the raw
count.  OR distributed over a context (`orDist`) is not: the context appears
in both branches of a case, and only the additive count puts it in stratum 1
(`orDist_needs_additive`).

**Both conjuncts: the split.**  A projection uses one half of a pair.  A
term that uses both halves of one pair variable by projections,
`λp. (snd p, fst p)`, mentions `p` twice, so the census puts it in stratum 2
(`swapT_not_affA`).  The split `split p k` binds both halves at once, in
`k`'s two arguments, and mentions `p` once.  So AND-commutation by split,
`λp. split p (λ a b. (b, a))`, is in stratum 1 (`andComm_s1`), as is split
itself (`splitE_s1`).  The glue proved here is the list in
`glue_stratum1`.
-/

namespace Rz

open Tm

-- ---------------------------------------------------------------------------
-- Formulas, threshold, plans
-- ---------------------------------------------------------------------------

/-- Base types: an atom's witness type, the unit of `top`, and the empty type of `bot`. -/
inductive SBase where
  | atomT (i : Nat)
  | unitT
  | voidT

/-- Σ-formulas: threshold is derived. -/
inductive SF where
  | atom (i : Nat)
  | top
  | bot
  | and (φ ψ : SF)
  | or (φ ψ : SF)

/-- **Threshold**, `k` of `φs`, as a fold over AND and OR. -/
def thrF : Nat → List SF → SF
  | 0, [] => .top
  | 0, _ :: _ => .top
  | _ + 1, [] => .bot
  | k + 1, φ :: φs => .or (.and φ (thrF k φs)) (thrF (k + 1) φs)

/-- Realizer types. -/
def den : SF → Ty SBase
  | .atom i => .base (.atomT i)
  | .top => .arr (.base .unitT) (.base .unitT)
  | .bot => .base .voidT
  | .and φ ψ => .prod (den φ) (den ψ)
  | .or φ ψ => .sum (den φ) (den ψ)

/-- A proof plan: which parts the prover proves.  `bot` has none. -/
inductive Plan : SF → Type where
  | atom (i : Nat) : Plan (.atom i)
  | top : Plan .top
  | and {φ ψ : SF} : Plan φ → Plan ψ → Plan (.and φ ψ)
  | inl {φ ψ : SF} : Plan φ → Plan (.or φ ψ)
  | inr {φ ψ : SF} : Plan ψ → Plan (.or φ ψ)

/-- An optional plan for each component. -/
inductive OPlans : List SF → Type where
  | nil : OPlans []
  | cons {φ : SF} {φs : List SF} : Option (Plan φ) → OPlans φs → OPlans (φ :: φs)

/-- The number of components with plans. -/
def OPlans.count : {φs : List SF} → OPlans φs → Nat
  | _, .nil => 0
  | _, .cons none os => os.count
  | _, .cons (some _) os => os.count + 1

/-- No component planned. -/
def OPlans.empty : (φs : List SF) → OPlans φs
  | [] => .nil
  | _ :: φs => .cons Option.none (OPlans.empty φs)

/-- The greedy threshold plan: take a planned component whenever `k` more
    follow, else skip it. -/
def thrPlan : (k : Nat) → {φs : List SF} → OPlans φs → Option (Plan (thrF k φs))
  | 0, _, .nil => some .top
  | 0, _, .cons _ _ => some .top
  | _ + 1, _, .nil => none
  | k + 1, _, @OPlans.cons φ φs o os =>
    match o with
    | some p =>
      match thrPlan k os with
      | some r => some (.inl (.and p r))
      | none => (thrPlan (k + 1) os).map .inr
    | none => (thrPlan (k + 1) os).map .inr

/-- **Threshold, completeness**: if at least `k` components have plans, so
    does `thr k φs`. -/
theorem thrPlan_isSome : ∀ (k : Nat) {φs : List SF} (os : OPlans φs), k ≤ os.count →
    (thrPlan k os).isSome = true
  | 0, _, .nil, _ => rfl
  | 0, _, .cons _ _, _ => rfl
  | k + 1, _, .nil, h => by simp [OPlans.count] at h
  | k + 1, _, .cons none os, h => by
    have ih := thrPlan_isSome (k + 1) os (by simpa [OPlans.count] using h)
    show ((thrPlan (k + 1) os).map Plan.inr).isSome = true
    cases hr : thrPlan (k + 1) os with
    | none => rw [hr] at ih; cases ih
    | some r => rfl
  | k + 1, _, .cons (some p) os, h => by
    have ih := thrPlan_isSome k os (by simp only [OPlans.count] at h; omega)
    show (match thrPlan k os with
      | some r => some (Plan.inl (Plan.and p r))
      | none => (thrPlan (k + 1) os).map Plan.inr).isSome = true
    cases hr : thrPlan k os with
    | none => rw [hr] at ih; cases ih
    | some r => rfl

/-- **Threshold, soundness**: a plan for `thr k φs` plans at least `k`
    components. -/
def thrPlan_extract : (k : Nat) → (φs : List SF) → Plan (thrF k φs) →
    { os : OPlans φs // k ≤ os.count }
  | 0, [], _ => ⟨.nil, Nat.le_refl 0⟩
  | 0, _ :: φs, _ => ⟨.cons none (OPlans.empty φs), Nat.zero_le _⟩
  | k + 1, [], p => nomatch p
  | k + 1, φ :: φs, p =>
    match (p : Plan (.or (.and φ (thrF k φs)) (thrF (k + 1) φs))) with
    | .inl (.and a r) =>
      let e := thrPlan_extract k φs r
      ⟨.cons (some a) e.1, by show k + 1 ≤ e.1.count + 1; exact Nat.succ_le_succ e.2⟩
    | .inr r =>
      let e := thrPlan_extract (k + 1) φs r
      ⟨.cons none e.1, e.2⟩

-- ---------------------------------------------------------------------------
-- Stratum 1
-- ---------------------------------------------------------------------------

/-- **Stratum 1**: closed, typed at `A` in every context, and additively
    affine. -/
def Stratum1 (t : Tm Empty) (A : Ty SBase) : Prop :=
  closedAt 0 t ∧ (∀ Γ : Nat → Ty SBase, Typed Empty.elim Γ t A) ∧ AffA t

/-- **Stratum 1 is closed under application**: glue applied to glue stays in
    stratum 1. -/
theorem Stratum1.app {f a : Tm Empty} {A B : Ty SBase} (hf : Stratum1 f (.arr A B))
    (ha : Stratum1 a A) : Stratum1 (.app f a) B :=
  ⟨⟨hf.1, ha.1⟩, fun Γ => .app (hf.2.1 Γ) (ha.2.1 Γ), ⟨hf.2.2, ha.2.2⟩⟩

/-- A stratum-1 term's call-by-name reductions are shorter than its additive
    size. -/
theorem Stratum1.source_bound {t u : Tm Empty} {A : Ty SBase} {n : Nat} (h : Stratum1 t A)
    (hn : WHN n t u) : n < asz t :=
  wh_steps_lt hn h.2.2

/-- A stratum-1 term's compiled term behaves at its type within its
    combinator count. -/
theorem Stratum1.compiled_bound {t : Tm Empty} {A : Ty SBase} (h : Stratum1 t A) :
    Q (gty A) (compiledA Empty.elim t) (compiledA Empty.elim t).leaves :=
  compiledA_Q Empty.elim (fun c => c.elim) (h.2.1 fun _ => A) h.1 h.2.2

theorem closedAt_mono : ∀ {t : Tm Empty} {d e : Nat}, closedAt d t → d ≤ e → closedAt e t
  | .var _, _, _, h, hde => Nat.lt_of_lt_of_le h hde
  | .const _, _, _, _, _ => trivial
  | .app _ _, _, _, h, hde => ⟨closedAt_mono h.1 hde, closedAt_mono h.2 hde⟩
  | .lam b, _, _, h, hde => closedAt_mono (t := b) h (Nat.succ_le_succ hde)
  | .pair _ _, _, _, h, hde => ⟨closedAt_mono h.1 hde, closedAt_mono h.2 hde⟩
  | .fst u, _, _, h, hde => closedAt_mono (t := u) h hde
  | .snd u, _, _, h, hde => closedAt_mono (t := u) h hde
  | .inl u, _, _, h, hde => closedAt_mono (t := u) h hde
  | .inr u, _, _, h, hde => closedAt_mono (t := u) h hde
  | .case _ _ _, _, _, h, hde =>
    ⟨closedAt_mono h.1 hde, closedAt_mono h.2.1 hde, closedAt_mono h.2.2 hde⟩
  | .split _ _, _, _, h, hde => ⟨closedAt_mono h.1 hde, closedAt_mono h.2 hde⟩

/-- A term closed at depth `d` has no occurrences at indices from `d` on. -/
theorem acnt_closed : ∀ {t : Tm Empty} {d i : Nat}, closedAt d t → d ≤ i → acnt i t = 0
  | .var j, _, i, h, hdi => by
    show (if j = i then 1 else 0) = 0
    rw [if_neg (by have : j < _ := h; omega)]
  | .const _, _, _, _, _ => rfl
  | .app f a, _, _, h, hdi => by
    show acnt _ f + acnt _ a = 0
    rw [acnt_closed h.1 hdi, acnt_closed h.2 hdi]
  | .lam b, _, _, h, hdi => by
    show acnt (_ + 1) b = 0
    exact acnt_closed (d := _ + 1) h (Nat.succ_le_succ hdi)
  | .pair a b, _, _, h, hdi => by
    show acnt _ a + acnt _ b = 0
    rw [acnt_closed h.1 hdi, acnt_closed h.2 hdi]
  | .fst t, _, _, h, hdi => acnt_closed (t := t) h hdi
  | .snd t, _, _, h, hdi => acnt_closed (t := t) h hdi
  | .inl a, _, _, h, hdi => acnt_closed (t := a) h hdi
  | .inr b, _, _, h, hdi => acnt_closed (t := b) h hdi
  | .case s f g, _, _, h, hdi => by
    show acnt _ s + max (acnt _ f) (acnt _ g) = 0
    rw [acnt_closed h.1 hdi, acnt_closed h.2.1 hdi, acnt_closed h.2.2 hdi]
    rfl
  | .split t k, _, _, h, hdi => by
    show acnt _ t + acnt _ k = 0
    rw [acnt_closed h.1 hdi, acnt_closed h.2 hdi]

-- ---------------------------------------------------------------------------
-- The glue
-- ---------------------------------------------------------------------------

/-- `top`'s realizer, the identity. -/
def idT : Tm Empty := .lam (.var 0)
/-- AND introduction, `λ a b. (a, b)`. -/
def andI : Tm Empty := .lam (.lam (.pair (.var 1) (.var 0)))
/-- The projections. -/
def fstE : Tm Empty := .lam (.fst (.var 0))
def sndE : Tm Empty := .lam (.snd (.var 0))
/-- OR introduction. -/
def inlI : Tm Empty := .lam (.inl (.var 0))
def inrI : Tm Empty := .lam (.inr (.var 0))
/-- OR elimination, `λ s f g. case s f g`. -/
def caseE : Tm Empty := .lam (.lam (.lam (.case (.var 2) (.var 1) (.var 0))))
/-- AND elimination by split, `λ p k. split p k`. -/
def splitE : Tm Empty := .lam (.lam (.split (.var 1) (.var 0)))
/-- AND commutes, by split: `λ p. split p (λ a b. (b, a))`.  Each half of
    the pair is bound once. -/
def andComm : Tm Empty := .lam (.split (.var 0) (.lam (.lam (.pair (.var 0) (.var 1)))))
/-- OR commutes: `λ s. case s (λ a. inr a) (λ b. inl b)`. -/
def orComm : Tm Empty := .lam (.case (.var 0) (.lam (.inr (.var 0))) (.lam (.inl (.var 0))))
/-- Threshold, take the first component: `λ a r. inl (a, r)`. -/
def thrTake : Tm Empty := .lam (.lam (.inl (.pair (.var 1) (.var 0))))
/-- Threshold, skip the first component: `λ r. inr r`. -/
def thrSkip : Tm Empty := .lam (.inr (.var 0))

/-- **Threshold weakening**, `thr (k + 1) φs ⇒ thr k φs`: a fold of cases.  A
    taken component is dropped, keeping the rest; a skipped one recurses. -/
def thrWeaken : Nat → List SF → Tm Empty
  | 0, [] => .lam idT
  | _ + 1, [] => .lam (.var 0)
  | 0, _ :: _ => .lam idT
  | k + 1, _ :: φs =>
    .lam (.case (.var 0) (.lam (.inr (.snd (.var 0))))
      (.lam (.inr (.app (thrWeaken (k + 1) φs) (.var 0)))))

theorem idT_s1 : Stratum1 idT (den .top) :=
  ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.var _ 0), ⟨by decide, trivial⟩⟩

theorem andI_s1 (φ ψ : SF) : Stratum1 andI (.arr (den φ) (.arr (den ψ) (den (.and φ ψ)))) :=
  ⟨⟨show 1 < 0 + 1 + 1 by omega, show 0 < 0 + 1 + 1 by omega⟩,
   fun _ => .lam (.lam (.pair (.var _ 1) (.var _ 0))), ⟨by decide, by decide, trivial, trivial⟩⟩

theorem fstE_s1 (φ ψ : SF) : Stratum1 fstE (.arr (den (.and φ ψ)) (den φ)) :=
  ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.fst (.var _ 0)), ⟨by decide, trivial⟩⟩

theorem sndE_s1 (φ ψ : SF) : Stratum1 sndE (.arr (den (.and φ ψ)) (den ψ)) :=
  ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.snd (.var _ 0)), ⟨by decide, trivial⟩⟩

theorem inlI_s1 (φ ψ : SF) : Stratum1 inlI (.arr (den φ) (den (.or φ ψ))) :=
  ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.inl (.var _ 0)), ⟨by decide, trivial⟩⟩

theorem inrI_s1 (φ ψ : SF) : Stratum1 inrI (.arr (den ψ) (den (.or φ ψ))) :=
  ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.inr (.var _ 0)), ⟨by decide, trivial⟩⟩

theorem caseE_s1 (φ ψ : SF) (C : Ty SBase) :
    Stratum1 caseE (.arr (den (.or φ ψ)) (.arr (.arr (den φ) C) (.arr (.arr (den ψ) C) C))) :=
  ⟨⟨show 2 < 0 + 1 + 1 + 1 by omega, show 1 < 0 + 1 + 1 + 1 by omega,
    show 0 < 0 + 1 + 1 + 1 by omega⟩,
   fun _ => .lam (.lam (.lam (.case (.var _ 2) (.var _ 1) (.var _ 0)))),
   ⟨by decide, by decide, by decide, trivial, trivial, trivial⟩⟩

theorem splitE_s1 (φ ψ : SF) (C : Ty SBase) :
    Stratum1 splitE (.arr (den (.and φ ψ)) (.arr (.arr (den φ) (.arr (den ψ) C)) C)) :=
  ⟨⟨show 1 < 0 + 1 + 1 by omega, show 0 < 0 + 1 + 1 by omega⟩,
   fun _ => .lam (.lam (.split (.var _ 1) (.var _ 0))),
   ⟨by decide, by decide, trivial, trivial⟩⟩

theorem andComm_s1 (φ ψ : SF) : Stratum1 andComm (.arr (den (.and φ ψ)) (den (.and ψ φ))) :=
  ⟨⟨show 0 < 0 + 1 by omega, show 0 < 0 + 1 + 1 + 1 by omega, show 1 < 0 + 1 + 1 + 1 by omega⟩,
   fun _ => .lam (.split (.var _ 0) (.lam (.lam (.pair (.var _ 0) (.var _ 1))))),
   ⟨by decide, trivial, by decide, by decide, trivial, trivial⟩⟩

theorem orComm_s1 (φ ψ : SF) : Stratum1 orComm (.arr (den (.or φ ψ)) (den (.or ψ φ))) :=
  ⟨⟨show 0 < 0 + 1 by omega, show 0 < 0 + 1 + 1 by omega, show 0 < 0 + 1 + 1 by omega⟩,
   fun _ => .lam (.case (.var _ 0) (.lam (.inr (.var _ 0))) (.lam (.inl (.var _ 0)))),
   ⟨by decide, trivial, ⟨by decide, trivial⟩, ⟨by decide, trivial⟩⟩⟩

theorem thrTake_s1 (φ : SF) (k : Nat) (φs : List SF) :
    Stratum1 thrTake (.arr (den φ) (.arr (den (thrF k φs)) (den (thrF (k + 1) (φ :: φs))))) :=
  ⟨⟨show 1 < 0 + 1 + 1 by omega, show 0 < 0 + 1 + 1 by omega⟩,
   fun _ => .lam (.lam (.inl (.pair (.var _ 1) (.var _ 0)))),
   ⟨by decide, by decide, trivial, trivial⟩⟩

theorem thrSkip_s1 (φ : SF) (k : Nat) (φs : List SF) :
    Stratum1 thrSkip (.arr (den (thrF (k + 1) φs)) (den (thrF (k + 1) (φ :: φs)))) :=
  ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.inr (.var _ 0)), ⟨by decide, trivial⟩⟩

theorem thrWeaken_s1 : ∀ (k : Nat) (φs : List SF),
    Stratum1 (thrWeaken k φs) (.arr (den (thrF (k + 1) φs)) (den (thrF k φs)))
  | 0, [] => ⟨show 0 < 0 + 1 + 1 by omega, fun _ => .lam (.lam (.var _ 0)),
      ⟨by decide, by decide, trivial⟩⟩
  | k + 1, [] => ⟨show 0 < 0 + 1 by omega, fun _ => .lam (.var _ 0), ⟨by decide, trivial⟩⟩
  | 0, _ :: _ => ⟨show 0 < 0 + 1 + 1 by omega, fun _ => .lam (.lam (.var _ 0)),
      ⟨by decide, by decide, trivial⟩⟩
  | k + 1, φ :: φs => by
    have ih := thrWeaken_s1 (k + 1) φs
    refine ⟨⟨show 0 < 0 + 1 by omega, show 0 < 0 + 1 + 1 by omega,
      closedAt_mono ih.1 (by omega), show 0 < 0 + 1 + 1 by omega⟩, fun Γ => ?_, ?_⟩
    · exact .lam (.case (.var _ 0) (.lam (.inr (.snd (.var _ 0))))
        (.lam (.inr (.app (ih.2.1 _) (.var _ 0)))))
    · refine ⟨?_, trivial, ⟨by decide, trivial⟩, ⟨?_, ih.2.2, trivial⟩⟩
      · show acnt 0 (.case (.var 0) (.lam (.inr (.snd (.var 0))))
          (.lam (.inr (.app (thrWeaken (k + 1) φs) (.var 0))))) ≤ 1
        show (if (0 : Nat) = 0 then 1 else 0) + max (acnt 1 (.inr (.snd (.var 0) : Tm Empty)))
          (acnt 1 (thrWeaken (k + 1) φs) + acnt 1 (.var 0 : Tm Empty)) ≤ 1
        rw [acnt_closed ih.1 (by omega)]
        decide
      · show acnt 0 (thrWeaken (k + 1) φs) + acnt 0 (.var 0 : Tm Empty) ≤ 1
        rw [acnt_closed ih.1 (by omega)]
        decide

/-- **OR distributes over a context**, `D ⇒ A ∨ B ⇒ (A ∧ D) ∨ (B ∧ D)`:
    `λ d s. case s (λ a. inl (a, d)) (λ b. inr (b, d))`.  The context `d` is
    shared by both branches, and only one runs. -/
def orDist : Tm Empty :=
  .lam (.lam (.case (.var 0) (.lam (.inl (.pair (.var 0) (.var 2))))
    (.lam (.inr (.pair (.var 0) (.var 2))))))

theorem orDist_s1 (δ φ ψ : SF) :
    Stratum1 orDist (.arr (den δ) (.arr (den (.or φ ψ)) (den (.or (.and φ δ) (.and ψ δ))))) :=
  ⟨⟨show 0 < 0 + 1 + 1 by omega,
    ⟨show 0 < 0 + 1 + 1 + 1 by omega, show 2 < 0 + 1 + 1 + 1 by omega⟩,
    ⟨show 0 < 0 + 1 + 1 + 1 by omega, show 2 < 0 + 1 + 1 + 1 by omega⟩⟩,
   fun _ => .lam (.lam (.case (.var _ 0) (.lam (.inl (.pair (.var _ 0) (.var _ 2))))
     (.lam (.inr (.pair (.var _ 0) (.var _ 2)))))),
   ⟨by decide, by decide, trivial, ⟨by decide, trivial, trivial⟩, ⟨by decide, trivial, trivial⟩⟩⟩

/-- **The introductions are affine under the raw count**: AND, OR and
    threshold introduction need no additive rule. -/
theorem intros_raw_affine :
    Tm.Aff andI ∧ Tm.Aff inlI ∧ Tm.Aff inrI ∧ Tm.Aff thrTake ∧ Tm.Aff thrSkip :=
  ⟨⟨by decide, by decide, trivial, trivial⟩, ⟨by decide, trivial⟩, ⟨by decide, trivial⟩,
   ⟨by decide, by decide, trivial, trivial⟩, ⟨by decide, trivial⟩⟩

/-- **The additive rule is needed for glue**: distributing OR over a context
    mentions the context in both branches, so the raw count scores it as
    contraction, while it is in stratum 1. -/
theorem orDist_needs_additive : ¬ Tm.Aff orDist := fun h => absurd h.1 (by decide)

-- ---------------------------------------------------------------------------
-- The prover's composition
-- ---------------------------------------------------------------------------

/-- The witnesses a plan uses: one per atom it proves. -/
def Plan.nA : {φ : SF} → Plan φ → Nat
  | _, .atom _ => 1
  | _, .top => 0
  | _, .and p q => p.nA + q.nA
  | _, .inl p => p.nA
  | _, .inr q => q.nA

/-- The type of the `j`-th witness, left to right. -/
def Plan.slotTy : {φ : SF} → Plan φ → Nat → Ty SBase
  | _, .atom i => fun _ => .base (.atomT i)
  | _, .top => fun _ => .base .unitT
  | _, .and p q => fun j => if j < p.nA then p.slotTy j else q.slotTy (j - p.nA)
  | _, .inl p => p.slotTy
  | _, .inr q => q.slotTy

/-- The realizer a plan builds, its `j`-th witness the variable `s + j`. -/
def Plan.build : {φ : SF} → Plan φ → Nat → Tm Empty
  | _, .atom _, s => .var s
  | _, .top, _ => idT
  | _, .and p q, s => .pair (p.build s) (q.build (s + p.nA))
  | _, .inl p, s => .inl (p.build s)
  | _, .inr q, s => .inr (q.build s)

theorem Plan.build_typed : ∀ {φ : SF} (p : Plan φ) (Γ : Nat → Ty SBase) (s : Nat),
    (∀ j, j < p.nA → Γ (s + j) = p.slotTy j) → Typed Empty.elim Γ (p.build s) (den φ)
  | _, .atom i, Γ, s, h => by
    have e : Γ s = .base (.atomT i) := h 0 (by show 0 < 1; omega)
    show Typed Empty.elim Γ (.var s) (.base (.atomT i))
    rw [← e]
    exact .var Γ s
  | _, .top, Γ, _, _ => .lam (.var _ 0)
  | _, .and p q, Γ, s, h => by
    refine .pair (p.build_typed Γ s fun j hj => ?_) (q.build_typed Γ (s + p.nA) fun j hj => ?_)
    · have := h j (by show j < p.nA + q.nA; omega)
      rw [this]; show (if j < p.nA then _ else _) = _; rw [if_pos hj]
    · have := h (p.nA + j) (by show p.nA + j < p.nA + q.nA; omega)
      rw [← Nat.add_assoc] at this
      rw [this]; show (if p.nA + j < p.nA then _ else _) = _
      rw [if_neg (by omega), show p.nA + j - p.nA = j by omega]
  | _, .inl p, Γ, s, h => .inl (p.build_typed Γ s h)
  | _, .inr q, Γ, s, h => .inr (q.build_typed Γ s h)

theorem Plan.build_closed : ∀ {φ : SF} (p : Plan φ) (d s : Nat), s + p.nA ≤ d →
    closedAt d (p.build s)
  | _, .atom _, _, _, h => by show _ < _; have : _ + 1 ≤ _ := h; omega
  | _, .top, d, _, _ => closedAt_mono idT_s1.1 (Nat.zero_le d)
  | _, .and p q, d, s, h => by
    have h' : s + (p.nA + q.nA) ≤ d := h
    exact ⟨p.build_closed d s (by omega), q.build_closed d (s + p.nA) (by omega)⟩
  | _, .inl p, d, s, h => p.build_closed d s h
  | _, .inr q, d, s, h => q.build_closed d s h

/-- Each witness occurs exactly once, and nothing else occurs. -/
theorem Plan.build_acnt : ∀ {φ : SF} (p : Plan φ) (s i : Nat),
    acnt i (p.build s) = if s ≤ i ∧ i < s + p.nA then 1 else 0
  | _, .atom _, s, i => by
    show (if s = i then 1 else 0) = if s ≤ i ∧ i < s + 1 then 1 else 0
    by_cases h : s = i
    · rw [if_pos h, if_pos ⟨by omega, by omega⟩]
    · rw [if_neg h, if_neg (fun hh => h (by have := hh.1; have := hh.2; omega))]
  | _, .top, s, i => by
    show acnt i idT = if s ≤ i ∧ i < s + 0 then 1 else 0
    rw [acnt_closed idT_s1.1 (Nat.zero_le i), if_neg (fun hh => by have := hh.1; have := hh.2; omega)]
  | _, .and p q, s, i => by
    show acnt i (p.build s) + acnt i (q.build (s + p.nA)) = _
    rw [p.build_acnt s i, q.build_acnt (s + p.nA) i]
    show _ = if s ≤ i ∧ i < s + (p.nA + q.nA) then 1 else 0
    by_cases h1 : s ≤ i ∧ i < s + p.nA
    · have a1 := h1.1; have a2 := h1.2
      rw [if_pos h1, if_neg (fun hh => by have := hh.1; omega), if_pos ⟨by omega, by omega⟩]
    · rw [if_neg h1]
      by_cases h2 : s + p.nA ≤ i ∧ i < s + p.nA + q.nA
      · have a1 := h2.1; have a2 := h2.2
        rw [if_pos h2, if_pos ⟨by omega, by omega⟩]
      · rw [if_neg h2]
        refine (if_neg (fun hh => ?_)).symm
        have b1 := hh.1; have b2 := hh.2
        by_cases c : i < s + p.nA
        · exact h1 ⟨b1, c⟩
        · exact h2 ⟨by omega, by omega⟩
  | _, .inl p, s, i => p.build_acnt s i
  | _, .inr q, s, i => q.build_acnt s i

theorem Plan.build_affA : ∀ {φ : SF} (p : Plan φ) (s : Nat), AffA (p.build s)
  | _, .atom _, _ => trivial
  | _, .top, _ => idT_s1.2.2
  | _, .and p q, s => ⟨p.build_affA s, q.build_affA (s + p.nA)⟩
  | _, .inl p, s => p.build_affA s
  | _, .inr q, s => q.build_affA s

/-- `λ x₁ … xₘ. b`. -/
def lams : Nat → Tm Empty → Tm Empty
  | 0, b => b
  | m + 1, b => .lam (lams m b)

/-- `T (m - 1) ⇒ … ⇒ T 0 ⇒ B`. -/
def arrowsDesc : Nat → (Nat → Ty SBase) → Ty SBase → Ty SBase
  | 0, _, B => B
  | m + 1, T, B => .arr (T m) (arrowsDesc m T B)

theorem acnt_lams (b : Tm Empty) : ∀ (m i : Nat), acnt i (lams m b) = acnt (i + m) b
  | 0, _ => rfl
  | m + 1, i => by
    show acnt (i + 1) (lams m b) = _
    rw [acnt_lams b m (i + 1), show i + 1 + m = i + (m + 1) by omega]

theorem closedAt_lams (b : Tm Empty) : ∀ (m d : Nat), closedAt (d + m) b → closedAt d (lams m b)
  | 0, _, h => h
  | m + 1, d, h => closedAt_lams b m (d + 1) (by rw [show d + 1 + m = d + (m + 1) by omega]; exact h)

theorem lams_typed (b : Tm Empty) (B : Ty SBase) (T : Nat → Ty SBase) :
    ∀ (m : Nat) (Γ Δ : Nat → Ty SBase), (∀ j, j < m → Δ j = T j) → (∀ i, Δ (m + i) = Γ i) →
      Typed Empty.elim Δ b B → Typed Empty.elim Γ (lams m b) (arrowsDesc m T B)
  | 0, Γ, Δ, _, h2, hb => by
    have e : Δ = Γ := funext fun i => by have := h2 i; rw [Nat.zero_add] at this; exact this
    rw [← e]; exact hb
  | m + 1, Γ, Δ, h1, h2, hb => by
    refine .lam (lams_typed b B T m (Ty.cons (T m) Γ) Δ (fun j hj => h1 j (by omega)) ?_ hb)
    intro i
    cases i with
    | zero => exact h1 m (by omega)
    | succ i => rw [show m + (i + 1) = m + 1 + i by omega]; exact h2 i

theorem lams_affA (b : Tm Empty) : ∀ (m : Nat), (∀ j, j < m → acnt j b ≤ 1) → AffA b →
    AffA (lams m b)
  | 0, _, hb => hb
  | m + 1, h, hb => by
    refine ⟨?_, lams_affA b m (fun j hj => h j (by omega)) hb⟩
    show acnt 0 (lams m b) ≤ 1
    rw [acnt_lams, Nat.zero_add]
    exact h m (by omega)

/-- **The prover's composition**: the realizer of a plan, as a function of
    its witnesses. -/
def Plan.compose {φ : SF} (p : Plan φ) : Tm Empty := lams p.nA (p.build 0)

/-- **The prover's composition is in stratum 1**, for every plan of every
    Σ-formula, threshold included. -/
theorem Plan.compose_s1 {φ : SF} (p : Plan φ) :
    Stratum1 p.compose (arrowsDesc p.nA p.slotTy (den φ)) := by
  refine ⟨closedAt_lams _ _ 0 (p.build_closed _ 0 (by omega)), fun Γ => ?_,
    lams_affA _ _ (fun j _ => ?_) (p.build_affA 0)⟩
  · refine lams_typed _ _ _ p.nA Γ (fun j => if j < p.nA then p.slotTy j else Γ (j - p.nA))
      (fun j hj => if_pos hj) (fun i => ?_) (p.build_typed _ 0 fun j hj => ?_)
    · show (if p.nA + i < p.nA then _ else _) = _
      rw [if_neg (by omega), show p.nA + i - p.nA = i by omega]
    · show (if 0 + j < p.nA then _ else _) = _
      rw [if_pos (by omega), Nat.zero_add]
  · rw [p.build_acnt 0 j]
    split
    · exact Nat.le_refl 1
    · exact Nat.zero_le 1

/-- **Threshold, composed**: if at least `k` components have plans, the
    threshold statement has a plan, and its composition is in stratum 1. -/
theorem thr_compose_s1 (k : Nat) {φs : List SF} (os : OPlans φs) (h : k ≤ os.count) :
    ∃ p : Plan (thrF k φs), Stratum1 p.compose (arrowsDesc p.nA p.slotTy (den (thrF k φs))) := by
  cases hp : thrPlan k os with
  | none => have := thrPlan_isSome k os h; rw [hp] at this; cases this
  | some p => exact ⟨p, p.compose_s1⟩

-- ---------------------------------------------------------------------------
-- The theorem
-- ---------------------------------------------------------------------------

/-- **The glue of the Σ-protocol algebra lies in stratum 1**: AND, OR and
    threshold introduction, projection, split, case, commutation of AND and
    of OR, OR distributed over a context, threshold weakening, and the
    prover's composition of every plan, each at its type. -/
theorem glue_stratum1 :
    Stratum1 idT (den .top) ∧
    (∀ φ ψ, Stratum1 andI (.arr (den φ) (.arr (den ψ) (den (.and φ ψ))))) ∧
    (∀ φ ψ, Stratum1 fstE (.arr (den (.and φ ψ)) (den φ))) ∧
    (∀ φ ψ, Stratum1 sndE (.arr (den (.and φ ψ)) (den ψ))) ∧
    (∀ φ ψ, Stratum1 inlI (.arr (den φ) (den (.or φ ψ)))) ∧
    (∀ φ ψ, Stratum1 inrI (.arr (den ψ) (den (.or φ ψ)))) ∧
    (∀ φ ψ C, Stratum1 caseE
      (.arr (den (.or φ ψ)) (.arr (.arr (den φ) C) (.arr (.arr (den ψ) C) C)))) ∧
    (∀ φ ψ C, Stratum1 splitE
      (.arr (den (.and φ ψ)) (.arr (.arr (den φ) (.arr (den ψ) C)) C))) ∧
    (∀ φ ψ, Stratum1 andComm (.arr (den (.and φ ψ)) (den (.and ψ φ)))) ∧
    (∀ φ ψ, Stratum1 orComm (.arr (den (.or φ ψ)) (den (.or ψ φ)))) ∧
    (∀ δ φ ψ, Stratum1 orDist
      (.arr (den δ) (.arr (den (.or φ ψ)) (den (.or (.and φ δ) (.and ψ δ)))))) ∧
    (∀ φ k φs, Stratum1 thrTake
      (.arr (den φ) (.arr (den (thrF k φs)) (den (thrF (k + 1) (φ :: φs)))))) ∧
    (∀ φ k φs, Stratum1 thrSkip (.arr (den (thrF (k + 1) φs)) (den (thrF (k + 1) (φ :: φs))))) ∧
    (∀ k φs, Stratum1 (thrWeaken k φs) (.arr (den (thrF (k + 1) φs)) (den (thrF k φs)))) ∧
    (∀ φ (p : Plan φ), Stratum1 p.compose (arrowsDesc p.nA p.slotTy (den φ))) :=
  ⟨idT_s1, andI_s1, fstE_s1, sndE_s1, inlI_s1, inrI_s1, caseE_s1, splitE_s1, andComm_s1,
    orComm_s1, orDist_s1, thrTake_s1, thrSkip_s1, thrWeaken_s1, fun _ p => p.compose_s1⟩

/-- **The stratum-1 bounds, for the glue**: a glue term, alone or applied to
    other glue, takes fewer call-by-name steps than its additive size, and its
    compiled term (the threaded compilation `compiledA`) behaves at its type
    within its combinator count.  No closed constant-free term has a base type,
    so witnesses enter as the arguments of the compiled term, where `Q`
    charges their own costs. -/
theorem glue_bounds {t : Tm Empty} {A : Ty SBase} (h : Stratum1 t A) :
    (∀ n u, WHN n t u → n < asz t) ∧
    Q (gty A) (compiledA Empty.elim t) (compiledA Empty.elim t).leaves :=
  ⟨fun _ _ hn => h.source_bound hn, h.compiled_bound⟩

/-- `λ p. (snd p, fst p)`: AND-commutation by projections, using both halves
    of one pair variable. -/
def swapT : Tm Empty := .lam (.pair (.snd (.var 0)) (.fst (.var 0)))

/-- **The boundary**: swapping a pair's halves by projections mentions the
    pair twice, so it is not additively affine; it is contraction, in
    stratum 2.  The split does the same work in stratum 1 (`andComm_s1`). -/
theorem swapT_not_affA : ¬ AffA swapT := fun h => absurd h.1 (by decide)

end Rz
