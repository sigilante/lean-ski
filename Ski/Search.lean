import Ski.LiftBool

open Term

/-!
# Berger's search over Cantor space, for m-local predicates

Lemma 2 of the B2 note `notes/B2-cantor-lift.md`, mechanized: the core of the
positive half of the staging line at Stream → Bool.

- Streams are Scott pairs, `consC h t ⬝ k ↠ k h t`.  A term `s` *has the
  prefix* `w` (`HasPrefix w s`) when it weakly reduces to a cons cell of
  `w`'s first bit whose tail has the prefix of the rest.  The last tail is
  arbitrary: it may diverge.
- `Local m φ q`: on every term with a prefix `w` of length `m`, `q` reduces
  to the boolean `φ w`.  So `q` forces at most `m` bits, and its value
  depends on them alone.  (`hd_local`: the head is 1-local.)
- `findT`, Berger's search, as a fixpoint:

      find p = (λ l. p l l (cons true (find (p ∘ cons true))))
                 (cons false (find (p ∘ cons false)))

  with `p ∘ cons b = S (K p) (cons b)` (`pre`).

**`search`**: for a k-local `p` with table `φ`, `find p` has a prefix `u` of
length `k`, and `φ u` is true whenever `φ` is true anywhere.  So
`p (find p)` decides whether `p` is satisfiable (`search_decides`).  The
proof is the paper's induction on `k`; no termination of `find` is claimed
or needed (it has no normal form), only existential weak reductions.
-/

namespace Search

open NoLift LiftBool

-- ---------------------------------------------------------------------------
-- Streams
-- ---------------------------------------------------------------------------

/-- `cons = λ h t k. k h t`. -/
def consC : Term := toTerm (absN [0, 1, 2] (.var 2 ⬝ₒ .var 0 ⬝ₒ .var 1))

theorem cons_sel (h t k : Term) : WSteps (consC ⬝ h ⬝ t ⬝ k) (k ⬝ h ⬝ t) := by
  have e := absN_beta_close [0, 1, 2] (.var 2 ⬝ₒ .var 0 ⬝ₒ .var 1) (fun _ => K) [h, t, k] rfl
  simp only [OTerm.close, overrideC, updC, appT] at e
  exact e

/-- `s` has the prefix `w`. -/
def HasPrefix : List Bool → Term → Prop
  | [], _ => True
  | b :: w, s => ∃ s', WSteps s (consC ⬝ boolT b ⬝ s') ∧ HasPrefix w s'

/-- Having a prefix is closed under backward reduction. -/
theorem HasPrefix.back {w : List Bool} {s t : Term} (h : WSteps t s) (hs : HasPrefix w s) :
    HasPrefix w t := by
  cases w with
  | nil => trivial
  | cons b w =>
    obtain ⟨s', h1, h2⟩ := hs
    exact ⟨s', h.trans h1, h2⟩

theorem prefix_cons (b : Bool) {w : List Bool} {t : Term} (h : HasPrefix w t) :
    HasPrefix (b :: w) (consC ⬝ boolT b ⬝ t) :=
  ⟨t, .refl _, h⟩

/-- `q` is `m`-local with table `φ`. -/
def Local (m : Nat) (φ : List Bool → Bool) (q : Term) : Prop :=
  ∀ w : List Bool, w.length = m → ∀ s, HasPrefix w s → WSteps (q ⬝ s) (boolT (φ w))

/-- `hd = λ s. s true`, as `S I (K K)`. -/
def hdT : Term := S ⬝ I ⬝ (K ⬝ K)

/-- The head is 1-local: the hypothesis is satisfiable by natural
    functionals. -/
theorem hd_local : Local 1 (fun w => w.headD false) hdT := by
  intro w hw s hs
  match w, hw, hs with
  | [b], _, ⟨s', h1, _⟩ =>
    have h0 : WSteps (hdT ⬝ s) (s ⬝ K) :=
      (iter_sound (k := 2) rfl : Steps (hdT ⬝ s) (s ⬝ (K ⬝ K ⬝ s))).weak.trans
        (WSteps.right s (.single (.K K s)))
    exact (h0.trans (WSteps.left K h1)).trans ((cons_sel _ _ _).trans (.single (.K _ _)))

-- ---------------------------------------------------------------------------
-- Shifting a predicate
-- ---------------------------------------------------------------------------

/-- `p ∘ cons b = λ a. p (cons b a)`. -/
def pre (p : Term) (b : Bool) : Term := S ⬝ (K ⬝ p) ⬝ (consC ⬝ boolT b)

theorem pre_wsteps (p : Term) (b : Bool) (a : Term) :
    WSteps (pre p b ⬝ a) (p ⬝ (consC ⬝ boolT b ⬝ a)) :=
  (WSteps.single (WStep.S _ _ _)).trans (WSteps.left _ (.single (.K _ _)))

/-- **Lemma 1 (shifting).** -/
theorem local_pre {m : Nat} {φ : List Bool → Bool} {p : Term} (hp : Local (m + 1) φ p) (b : Bool) :
    Local m (fun w => φ (b :: w)) (pre p b) := by
  intro w hw a ha
  exact (pre_wsteps p b a).trans (hp (b :: w) (by simp [hw]) _ (prefix_cons b ha))

theorem local_zero {φ : List Bool → Bool} {p : Term} (hp : Local 0 φ p) (s : Term) :
    WSteps (p ⬝ s) (boolT (φ [])) :=
  hp [] rfl s trivial

-- ---------------------------------------------------------------------------
-- The search
-- ---------------------------------------------------------------------------

/-- `p ∘ cons b` over `p` as variable `x`. -/
def preO (x : Nat) (b : Bool) : OTerm := S.toO ⬝ₒ (K.toO ⬝ₒ .var x) ⬝ₒ (consC ⬝ boolT b).toO

/-- `λ l. p l l (cons true (f (p ∘ cons true)))`, over `f` (0), `p` (1), `l` (2). -/
def findIn : OTerm :=
  absN [2] (.var 1 ⬝ₒ .var 2 ⬝ₒ .var 2 ⬝ₒ ((consC ⬝ boolT true).toO ⬝ₒ (.var 0 ⬝ₒ preO 1 true)))

/-- The step function's body, over `f` (0) and `p` (1). -/
def findBody : OTerm := findIn ⬝ₒ ((consC ⬝ boolT false).toO ⬝ₒ (.var 0 ⬝ₒ preO 1 false))

def findStep : Term := toTerm (absN [0, 1] findBody)

/-- **Berger's search**, the fixpoint of `findStep`. -/
def findT : Term := fixSelf findStep (fixB findStep)

theorem find_unroll : WSteps findT (findStep ⬝ findT) := by
  have h := (fixSelf_unroll (F := findStep) (Steps.refl (fixB findStep))).weak
  have hI : WSteps (fixSelf findStep (I ⬝ fixB findStep)) findT := WSteps.right _ (.single (.I _))
  exact h.trans (WSteps.right _ hI)

/-- One unrolling: `find p ↠ p l l r`. -/
theorem find_unfold (p : Term) :
    WSteps (findT ⬝ p)
      (p ⬝ (consC ⬝ boolT false ⬝ (findT ⬝ pre p false)) ⬝ (consC ⬝ boolT false ⬝ (findT ⬝ pre p false))
        ⬝ (consC ⬝ boolT true ⬝ (findT ⬝ pre p true))) := by
  have h1 := absN_beta_close [0, 1] findBody (fun _ => K) [findT, p] rfl
  simp only [findBody, OTerm.close, close_toO] at h1
  have h0 := (WSteps.left p find_unroll).trans h1
  refine h0.trans ?_
  have h2 := absN_beta_close [2]
    (.var 1 ⬝ₒ .var 2 ⬝ₒ .var 2 ⬝ₒ ((consC ⬝ boolT true).toO ⬝ₒ (.var 0 ⬝ₒ preO 1 true)))
    (overrideC (fun _ => K) [0, 1] [findT, p])
    [consC ⬝ boolT false ⬝ (findT ⬝ (preO 1 false).close (overrideC (fun _ => K) [0, 1] [findT, p]))] rfl
  simp only [OTerm.close, close_toO, preO, overrideC, updC] at h2
  simpa [findIn, preO, pre, OTerm.close, close_toO, overrideC, updC, appT] using h2

/-- **Lemma 2 (search).**  For a `k`-local `p` with table `φ`, `find p` has a
    prefix `u` of length `k`, and `φ u` is true whenever `φ` is true on some
    word of length `k`. -/
theorem search : ∀ (k : Nat) (φ : List Bool → Bool) (p : Term), Local k φ p →
    ∃ u : List Bool, u.length = k ∧ HasPrefix u (findT ⬝ p) ∧
      ((∃ w : List Bool, w.length = k ∧ φ w = true) → φ u = true) := by
  intro k
  induction k with
  | zero =>
    intro φ p hp
    refine ⟨[], rfl, trivial, ?_⟩
    rintro ⟨w, hw, hφ⟩
    rw [List.length_eq_zero_iff.1 hw] at hφ
    exact hφ
  | succ k ih =>
    intro φ p hp
    obtain ⟨u0, hl0, hpre0, hc0⟩ := ih _ _ (local_pre hp false)
    obtain ⟨u1, hl1, hpre1, hc1⟩ := ih _ _ (local_pre hp true)
    let l := consC ⬝ boolT false ⬝ (findT ⬝ pre p false)
    let r := consC ⬝ boolT true ⬝ (findT ⬝ pre p true)
    have hlp : HasPrefix (false :: u0) l := prefix_cons false hpre0
    have hpl := hp (false :: u0) (by simp [hl0]) l hlp
    have hf := find_unfold p
    cases hv : φ (false :: u0) with
    | true =>
      rw [hv] at hpl
      have hsel : WSteps (findT ⬝ p) l :=
        hf.trans ((WSteps.left _ (WSteps.left _ hpl)).trans (sel true _ _))
      exact ⟨false :: u0, by simp [hl0], hlp.back hsel, fun _ => hv⟩
    | false =>
      rw [hv] at hpl
      have hsel : WSteps (findT ⬝ p) r :=
        hf.trans ((WSteps.left _ (WSteps.left _ hpl)).trans (sel false _ _))
      refine ⟨true :: u1, by simp [hl1], (prefix_cons true hpre1).back hsel, ?_⟩
      rintro ⟨w, hw, hφ⟩
      match w, hw, hφ with
      | false :: w', hw', hφ' =>
        have := hc0 ⟨w', by simpa using hw', hφ'⟩
        rw [hv] at this; exact absurd this (by simp)
      | true :: w', hw', hφ' => exact hc1 ⟨w', by simpa using hw', hφ'⟩

/-- **The search decides satisfiability**: `p (find p)` reduces to `true`
    exactly when `p`'s table is true somewhere. -/
theorem search_decides {k : Nat} {φ : List Bool → Bool} {p : Term} (hp : Local k φ p) :
    ∃ u : List Bool, u.length = k ∧ WSteps (p ⬝ (findT ⬝ p)) (boolT (φ u)) ∧
      (φ u = true ↔ ∃ w : List Bool, w.length = k ∧ φ w = true) := by
  obtain ⟨u, hu, hpre, hc⟩ := search k φ p hp
  exact ⟨u, hu, hp u hu _ hpre, ⟨fun h => ⟨u, hu, h⟩, hc⟩⟩

end Search
