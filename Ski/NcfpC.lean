import Ski.NcfpTheta
open Term

/-!
# NCFP: Theorems C and NC, left combs (pure S)

**Theorem C** (`thm_C`, `thm_C_hnf`).  Let `p` be a closed S-term with a head normal form
(`HasHnf p`, equivalently `fold p ≠ 36`: `Conv.stable_iff`) and `x₁, …, x_k`, `k ≥ 1`, closed
S-terms.  If `p` is convertible to `p x₁ ⋯ x_k`, then every `xᵢ` is the literal `S` and the block
of `p` is 12 (`fold p = 12`).  Consequences: `cor_C` (some `xᵢ` is not `S`), `cor_C_sub` (`p` is
a subterm of some `xᵢ`), `cor_C_block` (the block of `p` is not 12).

**Theorem NC** (`thm_NC`, `thm_NC_hnf`).  A closed S-term `p` with a head normal form is not
convertible to `p x₁ ⋯ x_k` for any closed S-terms `x₁, …, x_k`, `k ≥ 1`; the `xᵢ` need not
normalize.  With Corollary B1 (`cor_B1`: `p` without a head normal form, normalizing `xᵢ`) this
gives `ncfp_left_comb`: no closed `p` is convertible to `p x₁ ⋯ x_k` with closed normalizing
`xᵢ`.  The case of `p` without a head normal form and some `xᵢ` without a normal form is not
covered.

**Proof of Theorem NC.**  By Theorem C the remaining case is `p =β p S ⋯ S` with `fold p = 12`.
A kernel check (`hnf12B_eq`) shows that a head normal form of block 12 is `S a b` with `a` of
block `0`, so `a = S`: the head run of `p` reaches `S S b` (`hnf2_conv`).  Then
`p S ⋯ S ↠ S S (b S ⋯ S)` (`comb_S_steps`), so `b =β b S ⋯ S` by `hnf2_conv` and the determinism
of the head run; and `b` has a head normal form by Corollary B1.  So these terms form a set
(`SComb`) in which every member has the head normal form `S S b` with `b` in the set
(`scomb_closed`), a right comb with teeth `S`, which is empty by Theorem 2 (`right_combs`).

**Proof of Theorem C.**  The block `fold` into S1's 38-element table (`HnfS.blockTable`) is a
conversion invariant of closed S-terms (`fold_conv`: Church–Rosser, `Conv.conv_iff_join`, and
`HnfS.fold_wsteps`, which rests on the S-law of the table, `HnfS.compat`), and the block of
`p x₁ ⋯ x_k` is obtained from the block of `p` by `k` steps
`v ↦ β v (fold xᵢ)`.  So a conversion `p =β p x₁ ⋯ x_k` is a closed walk of length `k` at
`fold p` in the graph on the 38 blocks with an edge `v → β v w` for every `w`.  One kernel
check over the 38 × 38 pairs (`walkB_eq`) certifies, by the rank table `rkTable`, that every edge
`a → β a b` either ends at `⊥ = 36`, or lowers the rank, or is the loop `β 12 0 = 12`, and that
no `β a b` is `0`.  Since `⊥` is absorbing, a closed walk at a block other than `⊥` uses only the
loop, so the block is 12 and every `fold xᵢ` is `0`; and `fold x = 0` only for `x = S`
(`fold_eq_zero`).  The rank is a certificate only: its values are not part of any statement.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## The finite check -/

/-- A rank on the 38 blocks: the length of the longest walk from a block that avoids `⊥ = 36` and
the loop at 12.  Only the property `β_rank` is used. -/
def rkTable : List Nat :=
  [7, 6, 4, 5, 4, 5, 4, 3, 3, 2, 3, 2, 3, 3, 2, 3, 4, 2, 2, 3, 2, 3, 2, 2, 4, 1, 2, 1, 2, 2, 1, 0,
   2, 3, 1, 2, 0, 1]

/-- The rank of a block. -/
def rk (a : Nat) : Nat := rkTable.getD a 0

/-- The check: no product of blocks is `0`, and every product is `⊥`, or of lower rank than its
left factor, or the loop `β 12 0 = 12`. -/
def walkB : Bool :=
  r38.all fun a => r38.all fun b =>
    (β a b != 0) &&
      (β a b == 36 || decide (rk (β a b) < rk a) || (a == 12 && b == 0 && β a b == 12))

theorem walkB_eq : walkB = true := by decide +kernel

theorem walk_pair {a b : Nat} (ha : a < 38) (hb : b < 38) :
    β a b ≠ 0 ∧ (β a b = 36 ∨ rk (β a b) < rk a ∨ (a = 12 ∧ b = 0 ∧ β a b = 12)) := by
  have h := walkB_eq
  simp only [walkB, r38, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h a ha b hb
  refine ⟨h1, ?_⟩
  rcases h2 with (h2 | h2) | ⟨⟨h2, h3⟩, h4⟩
  · exact .inl h2
  · exact .inr (.inl h2)
  · exact .inr (.inr ⟨h2, h3, h4⟩)

/-- No product of two blocks is the block `0` of `S`. -/
theorem β_ne_zero {a b : Nat} (ha : a < 38) (hb : b < 38) : β a b ≠ 0 := (walk_pair ha hb).1

/-- A step `a → β a b` that does not end at `⊥` lowers the rank or is the loop at 12. -/
theorem β_rank {a b : Nat} (ha : a < 38) (hb : b < 38) (h : β a b ≠ 36) :
    rk (β a b) < rk a ∨ (a = 12 ∧ b = 0 ∧ β a b = 12) :=
  (walk_pair ha hb).2.resolve_left h

/-- The loop at 12 exists: `β 12 0 = 12`. -/
theorem β_loop : β 12 0 = 12 := by decide

/-- The check for head normal forms of block 12: no `β 0 a` is 12, and `β (β 0 a) b = 12` only
for `a = 0`. -/
def hnf12B : Bool :=
  r38.all fun a => (β 0 a != 12) && r38.all fun b => (β (β 0 a) b != 12 || a == 0)

theorem hnf12B_eq : hnf12B = true := by decide +kernel

/-- A head normal form of block 12 is not `S a`, and if it is `S a b` then `a` has block `0`. -/
theorem hnf12 {a b : Nat} (ha : a < 38) (hb : b < 38) :
    β 0 a ≠ 12 ∧ (β (β 0 a) b = 12 → a = 0) := by
  have h := hnf12B_eq
  simp only [hnf12B, r38, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h a ha
  exact ⟨h1, fun e => (h2 b hb).resolve_left (fun n => n e)⟩

/-! ## Blocks of terms -/

/-- Among closed S-terms only the literal `S` has block `0`. -/
theorem fold_eq_zero {t : Term} (ht : PureS t) : fold t = 0 ↔ t = S := by
  constructor
  · intro h
    cases ht with
    | S => rfl
    | app hf hx => exact absurd h (β_ne_zero (fold_lt hf) (fold_lt hx))
  · intro e
    rw [e]
    rfl

/-- The walk of blocks along a left comb: if the block of `p x₁ ⋯ x_k` is not `⊥`, its rank is at
most that of the block of `p`; if the ranks are equal, every `xᵢ` is `S`, and the block of `p` is
12 when `k ≥ 1`. -/
theorem comb_walk : ∀ (L : List Term) {p : Term}, PureS p → (∀ x ∈ L, PureS x) →
    fold (apps p L) ≠ 36 →
    rk (fold (apps p L)) ≤ rk (fold p) ∧
      (rk (fold (apps p L)) = rk (fold p) → (∀ x ∈ L, x = S) ∧ (L ≠ [] → fold p = 12)) := by
  intro L
  induction L with
  | nil =>
    intro p _ _ _
    exact ⟨Nat.le_refl _, fun _ => ⟨fun x hx => (nomatch hx), fun h => absurd rfl h⟩⟩
  | cons a L ih =>
    intro p hp hL h
    have ha : PureS a := hL a (List.Mem.head _)
    have hL' : ∀ x ∈ L, PureS x := fun x hx => hL x (List.Mem.tail _ hx)
    have h' : fold (apps (p ⬝ a) L) ≠ 36 := h
    have hpa : fold (p ⬝ a) ≠ 36 := fun e => h' (fold_apps e L hL')
    obtain ⟨ih1, ih2⟩ := ih (hp.app ha) hL' h'
    show rk (fold (apps (p ⬝ a) L)) ≤ rk (fold p) ∧
      (rk (fold (apps (p ⬝ a) L)) = rk (fold p) → (∀ x ∈ a :: L, x = S) ∧ (a :: L ≠ [] → fold p = 12))
    rcases β_rank (fold_lt hp) (fold_lt ha) hpa with hlt | ⟨e1, e2, e3⟩
    · have hlt' : rk (fold (apps (p ⬝ a) L)) < rk (fold p) := Nat.lt_of_le_of_lt ih1 hlt
      exact ⟨Nat.le_of_lt hlt', fun e => absurd (e ▸ hlt') (Nat.lt_irrefl _)⟩
    · have e3' : fold (p ⬝ a) = fold p := e3.trans e1.symm
      rw [e3'] at ih1 ih2
      refine ⟨ih1, fun e => ⟨?_, fun _ => e1⟩⟩
      intro x hx
      rcases List.mem_cons.mp hx with e' | hx'
      · rw [e']
        exact (fold_eq_zero ha).mp e2
      · exact (ih2 e).1 x hx'

/-! ## Theorem C -/

/-- **Theorem C** (block form).  If the closed S-term `p` has block other than `⊥ = 36` and is
convertible to `p x₁ ⋯ x_k` with `k ≥ 1` and the `xᵢ` closed S-terms, then every `xᵢ` is `S` and
the block of `p` is 12. -/
theorem thm_C {p : Term} (hp : PureS p) (hb : fold p ≠ 36) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x) (hc : Convertible p (apps p L)) :
    (∀ x ∈ L, x = S) ∧ fold p = 12 := by
  have e : fold p = fold (apps p L) := fold_conv hp (pure_apps_of hp L hx) hc
  obtain ⟨h1, h2⟩ := (comb_walk L hp hx (fun h => hb (e.trans h))).2 (congrArg rk e.symm)
  exact ⟨h1, h2 hL⟩

/-- **Theorem C.**  If the closed S-term `p` has a head normal form and is convertible to
`p x₁ ⋯ x_k` with `k ≥ 1` and the `xᵢ` closed S-terms, then every `xᵢ` is `S` and the block of
`p` is 12. -/
theorem thm_C_hnf {p : Term} (hp : PureS p) (hh : HasHnf p) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x) (hc : Convertible p (apps p L)) :
    (∀ x ∈ L, x = S) ∧ fold p = 12 :=
  thm_C hp (fun e => (stable_iff hp).mp e hh) hL hx hc

/-- **Corollary C1.**  A closed S-term `p` with a head normal form is not convertible to
`p x₁ ⋯ x_k` when some `xᵢ` is not the literal `S`. -/
theorem cor_C {p : Term} (hp : PureS p) (hh : HasHnf p) {L : List Term}
    (hx : ∀ x ∈ L, PureS x) {x : Term} (hxL : x ∈ L) (hxS : x ≠ S) :
    ¬ Convertible p (apps p L) := fun hc =>
  hxS ((thm_C_hnf hp hh (List.ne_nil_of_mem hxL) hx hc).1 x hxL)

/-- **Corollary C2.**  A closed S-term `p` with a head normal form is not convertible to
`p x₁ ⋯ x_k` when `p` is a subterm of some `xᵢ`. -/
theorem cor_C_sub {p : Term} (hp : PureS p) (hh : HasHnf p) {L : List Term}
    (hx : ∀ x ∈ L, PureS x) {x : Term} (hxL : x ∈ L) (hs : Sub p x) :
    ¬ Convertible p (apps p L) := by
  intro hc
  obtain ⟨h1, h2⟩ := thm_C_hnf hp hh (List.ne_nil_of_mem hxL) hx hc
  have e : x = S := h1 x hxL
  rw [e] at hs
  cases hs
  exact absurd h2 (by decide)

/-- **Corollary C3.**  A closed S-term `p` whose block is neither `⊥ = 36` nor 12 is not
convertible to `p x₁ ⋯ x_k` for any closed S-terms `x₁, …, x_k`, `k ≥ 1`. -/
theorem cor_C_block {p : Term} (hp : PureS p) (hb : fold p ≠ 36) (h12 : fold p ≠ 12)
    {L : List Term} (hL : L ≠ []) (hx : ∀ x ∈ L, PureS x) : ¬ Convertible p (apps p L) :=
  fun hc => h12 (thm_C hp hb hL hx hc).2

/-! ## Theorem NC -/

/-- `S S b S ⋯ S` head-reduces to `S S (b S ⋯ S)`. -/
theorem comb_S_steps : ∀ (L : List Term) (b : Term), (∀ x ∈ L, x = S) →
    Steps (apps (S ⬝ S ⬝ b) L) (S ⬝ S ⬝ apps b L) := by
  intro L
  induction L with
  | nil => intro b _; exact .refl _
  | cons a L ih =>
    intro b h
    have ea : a = S := h a (List.Mem.head _)
    rw [ea]
    show Steps (apps (S ⬝ S ⬝ b ⬝ S) L) (S ⬝ S ⬝ apps (b ⬝ S) L)
    exact (steps_apps L (Steps.single (Step.S S b S))).trans
      (ih (b ⬝ S) (fun x hx => h x (List.Mem.tail _ hx)))

/-- The set of Theorem NC: closed S-terms `q` with a head normal form (`fold q ≠ 36`) that are
convertible to `q S ⋯ S` with at least one `S`. -/
def SComb (q : Term) : Prop :=
  PureS q ∧ fold q ≠ 36 ∧ ∃ L : List Term, L ≠ [] ∧ (∀ x ∈ L, x = S) ∧ Convertible q (apps q L)

/-- Every member `q` of `SComb` has the head normal form `S S b` on its head run, with `b` in
`SComb`: the set is a right comb with teeth `S`. -/
theorem scomb_closed : Closed 1 SComb := by
  rintro q ⟨hq, hb, L, hL, hS, hc⟩
  refine ⟨hq, ?_⟩
  have hLp : ∀ x ∈ L, PureS x := fun x hx => (hS x hx) ▸ PureS.S
  have h12 : fold q = 12 := (thm_C hq hb hL hLp hc).2
  -- the head normal form of `q` is `S S y`
  have hy : ∃ y, PureS y ∧ Convertible q (S ⬝ S ⬝ y) := by
    obtain ⟨u, hu, hnf⟩ := HnfSound.sound q hq hb
    obtain ⟨hpu, eu⟩ := fold_wsteps hu hq
    rw [h12] at eu
    rcases hnf with e | ⟨x, e⟩ | ⟨x, y, e⟩
    · rw [e] at eu
      exact absurd eu (by decide)
    · rw [e] at eu hpu
      exact absurd eu (hnf12 (fold_lt hpu.app_inv.2) (by decide : 0 < 38)).1
    · rw [e] at eu hpu hu
      have hx := hpu.app_inv.1.app_inv.2
      have hy := hpu.app_inv.2
      have ex : x = S := (fold_eq_zero hx).mp ((hnf12 (fold_lt hx) (fold_lt hy)).2 eu)
      rw [ex] at hu
      exact ⟨y, hy, .of_wsteps hu⟩
  obtain ⟨y, hy, cy⟩ := hy
  obtain ⟨a, b, hs, ca, _⟩ := hnf2_conv hq .S hy cy
  have hab := steps_pure hq hs
  have hpa := hab.app_inv.1.app_inv.2
  have hpb := hab.app_inv.2
  have ea : a = S := (fold_eq_zero hpa).mp (fold_conv hpa .S ca)
  rw [ea] at hs
  -- `q =β q S ⋯ S ↠ S S b S ⋯ S ↠ S S (b S ⋯ S)`
  have hc' : Convertible q (S ⬝ S ⬝ apps b L) :=
    hc.trans (.of_wsteps ((steps_apps L hs).trans (comb_S_steps L b hS)).weak)
  obtain ⟨a', b', hs', _, cb⟩ := hnf2_conv hq .S (pure_apps_of hpb L hLp) hc'
  have e := run_hnf_hnf (.inr (.inr ⟨a', b', rfl⟩)) (.inr (.inr ⟨S, b, rfl⟩)) hs' hs
  injection e with _ eb
  rw [eb] at cb
  refine ⟨b, ⟨hpb, ?_, L, hL, hS, cb⟩, .inr ⟨S, Nat.le_refl 1, hs⟩⟩
  -- `b` has a head normal form, by Corollary B1
  intro hb36
  exact cor_B1 hpb hb36 hL
    (fun x hx => ⟨hLp x hx, (hS x hx) ▸ ⟨S, .refl _, fun _ s => by cases s⟩⟩) cb

/-- **Theorem NC** (block form).  A closed S-term `p` whose block is not `⊥ = 36` is not
convertible to `p x₁ ⋯ x_k` for any closed S-terms `x₁, …, x_k`, `k ≥ 1`. -/
theorem thm_NC {p : Term} (hp : PureS p) (hb : fold p ≠ 36) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x) : ¬ Convertible p (apps p L) := fun hc =>
  right_combs scomb_closed p ⟨hp, hb, L, hL, (thm_C hp hb hL hx hc).1, hc⟩

/-- **Theorem NC.**  A closed S-term `p` with a head normal form is not convertible to
`p x₁ ⋯ x_k` for any closed S-terms `x₁, …, x_k`, `k ≥ 1`. -/
theorem thm_NC_hnf {p : Term} (hp : PureS p) (hh : HasHnf p) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x) : ¬ Convertible p (apps p L) :=
  thm_NC hp (fun e => (stable_iff hp).mp e hh) hL hx

/-- **Left combs.**  A closed S-term `p` is not convertible to `p x₁ ⋯ x_k`, `k ≥ 1`, when the
`xᵢ` are closed S-terms with normal forms (Theorem NC if `p` has a head normal form, Corollary
B1 if not; the case split is on the block of `p`, which is decidable). -/
theorem ncfp_left_comb {p : Term} (hp : PureS p) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x ∧ Normalizing x) : ¬ Convertible p (apps p L) := by
  cases Nat.decEq (fold p) 36 with
  | isTrue e => exact cor_B1 hp e hL hx
  | isFalse ne => exact thm_NC hp ne hL (fun x h => (hx x h).1)

end Ncfp
