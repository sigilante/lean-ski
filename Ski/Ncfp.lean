import Ski.HeadRec
import Ski.Tower
open Term

/-!
# No conversion fixed points (NCFP): the proved cases

**Conjecture NCFP** (open, not proved here): no closed S-term `p` and context `E ≠ hole` with one
or more holes have `p =β E[p]`.  This module mechanizes the cases that are proved on paper
(`notes/A1-lock1-S3.md`, section "NCFP").

Setting: closed terms over `S` (`HnfS.PureS`), weak reduction `WStep` (a contraction at any
position), head reduction `Step`, convertibility `Conv.Convertible`.  Contexts are `Phi.Ctx`:
terms over `S` and a hole constructor, any number of holes, with `Ctx.plug` filling every hole
with the same term.  `Holed E` says that `E` has at least one hole.  `sz` is the leaf count,
which for a closed S-term is its number of `S`.

What is proved:

* `prop0` (Prop. 0): NCFP for every `p` with a normal form and every `E ≠ hole` with a hole.
* `ncfp_S`: no closed `p` with `p =β S p`, by descent on `sz p` (Church–Rosser,
  standardization, and the fact that a one-item head normal form is literal).
* `lemma_L` (Lemma L, last frame), `hnf1_literal`, `last_item_step`.
* `right_combs` (Theorem 2, right combs with bounded teeth), for a predicate closed under
  "next tooth"; `right_combs_seq` is the paper's statement for a sequence.  It uses
  `HeadRec.no_ground_loop` (Waldmann's theorem, S7).
* `right_combs_conv`: the same with conversion in place of head runs, and teeth with normal forms
  of bounded size (the direct Church–Rosser and standardization chain).
* `ncfp_comb`: NCFP for every comb context, any closed `p`.
* `first_combs`, `first_combs_seq` (Theorem F of `notes/NCFP-proof.md`, first-item combs with
  bounded teeth).
* `mixed_combs`, `mixed_combs_seq`, `mixed_combs_conv` (Theorem G, mixed combs with bounded
  teeth; it contains Theorems 2 and F), with `lemma_P`, and `ncfp_gcomb` (Corollary G1: NCFP for
  one-hole contexts built by `S E`, `S n E`, `S E n`, `n` normalizing; it contains Corollary F1).
* `no_fixed_point_combinator`, `no_fpc`: pure S has no fixed-point combinator.

* `teeth_unbounded`, `teeth_unbounded_seq` (Theorem B of `notes/NCFP-proof.md`: the teeth of an
  hnf-less term are unbounded), with `lemma_T`, `lemma_A`, `bmove` (the Moves), and `cor_B1`
  (`p ≠β p x₁ ⋯ x_k` for hnf-less `p` and normalizing `xᵢ`).

What is not proved: NCFP itself; combs with non-normalizing teeth; contexts with two or more holes such as `p =β S p p`; any statement
about the infinite normal form `t^∞` (the paper's corollaries about trees are not stated here);
Prop. A, Corollary B2 and Prop. E of `notes/NCFP-proof.md`.

All proofs are constructive: `right_combs` is stated for a predicate, not for a sequence, so that
no choice is needed to follow the comb, and the "finitely often" steps of the paper are bounded
inductions.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Size and normal forms -/

/-- A weak step of a closed S-term does not lower the leaf count (`S f g x → f x (g x)` changes
it by `sz x - 1`). -/
theorem sz_wstep {t u : Term} (ht : PureS t) (h : WStep t u) : sz t ≤ sz u := by
  induction h with
  | S f g x =>
    have := sz_pos x
    simp only [sz]
    omega
  | K x y => exact absurd ht.app_inv.1.app_inv.1 PureS.not_K
  | I x => exact absurd ht.app_inv.1 PureS.not_I
  | left x _ ih =>
    have := ih ht.app_inv.1
    simp only [sz]
    omega
  | right f _ ih =>
    have := ih ht.app_inv.2
    simp only [sz]
    omega

theorem sz_wsteps {t u : Term} (ht : PureS t) (h : WSteps t u) : sz t ≤ sz u := by
  induction h with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans (sz_wstep ht s) (ih (wstep_pure s ht).1)

/-- Normal: no contraction at any position. -/
def Normal (n : Term) : Prop := ∀ u, ¬ WStep n u

/-- `a` weakly reduces to a normal term. -/
def Normalizing (a : Term) : Prop := ∃ n, WSteps a n ∧ Normal n

theorem Normal.wsteps {n w : Term} (hn : Normal n) (h : WSteps n w) : w = n := by
  cases h with
  | refl => rfl
  | step s _ => exact absurd s (hn _)

/-- Every reduct of a term reduces to its normal form (Church–Rosser). -/
theorem wsteps_to_normal {a a' n : Term} (h : WSteps a a') (hn : WSteps a n) (nf : Normal n) :
    WSteps a' n := by
  obtain ⟨w, h1, h2⟩ := church_rosser h hn
  have e := nf.wsteps h2
  rw [e] at h1
  exact h1

/-! ## Contexts -/

/-- The context has at least one hole. -/
inductive Holed : Phi.Ctx → Prop
  | hole : Holed .hole
  | left {c : Phi.Ctx} (d : Phi.Ctx) : Holed c → Holed (.app c d)
  | right (c : Phi.Ctx) {d : Phi.Ctx} : Holed d → Holed (.app c d)

theorem wsteps_plug (C : Phi.Ctx) {t t' : Term} (h : WSteps t t') :
    WSteps (C.plug t) (C.plug t') := by
  induction C with
  | hole => exact h
  | s => exact .refl _
  | app c d ihc ihd => exact WSteps.app ihc ihd

theorem Holed.sz_le {E : Phi.Ctx} (h : Holed E) (t : Term) : sz t ≤ sz (E.plug t) := by
  induction h with
  | hole => exact Nat.le_refl _
  | @left c d _ ih =>
    exact Nat.le_trans ih (Nat.le_of_lt (sz_fun_lt (c.plug t) (d.plug t)))
  | @right c d _ ih =>
    exact Nat.le_trans ih (Nat.le_of_lt (sz_arg_lt (c.plug t) (d.plug t)))

/-- Filling a context other than the hole itself, with a hole, gives a larger term. -/
theorem Holed.sz_lt {E : Phi.Ctx} (h : Holed E) (hne : E ≠ .hole) (t : Term) :
    sz t < sz (E.plug t) := by
  cases h with
  | hole => exact absurd rfl hne
  | @left c d hc => exact Nat.lt_of_le_of_lt (hc.sz_le t) (sz_fun_lt (c.plug t) (d.plug t))
  | @right c d hd => exact Nat.lt_of_le_of_lt (hd.sz_le t) (sz_arg_lt (c.plug t) (d.plug t))

/-! ## Prop. 0 -/

/-- **Prop. 0** (NCFP for normalizing terms).  If the closed S-term `p` has a normal form, then
for no context `E ≠ hole` with at least one hole is `p` convertible to `E[p]`.

Proof as in the note: `E[p]` reduces to the normal form `n` of `p` and to `E[n]`, so `E[n]`
reduces to `n` (Church–Rosser); but `E[n]` is larger than `n` and reduction does not lower the
leaf count.  Nothing is claimed for `p` without a normal form. -/
theorem prop0 {p n : Term} (hp : PureS p) (hn : WSteps p n) (nf : Normal n) {E : Phi.Ctx}
    (hE : Holed E) (hne : E ≠ .hole) : ¬ Convertible p (E.plug p) := by
  intro h
  obtain ⟨w, h1, h2⟩ := conv_iff_join.mp h
  have h3 : WSteps (E.plug p) n := h2.trans (wsteps_to_normal h1 hn nf)
  have h4 : WSteps (E.plug n) n := wsteps_to_normal (wsteps_plug E hn) h3 nf
  have hpn := (fold_wsteps hn hp).1
  have h5 := sz_wsteps (Tower.plug_pure E hpn) h4
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hE.sz_lt hne n) h5)

/-! ## Head runs: Lemma L -/

/-- A term with a head step is an application. -/
theorem step_app {t u : Term} (s : Step t u) : ∃ e l, t = e ⬝ l := by
  cases s with
  | S f g x => exact ⟨_, _, rfl⟩
  | K x y => exact ⟨_, _, rfl⟩
  | I x => exact ⟨_, _, rfl⟩
  | left x _ => exact ⟨_, _, rfl⟩

/-- One or more head steps end with a last step. -/
theorem plus_last {t w : Term} (h : Plus t w) : ∃ t', Steps t t' ∧ Step t' w := by
  obtain ⟨t₁, s, r⟩ := h
  rcases steps_last r with e | ⟨t', r₁, s'⟩
  · rw [← e]
    exact ⟨t, .refl _, s⟩
  · exact ⟨t', .step s r₁, s'⟩

/-- A one-item head normal form is literal: a head run that ends in `S a` has no step. -/
theorem hnf1_literal {q a : Term} (hq : PureS q) (h : Steps q (S ⬝ a)) : q = S ⬝ a := by
  rcases steps_last h with e | ⟨t', h1, s⟩
  · exact e
  · obtain ⟨x, b, c, e⟩ := step_two (steps_pure hq h1) s
    injection e with e1 _
    cases e1

/-- **Lemma L** (last frame).  If the head run of the closed S-term `q` takes at least one step
to a two-item head normal form `S a b`, then its last frame is `S S y a` and `b = y a`: the head
normal form is `S z (y z)` with `z = a`. -/
theorem lemma_L {q a b : Term} (hq : PureS q) (h : Plus q (S ⬝ a ⬝ b)) :
    ∃ y, Steps q (S ⬝ S ⬝ y ⬝ a) ∧ b = y ⬝ a := by
  obtain ⟨t', h1, s⟩ := plus_last h
  obtain ⟨y, e1, e2⟩ := step_to_S2 (steps_pure hq h1) s
  rw [e1] at h1
  exact ⟨y, h1, e2⟩

/-- Lemma L for a head run that is not literal. -/
theorem lemma_L' {q a b : Term} (hq : PureS q) (h : Steps q (S ⬝ a ⬝ b)) (hne : q ≠ S ⬝ a ⬝ b) :
    ∃ y, Steps q (S ⬝ S ⬝ y ⬝ a) ∧ b = y ⬝ a :=
  lemma_L hq (plus_of_steps_ne h hne)

/-- The second half of Lemma L: a head step changes the last item `G` of a frame only when it
is the root step of a three-item frame `S x y G`, and then the new last item is `y G`.  (This is
`HeadRec.step_inv`; `HeadRec.last_wrap` is its run form.) -/
theorem last_item_step {u G w : Term} (hp : PureS (u ⬝ G)) (s : Step (u ⬝ G) w) :
    (∃ u', w = u' ⬝ G) ∨ ∃ x y, u = S ⬝ x ⬝ y ∧ w = x ⬝ G ⬝ (y ⬝ G) := by
  rcases step_inv hp.app_inv.1 s with ⟨u', _, e⟩ | ⟨f, g, e1, e2⟩
  · exact .inl ⟨u', e⟩
  · exact .inr ⟨f, g, e1, e2⟩

/-- A head run from `y a` to a frame `S S y' a'`: the last item was not touched and the run is a
head run of `y`, or the last item has grown. -/
theorem link {y a y' a' : Term} (hp : PureS (y ⬝ a)) (h : Steps (y ⬝ a) (S ⬝ S ⬝ y' ⬝ a')) :
    (a' = a ∧ Steps y (S ⬝ S ⬝ y')) ∨ sz a < sz a' := by
  rcases split h rfl hp with ⟨e', he, hs⟩ | ⟨f, g, h1, h2⟩
  · injection he with e1 e2
    rw [← e1] at hs
    exact .inl ⟨e2, hs⟩
  · have hfg := steps_pure hp.app_inv.1 h1
    have ha := hp.app_inv.2
    have hp' : PureS (f ⬝ a ⬝ (g ⬝ a)) :=
      .app (.app hfg.app_inv.1.app_inv.2 ha) (.app hfg.app_inv.2 ha)
    obtain ⟨u', G', e, hw⟩ := last_wrap h2 rfl hp'
    injection e with _ e2
    rw [← e2] at hw
    exact .inr (Nat.lt_of_lt_of_le (sz_arg_lt g a) hw.sz_le)

/-! ## SS-chains -/

/-- A head run of one or more steps to `S S g'`: the term is `h S`, `g' = y S`, and `h` has the
head run to `S S y`. -/
theorem ss_link {g g' : Term} (hg : PureS g) (h : Plus g (S ⬝ S ⬝ g')) :
    ∃ h y, g = h ⬝ S ∧ g' = y ⬝ S ∧ Steps h (S ⬝ S ⬝ y) := by
  obtain ⟨y, hs, e⟩ := lemma_L hg h
  obtain ⟨_, s, _⟩ := h
  obtain ⟨e₀, l, rfl⟩ := step_app s
  rcases link hg hs with ⟨el, hy⟩ | lt
  · rw [← el]
    exact ⟨e₀, y, rfl, e, hy⟩
  · have := sz_pos l
    have e1 : sz S = 1 := rfl
    exfalso
    omega

/-- `SSPath k g g'`: `k` links `gᵢ →h* S S gᵢ₊₁` from `g` to `g'`. -/
inductive SSPath : Nat → Term → Term → Prop
  | zero (g : Term) : SSPath 0 g g
  | succ {k : Nat} {g g₁ g' : Term} : Steps g (S ⬝ S ⬝ g₁) → SSPath k g₁ g' → SSPath (k + 1) g g'

theorem SSPath.snoc {k : Nat} {g g' g'' : Term} (h : SSPath k g g') (hs : Steps g' (S ⬝ S ⬝ g'')) :
    SSPath (k + 1) g g'' := by
  induction h with
  | zero g => exact .succ hs (.zero _)
  | succ h1 _ ih => exact .succ h1 (ih hs)

/-- A path from `h S` of `k + 1` links gives a path from `h` of `k` links. -/
theorem sspath_strip : ∀ (k : Nat) (h g' : Term), PureS (h ⬝ S) → SSPath (k + 1) (h ⬝ S) g' →
    ∃ h', SSPath k h h' := by
  intro k
  induction k with
  | zero => intro h _ _ _; exact ⟨h, .zero h⟩
  | succ k ih =>
    intro h g' hp hpath
    cases hpath with
    | @succ _ _ g₁ _ hs rest =>
      rcases Decidable.em (h ⬝ S = S ⬝ S ⬝ g₁) with e | ne
      · injection e with _ e2
        rw [← e2] at rest
        cases rest with
        | succ hs' _ => cases steps_S hs'
      · obtain ⟨h₀, y, e1, e2, hs₀⟩ := ss_link hp (plus_of_steps_ne hs ne)
        injection e1 with e3 _
        rw [← e3] at hs₀
        rw [e2] at rest
        have hpy : PureS (y ⬝ S) := by
          have := (steps_pure hp hs).app_inv.2
          rw [e2] at this
          exact this
        obtain ⟨h', path⟩ := ih y g' hpy rest
        exact ⟨h', .succ hs₀ path⟩

/-- **No long SS-chain.**  A chain `g₀ →h* S S g₁`, `g₁ →h* S S g₂`, … from a closed S-term
`g₀` has at most `2 · sz g₀` links.  In particular there is no infinite one. -/
theorem ss_bound : ∀ (n : Nat) (g : Term), sz g ≤ n → PureS g → ∀ (L : Nat) (g' : Term),
    SSPath L g g' → L ≤ 2 * sz g := by
  intro n
  induction n with
  | zero =>
    intro g h
    have := sz_pos g
    exfalso
    omega
  | succ n ih =>
    intro g hsz hg L g' hpath
    cases hpath with
    | zero => exact Nat.zero_le _
    | @succ k _ g₁ _ hs rest =>
      rcases Decidable.em (g = S ⬝ S ⬝ g₁) with e | ne
      · rw [e] at hsz hg ⊢
        have h1 : sz (S ⬝ S ⬝ g₁) = 2 + sz g₁ := rfl
        have := ih g₁ (by omega) hg.app_inv.2 k g' rest
        omega
      · obtain ⟨h, y, e1, e2, hs₀⟩ := ss_link hg (plus_of_steps_ne hs ne)
        rw [e1] at hsz hg hs ⊢
        have h1 : sz (h ⬝ S) = sz h + 1 := rfl
        obtain ⟨h', path⟩ := sspath_strip k h g' hg (.succ hs rest)
        have := ih h (by omega) hg.app_inv.1 k h' path
        omega

/-! ## Descendants -/

/-- `PSub t w`: `t` occurs in `w` as a proper subterm. -/
inductive PSub (t : Term) : Term → Prop
  | left {f : Term} (x : Term) : HeadRec.Sub t f → PSub t (f ⬝ x)
  | right (f : Term) {x : Term} : HeadRec.Sub t x → PSub t (f ⬝ x)

theorem sub_sz_le {t w : Term} (h : HeadRec.Sub t w) : sz t ≤ sz w := by
  induction h with
  | refl => exact Nat.le_refl _
  | left x _ ih => exact Nat.le_trans ih (Nat.le_of_lt (sz_fun_lt _ x))
  | right f _ ih => exact Nat.le_trans ih (Nat.le_of_lt (sz_arg_lt f _))

theorem PSub.sub {t w : Term} (h : PSub t w) : HeadRec.Sub t w := by
  cases h with
  | left x h => exact .left x h
  | right f h => exact .right f h

theorem PSub.sz_lt {t w : Term} (h : PSub t w) : sz t < sz w := by
  cases h with
  | left x h => exact Nat.lt_of_le_of_lt (sub_sz_le h) (sz_fun_lt _ x)
  | right f h => exact Nat.lt_of_le_of_lt (sub_sz_le h) (sz_arg_lt f _)

theorem sub_psub {a b c : Term} (h : HeadRec.Sub a b) (h' : PSub b c) : PSub a c := by
  cases h' with
  | left x hb => exact .left x (Sub.trans h hb)
  | right f hb => exact .right f (Sub.trans h hb)

/-- A reduction of a subterm is a reduction of the term. -/
theorem sub_wsteps {t t' w : Term} (h : HeadRec.Sub t w) (r : WSteps t t') :
    ∃ w', WSteps w w' ∧ HeadRec.Sub t' w' := by
  induction h with
  | refl => exact ⟨t', r, .refl⟩
  | left x _ ih =>
    obtain ⟨w', h1, h2⟩ := ih
    exact ⟨w' ⬝ x, WSteps.left x h1, .left x h2⟩
  | right f _ ih =>
    obtain ⟨w', h1, h2⟩ := ih
    exact ⟨f ⬝ w', WSteps.right f h1, .right f h2⟩

theorem psub_wsteps {t t' w : Term} (h : PSub t w) (r : WSteps t t') :
    ∃ w', WSteps w w' ∧ PSub t' w' := by
  cases h with
  | left x h =>
    obtain ⟨w', h1, h2⟩ := sub_wsteps h r
    exact ⟨w' ⬝ x, WSteps.left x h1, .left x h2⟩
  | right f h =>
    obtain ⟨w', h1, h2⟩ := sub_wsteps h r
    exact ⟨f ⬝ w', WSteps.right f h1, .right f h2⟩

/-- `Desc t t'`: `t` weakly reduces to a term that properly contains `t'`. -/
def Desc (t t' : Term) : Prop := ∃ u, WSteps t u ∧ PSub t' u

theorem Desc.trans {a b c : Term} (h1 : Desc a b) (h2 : Desc b c) : Desc a c := by
  obtain ⟨u, r1, p1⟩ := h1
  obtain ⟨v, r2, p2⟩ := h2
  obtain ⟨w', r3, p3⟩ := psub_wsteps p1 r2
  exact ⟨w', r1.trans r3, sub_psub p2.sub p3⟩

/-- No closed S-term is its own descendant (`HeadRec.no_ground_loop`). -/
theorem Desc.irrefl {t : Term} (ht : PureS t) : ¬ Desc t t := by
  rintro ⟨u, r, p⟩
  cases r with
  | refl => exact Nat.lt_irrefl _ p.sz_lt
  | step s r' => exact no_ground_loop ht s r' p.sub

/-! ## Theorem 2: right combs with bounded teeth -/

/-- `Next B t t'`: the head run of `t` ends in the head normal form `S t'`, or in `S a t'` with a
tooth `a` of leaf count at most `B`. -/
def Next (B : Nat) (t t' : Term) : Prop :=
  Steps t (S ⬝ t') ∨ ∃ a, sz a ≤ B ∧ Steps t (S ⬝ a ⬝ t')

theorem Next.desc {B : Nat} {t t' : Term} (h : Next B t t') : Desc t t' := by
  rcases h with h1 | ⟨a, _, h2⟩
  · exact ⟨_, h1.weak, .right _ .refl⟩
  · exact ⟨_, h2.weak, .right _ .refl⟩

/-- `P` is a set of closed S-terms each of which has a next term in `P`. -/
def Closed (B : Nat) (P : Term → Prop) : Prop :=
  ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ Next B t t'

/-- From every term of the comb one reaches a term whose head run is not literal. -/
theorem nonlit_exists {B : Nat} {P : Term → Prop} (hC : Closed B P) :
    ∀ (n : Nat) (t : Term), sz t ≤ n → P t →
      ∃ t₁ y a, P t₁ ∧ (t₁ = t ∨ Desc t t₁) ∧ sz a ≤ B ∧ Steps t₁ (S ⬝ S ⬝ y ⬝ a) ∧
        P (y ⬝ a) := by
  intro n
  induction n with
  | zero =>
    intro t h
    have := sz_pos t
    exfalso
    omega
  | succ n ih =>
    intro t hsz hP
    obtain ⟨ht, t', hP', hN⟩ := hC t hP
    have down : t = S ⬝ t' ∨ (∃ a, t = S ⬝ a ⬝ t') →
        ∃ t₁ y a, P t₁ ∧ (t₁ = t ∨ Desc t t₁) ∧ sz a ≤ B ∧ Steps t₁ (S ⬝ S ⬝ y ⬝ a) ∧
          P (y ⬝ a) := by
      intro hlit
      have hlt : sz t' < sz t := by
        rcases hlit with e | ⟨a, e⟩
        · rw [e]; exact sz_arg_lt _ _
        · rw [e]; exact sz_arg_lt _ _
      obtain ⟨t₁, y, a, h1, h2, h3, h4, h5⟩ := ih t' (by omega) hP'
      refine ⟨t₁, y, a, h1, .inr ?_, h3, h4, h5⟩
      rcases h2 with e | d
      · rw [e]; exact hN.desc
      · exact hN.desc.trans d
    rcases hN with h1 | ⟨a, ha, h2⟩
    · exact down (.inl (hnf1_literal ht h1))
    · rcases Decidable.em (t = S ⬝ a ⬝ t') with e | ne
      · exact down (.inr ⟨a, e⟩)
      · obtain ⟨y, hs, e⟩ := lemma_L' ht h2 ne
        rw [e] at hP'
        exact ⟨t, y, a, hP, .inl rfl, ha, hs, hP'⟩

/-- Inside a run of non-literal terms with last item `a`: after `i` further terms, a term of the
comb of leaf count at most `B` has appeared below `t₁`, or the run has produced an SS-chain of
`i` links from `y₀`.  `grow` handles the case that the last item grows. -/
theorem run_inner {B : Nat} {P : Term → Prop} (hC : Closed B P) {t₁ y₀ a : Term}
    (ha : sz a ≤ B) (hD₀ : Desc t₁ (y₀ ⬝ a)) (hP₀ : P (y₀ ⬝ a))
    (grow : ∀ t y' a', P t → Desc t₁ t → sz a < sz a' → sz a' ≤ B →
      Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B) :
    ∀ i : Nat, (∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B) ∨
      ∃ y, SSPath i y₀ y ∧ P (y ⬝ a) ∧ Desc t₁ (y ⬝ a) := by
  intro i
  induction i with
  | zero => exact .inr ⟨y₀, .zero _, hP₀, hD₀⟩
  | succ i ih =>
    rcases ih with ev | ⟨y, path, hPy, hDy⟩
    · exact .inl ev
    · obtain ⟨hpure, t', hP', hN⟩ := hC _ hPy
      have hDt' : Desc t₁ t' := hDy.trans hN.desc
      rcases hN with h1 | ⟨a', ha', h2⟩
      · have e := hnf1_literal hpure h1
        injection e with _ e2
        rw [e2] at ha
        exact .inl ⟨t', hP', hDt', ha⟩
      · rcases Decidable.em (y ⬝ a = S ⬝ a' ⬝ t') with e | ne
        · injection e with _ e2
          rw [e2] at ha
          exact .inl ⟨t', hP', hDt', ha⟩
        · obtain ⟨y', hs, e⟩ := lemma_L' hpure h2 ne
          rw [e] at hP' hDt'
          rcases link hpure hs with ⟨ea, hy⟩ | lt
          · rw [ea] at hP' hDt'
            exact .inr ⟨y', path.snoc hy, hP', hDt'⟩
          · exact .inl (grow (y ⬝ a) y' a' hPy hDy lt ha' hs hP')

/-- From a term of the comb whose head run is not literal (last frame `S S y a`), a term of the
comb of leaf count at most `B` appears below it.  Induction on `B - sz a`; the inner bound is
`ss_bound`. -/
theorem run {B : Nat} {P : Term → Prop} (hC : Closed B P) :
    ∀ (d : Nat) (t₁ y a : Term), B - sz a ≤ d → sz a ≤ B → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) →
      P (y ⬝ a) → ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B := by
  have fin : ∀ (t₁ y a : Term), sz a ≤ B → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) → P (y ⬝ a) →
      (∀ t y' a', P t → Desc t₁ t → sz a < sz a' → sz a' ≤ B →
        Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B) →
      ∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ B := by
    intro t₁ y a ha hP₁ hs hPy grow
    have hD₀ : Desc t₁ (y ⬝ a) :=
      ⟨S ⬝ a ⬝ (y ⬝ a), (hs.trans (.single (.S S y a))).weak, .right _ .refl⟩
    have hy : PureS y := (steps_pure (hC t₁ hP₁).1 hs).app_inv.1.app_inv.2
    rcases run_inner hC ha hD₀ hPy grow (2 * sz y + 1) with ev | ⟨y', path, _, _⟩
    · exact ev
    · have := ss_bound (sz y) y (Nat.le_refl _) hy _ _ path
      exfalso
      omega
  intro d
  induction d with
  | zero =>
    intro t₁ y a hd ha hP₁ hs hPy
    exact fin t₁ y a ha hP₁ hs hPy (fun _ _ a' _ _ lt ha' _ _ => by exfalso; omega)
  | succ d ih =>
    intro t₁ y a hd ha hP₁ hs hPy
    refine fin t₁ y a ha hP₁ hs hPy (fun t y' a' hPt hDt lt ha' hs' hP' => ?_)
    obtain ⟨t₃, h1, h2, h3⟩ := ih t y' a' (by omega) ha' hPt hs' hP'
    exact ⟨t₃, h1, hDt.trans h2, h3⟩

/-- Below every term of the comb there is a term of the comb of leaf count at most `B`. -/
theorem small_desc {B : Nat} {P : Term → Prop} (hC : Closed B P) {t : Term} (hP : P t) :
    ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ B := by
  obtain ⟨t₁, y, a, hP₁, hr, ha, hs, hPy⟩ := nonlit_exists hC (sz t) t (Nat.le_refl _) hP
  obtain ⟨t₃, h1, h2, h3⟩ := run hC (B - sz a) t₁ y a (Nat.le_refl _) ha hP₁ hs hPy
  rcases hr with e | d
  · rw [e] at h2
    exact ⟨t₃, h1, h2, h3⟩
  · exact ⟨t₃, h1, d.trans h2, h3⟩

/-- A list of the closed S-terms of leaf count at most `n` (with repetitions). -/
def enum : Nat → List Term
  | 0 => []
  | n + 1 => S :: (enum n).flatMap (fun f => (enum n).map (fun x => f ⬝ x))

theorem mem_enum : ∀ (n : Nat) {t : Term}, PureS t → sz t ≤ n → t ∈ enum n := by
  intro n
  induction n with
  | zero =>
    intro t _ h
    have := sz_pos t
    exfalso
    omega
  | succ n ih =>
    intro t ht h
    cases ht with
    | S => exact List.Mem.head _
    | @app f x hf hx =>
      have h1 : sz (f ⬝ x) = sz f + sz x := rfl
      have := sz_pos f
      have := sz_pos x
      exact List.Mem.tail _ (List.mem_flatMap.mpr ⟨f, ih hf (by omega),
        List.mem_map.mpr ⟨x, ih hx (by omega), rfl⟩⟩)

/-- Remove every occurrence of `x`.  (Core's `List.erase` lemmas depend on `Classical.choice`
in this toolchain, so the pigeonhole below uses its own deletion.) -/
def del (x : Term) : List Term → List Term
  | [] => []
  | a :: l => if a = x then del x l else a :: del x l

theorem mem_del {x t : Term} (hne : t ≠ x) : ∀ {l : List Term}, t ∈ l → t ∈ del x l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons a l ih =>
    intro h
    rcases Decidable.em (a = x) with h1 | h1
    · have e : del x (a :: l) = del x l := if_pos h1
      rw [e]
      rcases List.mem_cons.mp h with e' | h'
      · exact absurd (e'.trans h1) hne
      · exact ih h'
    · have e : del x (a :: l) = a :: del x l := if_neg h1
      rw [e]
      rcases List.mem_cons.mp h with e' | h'
      · rw [e']; exact List.Mem.head _
      · exact List.Mem.tail _ (ih h')

theorem del_length_le (x : Term) : ∀ l : List Term, (del x l).length ≤ l.length := by
  intro l
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    rcases Decidable.em (a = x) with h1 | h1
    · have e : del x (a :: l) = del x l := if_pos h1
      rw [e]
      exact Nat.le_succ_of_le ih
    · have e : del x (a :: l) = a :: del x l := if_neg h1
      rw [e]
      exact Nat.succ_le_succ ih

theorem del_length_lt {x : Term} : ∀ {l : List Term}, x ∈ l → (del x l).length < l.length := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons a l ih =>
    intro h
    rcases Decidable.em (a = x) with h1 | h1
    · have e : del x (a :: l) = del x l := if_pos h1
      rw [e]
      exact Nat.lt_succ_of_le (del_length_le x l)
    · have e : del x (a :: l) = a :: del x l := if_neg h1
      rw [e]
      rcases List.mem_cons.mp h with e' | h'
      · exact absurd e'.symm h1
      · exact Nat.succ_lt_succ (ih h')

/-- The pigeonhole step, choice-free.  Let `D` be a transitive relation that is irreflexive on
`P`, a set of closed S-terms.  If every term of `P` has a `D`-successor in `P` of leaf count at
most `B`, then `P` is empty.  (The small successors along a chain are pairwise distinct, and there
are finitely many closed S-terms of leaf count at most `B`.) -/
theorem finite_descent {B : Nat} {P : Term → Prop} {D : Term → Term → Prop}
    (hp : ∀ t, P t → PureS t) (trans : ∀ {a b c : Term}, D a b → D b c → D a c)
    (irr : ∀ t, P t → ¬ D t t)
    (hd : ∀ t, P t → ∃ t₃, P t₃ ∧ D t t₃ ∧ sz t₃ ≤ B) : ∀ t, ¬ P t := by
  have key : ∀ (k : Nat) (l : List Term), l.length ≤ k → ∀ t, P t →
      (∀ t', P t' → D t t' → sz t' ≤ B → t' ∈ l) → False := by
    intro k
    induction k with
    | zero =>
      intro l hl t hP hmem
      obtain ⟨t₃, h1, h2, h3⟩ := hd t hP
      have := List.length_pos_of_mem (hmem t₃ h1 h2 h3)
      omega
    | succ k ih =>
      intro l hl t hP hmem
      obtain ⟨t₃, h1, h2, h3⟩ := hd t hP
      have hin := hmem t₃ h1 h2 h3
      have hlen := del_length_lt hin
      refine ih (del t₃ l) (by omega) t₃ h1 (fun t' hP' hD' hs' => ?_)
      have ne : t' ≠ t₃ := by
        intro e
        rw [e] at hD'
        exact irr t₃ h1 hD'
      exact mem_del ne (hmem t' hP' (trans h2 hD') hs')
  intro t hP
  exact key _ (enum B) (Nat.le_refl _) t hP (fun t' hP' _ hs => mem_enum B (hp t' hP') hs)

/-- `finite_descent` for the descendant relation `Desc`. -/
theorem desc_finite {B : Nat} {P : Term → Prop} (hp : ∀ t, P t → PureS t)
    (hd : ∀ t, P t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ B) : ∀ t, ¬ P t :=
  finite_descent (D := Desc) hp (fun h1 h2 => Desc.trans h1 h2)
    (fun t hP => Desc.irrefl (hp t hP)) hd

/-- **Theorem 2** (right combs with bounded teeth), choice-free form.  Let `P` be a set of closed
S-terms such that every `t` in `P` has, on its head run, the head normal form `S t'` or `S a t'`
with `t'` in `P` and `sz a ≤ B`.  Then `P` is empty.

The paper's statement, for a sequence, is `right_combs_seq`.  The proof uses
`HeadRec.no_ground_loop`.  The teeth are bounded in leaf count; nothing is claimed for unbounded
teeth. -/
theorem right_combs {B : Nat} {P : Term → Prop} (hC : Closed B P) : ∀ t, ¬ P t :=
  desc_finite (fun t hP => (hC t hP).1) (fun _ hP => small_desc hC hP)

/-- **Theorem 2**, as in the paper: there is no sequence of closed S-terms `q₀, q₁, …` in which
every `qₙ` has, on its head run, the head normal form `S qₙ₊₁` or `S aₙ qₙ₊₁` with
`sz aₙ ≤ B`. -/
theorem right_combs_seq {B : Nat} (q : Nat → Term) (h0 : PureS (q 0))
    (H : ∀ n, Next B (q n) (q (n + 1))) : False := by
  have pure : ∀ n, PureS (q n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rcases H n with h1 | ⟨a, _, h2⟩
      · exact (steps_pure ih h1).app_inv.2
      · exact (steps_pure ih h2).app_inv.2
  have hC : Closed B (fun t => ∃ n, t = q n) := by
    rintro t ⟨n, e⟩
    rw [e]
    exact ⟨pure n, q (n + 1), ⟨n + 1, rfl⟩, H n⟩
  exact right_combs hC (q 0) ⟨0, rfl⟩

/-! ## Theorem 2 up to conversion -/

/-- `NextC B t t'`: `t` is convertible to `S t'`, or to `S a t'` for a closed `a` whose normal
form has leaf count at most `B`. -/
def NextC (B : Nat) (t t' : Term) : Prop :=
  Convertible t (S ⬝ t') ∨
    ∃ a n, PureS a ∧ WSteps a n ∧ Normal n ∧ sz n ≤ B ∧ Convertible t (S ⬝ a ⬝ t')

/-- **Theorem 2 up to conversion.**  Let `P` be a set of closed S-terms such that every `t` in
`P` is convertible to `S t'` or to `S a t'` with `t'` in `P` and `a` closed with a normal form of
leaf count at most `B`.  Then `P` is empty.

Proof: the set of closed terms convertible to a member of `P` is closed under `Next B`, by
Church–Rosser and standardization (the head run of `t` reaches `S a″ t″` with `a″ ↠ a′ ↞ a` and
`t″ ↠ · ↞ t'`, and `sz a″ ≤ sz (nf a)`); then `right_combs`. -/
theorem right_combs_conv {B : Nat} {P : Term → Prop}
    (hC : ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ NextC B t t') : ∀ t, ¬ P t := by
  have hQ : Closed B (fun t => PureS t ∧ ∃ t₀, P t₀ ∧ Convertible t t₀) := by
    rintro t ⟨ht, t₀, hP₀, hc⟩
    obtain ⟨_, t', hP', hN⟩ := hC t₀ hP₀
    have ht' := (hC t' hP').1
    refine ⟨ht, ?_⟩
    rcases hN with c1 | ⟨a, n, hpa, han, nf, hsz, c2⟩
    · obtain ⟨w, h1, h2⟩ := conv_iff_join.mp (hc.trans c1)
      obtain ⟨r', e, hr⟩ := hnf1_wsteps (.app .S ht') h2
      rw [e] at h1
      obtain ⟨T, hs, hi⟩ := wsteps_split h1
      obtain ⟨f, r'', e', hf, hr''⟩ := parIs_app hi
      rw [e', parIs_S hf] at hs
      have hpr := (steps_pure ht hs).app_inv.2
      exact ⟨r'', ⟨hpr, t', hP', conv_iff_join.mpr ⟨r', hr'', hr⟩⟩, .inl hs⟩
    · obtain ⟨w, h1, h2⟩ := conv_iff_join.mp (hc.trans c2)
      obtain ⟨a', r', e, ha', hr⟩ := hnf2_wsteps (.app (.app .S hpa) ht') h2
      rw [e] at h1
      obtain ⟨T, hs, hi⟩ := wsteps_split h1
      obtain ⟨g, r'', e', hg, hr''⟩ := parIs_app hi
      obtain ⟨f, a'', e'', hf, ha''⟩ := parIs_app hg
      rw [e', e'', parIs_S hf] at hs
      have hp := steps_pure ht hs
      have hpr := hp.app_inv.2
      have hpa'' := hp.app_inv.1.app_inv.2
      have hle : sz a'' ≤ B :=
        Nat.le_trans (sz_wsteps hpa'' (ha''.trans (wsteps_to_normal ha' han nf))) hsz
      exact ⟨r'', ⟨hpr, t', hP', conv_iff_join.mpr ⟨r', hr'', hr⟩⟩, .inr ⟨a'', hle, hs⟩⟩
  intro t hP
  exact right_combs hQ t ⟨(hC t hP).1, t, hP, .refl t⟩

/-! ## Comb contexts -/

/-- **Comb contexts**: built from the hole by `E ↦ S E` and `E ↦ S a E` with `a` a closed
S-term that has a normal form.  (The hole itself is a comb; the theorems exclude it.) -/
inductive Comb : Phi.Ctx → Prop
  | hole : Comb .hole
  | s1 {E : Phi.Ctx} : Comb E → Comb (.app .s E)
  | s2 {a : Term} {E : Phi.Ctx} : PureS a → Normalizing a → Comb E →
      Comb (.app (.app .s (Tower.ofTerm a)) E)

/-- A comb context whose teeth have normal forms of leaf count at most `B`. -/
inductive CombB (B : Nat) : Phi.Ctx → Prop
  | hole : CombB B .hole
  | s1 {E : Phi.Ctx} : CombB B E → CombB B (.app .s E)
  | s2 {a n : Term} {E : Phi.Ctx} : PureS a → WSteps a n → Normal n → sz n ≤ B → CombB B E →
      CombB B (.app (.app .s (Tower.ofTerm a)) E)

theorem CombB.mono {B B' : Nat} (h : B ≤ B') {E : Phi.Ctx} (hE : CombB B E) : CombB B' E := by
  induction hE with
  | hole => exact .hole
  | s1 _ ih => exact .s1 ih
  | s2 hpa han nf hsz _ ih => exact .s2 hpa han nf (Nat.le_trans hsz h) ih

theorem Comb.bound {E : Phi.Ctx} (hE : Comb E) : ∃ B, CombB B E := by
  induction hE with
  | hole => exact ⟨0, .hole⟩
  | s1 _ ih =>
    obtain ⟨B, h⟩ := ih
    exact ⟨B, .s1 h⟩
  | s2 hpa hn _ ih =>
    obtain ⟨B, h⟩ := ih
    obtain ⟨n, han, nf⟩ := hn
    exact ⟨B + sz n, .s2 hpa han nf (Nat.le_add_left _ _) (h.mono (Nat.le_add_right _ _))⟩

/-- **NCFP for comb contexts.**  Let `E ≠ hole` be built from the hole by `E ↦ S E` and
`E ↦ S a E` with every `a` closed and normalizing.  Then no closed S-term `p` (with or without a
normal form) is convertible to `E[p]`.

Proof: the set of terms `E'[p]`, `E'` a comb with the same bound on the teeth, satisfies the
hypothesis of `right_combs_conv`; a term `p` itself is convertible to `E[p]`. -/
theorem ncfp_comb {p : Term} (hp : PureS p) {E : Phi.Ctx} (hE : Comb E) (hne : E ≠ .hole) :
    ¬ Convertible p (E.plug p) := by
  intro hc
  obtain ⟨B, hB⟩ := hE.bound
  have key : ∀ E' : Phi.Ctx, CombB B E' → E' ≠ .hole → ∀ t, Convertible t (E'.plug p) →
      ∃ t', (∃ E'', CombB B E'' ∧ t' = E''.plug p) ∧ NextC B t t' := by
    intro E' hE' hne' t ht
    cases hE' with
    | hole => exact absurd rfl hne'
    | @s1 E'' h => exact ⟨E''.plug p, ⟨E'', h, rfl⟩, .inl ht⟩
    | @s2 a n E'' hpa han nf hsz h =>
      have e : (Phi.Ctx.app (.app .s (Tower.ofTerm a)) E'').plug p = S ⬝ a ⬝ E''.plug p := by
        show S ⬝ (Tower.ofTerm a).plug p ⬝ E''.plug p = _
        rw [Tower.plug_ofTerm hpa]
      rw [e] at ht
      exact ⟨E''.plug p, ⟨E'', h, rfl⟩, .inr ⟨a, n, hpa, han, nf, hsz, ht⟩⟩
  have hC : ∀ t, (∃ E', CombB B E' ∧ t = E'.plug p) →
      PureS t ∧ ∃ t', (∃ E'', CombB B E'' ∧ t' = E''.plug p) ∧ NextC B t t' := by
    rintro t ⟨E', hE', e⟩
    rw [e]
    refine ⟨Tower.plug_pure E' hp, ?_⟩
    cases hE' with
    | hole => exact key E hB hne p hc
    | @s1 E'' h => exact key _ (.s1 h) (fun e => by cases e) _ (.refl _)
    | @s2 a n E'' hpa han nf hsz h =>
      exact key _ (.s2 hpa han nf hsz h) (fun e => by cases e) _ (.refl _)
  exact right_combs_conv hC p ⟨.hole, .hole, rfl⟩

/-! ## Theorem F: first-item combs with bounded teeth -/

/-- `NextF B t t'`: the head run of `t` ends in the head normal form `S t'`, or in `S t' b` with
`sz b ≤ B`. -/
def NextF (B : Nat) (t t' : Term) : Prop :=
  Steps t (S ⬝ t') ∨ ∃ b, sz b ≤ B ∧ Steps t (S ⬝ t' ⬝ b)

theorem NextF.desc {B : Nat} {t t' : Term} (h : NextF B t t') : Desc t t' := by
  rcases h with h1 | ⟨b, _, h2⟩
  · exact ⟨_, h1.weak, .right _ .refl⟩
  · exact ⟨_, h2.weak, .left b (.right _ .refl)⟩

/-- Below every term of a first-item comb there is a term of the comb of leaf count at most `B`:
a literal step lowers the size, and at a step that is not literal Lemma L gives `b = y t'`. -/
theorem small_descF {B : Nat} {P : Term → Prop}
    (hC : ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ NextF B t t') :
    ∀ (n : Nat) (t : Term), sz t ≤ n → P t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ B := by
  intro n
  induction n with
  | zero =>
    intro t h
    have := sz_pos t
    exfalso
    omega
  | succ n ih =>
    intro t hsz hP
    obtain ⟨ht, t', hP', hN⟩ := hC t hP
    have down : sz t' < sz t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ B := by
      intro hlt
      obtain ⟨t₃, h1, h2, h3⟩ := ih t' (by omega) hP'
      exact ⟨t₃, h1, hN.desc.trans h2, h3⟩
    rcases hN with h1 | ⟨b, hb, h2⟩
    · have e := hnf1_literal ht h1
      exact down (by rw [e]; exact sz_arg_lt _ _)
    · rcases Decidable.em (t = S ⬝ t' ⬝ b) with e | ne
      · refine down ?_
        rw [e]
        exact Nat.lt_trans (sz_arg_lt S t') (sz_fun_lt _ b)
      · obtain ⟨y, _, e⟩ := lemma_L' ht h2 ne
        have hlt := sz_arg_lt y t'
        rw [← e] at hlt
        exact ⟨t', hP', (NextF.desc (.inr ⟨b, hb, h2⟩)), by omega⟩

/-- **Theorem F** (first-item combs with bounded teeth), choice-free form.  Let `P` be a set of
closed S-terms such that every `t` in `P` has, on its head run, the head normal form `S t'` or
`S t' b` with `t'` in `P` and `sz b ≤ B`.  Then `P` is empty.  Uses `HeadRec.no_ground_loop`. -/
theorem first_combs {B : Nat} {P : Term → Prop}
    (hC : ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ NextF B t t') : ∀ t, ¬ P t :=
  desc_finite (fun t hP => (hC t hP).1) (fun t hP => small_descF hC (sz t) t (Nat.le_refl _) hP)

/-- **Theorem F**, for a sequence: there is no sequence of closed S-terms `q₀, q₁, …` in which
every `qₙ` has, on its head run, the head normal form `S qₙ₊₁` or `S qₙ₊₁ bₙ` with
`sz bₙ ≤ B`. -/
theorem first_combs_seq {B : Nat} (q : Nat → Term) (h0 : PureS (q 0))
    (H : ∀ n, NextF B (q n) (q (n + 1))) : False := by
  have pure : ∀ n, PureS (q n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rcases H n with h1 | ⟨b, _, h2⟩
      · exact (steps_pure ih h1).app_inv.2
      · exact (steps_pure ih h2).app_inv.1.app_inv.2
  have hC : ∀ t, (∃ n, t = q n) → PureS t ∧ ∃ t', (∃ n, t' = q n) ∧ NextF B t t' := by
    rintro t ⟨n, e⟩
    rw [e]
    exact ⟨pure n, q (n + 1), ⟨n + 1, rfl⟩, H n⟩
  exact first_combs hC (q 0) ⟨0, rfl⟩

/-! ## Theorem G: mixed head-normal-form combs with bounded teeth

Source: `notes/NCFP-proof.md`, §9.  The teeth have leaf count at most `M`; "small" below means
leaf count at most `M + 1` (the note takes `M ≥ 1`). -/

/-- **Lemma P** (predecessor).  If a head step yields the three-item frame `S S y a`, the frame
before it is `S S y' S a` with `y = y' S`, or `S (S S) y' y` with `a = y' y`. -/
theorem lemma_P {F' y a : Term} (hp : PureS F') (s : Step F' (S ⬝ S ⬝ y ⬝ a)) :
    (∃ y', F' = S ⬝ S ⬝ y' ⬝ S ⬝ a ∧ y = y' ⬝ S) ∨
      (∃ y', F' = S ⬝ (S ⬝ S) ⬝ y' ⬝ y ∧ a = y' ⬝ y) := by
  obtain ⟨u, l, e⟩ := step_app s
  rw [e] at hp s
  rcases step_inv hp.app_inv.1 s with ⟨u', s', e'⟩ | ⟨f, g, e1, e2⟩
  · injection e' with e3 e4
    rw [← e3] at s'
    obtain ⟨y', e5, e6⟩ := step_to_S2 hp.app_inv.1 s'
    exact .inl ⟨y', by rw [e, e5, ← e4], e6⟩
  · injection e2 with e3 e4
    injection e3 with e5 e6
    exact .inr ⟨g, by rw [e, e1, ← e5, ← e6], by rw [e4, ← e6]⟩

/-- A frame `S S g a` with `a` smaller than `g` and `g` not of the form `y' S` has no
predecessor: a head run that ends in it has no step. -/
theorem no_pred {q g a : Term} (hq : PureS q) (h : Steps q (S ⬝ S ⬝ g ⬝ a)) (hsz : sz a < sz g)
    (hg : ∀ y', g ≠ y' ⬝ S) : q = S ⬝ S ⬝ g ⬝ a := by
  rcases steps_last h with e | ⟨t', h1, s⟩
  · exact e
  · rcases lemma_P (steps_pure hq h1) s with ⟨y', _, e⟩ | ⟨y', _, e⟩
    · exact absurd e (hg y')
    · have := sz_arg_lt y' g
      rw [← e] at this
      exfalso
      omega

/-- `Rigid u g`: `g` is `S u`, `S S (S u)`, `S S (S S (S u))`, … (the note's `gᵢ`). -/
inductive Rigid (u : Term) : Term → Prop
  | base : Rigid u (S ⬝ u)
  | step {g : Term} : Rigid u g → Rigid u (S ⬝ S ⬝ g)

theorem Rigid.sub {u g : Term} (h : Rigid u g) : HeadRec.Sub u g := by
  induction h with
  | base => exact .right _ .refl
  | step _ ih => exact .right _ ih

theorem Rigid.sz_lt {u g : Term} (h : Rigid u g) : sz u < sz g := by
  induction h with
  | base => exact sz_arg_lt _ _
  | step _ ih => exact Nat.lt_trans ih (sz_arg_lt _ _)

theorem Rigid.not_appS {u g : Term} (h : Rigid u g) (hu : u ≠ S) : ∀ y', g ≠ y' ⬝ S := by
  intro y' e
  cases h with
  | base =>
    injection e with _ e2
    exact hu e2
  | step h' =>
    injection e with _ e2
    rw [e2] at h'
    cases h'

/-- An SS-chain that ends in a rigid term is literal, so it starts in a rigid term. -/
theorem sspath_rigid {u : Term} (hu : u ≠ S) : ∀ {i : Nat} {y₀ y : Term}, PureS y₀ →
    SSPath i y₀ y → Rigid u y → Rigid u y₀ := by
  intro i y₀ y hp hpath
  induction hpath with
  | zero g => exact fun h => h
  | @succ k g g₁ g' hs _ ih =>
    intro hr
    have hr₁ := ih (steps_pure hp hs).app_inv.2 hr
    rcases Decidable.em (g = S ⬝ S ⬝ g₁) with e | ne
    · rw [e]
      exact .step hr₁
    · obtain ⟨y', _, e⟩ := lemma_L' hp hs ne
      exact absurd e (hr₁.not_appS hu y')

/-- `NextG M t t'`: the head run of `t` ends in `S t'`, in `S a t'` with `sz a ≤ M`, or in
`S t' b` with `sz b ≤ M`. -/
def NextG (M : Nat) (t t' : Term) : Prop :=
  Steps t (S ⬝ t') ∨ (∃ a, sz a ≤ M ∧ Steps t (S ⬝ a ⬝ t')) ∨ ∃ b, sz b ≤ M ∧ Steps t (S ⬝ t' ⬝ b)

theorem NextG.desc {M : Nat} {t t' : Term} (h : NextG M t t') : Desc t t' := by
  rcases h with h1 | ⟨a, _, h2⟩ | ⟨b, _, h3⟩
  · exact ⟨_, h1.weak, .right _ .refl⟩
  · exact ⟨_, h2.weak, .right _ .refl⟩
  · exact ⟨_, h3.weak, .left b (.right _ .refl)⟩

/-- `P` is a set of closed S-terms each of which has a next term in `P`, in any of the three
directions. -/
def ClosedG (M : Nat) (P : Term → Prop) : Prop :=
  ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ NextG M t t'

/-- The outcome of a block that starts at `t` with last frame `S S y a`: a small term of the comb
below `t`, or `t = S S g a` literally with `g` rigid over a large term `u` of the comb. -/
def Res (M : Nat) (P : Term → Prop) (t a : Term) : Prop :=
  (∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M + 1) ∨
    ∃ u g, P u ∧ Rigid u g ∧ M + 1 < sz u ∧ t = S ⬝ S ⬝ g ⬝ a

/-- Inside a block of non-literal terms with last item `a` (the mixed analogue of
`run_inner`): a small term has appeared, or the block has ended at a large `u` with `y₀` rigid
over `u`, or the block has produced an SS-chain of `i` links. -/
theorem runG_inner {M : Nat} {P : Term → Prop} (hC : ClosedG M P) {t₁ y₀ a : Term}
    (ha : sz a ≤ M) (hy₀ : PureS y₀) (hD₀ : Desc t₁ (y₀ ⬝ a)) (hP₀ : P (y₀ ⬝ a))
    (grow : ∀ t y' a', P t → sz a < sz a' → sz a' ≤ M →
      Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → Res M P t a') :
    ∀ i : Nat, (∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ M + 1) ∨
      (∃ u, P u ∧ M + 1 < sz u ∧ Rigid u y₀) ∨
      ∃ y, SSPath i y₀ y ∧ P (y ⬝ a) ∧ Desc t₁ (y ⬝ a) := by
  intro i
  induction i with
  | zero => exact .inr (.inr ⟨y₀, .zero _, hP₀, hD₀⟩)
  | succ i ih =>
    rcases ih with ev | blk | ⟨y, path, hPy, hDy⟩
    · exact .inl ev
    · exact .inr (.inl blk)
    · obtain ⟨hpure, t', hP', hN⟩ := hC _ hPy
      have hDt' : Desc t₁ t' := hDy.trans hN.desc
      have small : sz t' ≤ M → (∃ t₃, P t₃ ∧ Desc t₁ t₃ ∧ sz t₃ ≤ M + 1) :=
        fun h => ⟨t', hP', hDt', Nat.le_succ_of_le h⟩
      rcases hN with h1 | ⟨a', ha', h2⟩ | ⟨b, hb, h3⟩
      · have e := hnf1_literal hpure h1
        injection e with _ e2
        rw [e2] at ha
        exact .inl (small ha)
      · rcases Decidable.em (y ⬝ a = S ⬝ a' ⬝ t') with e | ne
        · injection e with _ e2
          rw [e2] at ha
          exact .inl (small ha)
        · obtain ⟨y', hs, e⟩ := lemma_L' hpure h2 ne
          rw [e] at hP' hDt'
          rcases link hpure hs with ⟨ea, hy⟩ | lt
          · rw [ea] at hP' hDt'
            exact .inr (.inr ⟨y', path.snoc hy, hP', hDt'⟩)
          · rcases grow (y ⬝ a) y' a' hPy lt ha' hs hP' with ⟨t₃, h4, h5, h6⟩ | ⟨u, g, _, _, _, eq⟩
            · exact .inl ⟨t₃, h4, hDy.trans h5, h6⟩
            · injection eq with _ e2
              rw [e2] at lt
              exact absurd lt (Nat.lt_irrefl _)
      · rcases Decidable.em (y ⬝ a = S ⬝ t' ⬝ b) with e | ne
        · injection e with e1 _
          rcases Nat.lt_or_ge (M + 1) (sz t') with big | le
          · have hne : t' ≠ S := by
              intro e'
              rw [e'] at big
              have e1 : sz S = 1 := rfl
              omega
            have hr : Rigid t' y := by rw [e1]; exact .base
            exact .inr (.inl ⟨t', hP', big, sspath_rigid hne hy₀ path hr⟩)
          · exact .inl ⟨t', hP', hDt', le⟩
        · obtain ⟨y', _, e⟩ := lemma_L' hpure h3 ne
          have := sz_arg_lt y' t'
          rw [← e] at this
          exact .inl (small (by omega))

/-- A block of the mixed comb, from its first term `t₁` with last frame `S S y a` (the mixed
analogue of `run`). -/
theorem runG {M : Nat} {P : Term → Prop} (hC : ClosedG M P) :
    ∀ (d : Nat) (t₁ y a : Term), M - sz a ≤ d → sz a ≤ M → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) →
      P (y ⬝ a) → Res M P t₁ a := by
  have fin : ∀ (t₁ y a : Term), sz a ≤ M → P t₁ → Steps t₁ (S ⬝ S ⬝ y ⬝ a) → P (y ⬝ a) →
      (∀ t y' a', P t → sz a < sz a' → sz a' ≤ M →
        Steps t (S ⬝ S ⬝ y' ⬝ a') → P (y' ⬝ a') → Res M P t a') → Res M P t₁ a := by
    intro t₁ y a ha hP₁ hs hPy grow
    have ht₁ := (hC t₁ hP₁).1
    have hD₀ : Desc t₁ (y ⬝ a) :=
      ⟨S ⬝ a ⬝ (y ⬝ a), (hs.trans (.single (.S S y a))).weak, .right _ .refl⟩
    have hy : PureS y := (steps_pure ht₁ hs).app_inv.1.app_inv.2
    rcases runG_inner hC ha hy hD₀ hPy grow (2 * sz y + 1) with ev | ⟨u, hPu, big, hr⟩ |
      ⟨y', path, _, _⟩
    · exact .inl ev
    · have hne : u ≠ S := by
        intro e'
        rw [e'] at big
        have e1 : sz S = 1 := rfl
        omega
      have hlt := hr.sz_lt
      have e := no_pred ht₁ hs (by omega) (hr.not_appS hne)
      exact .inr ⟨u, y, hPu, hr, big, e⟩
    · have := ss_bound (sz y) y (Nat.le_refl _) hy _ _ path
      exfalso
      omega
  intro d
  induction d with
  | zero =>
    intro t₁ y a hd ha hP₁ hs hPy
    exact fin t₁ y a ha hP₁ hs hPy (fun _ _ a' _ lt ha' _ _ => by exfalso; omega)
  | succ d ih =>
    intro t₁ y a hd ha hP₁ hs hPy
    exact fin t₁ y a ha hP₁ hs hPy
      (fun t y' a' hPt lt ha' hs' hP' => ih t y' a' (by omega) ha' hPt hs' hP')

/-- Below every term of a mixed comb there is a small term of the comb.  Induction on the leaf
count: a literal step and a completed block both lead to a smaller term. -/
theorem small_descG {M : Nat} {P : Term → Prop} (hC : ClosedG M P) :
    ∀ (n : Nat) (t : Term), sz t ≤ n → P t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M + 1 := by
  intro n
  induction n with
  | zero =>
    intro t h
    have := sz_pos t
    exfalso
    omega
  | succ n ih =>
    intro t hsz hP
    obtain ⟨ht, t', hP', hN⟩ := hC t hP
    have down : ∀ u, P u → Desc t u → sz u < sz t → ∃ t₃, P t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M + 1 := by
      intro u hPu hD hlt
      obtain ⟨t₃, h1, h2, h3⟩ := ih u (by omega) hPu
      exact ⟨t₃, h1, hD.trans h2, h3⟩
    have hD := hN.desc
    rcases hN with h1 | ⟨a, ha, h2⟩ | ⟨b, hb, h3⟩
    · have e := hnf1_literal ht h1
      exact down t' hP' hD (by rw [e]; exact sz_arg_lt _ _)
    · rcases Decidable.em (t = S ⬝ a ⬝ t') with e | ne
      · exact down t' hP' hD (by rw [e]; exact sz_arg_lt _ _)
      · obtain ⟨y, hs, e⟩ := lemma_L' ht h2 ne
        rw [e] at hP'
        rcases runG hC (M - sz a) t y a (Nat.le_refl _) ha hP hs hP' with ev | ⟨u, g, hPu, hr, _, eq⟩
        · exact ev
        · have hsub : PSub u t := by rw [eq]; exact .left a (.right _ hr.sub)
          exact down u hPu ⟨t, .refl t, hsub⟩ hsub.sz_lt
    · rcases Decidable.em (t = S ⬝ t' ⬝ b) with e | ne
      · exact down t' hP' hD (by rw [e]; exact Nat.lt_trans (sz_arg_lt S t') (sz_fun_lt _ b))
      · obtain ⟨y, _, e⟩ := lemma_L' ht h3 ne
        have := sz_arg_lt y t'
        rw [← e] at this
        exact ⟨t', hP', hD, by omega⟩

/-- **Theorem G** (mixed head-normal-form combs with bounded teeth), choice-free form.  Let `P`
be a set of closed S-terms such that every `t` in `P` has, on its head run, a head normal form
`S t'`, `S a t'` with `sz a ≤ M`, or `S t' b` with `sz b ≤ M`, where `t'` is in `P`.  Then `P` is
empty.  It contains Theorem 2 (`right_combs`) and Theorem F (`first_combs`).

Uses Lemma L, Lemma P, `HeadRec.no_ground_loop` and the SS-chain bound `ss_bound` (the core of
Theorem 2). -/
theorem mixed_combs {M : Nat} {P : Term → Prop} (hC : ClosedG M P) : ∀ t, ¬ P t :=
  desc_finite (fun t hP => (hC t hP).1) (fun t hP => small_descG hC (sz t) t (Nat.le_refl _) hP)

/-- **Theorem G**, for a sequence: there is no sequence of closed S-terms `q₀, q₁, …` in which
every `qₙ` has, on its head run, the head normal form `S qₙ₊₁`, `S aₙ qₙ₊₁` with `sz aₙ ≤ M`, or
`S qₙ₊₁ bₙ` with `sz bₙ ≤ M`. -/
theorem mixed_combs_seq {M : Nat} (q : Nat → Term) (h0 : PureS (q 0))
    (H : ∀ n, NextG M (q n) (q (n + 1))) : False := by
  have pure : ∀ n, PureS (q n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rcases H n with h1 | ⟨a, _, h2⟩ | ⟨b, _, h3⟩
      · exact (steps_pure ih h1).app_inv.2
      · exact (steps_pure ih h2).app_inv.2
      · exact (steps_pure ih h3).app_inv.1.app_inv.2
  have hC : ClosedG M (fun t => ∃ n, t = q n) := by
    rintro t ⟨n, e⟩
    rw [e]
    exact ⟨pure n, q (n + 1), ⟨n + 1, rfl⟩, H n⟩
  exact mixed_combs hC (q 0) ⟨0, rfl⟩

/-- `NextGC M t t'`: `t` is convertible to `S t'`, to `S a t'`, or to `S t' a`, for a closed `a`
whose normal form has leaf count at most `M`. -/
def NextGC (M : Nat) (t t' : Term) : Prop :=
  Convertible t (S ⬝ t') ∨
    ∃ a n, PureS a ∧ WSteps a n ∧ Normal n ∧ sz n ≤ M ∧
      (Convertible t (S ⬝ a ⬝ t') ∨ Convertible t (S ⬝ t' ⬝ a))

/-- **Theorem G up to conversion.**  Let `P` be a set of closed S-terms such that every `t` in
`P` is convertible to `S t'`, `S a t'` or `S t' a` with `t'` in `P` and `a` closed with a normal
form of leaf count at most `M`.  Then `P` is empty.  (Church–Rosser and standardization, then
`mixed_combs`.) -/
theorem mixed_combs_conv {M : Nat} {P : Term → Prop}
    (hC : ∀ t, P t → PureS t ∧ ∃ t', P t' ∧ NextGC M t t') : ∀ t, ¬ P t := by
  have hQ : ClosedG M (fun t => PureS t ∧ ∃ t₀, P t₀ ∧ Convertible t t₀) := by
    rintro t ⟨ht, t₀, hP₀, hc⟩
    obtain ⟨_, t', hP', hN⟩ := hC t₀ hP₀
    have ht' := (hC t' hP').1
    refine ⟨ht, ?_⟩
    rcases hN with c1 | ⟨a, n, hpa, han, nf, hsz, c2 | c3⟩
    · obtain ⟨w, h1, h2⟩ := conv_iff_join.mp (hc.trans c1)
      obtain ⟨r', e, hr⟩ := hnf1_wsteps (.app .S ht') h2
      rw [e] at h1
      obtain ⟨T, hs, hi⟩ := wsteps_split h1
      obtain ⟨f, r'', e', hf, hr''⟩ := parIs_app hi
      rw [e', parIs_S hf] at hs
      have hpr := (steps_pure ht hs).app_inv.2
      exact ⟨r'', ⟨hpr, t', hP', conv_iff_join.mpr ⟨r', hr'', hr⟩⟩, .inl hs⟩
    · obtain ⟨w, h1, h2⟩ := conv_iff_join.mp (hc.trans c2)
      obtain ⟨a', r', e, ha', hr⟩ := hnf2_wsteps (.app (.app .S hpa) ht') h2
      rw [e] at h1
      obtain ⟨T, hs, hi⟩ := wsteps_split h1
      obtain ⟨g, r'', e', hg, hr''⟩ := parIs_app hi
      obtain ⟨f, a'', e'', hf, ha''⟩ := parIs_app hg
      rw [e', e'', parIs_S hf] at hs
      have hp := steps_pure ht hs
      have hle : sz a'' ≤ M := Nat.le_trans
        (sz_wsteps hp.app_inv.1.app_inv.2 (ha''.trans (wsteps_to_normal ha' han nf))) hsz
      exact ⟨r'', ⟨hp.app_inv.2, t', hP', conv_iff_join.mpr ⟨r', hr'', hr⟩⟩,
        .inr (.inl ⟨a'', hle, hs⟩)⟩
    · obtain ⟨w, h1, h2⟩ := conv_iff_join.mp (hc.trans c3)
      obtain ⟨r', a', e, hr, ha'⟩ := hnf2_wsteps (.app (.app .S ht') hpa) h2
      rw [e] at h1
      obtain ⟨T, hs, hi⟩ := wsteps_split h1
      obtain ⟨g, a'', e', hg, ha''⟩ := parIs_app hi
      obtain ⟨f, r'', e'', hf, hr''⟩ := parIs_app hg
      rw [e', e'', parIs_S hf] at hs
      have hp := steps_pure ht hs
      have hle : sz a'' ≤ M := Nat.le_trans
        (sz_wsteps hp.app_inv.2 (ha''.trans (wsteps_to_normal ha' han nf))) hsz
      exact ⟨r'', ⟨hp.app_inv.1.app_inv.2, t', hP', conv_iff_join.mpr ⟨r', hr'', hr⟩⟩,
        .inr (.inr ⟨a'', hle, hs⟩)⟩
  intro t hP
  exact mixed_combs hQ t ⟨(hC t hP).1, t, hP, .refl t⟩

/-- **Mixed comb contexts** (one hole): built from the hole by `E ↦ S E`, `E ↦ S n E` and
`E ↦ S E n` with `n` a closed S-term that has a normal form. -/
inductive GComb : Phi.Ctx → Prop
  | hole : GComb .hole
  | s1 {E : Phi.Ctx} : GComb E → GComb (.app .s E)
  | s2 {a : Term} {E : Phi.Ctx} : PureS a → Normalizing a → GComb E →
      GComb (.app (.app .s (Tower.ofTerm a)) E)
  | s3 {a : Term} {E : Phi.Ctx} : PureS a → Normalizing a → GComb E →
      GComb (.app (.app .s E) (Tower.ofTerm a))

/-- A mixed comb context whose teeth have normal forms of leaf count at most `M`. -/
inductive GCombB (M : Nat) : Phi.Ctx → Prop
  | hole : GCombB M .hole
  | s1 {E : Phi.Ctx} : GCombB M E → GCombB M (.app .s E)
  | s2 {a n : Term} {E : Phi.Ctx} : PureS a → WSteps a n → Normal n → sz n ≤ M → GCombB M E →
      GCombB M (.app (.app .s (Tower.ofTerm a)) E)
  | s3 {a n : Term} {E : Phi.Ctx} : PureS a → WSteps a n → Normal n → sz n ≤ M → GCombB M E →
      GCombB M (.app (.app .s E) (Tower.ofTerm a))

theorem GCombB.mono {M M' : Nat} (h : M ≤ M') {E : Phi.Ctx} (hE : GCombB M E) : GCombB M' E := by
  induction hE with
  | hole => exact .hole
  | s1 _ ih => exact .s1 ih
  | s2 hpa han nf hsz _ ih => exact .s2 hpa han nf (Nat.le_trans hsz h) ih
  | s3 hpa han nf hsz _ ih => exact .s3 hpa han nf (Nat.le_trans hsz h) ih

theorem GComb.bound {E : Phi.Ctx} (hE : GComb E) : ∃ M, GCombB M E := by
  induction hE with
  | hole => exact ⟨0, .hole⟩
  | s1 _ ih =>
    obtain ⟨M, h⟩ := ih
    exact ⟨M, .s1 h⟩
  | s2 hpa hn _ ih =>
    obtain ⟨M, h⟩ := ih
    obtain ⟨n, han, nf⟩ := hn
    exact ⟨M + sz n, .s2 hpa han nf (Nat.le_add_left _ _) (h.mono (Nat.le_add_right _ _))⟩
  | s3 hpa hn _ ih =>
    obtain ⟨M, h⟩ := ih
    obtain ⟨n, han, nf⟩ := hn
    exact ⟨M + sz n, .s3 hpa han nf (Nat.le_add_left _ _) (h.mono (Nat.le_add_right _ _))⟩

/-- Every comb context is a mixed comb context. -/
theorem Comb.gcomb {E : Phi.Ctx} (hE : Comb E) : GComb E := by
  induction hE with
  | hole => exact .hole
  | s1 _ ih => exact .s1 ih
  | s2 hpa hn _ ih => exact .s2 hpa hn ih

/-- **Corollary G1** (NCFP for mixed comb contexts).  Let `E ≠ hole` be built from the hole by
`E ↦ S E`, `E ↦ S n E` and `E ↦ S E n` with every `n` closed and normalizing (so `E` has one
hole).  Then no closed S-term `p` is convertible to `E[p]`.  In particular `p ≠β S p n`
(Corollary F1) and `p ≠β S n (S p m)` for normalizing `n`, `m`. -/
theorem ncfp_gcomb {p : Term} (hp : PureS p) {E : Phi.Ctx} (hE : GComb E) (hne : E ≠ .hole) :
    ¬ Convertible p (E.plug p) := by
  intro hc
  obtain ⟨M, hM⟩ := hE.bound
  have key : ∀ E' : Phi.Ctx, GCombB M E' → E' ≠ .hole → ∀ t, Convertible t (E'.plug p) →
      ∃ t', (∃ E'', GCombB M E'' ∧ t' = E''.plug p) ∧ NextGC M t t' := by
    intro E' hE' hne' t ht
    cases hE' with
    | hole => exact absurd rfl hne'
    | @s1 E'' h => exact ⟨E''.plug p, ⟨E'', h, rfl⟩, .inl ht⟩
    | @s2 a n E'' hpa han nf hsz h =>
      have e : (Phi.Ctx.app (.app .s (Tower.ofTerm a)) E'').plug p = S ⬝ a ⬝ E''.plug p := by
        show S ⬝ (Tower.ofTerm a).plug p ⬝ E''.plug p = _
        rw [Tower.plug_ofTerm hpa]
      rw [e] at ht
      exact ⟨E''.plug p, ⟨E'', h, rfl⟩, .inr ⟨a, n, hpa, han, nf, hsz, .inl ht⟩⟩
    | @s3 a n E'' hpa han nf hsz h =>
      have e : (Phi.Ctx.app (.app .s E'') (Tower.ofTerm a)).plug p = S ⬝ E''.plug p ⬝ a := by
        show S ⬝ E''.plug p ⬝ (Tower.ofTerm a).plug p = _
        rw [Tower.plug_ofTerm hpa]
      rw [e] at ht
      exact ⟨E''.plug p, ⟨E'', h, rfl⟩, .inr ⟨a, n, hpa, han, nf, hsz, .inr ht⟩⟩
  have hC : ∀ t, (∃ E', GCombB M E' ∧ t = E'.plug p) →
      PureS t ∧ ∃ t', (∃ E'', GCombB M E'' ∧ t' = E''.plug p) ∧ NextGC M t t' := by
    rintro t ⟨E', hE', e⟩
    rw [e]
    refine ⟨Tower.plug_pure E' hp, ?_⟩
    cases hE' with
    | hole => exact key E hM hne p hc
    | @s1 E'' h => exact key _ (.s1 h) (fun e => by cases e) _ (.refl _)
    | @s2 a n E'' hpa han nf hsz h =>
      exact key _ (.s2 hpa han nf hsz h) (fun e => by cases e) _ (.refl _)
    | @s3 a n E'' hpa han nf hsz h =>
      exact key _ (.s3 hpa han nf hsz h) (fun e => by cases e) _ (.refl _)
  exact mixed_combs_conv hC p ⟨.hole, .hole, rfl⟩

/-! ## No fixed-point combinator -/

theorem ncfp_S_aux : ∀ (n : Nat) (p : Term), sz p ≤ n → PureS p → ¬ Convertible p (S ⬝ p) := by
  intro n
  induction n with
  | zero =>
    intro p h
    have := sz_pos p
    exfalso
    omega
  | succ n ih =>
    intro p hsz hp hc
    obtain ⟨w, h1, h2⟩ := conv_iff_join.mp hc
    obtain ⟨a', e, ha⟩ := hnf1_wsteps (.app .S hp) h2
    rw [e] at h1
    obtain ⟨T, hs, hi⟩ := wsteps_split h1
    obtain ⟨f, d, e', hf, hd⟩ := parIs_app hi
    rw [e', parIs_S hf] at hs
    have e'' := hnf1_literal hp hs
    rw [e''] at hsz hp ha
    have h3 : sz (S ⬝ d) = 1 + sz d := rfl
    exact ih d (by omega) hp.app_inv.2 (conv_iff_join.mpr ⟨a', hd, ha⟩)

/-- **No `p =β S p`**, the short proof: no closed S-term `p` is convertible to `S p`.

By Church–Rosser and standardization the head run of `p` ends in a one-item head normal form
`S d` with `d =β S d`; a one-item head normal form is literal (`hnf1_literal`), so `p = S d`,
and `d` is smaller.  This proof does not use `HeadRec.no_ground_loop`. -/
theorem ncfp_S {p : Term} (hp : PureS p) : ¬ Convertible p (S ⬝ p) :=
  ncfp_S_aux (sz p) p (Nat.le_refl _) hp

/-- The same statement as the instance `E = S [ ]` of `ncfp_comb` (a second proof, through
Theorem 2). -/
theorem ncfp_S_comb {p : Term} (hp : PureS p) :
    ¬ Convertible p ((Phi.Ctx.app .s .hole).plug p) :=
  ncfp_comb hp (.s1 .hole) (fun e => by cases e)

/-- **No fixed-point combinator in pure S**, at the argument `S`: no closed S-term `Y` has
`Y S =β S (Y S)`.  This is `ncfp_S` at `p = Y S`. -/
theorem no_fixed_point_combinator {Y : Term} (hY : PureS Y) :
    ¬ Convertible (Y ⬝ S) (S ⬝ (Y ⬝ S)) :=
  ncfp_S (.app hY .S)

/-- **No fixed-point combinator in pure S**: no closed S-term `Y` has `Y f =β f (Y f)` for every
closed S-term `f`.  (Known: Statman; see *Dance of the Starlings*, Remark 15.) -/
theorem no_fpc : ¬ ∃ Y, PureS Y ∧ ∀ f, PureS f → Convertible (Y ⬝ f) (f ⬝ (Y ⬝ f)) :=
  fun ⟨_, hY, h⟩ => no_fixed_point_combinator hY (h S .S)

/-! ## Theorem B: the teeth of an hnf-less term are unbounded

Source: `notes/NCFP-proof.md`, §2–3.  A closed S-term is hnf-less iff its block is `36`
(`Conv.stable_iff`).  The *tooth* and the *rest* of an hnf-less `t` are the two parts of its first
stable frame, `Conv.FirstStable t f w`: `rest t = f`, `τ₁ t = w`. -/

/-- Head reduction is antisymmetric on closed S-terms (`HeadRec.no_head_cycle`). -/
theorem steps_antisymm {a b : Term} (ha : PureS a) (h : Steps a b) (h' : Steps b a) : a = b := by
  cases h with
  | refl => rfl
  | step s r => exact (no_head_cycle ha s (r.trans h')).elim

/-- An hnf-less closed S-term is an application. -/
theorem bot_app {t : Term} (ht : PureS t) (hb : fold t = 36) : ∃ f u, t = f ⬝ u := by
  cases ht with
  | S => exact absurd hb (fold_hnf .S (.inl rfl))
  | @app f u _ _ => exact ⟨f, u, rfl⟩

/-- Every hnf-less closed S-term has a first stable frame (F2, `Conv.reach_frame`). -/
theorem firstStable_exists {t : Term} (ht : PureS t) (hb : fold t = 36) :
    ∃ f w, FirstStable t f w := by
  obtain ⟨T, hs, hT⟩ := reach_frame ht
  rcases hT with hh | ⟨f, w, e, hf⟩
  · exact absurd ((InfNF.steps_fold ht hs).trans hb) (fold_hnf (steps_pure ht hs) hh)
  · rw [e] at hs
    obtain ⟨f₀, h, _⟩ := first_stable ht hs hf
    exact ⟨f₀, w, h⟩

/-- **Lemma T.**  If `t` and `t'` are convertible closed S-terms with stable stages `f w` and
`f' w'` on their head runs (`f`, `f'` hnf-less; in particular their first stable frames), then
`w =β w'` and `f =β f'`: convertible hnf-less terms have convertible teeth and rests. -/
theorem lemma_T {t t' f w f' w' : Term} (ht : PureS t) (ht' : PureS t')
    (hc : Convertible t t') (hs : Steps t (f ⬝ w)) (hb : fold f = 36)
    (hs' : Steps t' (f' ⬝ w')) (hb' : fold f' = 36) :
    Convertible w w' ∧ Convertible f f' := by
  have hp := steps_pure ht hs
  have hc' : Convertible (f ⬝ w) t' := (Convertible.of_wsteps hs.weak).symm.trans hc
  obtain ⟨c, h1, h2⟩ := conv_iff_join.mp hc'
  obtain ⟨fs, ws, e, hf, hw, _⟩ := InfNF.stable_wsteps hp (.inl hb) h1
  rw [e] at h2
  obtain ⟨T, h3, hi⟩ := wsteps_split h2
  obtain ⟨f₂, w₂, e₂, hf₂, hw₂⟩ := parIs_app hi
  rw [e₂] at h3
  have hp₂ := steps_pure ht' h3
  have hb₂ : fold f₂ = 36 :=
    ((fold_wsteps hf₂.wsteps hp₂.app_inv.1).2.symm.trans (fold_wsteps hf hp.app_inv.1).2).trans hb
  obtain ⟨ew, hff⟩ := run_bot_bot ht' hs' hb' h3 hb₂
  rw [← ew] at hw₂
  refine ⟨conv_iff_join.mpr ⟨ws, hw, hw₂⟩, ?_⟩
  have c1 : Convertible f f₂ := conv_iff_join.mpr ⟨fs, hf, hf₂.wsteps⟩
  rcases hff with h | h
  · exact c1.trans (Convertible.of_wsteps h.weak).symm
  · exact c1.trans (Convertible.of_wsteps h.weak)

/-- **Lemma A.**  If `p` is hnf-less, `p x` is its own first stable frame: tooth `x`, rest `p`. -/
theorem lemma_A {p : Term} (hb : fold p = 36) (x : Term) : FirstStable (p ⬝ x) p x :=
  ⟨.refl _, hb, fun _ _ h _ => h⟩

/-- Head steps, counted. -/
inductive StepsK : Nat → Term → Term → Prop
  | refl (t : Term) : StepsK 0 t t
  | step {k : Nat} {t t' u : Term} : Step t t' → StepsK k t' u → StepsK (k + 1) t u

theorem stepsK_of_steps {t u : Term} (h : Steps t u) : ∃ k, StepsK k t u := by
  induction h with
  | refl t => exact ⟨0, .refl t⟩
  | step s _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .step s hk⟩

/-- A later stage of a counted head run is nearer to its end. -/
theorem stepsK_later : ∀ (k : Nat) {T T' G : Term}, PureS T → StepsK k T G → Steps T T' →
    Steps T' G → ∃ k', k' ≤ k ∧ StepsK k' T' G := by
  intro k T T' G hp hk h
  induction h generalizing k with
  | refl => intro _; exact ⟨k, Nat.le_refl _, hk⟩
  | @step T T₁ T' s r ih =>
    intro hG
    cases hk with
    | refl => exact (no_head_cycle hp s (r.trans hG)).elim
    | @step k _ T₂ _ s' hk' =>
      rw [Step.det s' s] at hk'
      obtain ⟨k', hle, h'⟩ := ih k (wstep_pure s.weak hp).1 hk' hG
      exact ⟨k', Nat.le_succ_of_le hle, h'⟩

theorem steps_step_plus {a b c : Term} (h : Steps a b) (s : Step b c) : Plus a c := by
  cases h with
  | refl => exact ⟨c, s, .refl _⟩
  | step s' r => exact ⟨_, s', r.trans (.single s)⟩

/-- A stage one or more steps later on a counted head run is strictly nearer to its end. -/
theorem stepsK_plus {k : Nat} {T T' G : Term} (hp : PureS T) (hk : StepsK k T G)
    (h : Plus T T') (hG : Steps T' G) : ∃ k', k' < k ∧ StepsK k' T' G := by
  obtain ⟨T₁, s, r⟩ := h
  cases hk with
  | refl => exact (no_head_cycle hp s (r.trans hG)).elim
  | @step k₀ _ T₂ _ s' hk' =>
    rw [Step.det s' s] at hk'
    obtain ⟨k', hle, h'⟩ := stepsK_later k₀ (wstep_pure s.weak hp).1 hk' r hG
    exact ⟨k', Nat.lt_succ_of_le hle, h'⟩

/-- On a head run that reaches a stable frame `g w`, a root frame `S a b x` is before it: the
run goes on through `a x (b x)` to `g w`. -/
theorem past_root {T g w a b x : Term} (hT : PureS T) (hs : Steps T (g ⬝ w)) (hg : fold g = 36)
    (hX : Steps T (S ⬝ a ⬝ b ⬝ x)) : Steps (a ⬝ x ⬝ (b ⬝ x)) (g ⬝ w) := by
  have hpg := (steps_pure hT hs).app_inv.1
  have hpX := steps_pure hT hX
  have hne : fold (S ⬝ a ⬝ b) ≠ 36 := fold_hnf hpX.app_inv.1 (.inr (.inr ⟨a, b, rfl⟩))
  rcases InfNF.steps_cmp hs hX with h | h
  · obtain ⟨g', e, _, _, hg'⟩ := InfNF.steps_bot_fun hpg hg h
    injection e with e1 _
    rw [← e1] at hg'
    exact absurd hg' hne
  · cases h with
    | refl => exact absurd hg hne
    | step s r =>
      rw [Step.det s (.S a b x)] at r
      exact r

/-- **B-move.**  State `a v w'` on the head run to the first stable frame `g w`, with `v` smaller
than `w'` and `a` smaller than `A` or than `w'`.  Then `g = a' v'` with `v'` smaller than the
tooth `w`, and `a'` smaller than `A` or than `w`.  (Rounds of the note's B-move: while `a v` has
a head normal form `S a' b'`, the frame `S a' b' w'` steps to `a' w' (b' w')`; a literal entry
has `a = S a'`, a non-literal one has `b' = y a'` by Lemma L.) -/
theorem bmove {A : Nat} : ∀ (n k : Nat) (a v w' g w : Term), k ≤ n → PureS (a ⬝ v ⬝ w') →
    StepsK k (a ⬝ v ⬝ w') (g ⬝ w) → fold g = 36 →
    (∀ g' x, Steps (a ⬝ v ⬝ w') (g' ⬝ x) → fold g' = 36 → Steps (g ⬝ w) (g' ⬝ x)) →
    (sz a < A ∨ sz a < sz w') → sz v < sz w' →
    ∃ a' v', g = a' ⬝ v' ∧ (sz a' < A ∨ sz a' < sz w) ∧ sz v' < sz w := by
  have stepsOf : ∀ {k : Nat} {t u : Term}, StepsK k t u → Steps t u := by
    intro k t u h
    induction h with
    | refl t => exact .refl t
    | step s _ ih => exact .step s ih
  intro n
  induction n with
  | zero =>
    intro k a v w' g w hk hp hrun hg hmin hQ hv
    have hk0 : k = 0 := Nat.le_zero.mp hk
    rw [hk0] at hrun
    cases hrun with
    | refl => exact ⟨a, v, rfl, hQ, hv⟩
  | succ n ih =>
    intro k a v w' g w hk hp hrun hg hmin hQ hv
    have hs := stepsOf hrun
    rcases Nat.decEq (fold (a ⬝ v)) 36 with hne | heq
    · have hpav := hp.app_inv.1
      obtain ⟨H, hH, hT⟩ := reach_frame hpav
      have hpH := steps_pure hpav hH
      have hfH : fold H ≠ 36 := fun e => hne ((InfNF.steps_fold hpav hH).symm.trans e)
      have hfT : fold (a ⬝ v ⬝ w') = 36 :=
        (InfNF.steps_fold hp hs).symm.trans (Full.fold_frame (steps_pure hp hs).app_inv.2 hg)
      have hX : Steps (a ⬝ v ⬝ w') (H ⬝ w') := Steps.left w' hH
      have hfX : fold (H ⬝ w') = 36 := (InfNF.steps_fold hp hX).trans hfT
      have hpX := steps_pure hp hX
      rcases hT with (e | ⟨x, e⟩ | ⟨a', b', e⟩) | ⟨f, x, e, hf⟩
      · rw [e] at hfX hpX
        exact absurd hfX (fold_hnf hpX (.inr (.inl ⟨w', rfl⟩)))
      · rw [e] at hfX hpX
        exact absurd hfX (fold_hnf hpX (.inr (.inr ⟨x, w', rfl⟩)))
      · rw [e] at hX hH hpH
        have hrest := past_root hp hs hg hX
        have hT' : Steps (a ⬝ v ⬝ w') (a' ⬝ w' ⬝ (b' ⬝ w')) :=
          hX.trans (.single (.S a' b' w'))
        have hp' := steps_pure hp hT'
        obtain ⟨k', hlt, hk'⟩ := stepsK_plus hp hrun (steps_step_plus hX (.S a' b' w')) hrest
        have hQ' : sz a' < A ∨ sz a' < sz (b' ⬝ w') := by
          rcases Decidable.em (a ⬝ v = S ⬝ a' ⬝ b') with el | nl
          · injection el with e1 _
            have hlt : sz a' < sz a := by rw [e1]; exact sz_arg_lt _ _
            have := sz_arg_lt b' w'
            rcases hQ with h | h
            · exact .inl (Nat.lt_trans hlt h)
            · exact .inr (by omega)
          · obtain ⟨y, _, ey⟩ := lemma_L' hpav hH nl
            have h1 := sz_arg_lt y a'
            rw [← ey] at h1
            have h2 := sz_fun_lt b' w'
            exact .inr (by omega)
        exact ih k' a' w' (b' ⬝ w') g w (by omega) hp' hk' hg
          (fun g' x h hb => hmin g' x (hT'.trans h) hb) hQ' (sz_arg_lt b' w')
      · rw [e] at hH
        exact absurd ((InfNF.steps_fold hpav hH).symm.trans
          (Full.fold_frame (steps_pure hpav hH).app_inv.2 hf)) hne
    · have e := steps_antisymm hp hs (hmin (a ⬝ v) w' (.refl _) heq)
      injection e with e1 e2
      rw [← e2]
      exact ⟨a, v, e1.symm, hQ, hv⟩

/-- `HDesc t t'`: `t` head-reduces in one or more steps to `t' X₁ … X_k`, `k ≥ 0`. -/
def HDesc (t t' : Term) : Prop := ∃ L : List Term, Plus t (apps t' L)

theorem step_apps {f f' : Term} (L : List Term) (h : Step f f') :
    Step (apps f L) (apps f' L) := by
  induction L generalizing f f' with
  | nil => exact h
  | cons a L ih => exact ih (Step.left a h)

theorem plus_apps {f f' : Term} (L : List Term) (h : Plus f f') :
    Plus (apps f L) (apps f' L) := by
  obtain ⟨f₁, s, r⟩ := h
  exact ⟨apps f₁ L, step_apps L s, steps_apps L r⟩

theorem apps_append (c : Term) (L' L : List Term) : apps (apps c L') L = apps c (L' ++ L) := by
  induction L' generalizing c with
  | nil => rfl
  | cons a L' ih => exact ih (c ⬝ a)

/-- A head run to `b X⃗` followed by one of `b` with one or more steps. -/
theorem hdesc_of_steps {a b c : Term} {L : List Term} (h : Steps a (apps b L)) (h' : HDesc b c) :
    HDesc a c := by
  obtain ⟨L', hp⟩ := h'
  obtain ⟨t₁, s, r⟩ := plus_apps L hp
  rw [apps_append] at r
  cases h with
  | refl => exact ⟨L' ++ L, t₁, s, r⟩
  | step s' r' => exact ⟨L' ++ L, _, s', r'.trans (.step s r)⟩

theorem HDesc.trans {a b c : Term} (h : HDesc a b) (h' : HDesc b c) : HDesc a c := by
  obtain ⟨L, hp⟩ := h
  exact hdesc_of_steps hp.steps h'

/-- No closed S-term is its own head descendant (`HeadRec.no_head_recurrence`). -/
theorem HDesc.irrefl {t : Term} (ht : PureS t) : ¬ HDesc t t :=
  fun ⟨L, h⟩ => no_head_recurrence ht L h

/-- `P` is a set of hnf-less closed S-terms, closed under `rest`, all of whose first teeth have
leaf count at most `M`. -/
def Toothed (M : Nat) (P : Term → Prop) : Prop :=
  ∀ t, P t → PureS t ∧ fold t = 36 ∧ ∃ f w, FirstStable t f w ∧ sz w ≤ M ∧ P f

/-- One move of the proof of Theorem B, iterated: from every state `fm u` a state of leaf count
at most `2 M` is reached by one or more head steps.  Induction on `sz fm` (the note's `α`). -/
theorem tooth_descent {M : Nat} {P : Term → Prop} (hC : Toothed M P) :
    ∀ (n : Nat) (fm u : Term), sz fm ≤ n → P (fm ⬝ u) →
      ∃ t₃, P t₃ ∧ HDesc (fm ⬝ u) t₃ ∧ sz t₃ ≤ 2 * M := by
  intro n
  induction n with
  | zero =>
    intro fm u h
    have := sz_pos fm
    exfalso
    omega
  | succ n ih =>
    intro fm u hsz hP
    obtain ⟨hp, hb, g, w, ⟨hs, hg, hmin⟩, hw, hPg⟩ := hC _ hP
    have hpfm := hp.app_inv.1
    rcases Nat.decEq (fold fm) 36 with hne | heq
    · obtain ⟨H, hH, hT⟩ := reach_frame hpfm
      have hX : Steps (fm ⬝ u) (H ⬝ u) := Steps.left u hH
      have hfX : fold (H ⬝ u) = 36 := (InfNF.steps_fold hp hX).trans hb
      have hpX := steps_pure hp hX
      rcases hT with (e | ⟨x, e⟩ | ⟨a₀, b₀, e⟩) | ⟨f, x, e, hf⟩
      · rw [e] at hfX hpX
        exact absurd hfX (fold_hnf hpX (.inr (.inl ⟨u, rfl⟩)))
      · rw [e] at hfX hpX
        exact absurd hfX (fold_hnf hpX (.inr (.inr ⟨x, u, rfl⟩)))
      · rw [e] at hX hH
        have hrest := past_root hp hs hg hX
        have hplus : Plus (fm ⬝ u) (a₀ ⬝ u ⬝ (b₀ ⬝ u)) := steps_step_plus hX (.S a₀ b₀ u)
        have hT' := hplus.steps
        have hp' := steps_pure hp hT'
        obtain ⟨k, hk⟩ := stepsK_of_steps hrest
        have hQ : sz a₀ < sz fm ∨ sz a₀ < sz (b₀ ⬝ u) := by
          rcases Decidable.em (fm = S ⬝ a₀ ⬝ b₀) with el | nl
          · refine .inl ?_
            rw [el]
            exact Nat.lt_trans (sz_arg_lt S a₀) (sz_fun_lt _ b₀)
          · obtain ⟨y, _, ey⟩ := lemma_L' hpfm hH nl
            have h1 := sz_arg_lt y a₀
            rw [← ey] at h1
            have h2 := sz_fun_lt b₀ u
            exact .inr (by omega)
        obtain ⟨a', v', eg, hQ', hv'⟩ := bmove k k a₀ u (b₀ ⬝ u) g w (Nat.le_refl _) hp' hk hg
          (fun g' x h hb' => hmin g' x (hT'.trans h) hb') hQ (sz_arg_lt b₀ u)
        have hfg : HDesc (fm ⬝ u) g := by
          obtain ⟨t₁, s, r⟩ := hplus
          exact ⟨[w], t₁, s, r.trans hrest⟩
        rcases hQ' with hlt | hlt
        · rw [eg] at hPg hfg
          obtain ⟨t₃, h1, h2, h3⟩ := ih a' v' (by omega) hPg
          exact ⟨t₃, h1, hfg.trans h2, h3⟩
        · refine ⟨g, hPg, hfg, ?_⟩
          rw [eg]
          have e1 : sz (a' ⬝ v') = sz a' + sz v' := rfl
          omega
      · rw [e] at hH
        exact absurd ((InfNF.steps_fold hpfm hH).symm.trans
          (Full.fold_frame (steps_pure hpfm hH).app_inv.2 hf)) hne
    · have e := steps_antisymm hp hs (hmin fm u (.refl _) heq)
      injection e with e1 _
      rw [← e1] at hPg
      obtain ⟨f', u', e'⟩ := bot_app hpfm heq
      rw [e'] at hPg hsz ⊢
      have e2 : sz (f' ⬝ u') = sz f' + sz u' := rfl
      have := sz_pos u'
      obtain ⟨t₃, h1, h2, h3⟩ := ih f' u' (by omega) hPg
      exact ⟨t₃, h1, hdesc_of_steps (L := [u]) (.refl _) h2, h3⟩

/-- **Theorem B** (the teeth of an hnf-less term are unbounded), choice-free form.  Let `P` be a
set of hnf-less closed S-terms such that every `t` in `P` has a first stable frame `f w` with `f`
in `P` and `sz w ≤ M`.  Then `P` is empty.  So for no hnf-less closed `p` and no `M` do all teeth
`τₙ(p)` have leaf count at most `M`.

Uses F2 (`Conv.reach_frame`, the head run reaches a head normal form or a stable frame), Lemma L
and `HeadRec.no_head_recurrence`. -/
theorem teeth_unbounded {M : Nat} {P : Term → Prop} (hC : Toothed M P) : ∀ t, ¬ P t := by
  refine finite_descent (B := 2 * M) (D := HDesc) (fun t hP => (hC t hP).1) HDesc.trans
    (fun t hP => HDesc.irrefl (hC t hP).1) ?_
  intro t hP
  obtain ⟨ht, hb, _⟩ := hC t hP
  obtain ⟨fm, u, e⟩ := bot_app ht hb
  rw [e] at hP ⊢
  exact tooth_descent hC (sz fm) fm u (Nat.le_refl _) hP

/-- **Theorem B**, for the sequence of rests: there is no sequence `f₀, f₁, …` of closed S-terms
in which `fₙ₊₁ wₙ` is the first stable frame of `fₙ` and `sz wₙ ≤ M` for all
`n`. -/
theorem teeth_unbounded_seq {M : Nat} (f w : Nat → Term) (h0 : PureS (f 0))
    (H : ∀ n, FirstStable (f n) (f (n + 1)) (w n) ∧ sz (w n) ≤ M) : False := by
  have pure : ∀ n, PureS (f n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact (steps_pure ih (H n).1.1).app_inv.1
  have hC : Toothed M (fun t => ∃ n, t = f (n + 1)) := by
    rintro t ⟨n, e⟩
    rw [e]
    exact ⟨pure (n + 1), (H n).1.2.1, f (n + 2), w (n + 1), (H (n + 1)).1, (H (n + 1)).2,
      ⟨n + 1, rfl⟩⟩
  exact teeth_unbounded hC (f 1) ⟨0, rfl⟩

theorem fold_apps {p : Term} (hb : fold p = 36) :
    ∀ L : List Term, (∀ x ∈ L, PureS x) → fold (apps p L) = 36 := by
  intro L
  induction L generalizing p with
  | nil => intro _; exact hb
  | cons a L ih =>
    intro h
    exact ih (Full.fold_frame (h a (List.Mem.head _)) hb) (fun x hx => h x (List.Mem.tail _ hx))

theorem pure_apps_of {p : Term} (hp : PureS p) :
    ∀ L : List Term, (∀ x ∈ L, PureS x) → PureS (apps p L) := by
  intro L
  induction L generalizing p with
  | nil => intro _; exact hp
  | cons a L ih =>
    intro h
    exact ih (.app hp (h a (List.Mem.head _))) (fun x hx => h x (List.Mem.tail _ hx))

theorem snoc_cases : ∀ L : List Term, L = [] ∨ ∃ L₀ x, L = L₀ ++ [x] := by
  intro L
  induction L with
  | nil => exact .inl rfl
  | cons a L ih =>
    rcases ih with e | ⟨L₀, x, e⟩
    · rw [e]; exact .inr ⟨[], a, rfl⟩
    · rw [e]; exact .inr ⟨a :: L₀, x, rfl⟩

theorem norm_bound : ∀ L : List Term, (∀ x ∈ L, Normalizing x) →
    ∃ B, ∀ x ∈ L, ∃ n, WSteps x n ∧ Normal n ∧ sz n ≤ B := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, fun x hx => nomatch hx⟩
  | cons a L ih =>
    intro h
    obtain ⟨B, hB⟩ := ih (fun x hx => h x (List.Mem.tail _ hx))
    obtain ⟨n, han, nf⟩ := h a (List.Mem.head _)
    refine ⟨B + sz n, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with e | hx'
    · rw [e]; exact ⟨n, han, nf, Nat.le_add_left _ _⟩
    · obtain ⟨m, h1, h2, h3⟩ := hB x hx'
      exact ⟨m, h1, h2, Nat.le_trans h3 (Nat.le_add_right _ _)⟩

/-- The block is a conversion invariant of closed S-terms. -/
theorem fold_conv {t t' : Term} (ht : PureS t) (ht' : PureS t') (h : Convertible t t') :
    fold t = fold t' := by
  obtain ⟨c, h1, h2⟩ := conv_iff_join.mp h
  exact (fold_wsteps h1 ht).2.symm.trans (fold_wsteps h2 ht').2

/-- **Corollary B1** (left combs, hnf-less `p`).  If the closed S-term `p` is hnf-less
(`fold p = 36`) and `x₁, …, x_k`, `k ≥ 1`, are closed and normalizing, then `p` is not
convertible to `p x₁ ⋯ x_k`.  Nothing is claimed when some `xᵢ` has no normal form, or when `p`
has a head normal form. -/
theorem cor_B1 {p : Term} (hp : PureS p) (hb : fold p = 36) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x ∧ Normalizing x) : ¬ Convertible p (apps p L) := by
  intro hc
  obtain ⟨B, hB⟩ := norm_bound L (fun x h => (hx x h).2)
  have hC : Toothed B (fun t => PureS t ∧ fold t = 36 ∧
      ∃ L', (∀ x ∈ L', x ∈ L) ∧ Convertible t (apps p L')) := by
    rintro t ⟨ht, hbt, L', hL', hct⟩
    refine ⟨ht, hbt, ?_⟩
    have key : ∃ L₀ x, x ∈ L ∧ (∀ y ∈ L₀, y ∈ L) ∧ Convertible t (apps p L₀ ⬝ x) := by
      rcases snoc_cases L' with e | ⟨L₀, x, e⟩
      · rw [e] at hct
        rcases snoc_cases L with e' | ⟨L₁, x, e'⟩
        · exact absurd e' hL
        · refine ⟨L₁, x, ?_, ?_, ?_⟩
          · rw [e']; exact List.mem_append_right _ (List.Mem.head _)
          · intro y hy; rw [e']; exact List.mem_append_left _ hy
          · have hct0 : Convertible t p := hct
            have := hct0.trans hc
            rw [e', apps_snoc] at this
            exact this
      · refine ⟨L₀, x, ?_, ?_, ?_⟩
        · exact hL' x (by rw [e]; exact List.mem_append_right _ (List.Mem.head _))
        · intro y hy; exact hL' y (by rw [e]; exact List.mem_append_left _ hy)
        · rw [e, apps_snoc] at hct
          exact hct
    obtain ⟨L₀, x, hxL, hL₀, hct'⟩ := key
    have hpL₀ := pure_apps_of hp L₀ (fun y hy => (hx y (hL₀ y hy)).1)
    have hbL₀ := fold_apps hb L₀ (fun y hy => (hx y (hL₀ y hy)).1)
    have hpx := (hx x hxL).1
    obtain ⟨f, w, hF⟩ := firstStable_exists ht hbt
    obtain ⟨cw, cf⟩ := lemma_T ht (.app hpL₀ hpx) hct' hF.1 hF.2.1 (.refl _) hbL₀
    have hpfw := steps_pure ht hF.1
    refine ⟨f, w, hF, ?_, hpfw.app_inv.1, hF.2.1, L₀, hL₀, cf⟩
    obtain ⟨n, hxn, nf, hsz⟩ := hB x hxL
    obtain ⟨c, h1, h2⟩ := conv_iff_join.mp cw
    exact Nat.le_trans (sz_wsteps hpfw.app_inv.2 (h1.trans (wsteps_to_normal h2 hxn nf))) hsz
  exact teeth_unbounded hC p ⟨hp, hb, [], ⟨fun _ h => (by cases h), Convertible.refl _⟩⟩

/-- Corollary B1 with "hnf-less" stated as `¬ HasHnf p`. -/
theorem cor_B1' {p : Term} (hp : PureS p) (hn : ¬ HasHnf p) {L : List Term} (hL : L ≠ [])
    (hx : ∀ x ∈ L, PureS x ∧ Normalizing x) : ¬ Convertible p (apps p L) :=
  cor_B1 hp ((stable_iff hp).mpr hn) hL hx

end Ncfp
