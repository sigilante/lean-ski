import Ski.NcfpDepth2
open Term

/-!
# NCFP: Theorem X⁺ and Corollary X1

Source: `notes/NCFP-proof.md`, §16.1.  Setting and notation as in `Ski/Ncfp.lean`.

What is proved:

* `thm_Xplus` (Theorem X⁺): no nonempty set `Z` of closed S-terms in which every member has, on
  its head run, a head normal form with one or two items, each item in `Z` or of leaf count at
  most `M`, at least one item in `Z`, and every non-literal member has a first item `z` of leaf
  count at most `M` or a second item `S z` or `S c z` with `sz c ≤ M`.  `M ≥ 1` is not assumed.
  `thm_X_of_Xplus` is Theorem X (`thm_X`) as a special case.
* `cor_X1` (Corollary X1, sets), for a family indexed by any type, with the types given member by
  member, and with one more admissible kind of second entry (a set whose members have a small
  second item), which the note does not list.
* `ncfp_X1` (Corollary X1, contexts): `p` is not convertible to `E[p]` for the contexts `E ≠ hole`
  described by `X1Ctx (Simp E) E`: built from holes and closed normalizing terms by `S E′` and
  `S E′ E″`, with a hole, and such that every node `S E₁ E₂` with `E₁`, `E₂` both non-closed has
  `E₂` of the form `S E′` or `S n E′`, where a hole `E₂` is read as the root `E`.
* The equations for the nine two-hole contexts of depth 3 that the note lists under Corollary X1
  (`no_S_SpSnp`, `no_S_Sp_SnSp`, `no_S_n_SpSp`, `no_S_Snp_SSmp`, `no_S_SpSnp_m`, `no_S_Spn_SSpm`,
  `no_S_n_SpSmp`, `no_S_Snp_SmSkp`, `no_S_Spn_SmSpk`), with independent closed parts.

The proof of Theorem X⁺ follows the note with these changes of form.  The path is not chosen: the
statement proved is that every member has a descendant in `Z` of leaf count at most `M + 3`
(`xp_small`, under a double negation), and the pigeonhole `finite_descent_nn` replaces (Dist).  An
O-step and an E-step are one kind of step: the run passes through a three-item frame `S x p q`
with `p q ∈ Z`, `sz x ≤ M + 2`, `sz q ≤ M + 1` (`x = S` for an O-step; the note's sharper
`sz x ≤ 3` for an E-step is not needed).  Claim 2 is `right_combs` (Theorem 2) applied to the
function parts of the terms of a block with a fixed last item; Claim 1 is `fact_LI`; Claim 3 is
`xp_pred` with `lemma_P3`.

What is not proved here: Corollary X2 (it needs tameness, which is not mechanized); the count of
226 two-hole contexts of depth at most 3 (201 of them rest on a computation).

Constructivity: excluded middle is used only as `em_false` and under double negations.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Predecessors of a three-item frame -/

/-- A closed S-term other than `S` has at least two leaves. -/
theorem sz_ge_two {x : Term} (hx : PureS x) (hne : x ≠ S) : 2 ≤ sz x := by
  cases hx with
  | S => exact absurd rfl hne
  | @app f a _ _ =>
    have h1 := sz_pos f
    have h2 := sz_pos a
    show 2 ≤ sz f + sz a
    omega

/-- **Lemma P** for a three-item frame with any first item.  If a head step yields `S x p q`, the
frame before it is `S (S x) b p` with `q = b p`, or `S S b x q` with `p = b x`. -/
theorem lemma_P3 {F' x p q : Term} (hp : PureS F') (s : Step F' (S ⬝ x ⬝ p ⬝ q)) :
    (∃ b, F' = S ⬝ (S ⬝ x) ⬝ b ⬝ p ∧ q = b ⬝ p) ∨ (∃ b, F' = S ⬝ S ⬝ b ⬝ x ⬝ q ∧ p = b ⬝ x) := by
  obtain ⟨u, l, e⟩ := step_app s
  rw [e] at hp s
  rcases step_inv hp.app_inv.1 s with ⟨u', s', e'⟩ | ⟨f, g, e1, e2⟩
  · injection e' with e3 e4
    rw [← e3] at s'
    obtain ⟨y', e5, e6⟩ := step_to_S2 hp.app_inv.1 s'
    exact .inr ⟨y', by rw [e, e5, ← e4], e6⟩
  · injection e2 with e3 e4
    injection e3 with e5 e6
    exact .inl ⟨g, by rw [e, e1, ← e5, ← e6], by rw [e4, ← e6]⟩

/-- A frame `S x p q` with `q` not of the form `b p` and `p` not of the form `b x` has no
predecessor: a head run that ends in it has no step. -/
theorem no_pred3 {t x p q : Term} (ht : PureS t) (h : Steps t (S ⬝ x ⬝ p ⬝ q))
    (h1 : ∀ b, q ≠ b ⬝ p) (h2 : ∀ b, p ≠ b ⬝ x) : t = S ⬝ x ⬝ p ⬝ q := by
  rcases steps_last h with e | ⟨t', h3, s⟩
  · exact e
  · rcases lemma_P3 (steps_pure ht h3) s with ⟨b, _, e⟩ | ⟨b, _, e⟩
    · exact absurd e (h1 b)
    · exact absurd e (h2 b)

/-! ## Theorem X⁺ -/

/-- The hypothesis of Theorem X⁺ on a set `Z` of closed S-terms: every member has, on its head
run, a head normal form `S c` with `c ∈ Z`, or `S c d` where each of `c`, `d` is in `Z` or has
leaf count at most `M`, at least one of them is in `Z`, and, if the run takes a step, `sz c ≤ M`
or `d = S c` or `d = S c' c` with `sz c' ≤ M`. -/
def XplusSet (M : Nat) (Z : Term → Prop) : Prop :=
  ∀ t, Z t → PureS t ∧ ((∃ c, Steps t (S ⬝ c) ∧ Z c) ∨
    ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (Z c ∨ sz c ≤ M) ∧ (Z d ∨ sz d ≤ M) ∧ (Z c ∨ Z d) ∧
      (t ≠ S ⬝ c ⬝ d → sz c ≤ M ∨ d = S ⬝ c ∨ ∃ c', sz c' ≤ M ∧ d = S ⬝ c' ⬝ c))

/-- One step of the path of Theorem X⁺ from a member `t`: `t` is literal with an item in `Z`
(first two cases); or it has a descendant in `Z` of leaf count at most `M`; or its last item is in
`Z` (an exceptional member in case (A) of Lemma TD); or (a carrying step) its head run passes
through a three-item frame `S x p q` with `p q ∈ Z`, `sz x ≤ M + 2` and `sz q ≤ M + 1`. -/
theorem xp_cases {M : Nat} {Z : Term → Prop} (hZ : XplusSet M Z) {t : Term} (ht : Z t) :
    (∃ c, t = S ⬝ c ∧ Z c) ∨
    (∃ c d, t = S ⬝ c ⬝ d ∧ (Z c ∨ Z d)) ∨
    (∃ t₃, Z t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M) ∨
    (∃ tm z, t = tm ⬝ z ∧ Z z) ∨
    ∃ x p q, Steps t (S ⬝ x ⬝ p ⬝ q) ∧ Z (p ⬝ q) ∧ Desc t (p ⬝ q) ∧ sz x ≤ M + 2 ∧
      sz q ≤ M + 1 := by
  obtain ⟨hp, hk⟩ := hZ t ht
  have e1S : sz S = 1 := rfl
  rcases hk with ⟨c, hs, hc⟩ | ⟨c, d, hs, hc, _, hcd, hex⟩
  · exact .inl ⟨c, hnf1_literal hp hs, hc⟩
  · rcases Decidable.em (t = S ⬝ c ⬝ d) with e | ne
    · exact .inr (.inl ⟨c, d, e, hcd⟩)
    · have hplus := plus_of_steps_ne hs ne
      have hDc : Desc t c := ⟨_, hs.weak, .left d (.right S .refl)⟩
      rcases Nat.lt_or_ge M (sz c) with big | small
      · -- an exceptional member
        have hZc : Z c := by
          rcases hc with h | h
          · exact h
          · exact absurd h (Nat.not_le_of_gt big)
        obtain ⟨y, eb, _, hTD⟩ := lemma_TD hp hplus
        have hy : sz y ≤ M + 1 := by
          rcases hex ne with h | h | ⟨c', hc', h⟩
          · exact absurd h (Nat.not_le_of_gt big)
          · rw [eb] at h
            injection h with h1 _
            rw [h1]
            omega
          · rw [eb] at h
            injection h with h1 _
            rw [h1]
            show 1 + sz c' ≤ M + 1
            omega
        rcases hTD with ⟨tm, e, _⟩ | ⟨x, p, q, hfr, hx, ez, hxq⟩
        · exact .inr (.inr (.inr (.inl ⟨tm, c, e, hZc⟩)))
        · have hpfr := steps_pure hp hfr
          have hpx : PureS x := hpfr.app_inv.1.app_inv.1.app_inv.2
          have hpxq : PureS (x ⬝ q) := .app hpx hpfr.app_inv.2
          have hsz := lemma_SS_sz hpxq hxq
          have hsz' : sz (x ⬝ q) = sz x + sz q := rfl
          have hx2 := sz_ge_two hpx hx
          have hq1 := sz_pos q
          rw [ez] at hZc hDc
          exact .inr (.inr (.inr (.inr ⟨x, p, q, hfr, hZc, hDc, by omega, by omega⟩)))
      · -- an ordinary member
        rcases hcd with h | h
        · exact .inr (.inr (.inl ⟨c, h, hDc, small⟩))
        · obtain ⟨y, hs', eb⟩ := lemma_L hp hplus
          rw [eb] at h
          have hD : Desc t (y ⬝ c) :=
            ⟨S ⬝ c ⬝ (y ⬝ c), by rw [← eb]; exact hs.weak, .right _ .refl⟩
          exact .inr (.inr (.inr (.inr ⟨S, y, c, hs', h, hD, by omega, by omega⟩)))

/-- `t` has a descendant in `Z` of leaf count at most `M + 3`. -/
def XExit (M : Nat) (Z : Term → Prop) (t : Term) : Prop :=
  ∃ t₃, Z t₃ ∧ Desc t t₃ ∧ sz t₃ ≤ M + 3

/-- The end of a block: `t = H ℓ` where `H = c g` is an application whose argument `g` contains a
member `w` of `Z` of leaf count above `M + 3`. -/
def XEnd (M : Nat) (Z : Term → Prop) (t ℓ : Term) : Prop :=
  ∃ w c g, Z w ∧ M + 3 < sz w ∧ HeadRec.Sub w g ∧ t = c ⬝ g ⬝ ℓ

/-- Claim 3, one step back: if the head run of `t` reaches the frame `S x p q` of a carrying
step and `p q` is the end of a block, then `t` is that frame, and it is the end of a block. -/
theorem xp_pred {M : Nat} {Z : Term → Prop} {t x p q : Term} (ht : PureS t)
    (hs : Steps t (S ⬝ x ⬝ p ⬝ q)) (hx : sz x ≤ M + 2) (hq : sz q ≤ M + 1)
    (hE : XEnd M Z (p ⬝ q) q) : t = S ⬝ x ⬝ p ⬝ q ∧ XEnd M Z (S ⬝ x ⬝ p ⬝ q) q := by
  obtain ⟨w, c, g, hw, big, hsub, e⟩ := hE
  injection e with e1 _
  have hg := sub_sz_le hsub
  have hgp : sz g < sz p := by
    rw [e1]
    exact sz_arg_lt c g
  refine ⟨no_pred3 ht hs ?_ ?_, w, S ⬝ x, p, hw, big, ?_, rfl⟩
  · intro b eb
    have h1 := sz_arg_lt b p
    rw [← eb] at h1
    omega
  · intro b eb
    rw [e1] at eb
    injection eb with _ e2
    rw [e2] at hg
    omega
  · rw [e1]
    exact .right c hsub

/-- A block of carrying steps.  Let `f ℓ ∈ Z` with `sz ℓ ≤ M + 1`.  Then it is not the case that
`f ℓ` has no small descendant in `Z` and is not the end of a block.  Induction on `M + 1 - sz ℓ`
(the last item grows along carrying steps, Fact LI); for a fixed last item the function parts form
a right comb with teeth of leaf count at most `M + 2`, and Theorem 2 applies. -/
theorem xp_block {M : Nat} {Z : Term → Prop} (hZ : XplusSet M Z) :
    ∀ (d : Nat) (ℓ : Term), M + 1 - sz ℓ ≤ d → sz ℓ ≤ M + 1 → ∀ f, Z (f ⬝ ℓ) →
      ¬¬ (XExit M Z (f ⬝ ℓ) ∨ XEnd M Z (f ⬝ ℓ) ℓ) := by
  have fin : ∀ ℓ : Term, sz ℓ ≤ M + 1 →
      (∀ ℓ' : Term, sz ℓ < sz ℓ' → sz ℓ' ≤ M + 1 → ∀ f, Z (f ⬝ ℓ') →
        ¬¬ (XExit M Z (f ⬝ ℓ') ∨ XEnd M Z (f ⬝ ℓ') ℓ')) →
      ∀ f, Z (f ⬝ ℓ) → ¬¬ (XExit M Z (f ⬝ ℓ) ∨ XEnd M Z (f ⬝ ℓ) ℓ) := by
    intro ℓ hℓ grow f₀ hf₀ hno₀
    have hC : Closed (M + 2)
        (fun f => Z (f ⬝ ℓ) ∧ ¬ (XExit M Z (f ⬝ ℓ) ∨ XEnd M Z (f ⬝ ℓ) ℓ)) := by
      rintro f ⟨hf, hno⟩
      have hp := (hZ _ hf).1
      refine ⟨hp.app_inv.1, ?_⟩
      have hDℓ : Desc (f ⬝ ℓ) ℓ := ⟨_, .refl _, .right f .refl⟩
      rcases xp_cases hZ hf with ⟨c, e, hc⟩ | ⟨c, d, e, hcd⟩ | ⟨t₃, h1, h2, h3⟩ | ⟨tm, z, e, hz⟩ |
        ⟨x, p, q, hs, hpq, hD, hx, hq⟩
      · injection e with _ e2
        rw [← e2] at hc
        exact (hno (.inl ⟨ℓ, hc, hDℓ, by omega⟩)).elim
      · injection e with e1 e2
        rcases hcd with h | h
        · rcases Nat.lt_or_ge (M + 3) (sz c) with big | small
          · exact (hno (.inr ⟨c, S, c, h, big, .refl, by rw [e1]⟩)).elim
          · have hDc : Desc (f ⬝ ℓ) c :=
              ⟨_, .refl _, .left ℓ (by rw [e1]; exact .right S .refl)⟩
            exact (hno (.inl ⟨c, h, hDc, small⟩)).elim
        · rw [← e2] at h
          exact (hno (.inl ⟨ℓ, h, hDℓ, by omega⟩)).elim
      · exact (hno (.inl ⟨t₃, h1, h2, by omega⟩)).elim
      · injection e with _ e2
        rw [← e2] at hz
        exact (hno (.inl ⟨ℓ, hz, hDℓ, by omega⟩)).elim
      · obtain ⟨_, hLI⟩ := fact_LI hp hs
        have hback : ¬ (XExit M Z (p ⬝ q) ∨ XEnd M Z (p ⬝ q) q) := by
          rintro (⟨t₃, h1, h2, h3⟩ | hE)
          · exact hno (.inl ⟨t₃, h1, hD.trans h2, h3⟩)
          · obtain ⟨e, hE'⟩ := xp_pred hp hs hx hq hE
            rw [← e] at hE'
            injection e with _ e2
            rw [← e2] at hE'
            exact hno (.inr hE')
        rcases hLI with ⟨eq, hsf⟩ | lt
        · rw [eq] at hpq hback
          exact ⟨p, ⟨hpq, hback⟩, .inr ⟨x, hx, hsf⟩⟩
        · exact (grow q lt hq p hpq hback).elim
    exact right_combs hC f₀ ⟨hf₀, hno₀⟩
  intro d
  induction d with
  | zero =>
    intro ℓ hd hℓ
    exact fin ℓ hℓ (fun ℓ' lt hℓ' => by exfalso; omega)
  | succ d ih =>
    intro ℓ hd hℓ
    exact fin ℓ hℓ (fun ℓ' lt hℓ' => ih ℓ' (by omega) hℓ')

/-- Every member of `Z` has a descendant in `Z` of leaf count at most `M + 3` (under a double
negation).  Induction on the leaf count: a shrinking step and a completed block both lead to a
member that is a proper subterm. -/
theorem xp_small {M : Nat} {Z : Term → Prop} (hZ : XplusSet M Z) :
    ∀ (n : Nat) (t : Term), sz t ≤ n → Z t → ¬¬ XExit M Z t := by
  intro n
  induction n with
  | zero =>
    intro t h
    have := sz_pos t
    exfalso
    omega
  | succ n ih =>
    intro t hsz ht hno
    have hp := (hZ t ht).1
    have down : ∀ u, Z u → PSub u t → False := by
      intro u hu hsub
      have hlt := hsub.sz_lt
      apply ih u (by omega) hu
      rintro ⟨t₃, h1, h2, h3⟩
      exact hno ⟨t₃, h1, Desc.trans ⟨t, .refl t, hsub⟩ h2, h3⟩
    rcases xp_cases hZ ht with ⟨c, e, hc⟩ | ⟨c, d, e, hcd⟩ | ⟨t₃, h1, h2, h3⟩ | ⟨tm, z, e, hz⟩ |
      ⟨x, p, q, hs, hpq, hD, hx, hq⟩
    · exact down c hc (by rw [e]; exact .right S .refl)
    · rcases hcd with h | h
      · exact down c h (by rw [e]; exact .left d (.right S .refl))
      · exact down d h (by rw [e]; exact .right _ .refl)
    · exact hno ⟨t₃, h1, h2, by omega⟩
    · exact down z hz (by rw [e]; exact .right tm .refl)
    · apply xp_block hZ (M + 1 - sz q) q (Nat.le_refl _) hq p hpq
      rintro (⟨t₃, h1, h2, h3⟩ | hE)
      · exact hno ⟨t₃, h1, hD.trans h2, h3⟩
      · obtain ⟨e, w, c, g, hw, _, hsub, e'⟩ := xp_pred hp hs hx hq hE
        refine down w hw ?_
        rw [e, e']
        exact .left q (.right c hsub)

/-- **Theorem X⁺.**  Let `Z` be a set of closed S-terms such that every member has, on its head
run, a head normal form `S c` with `c ∈ Z`, or `S c d` where each of `c`, `d` is in `Z` or has
leaf count at most `M`, at least one of them is in `Z`, and, if the run takes a step, `sz c ≤ M`
or `d = S c` or `d = S c' c` with `sz c' ≤ M`.  Then `Z` is empty.  (`c'` need not normalize, and
`M ≥ 1` is not assumed.)  Uses `HeadRec.no_ground_loop` through Theorem 2 and the pigeonhole. -/
theorem thm_Xplus {M : Nat} {Z : Term → Prop}
    (hZ : ∀ t, Z t → PureS t ∧ ((∃ c, Steps t (S ⬝ c) ∧ Z c) ∨
      ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (Z c ∨ sz c ≤ M) ∧ (Z d ∨ sz d ≤ M) ∧ (Z c ∨ Z d) ∧
        (t ≠ S ⬝ c ⬝ d → sz c ≤ M ∨ d = S ⬝ c ∨ ∃ c', sz c' ≤ M ∧ d = S ⬝ c' ⬝ c))) :
    ∀ t, ¬ Z t :=
  finite_descent_nn (B := M + 3) (D := Desc) (fun t h => (hZ t h).1)
    (fun h1 h2 => Desc.trans h1 h2) (fun t h => Desc.irrefl (hZ t h).1)
    (fun t h => xp_small hZ (sz t) t (Nat.le_refl _) h)

/-- Theorem X (`thm_X`) is the case of Theorem X⁺ without exceptional members. -/
theorem thm_X_of_Xplus {M : Nat} {Z : Term → Prop}
    (hZ : ∀ t, Z t → PureS t ∧ ((∃ c, Steps t (S ⬝ c) ∧ Z c) ∨
      ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (Z c ∨ sz c ≤ M) ∧ (Z d ∨ sz d ≤ M) ∧ (Z c ∨ Z d) ∧
        (t ≠ S ⬝ c ⬝ d → sz c ≤ M))) : ∀ t, ¬ Z t := by
  refine thm_Xplus (M := M) (Z := Z) (fun t ht => ?_)
  obtain ⟨hp, hk⟩ := hZ t ht
  refine ⟨hp, ?_⟩
  rcases hk with h | ⟨c, d, hs, h1, h2, h3, h4⟩
  · exact .inl h
  · exact .inr ⟨c, d, hs, h1, h2, h3, fun ne => .inl (h4 ne)⟩

/-! ## Corollary X1, sets -/

/-- **Corollary X1** (sets).  Let `F i` be a family of sets of closed S-terms, and `K` a set of
indices such that every member of `F j`, `j ∈ K`, has a one-item head normal form, or a two-item
head normal form with a first or a second item of leaf count at most `M`.  Let every member of
every `F i` have, on its head run, a head normal form of one of the kinds
`S c` with `c ∈ F j`; `S c d` with `sz c ≤ M`, `d ∈ F j`; `S c d` with `c ∈ F j`, `sz d ≤ M`;
`S c d` with `c ∈ F j₁`, `d ∈ F j₂`, `j₂ ∈ K`.  Then every `F i` is empty.

The note gives the types set by set and asks the small entries to be normalizing; here they are
given member by member and only sizes are used.  The alternative "second item small" for `K` is
not in the note (there Lemma SR makes the member ordinary). -/
theorem cor_X1 {ι : Type} {M : Nat} {F : ι → Term → Prop} {K : ι → Prop}
    (hK : ∀ j t, K j → F j t → (∃ c, Steps t (S ⬝ c)) ∨
      ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (sz c ≤ M ∨ sz d ≤ M))
    (hF : ∀ i t, F i t → PureS t ∧
      ((∃ j c, Steps t (S ⬝ c) ∧ F j c) ∨
       (∃ j c d, Steps t (S ⬝ c ⬝ d) ∧ sz c ≤ M ∧ F j d) ∨
       (∃ j c d, Steps t (S ⬝ c ⬝ d) ∧ F j c ∧ sz d ≤ M) ∨
       (∃ j₁ j₂ c d, Steps t (S ⬝ c ⬝ d) ∧ F j₁ c ∧ F j₂ d ∧ K j₂))) : ∀ i t, ¬ F i t := by
  intro i₀ t₀ h₀
  refine thm_Xplus (M := M) (Z := fun t => ∃ i, F i t) ?_ t₀ ⟨i₀, h₀⟩
  rintro t ⟨i, hi⟩
  obtain ⟨hp, hk⟩ := hF i t hi
  refine ⟨hp, ?_⟩
  rcases hk with ⟨j, c, hs, hc⟩ | ⟨j, c, d, hs, hc, hd⟩ | ⟨j, c, d, hs, hc, hd⟩ |
    ⟨j₁, j₂, c, d, hs, hc, hd, hKj⟩
  · exact .inl ⟨c, hs, j, hc⟩
  · exact .inr ⟨c, d, hs, .inr hc, .inl ⟨j, hd⟩, .inr ⟨j, hd⟩, fun _ => .inl hc⟩
  · refine .inr ⟨c, d, hs, .inl ⟨j, hc⟩, .inr hd, .inl ⟨j, hc⟩, fun ne => .inl ?_⟩
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    have h1 := sz_arg_lt y c
    rw [← eb] at h1
    omega
  · refine .inr ⟨c, d, hs, .inl ⟨j₁, hc⟩, .inl ⟨j₂, hd⟩, .inl ⟨j₁, hc⟩, fun ne => ?_⟩
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    rcases Nat.lt_or_ge M (sz c) with big | small
    · have hpd := (hF j₂ d hd).1
      rcases hK j₂ d hKj hd with ⟨c₂, hs₂⟩ | ⟨c₂, d₂, hs₂, hsm⟩
      · have e := hnf1_literal hpd hs₂
        rw [eb] at e
        injection e with e1 _
        refine .inr (.inl ?_)
        rw [eb, e1]
      · rw [eb] at hpd hs₂
        rcases hsm with h | h
        · have hcS : c ≠ S := by
            intro e
            rw [e] at big
            have h1 := sz_pos c₂
            have e1 : sz S = 1 := rfl
            omega
          obtain ⟨e1, _⟩ := cor_LL1 hpd hcS hs₂ (by omega)
          exact .inr (.inr ⟨c₂, h, by rw [eb, e1]⟩)
        · exact .inl (Nat.le_trans (lemma_SR hpd hs₂).1 h)
    · exact .inl small

/-! ## Corollary X1, contexts -/

/-- A context of the form `S E′`, or `S n E′` with `n` closed and normalizing. -/
inductive Simp : Phi.Ctx → Prop
  | one (E : Phi.Ctx) : Simp (.app .s E)
  | nl {a : Term} (E : Phi.Ctx) : PureS a → Normalizing a →
      Simp (.app (.app .s (Tower.ofTerm a)) E)

/-- `Simp` with the normal forms of the closed parts of leaf count at most `M`. -/
inductive SimpB (M : Nat) : Phi.Ctx → Prop
  | one (E : Phi.Ctx) : SimpB M (.app .s E)
  | nl {a n : Term} (E : Phi.Ctx) : PureS a → WSteps a n → Normal n → sz n ≤ M →
      SimpB M (.app (.app .s (Tower.ofTerm a)) E)

theorem SimpB.mono {M M' : Nat} (h : M ≤ M') {E : Phi.Ctx} (hE : SimpB M E) : SimpB M' E := by
  cases hE with
  | one E' => exact .one E'
  | nl E' hpa han nf hsz => exact .nl E' hpa han nf (Nat.le_trans hsz h)

theorem Simp.bound {E : Phi.Ctx} (hE : Simp E) : ∃ M, SimpB M E := by
  cases hE with
  | one E' => exact ⟨0, .one E'⟩
  | nl E' hpa hn =>
    obtain ⟨n, han, nf⟩ := hn
    exact ⟨sz n, .nl E' hpa han nf (Nat.le_refl _)⟩

/-- The contexts of Corollary X1.  `X1Ctx R E`: `E` is built from holes and closed normalizing
terms by `S E′` and `S E′ E″`, it has a hole (`X1Ctx.holed`), and every node `S E₁ E₂` with `E₁`,
`E₂` both non-closed has `E₂` of the form `S E′` or `S n E′` (`Simp`), or `E₂` is a hole and `R`
holds.  The constructors are the four kinds of node with a hole: `S E′`; `S n E′` and `S E′ n`
with `n` closed and normalizing; `S E₁ E₂` with a hole on both sides.  In Corollary X1, `R` says
that the root is of the form `S E′` or `S n E′`. -/
inductive X1Ctx (R : Prop) : Phi.Ctx → Prop
  | hole : X1Ctx R .hole
  | one {E : Phi.Ctx} : X1Ctx R E → X1Ctx R (.app .s E)
  | nl {a : Term} {E : Phi.Ctx} : PureS a → Normalizing a → X1Ctx R E →
      X1Ctx R (.app (.app .s (Tower.ofTerm a)) E)
  | nr {a : Term} {E : Phi.Ctx} : PureS a → Normalizing a → X1Ctx R E →
      X1Ctx R (.app (.app .s E) (Tower.ofTerm a))
  | two {E₁ E₂ : Phi.Ctx} : X1Ctx R E₁ → X1Ctx R E₂ → ((E₂ = .hole ∧ R) ∨ Simp E₂) →
      X1Ctx R (.app (.app .s E₁) E₂)

/-- `X1Ctx` with the normal forms of the closed parts of leaf count at most `M`. -/
inductive X1B (M : Nat) (R : Prop) : Phi.Ctx → Prop
  | hole : X1B M R .hole
  | one {E : Phi.Ctx} : X1B M R E → X1B M R (.app .s E)
  | nl {a n : Term} {E : Phi.Ctx} : PureS a → WSteps a n → Normal n → sz n ≤ M → X1B M R E →
      X1B M R (.app (.app .s (Tower.ofTerm a)) E)
  | nr {a n : Term} {E : Phi.Ctx} : PureS a → WSteps a n → Normal n → sz n ≤ M → X1B M R E →
      X1B M R (.app (.app .s E) (Tower.ofTerm a))
  | two {E₁ E₂ : Phi.Ctx} : X1B M R E₁ → X1B M R E₂ → ((E₂ = .hole ∧ R) ∨ SimpB M E₂) →
      X1B M R (.app (.app .s E₁) E₂)

/-- A context of Corollary X1 has a hole. -/
theorem X1Ctx.holed {R : Prop} {E : Phi.Ctx} (hE : X1Ctx R E) : Holed E := by
  induction hE with
  | hole => exact .hole
  | one _ ih => exact .right _ ih
  | nl _ _ _ ih => exact .right _ ih
  | nr _ _ _ ih => exact .left _ (.right _ ih)
  | two _ _ _ _ ih₂ => exact .right _ ih₂

theorem X1B.mono {M M' : Nat} (h : M ≤ M') {R : Prop} {E : Phi.Ctx} (hE : X1B M R E) :
    X1B M' R E := by
  induction hE with
  | hole => exact .hole
  | one _ ih => exact .one ih
  | nl hpa han nf hsz _ ih => exact .nl hpa han nf (Nat.le_trans hsz h) ih
  | nr hpa han nf hsz _ ih => exact .nr hpa han nf (Nat.le_trans hsz h) ih
  | two _ _ hs ih₁ ih₂ =>
    refine .two ih₁ ih₂ ?_
    rcases hs with h' | h'
    · exact .inl h'
    · exact .inr (h'.mono h)

theorem X1Ctx.bound {R : Prop} {E : Phi.Ctx} (hE : X1Ctx R E) : ∃ M, X1B M R E := by
  induction hE with
  | hole => exact ⟨0, .hole⟩
  | one _ ih =>
    obtain ⟨M, h⟩ := ih
    exact ⟨M, .one h⟩
  | nl hpa hn _ ih =>
    obtain ⟨M, h⟩ := ih
    obtain ⟨n, han, nf⟩ := hn
    exact ⟨M + sz n, .nl hpa han nf (Nat.le_add_left _ _) (h.mono (Nat.le_add_right _ _))⟩
  | nr hpa hn _ ih =>
    obtain ⟨M, h⟩ := ih
    obtain ⟨n, han, nf⟩ := hn
    exact ⟨M + sz n, .nr hpa han nf (Nat.le_add_left _ _) (h.mono (Nat.le_add_right _ _))⟩
  | two _ _ hs ih₁ ih₂ =>
    obtain ⟨M₁, h₁⟩ := ih₁
    obtain ⟨M₂, h₂⟩ := ih₂
    rcases hs with h' | h'
    · exact ⟨M₁ + M₂, .two (h₁.mono (Nat.le_add_right _ _)) (h₂.mono (Nat.le_add_left _ _))
        (.inl h')⟩
    · obtain ⟨M₃, h₃⟩ := h'.bound
      exact ⟨M₁ + M₂ + M₃,
        .two (h₁.mono (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
          (h₂.mono (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)))
          (.inr (h₃.mono (Nat.le_add_left _ _)))⟩

/-- The head normal form of a term convertible to an instance of a `SimpB` context: one item, or
two items with a first item of leaf count at most `M`. -/
theorem simpB_hnf {M : Nat} {p : Term} (hp : PureS p) {E' : Phi.Ctx} (h : SimpB M E') {t : Term}
    (ht : PureS t) (hct : Convertible t (E'.plug p)) :
    (∃ c, Steps t (S ⬝ c)) ∨ ∃ c d, Steps t (S ⬝ c ⬝ d) ∧ (sz c ≤ M ∨ sz d ≤ M) := by
  cases h with
  | one E'' =>
    have hct' : Convertible t (S ⬝ E''.plug p) := hct
    obtain ⟨a, e, _⟩ := hnf1_conv ht (Tower.plug_pure E'' hp) hct'
    exact .inl ⟨a, by rw [e]; exact .refl _⟩
  | @nl a n E'' hpa han nf hsz =>
    have e : (Phi.Ctx.app (.app .s (Tower.ofTerm a)) E'').plug p = S ⬝ a ⬝ E''.plug p := by
      show S ⬝ (Tower.ofTerm a).plug p ⬝ E''.plug p = _
      rw [Tower.plug_ofTerm hpa]
    rw [e] at hct
    obtain ⟨m, a', hs, _, _, _, hm⟩ := hnf2_conv_left ht (Tower.plug_pure E'' hp) hpa han nf hct
    exact .inr ⟨m, a', hs, .inl (Nat.le_trans hm hsz)⟩

/-- **Corollary X1** (contexts).  Let `E ≠ hole` be a context of Corollary X1 (`X1Ctx`, with the
root `E` in place of a hole in the condition on second entries).  Then no closed S-term `p` is
convertible to `E[p]`.  The sets of the proof are the conversion classes of the instances `E′[p]`
of the subcontexts ((Eq) of the note). -/
theorem ncfp_X1 {p : Term} (hp : PureS p) {E : Phi.Ctx} (hE : X1Ctx (Simp E) E)
    (hne : E ≠ .hole) : ¬ Convertible p (E.plug p) := by
  intro hc
  obtain ⟨M₁, hM₁⟩ := hE.bound
  refine em_false (A := Simp E) (fun hem => ?_)
  have hex : ∃ M, X1B M (Simp E) E ∧ (Simp E → SimpB M E) := by
    rcases hem with h | h
    · obtain ⟨M₂, h₂⟩ := h.bound
      exact ⟨M₁ + M₂, hM₁.mono (Nat.le_add_right _ _), fun _ => h₂.mono (Nat.le_add_left _ _)⟩
    · exact ⟨M₁, hM₁, fun h' => absurd h' h⟩
  obtain ⟨M, hM, hR⟩ := hex
  have key : ∀ E' : Phi.Ctx, X1B M (Simp E) E' → E' ≠ .hole → ∀ t, PureS t →
      Convertible t (E'.plug p) →
      ((∃ j c, Steps t (S ⬝ c) ∧ (X1B M (Simp E) j ∧ PureS c ∧ Convertible c (j.plug p))) ∨
       (∃ j c d, Steps t (S ⬝ c ⬝ d) ∧ sz c ≤ M ∧
         (X1B M (Simp E) j ∧ PureS d ∧ Convertible d (j.plug p))) ∨
       (∃ j c d, Steps t (S ⬝ c ⬝ d) ∧
         (X1B M (Simp E) j ∧ PureS c ∧ Convertible c (j.plug p)) ∧ sz d ≤ M) ∨
       (∃ j₁ j₂ c d, Steps t (S ⬝ c ⬝ d) ∧
         (X1B M (Simp E) j₁ ∧ PureS c ∧ Convertible c (j₁.plug p)) ∧
         (X1B M (Simp E) j₂ ∧ PureS d ∧ Convertible d (j₂.plug p)) ∧
         ((j₂ = .hole ∧ Simp E) ∨ SimpB M j₂))) := by
    intro E' hE' hne' t ht hct
    cases hE' with
    | hole => exact absurd rfl hne'
    | @one E₁ h1 =>
      have hct' : Convertible t (S ⬝ E₁.plug p) := hct
      obtain ⟨a, e, ca⟩ := hnf1_conv ht (Tower.plug_pure E₁ hp) hct'
      have hpa : PureS a := by
        rw [e] at ht
        exact ht.app_inv.2
      exact .inl ⟨E₁, a, by rw [e]; exact .refl _, h1, hpa, ca⟩
    | @nl a n E₁ hpa han nf hsz h1 =>
      have e : (Phi.Ctx.app (.app .s (Tower.ofTerm a)) E₁).plug p = S ⬝ a ⬝ E₁.plug p := by
        show S ⬝ (Tower.ofTerm a).plug p ⬝ E₁.plug p = _
        rw [Tower.plug_ofTerm hpa]
      rw [e] at hct
      obtain ⟨m, a', hs, hpa', ca, _, hm⟩ :=
        hnf2_conv_left ht (Tower.plug_pure E₁ hp) hpa han nf hct
      exact .inr (.inl ⟨E₁, m, a', hs, Nat.le_trans hm hsz, h1, hpa', ca⟩)
    | @nr a n E₁ hpa han nf hsz h1 =>
      have e : (Phi.Ctx.app (.app .s E₁) (Tower.ofTerm a)).plug p = S ⬝ E₁.plug p ⬝ a := by
        show S ⬝ E₁.plug p ⬝ (Tower.ofTerm a).plug p = _
        rw [Tower.plug_ofTerm hpa]
      rw [e] at hct
      obtain ⟨a', m, hs, hpa', ca, _, hm⟩ :=
        hnf2_conv_right ht (Tower.plug_pure E₁ hp) hpa han nf hct
      exact .inr (.inr (.inl ⟨E₁, a', m, hs, ⟨h1, hpa', ca⟩, Nat.le_trans hm hsz⟩))
    | @two E₁ E₂ h1 h2 hs2 =>
      have hct' : Convertible t (S ⬝ E₁.plug p ⬝ E₂.plug p) := hct
      obtain ⟨a, b, hs, ca, cb⟩ :=
        hnf2_conv ht (Tower.plug_pure E₁ hp) (Tower.plug_pure E₂ hp) hct'
      have hpab := steps_pure ht hs
      exact .inr (.inr (.inr ⟨E₁, E₂, a, b, hs, ⟨h1, hpab.app_inv.1.app_inv.2, ca⟩,
        ⟨h2, hpab.app_inv.2, cb⟩, hs2⟩))
  refine cor_X1 (M := M)
    (F := fun (E' : Phi.Ctx) t => X1B M (Simp E) E' ∧ PureS t ∧ Convertible t (E'.plug p))
    (K := fun E' => (E' = .hole ∧ Simp E) ∨ SimpB M E') ?_ ?_ .hole p
    ⟨.hole, hp, Convertible.refl p⟩
  · rintro j t hKj ⟨_, ht, hct⟩
    rcases hKj with ⟨e, hS⟩ | h
    · rw [e] at hct
      have hct0 : Convertible t p := hct
      exact simpB_hnf hp (hR hS) ht (hct0.trans hc)
    · exact simpB_hnf hp h ht hct
  · rintro i t ⟨hi, ht, hct⟩
    refine ⟨ht, ?_⟩
    cases hi with
    | hole =>
      have hct0 : Convertible t p := hct
      exact key E hM hne t ht (hct0.trans hc)
    | one h1 => exact key _ (.one h1) (fun e => by cases e) t ht hct
    | nl hpa han nf hsz h1 => exact key _ (.nl hpa han nf hsz h1) (fun e => by cases e) t ht hct
    | nr hpa han nf hsz h1 => exact key _ (.nr hpa han nf hsz h1) (fun e => by cases e) t ht hct
    | two h1 h2 hs2 => exact key _ (.two h1 h2 hs2) (fun e => by cases e) t ht hct

/-! ## The nine two-hole contexts of depth 3 of Corollary X1 -/

/-- `p` is not convertible to `S (S p (S n p))`, for closed `p` and closed normalizing `n`. -/
theorem no_S_SpSnp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ (S ⬝ n ⬝ p))) := by
  have h := ncfp_X1 hp (E := (.app .s (.app (.app .s .hole) (.app (.app .s (Tower.ofTerm n)) .hole))))
    (.one (.two .hole (.nl hn hnn .hole) (.inr (.nl .hole hn hnn)))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn] at h
  exact h

/-- `p` is not convertible to `S (S p) (S n (S p))`, for closed `p` and closed normalizing `n`. -/
theorem no_S_Sp_SnSp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p) ⬝ (S ⬝ n ⬝ (S ⬝ p))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (.app .s .hole)) (.app (.app .s (Tower.ofTerm n)) (.app .s .hole))))
    (.two (.one .hole) (.nl hn hnn (.one .hole)) (.inr (.nl _ hn hnn))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn] at h
  exact h

/-- `p` is not convertible to `S n (S p (S p))`, for closed `p` and closed normalizing `n`. -/
theorem no_S_n_SpSp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ n ⬝ (S ⬝ p ⬝ (S ⬝ p))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (Tower.ofTerm n)) (.app (.app .s .hole) (.app .s .hole))))
    (.nl hn hnn (.two .hole (.one .hole) (.inr (.one _)))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn] at h
  exact h

/-- `p` is not convertible to `S (S n p) (S (S m p))`, for closed `p` and closed normalizing `n`, `m`. -/
theorem no_S_Snp_SSmp {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ (S ⬝ m ⬝ p))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (.app (.app .s (Tower.ofTerm n)) .hole)) (.app .s (.app (.app .s (Tower.ofTerm m)) .hole))))
    (.two (.nl hn hnn .hole) (.one (.nl hm hmm .hole)) (.inr (.one _))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn, Tower.plug_ofTerm hm] at h
  exact h

/-- `p` is not convertible to `S (S p (S n p)) m`, for closed `p` and closed normalizing `n`, `m`. -/
theorem no_S_SpSnp_m {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ (S ⬝ n ⬝ p)) ⬝ m) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (.app (.app .s .hole) (.app (.app .s (Tower.ofTerm n)) .hole))) (Tower.ofTerm m)))
    (.nr hm hmm (.two .hole (.nl hn hnn .hole) (.inr (.nl _ hn hnn)))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn, Tower.plug_ofTerm hm] at h
  exact h

/-- `p` is not convertible to `S (S p n) (S (S p m))`, for closed `p` and closed normalizing `n`, `m`. -/
theorem no_S_Spn_SSpm {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ (S ⬝ p ⬝ m))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (.app (.app .s .hole) (Tower.ofTerm n))) (.app .s (.app (.app .s .hole) (Tower.ofTerm m)))))
    (.two (.nr hn hnn .hole) (.one (.nr hm hmm .hole)) (.inr (.one _))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn, Tower.plug_ofTerm hm] at h
  exact h

/-- `p` is not convertible to `S n (S p (S m p))`, for closed `p` and closed normalizing `n`, `m`. -/
theorem no_S_n_SpSmp {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ n ⬝ (S ⬝ p ⬝ (S ⬝ m ⬝ p))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (Tower.ofTerm n)) (.app (.app .s .hole) (.app (.app .s (Tower.ofTerm m)) .hole))))
    (.nl hn hnn (.two .hole (.nl hm hmm .hole) (.inr (.nl _ hm hmm)))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn, Tower.plug_ofTerm hm] at h
  exact h

/-- `p` is not convertible to `S (S n p) (S m (S k p))`, for closed `p` and closed normalizing `n`, `m`, `k`. -/
theorem no_S_Snp_SmSkp {p n m k : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) (hk : PureS k) (hkk : Normalizing k) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ m ⬝ (S ⬝ k ⬝ p))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (.app (.app .s (Tower.ofTerm n)) .hole)) (.app (.app .s (Tower.ofTerm m)) (.app (.app .s (Tower.ofTerm k)) .hole))))
    (.two (.nl hn hnn .hole) (.nl hm hmm (.nl hk hkk .hole)) (.inr (.nl _ hm hmm))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn, Tower.plug_ofTerm hm, Tower.plug_ofTerm hk] at h
  exact h

/-- `p` is not convertible to `S (S p n) (S m (S p k))`, for closed `p` and closed normalizing `n`, `m`, `k`. -/
theorem no_S_Spn_SmSpk {p n m k : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) (hk : PureS k) (hkk : Normalizing k) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ m ⬝ (S ⬝ p ⬝ k))) := by
  have h := ncfp_X1 hp (E := (.app (.app .s (.app (.app .s .hole) (Tower.ofTerm n))) (.app (.app .s (Tower.ofTerm m)) (.app (.app .s .hole) (Tower.ofTerm k)))))
    (.two (.nr hn hnn .hole) (.nl hm hmm (.nr hk hkk .hole)) (.inr (.nl _ hm hmm))) (fun e => by cases e)
  simp only [Phi.Ctx.plug, Tower.plug_ofTerm hn, Tower.plug_ofTerm hm, Tower.plug_ofTerm hk] at h
  exact h

end Ncfp
