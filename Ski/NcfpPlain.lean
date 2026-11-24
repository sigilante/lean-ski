import Ski.NcfpThree
open Term

/-!
# NCFP for the plain contexts of depth at most 2

Source: `notes/NCFP-proof.md`, §15 (Cor. T2 as a statement; the note assembles it from Cor. G1, Cor. L1, N2–N10 and Cor. T1,
here it is a case analysis onto the theorems already proved).  Setting as in `Ski/Ncfp.lean`.

`PlainD d E`: the context `E` is built from holes and closed normalizing terms by `S E′` and
`S E′ E″` with nesting depth at most `d` (a closed normalizing term counts as a leaf).

What is proved:

* `ncfp_depth2`: for every closed S-term `p` and every `E ≠ hole` with a hole and `PlainD 2 E`,
  `p` is not convertible to `E[p]`.  The 40 shapes are: 5 of the form `S X` and 35 of the form
  `S X Y`, with `X`, `Y` among `p`, `n`, `S p`, `S p p`, `S n p`, `S p n` (`Plain1`).  Of these,
  12 are contexts without closed parts (`ncfp_S_comb`, `ncfp_holes`), 10 have one hole and a
  closed part (`ncfp_gcomb`), and 18 are the named theorems of `Ski/NcfpN.lean`,
  `Ski/NcfpN2.lean`, `Ski/NcfpScheme.lean` and `Ski/NcfpThree.lean`.

What is not proved: anything for depth 3 or more beyond the theorems of the other modules.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-- `S a b` is normalizing if `a` and `b` are. -/
theorem normalizing_S2 {a b : Term} (ha : Normalizing a) (hb : Normalizing b) :
    Normalizing (S ⬝ a ⬝ b) := by
  obtain ⟨a', hsa, nfa⟩ := ha
  obtain ⟨b', hsb, nfb⟩ := hb
  refine ⟨S ⬝ a' ⬝ b', (WSteps.left b (WSteps.right S hsa)).trans (WSteps.right (S ⬝ a') hsb), ?_⟩
  intro u s
  cases s with
  | left _ s' =>
    cases s' with
    | left _ s'' => cases s''
    | right _ s'' => exact nfa _ s''
  | right _ s' => exact nfb _ s'

/-- Plain contexts of depth at most `d`: built from holes and closed normalizing terms (leaves)
by `S E′` and `S E′ E″`. -/
inductive PlainD : Nat → Phi.Ctx → Prop
  | hole {d : Nat} : PlainD d .hole
  | nf {d : Nat} {a : Term} : PureS a → Normalizing a → PlainD d (Tower.ofTerm a)
  | one {d : Nat} {E : Phi.Ctx} : PlainD d E → PlainD (d + 1) (.app .s E)
  | two {d : Nat} {E₁ E₂ : Phi.Ctx} : PlainD d E₁ → PlainD d E₂ →
      PlainD (d + 1) (.app (.app .s E₁) E₂)

theorem PlainD.mono {d : Nat} {E : Phi.Ctx} (h : PlainD d E) : PlainD (d + 1) E := by
  induction h with
  | hole => exact .hole
  | nf ha hna => exact .nf ha hna
  | one _ ih => exact .one ih
  | two _ _ ih₁ ih₂ => exact .two ih₁ ih₂

/-- A closed S-term as a context has no hole. -/
theorem not_holed_ofTerm : ∀ a : Term, ¬ Holed (Tower.ofTerm a)
  | .app f x => by
    intro h
    have h' : Holed (.app (Tower.ofTerm f) (Tower.ofTerm x)) := h
    cases h' with
    | left _ h1 => exact not_holed_ofTerm f h1
    | right _ h1 => exact not_holed_ofTerm x h1
  | .S => by intro h; cases h
  | .K => by intro h; cases h
  | .I => by intro h; cases h

theorem not_holed_nf2 {a b : Term} (_ha : PureS a) (_hb : PureS b)
    (h : Holed (.app (.app .s (Tower.ofTerm a)) (Tower.ofTerm b))) : False := by
  cases h with
  | left _ h1 =>
    cases h1 with
    | left _ h2 => cases h2
    | right _ h2 => exact not_holed_ofTerm a h2
  | right _ h1 => exact not_holed_ofTerm b h1

/-- The six shapes of depth at most 1: `p`, a closed normalizing term, `S p`, `S p p`, `S n p`,
`S p n`. -/
inductive Plain1 : Phi.Ctx → Prop
  | hole : Plain1 .hole
  | nf {a : Term} : PureS a → Normalizing a → Plain1 (Tower.ofTerm a)
  | sp : Plain1 (.app .s .hole)
  | spp : Plain1 (.app (.app .s .hole) .hole)
  | snp {a : Term} : PureS a → Normalizing a → Plain1 (.app (.app .s (Tower.ofTerm a)) .hole)
  | spn {a : Term} : PureS a → Normalizing a → Plain1 (.app (.app .s .hole) (Tower.ofTerm a))

theorem plain0_cases {E : Phi.Ctx} (h : PlainD 0 E) :
    E = .hole ∨ ∃ a, PureS a ∧ Normalizing a ∧ E = Tower.ofTerm a := by
  cases h with
  | hole => exact .inl rfl
  | nf ha hna => exact .inr ⟨_, ha, hna, rfl⟩

/-- A plain context of depth at most 1 has one of the six shapes (closed subcontexts are closed
normalizing terms). -/
theorem plain1_cases {E : Phi.Ctx} (h : PlainD 1 E) : Plain1 E := by
  cases h with
  | hole => exact .hole
  | nf ha hna => exact .nf ha hna
  | one h1 =>
    rcases plain0_cases h1 with e | ⟨a, ha, hna, e⟩
    · rw [e]
      exact .sp
    · rw [e]
      exact Plain1.nf (a := S ⬝ a) (.app .S ha) (normalizing_S1 hna)
  | two h1 h2 =>
    rcases plain0_cases h1 with e1 | ⟨a, ha, hna, e1⟩
    · rcases plain0_cases h2 with e2 | ⟨b, hb, hnb, e2⟩
      · rw [e1, e2]
        exact .spp
      · rw [e1, e2]
        exact .spn hb hnb
    · rcases plain0_cases h2 with e2 | ⟨b, hb, hnb, e2⟩
      · rw [e1, e2]
        exact .snp ha hna
      · rw [e1, e2]
        exact Plain1.nf (a := S ⬝ a ⬝ b) (.app (.app .S ha) hb) (normalizing_S2 hna hnb)

/-- **NCFP for plain contexts of depth at most 2.**  Let `E ≠ hole` be built from holes and closed
normalizing terms by `S E′` and `S E′ E″` with nesting depth at most 2, with at least one hole.
Then no closed S-term `p` is convertible to `E[p]`. -/
theorem ncfp_depth2 {p : Term} (hp : PureS p) {E : Phi.Ctx} (hE : PlainD 2 E) (hh : Holed E)
    (hne : E ≠ .hole) : ¬ Convertible p (E.plug p) := by
  cases hE with
  | hole => exact absurd rfl hne
  | @nf _ a ha hna => exact (not_holed_ofTerm a hh).elim
  | one h1 =>
    have hX := plain1_cases h1
    cases hX with
    | hole => exact ncfp_S_comb hp
    | @nf a ha hna =>
      cases hh with
      | left _ h2 => cases h2
      | right _ h2 => exact (not_holed_ofTerm a h2).elim
    | sp => exact ncfp_holes hp (.one (.one .hole)) (fun e => by cases e)
    | spp => exact ncfp_holes hp (.one (.two .hole .hole)) (fun e => by cases e)
    | @snp a ha hna => exact ncfp_gcomb hp (.s1 (.s2 ha hna .hole)) (fun e => by cases e)
    | @spn a ha hna => exact ncfp_gcomb hp (.s1 (.s3 ha hna .hole)) (fun e => by cases e)
  | two h1 h2 =>
    have hX := plain1_cases h1
    have hY := plain1_cases h2
    cases hX with
    | hole =>
      cases hY with
      | hole =>
        exact ncfp_holes hp (.two .hole .hole) (fun e => by cases e)
      | @nf b hb hnb =>
        exact ncfp_gcomb hp (.s3 hb hnb .hole) (fun e => by cases e)
      | sp =>
        exact ncfp_holes hp (.two .hole (.one .hole)) (fun e => by cases e)
      | spp =>
        exact ncfp_holes hp (.two .hole (.two .hole .hole)) (fun e => by cases e)
      | @snp b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_p_Snp hp hb hnb
      | @spn b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_p_Spn hp hb hnb
    | @nf a ha hna =>
      cases hY with
      | hole =>
        exact ncfp_gcomb hp (.s2 ha hna .hole) (fun e => by cases e)
      | @nf b hb hnb =>
        exact (not_holed_nf2 ha hb hh).elim
      | sp =>
        exact ncfp_gcomb hp (.s2 ha hna (.s1 .hole)) (fun e => by cases e)
      | spp =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_n_Spp hp ha hna
      | @snp b hb hnb =>
        exact ncfp_gcomb hp (.s2 ha hna (.s2 hb hnb .hole)) (fun e => by cases e)
      | @spn b hb hnb =>
        exact ncfp_gcomb hp (.s2 ha hna (.s3 hb hnb .hole)) (fun e => by cases e)
    | sp =>
      cases hY with
      | hole =>
        exact ncfp_holes hp (.two (.one .hole) .hole) (fun e => by cases e)
      | @nf b hb hnb =>
        exact ncfp_gcomb hp (.s3 hb hnb (.s1 .hole)) (fun e => by cases e)
      | sp =>
        exact ncfp_holes hp (.two (.one .hole) (.one .hole)) (fun e => by cases e)
      | spp =>
        exact ncfp_holes hp (.two (.one .hole) (.two .hole .hole)) (fun e => by cases e)
      | @snp b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_Sp_Snp hp hb hnb
      | @spn b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_Sp_Spn hp hb hnb
    | spp =>
      cases hY with
      | hole =>
        exact ncfp_holes hp (.two (.two .hole .hole) .hole) (fun e => by cases e)
      | @nf b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_Spp_n hp hb hnb
      | sp =>
        exact ncfp_holes hp (.two (.two .hole .hole) (.one .hole)) (fun e => by cases e)
      | spp =>
        exact ncfp_holes hp (.two (.two .hole .hole) (.two .hole .hole)) (fun e => by cases e)
      | @snp b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_Spp_Snp hp hb hnb
      | @spn b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm hb]
        exact no_S_Spp_Spn hp hb hnb
    | @snp a ha hna =>
      cases hY with
      | hole =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_Snp_p hp ha hna
      | @nf b hb hnb =>
        exact ncfp_gcomb hp (.s3 hb hnb (.s2 ha hna .hole)) (fun e => by cases e)
      | sp =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_Snp_Sp hp ha hna
      | spp =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_Snp_Spp hp ha hna
      | @snp b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha, Tower.plug_ofTerm hb]
        exact no_S_Snp_Smp hp ha hna hb hnb
      | @spn b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha, Tower.plug_ofTerm hb]
        exact no_S_Snp_Spm hp ha hna hb hnb
    | @spn a ha hna =>
      cases hY with
      | hole =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_Spn_p hp ha hna
      | @nf b hb hnb =>
        exact ncfp_gcomb hp (.s3 hb hnb (.s3 ha hna .hole)) (fun e => by cases e)
      | sp =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_Spn_Sp hp ha hna
      | spp =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha]
        exact no_S_Spn_Spp hp ha hna
      | @snp b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha, Tower.plug_ofTerm hb]
        exact no_S_Spn_Smp hp ha hna hb hnb
      | @spn b hb hnb =>
        simp only [Phi.Ctx.plug, Tower.plug_ofTerm ha, Tower.plug_ofTerm hb]
        exact no_S_Spn_Spm hp ha hna hb hnb

end Ncfp
