import Ski.NcfpDepth2
open Term

/-!
# NCFP: typed systems closed at distance 0, and the two-hole shapes of depth 2

Source: `notes/NCFP-proof.md`, §15.2 and §15.4 (in part).  Setting as in `Ski/Ncfp.lean`.

A *scheme* over an index type `ι` gives every symbol a type (`Ty ι`): `one J` (a one-item head
normal form with item of class `J`) or `two L R` (two items), where a slot is a class or a closed
normalizing term (`Slot ι`).  A *typed system* (`Typed M ty Z`) is a family of sets `Z X` of
closed S-terms whose members have head normal forms of the type of `X`, with `nf` slots read as
"normalizing of leaf count at most `M`".  (The note also asks the sets to be pairwise disjoint;
that is not needed here.)

What is proved:

* `thm_T0`: there is no typed system over a scheme in which every type has a class entry and
  every symbol is `easy`: of kind one, or with a normalizing slot, or of type `[L, R]` with the type
  of `R` being `[_, n]`, or `[n, Y]` or `[Y]` with the types of `L` and `Y` syntactically apart
  (`Ty.apart`: different kinds, or a normalizing slot against a class slot).  This is the part of
  the note's Theorem T in which every exception is excluded at distance 0 by Lemma SR; the proof is
  Theorem X.  It contains the note's Theorems N6–N10 in set form.
* `ncfp_scheme`: the same for conversion classes given by representatives.
* The ten equations of N6–N10: for closed `p` and closed normalizing `n`, `m`, `p` is convertible
  to none of `S (S p p) n`, `S n (S p p)`, `S (S p) (S n p)`, `S (S n p) (S p m)`,
  `S (S p) (S p n)`, `S (S n p) (S p)`, `S (S p n) (S p)`, `S (S n p) (S m p)`,
  `S (S p n) (S m p)`, `S (S p n) (S p m)`.
* `thm_N11` (Theorem N11) and `no_S_SpSp_n`: `p` is not convertible to `S (S p (S p)) n`.

What is not proved: the pair graph `Γ`, Lemma W, tameness, the general Theorem T, Corollaries T1
and T2 (the three-hole shapes of depth 2 are not covered); Conj. HN; NCFP.
-/

namespace Ncfp
open HnfS HeadRec Conv

/-! ## Schemes -/

/-- A slot of a type: a class, or a closed normalizing term. -/
inductive Slot (ι : Type) where
  | cls (i : ι) : Slot ι
  | nf (n : Term) : Slot ι

/-- The type of a class: a one-item or a two-item head normal form. -/
inductive Ty (ι : Type) where
  | one (i : ι) : Ty ι
  | two (L R : Slot ι) : Ty ι

def Slot.isNf {ι : Type} : Slot ι → Bool
  | .cls _ => false
  | .nf _ => true

/-- The type has a class entry. -/
def Ty.hasCls {ι : Type} : Ty ι → Bool
  | .one _ => true
  | .two L R => !(L.isNf && R.isNf)

/-- Two types that no term can have both: different kinds, or a normalizing slot against a class
slot at the same position. -/
def Ty.apart {ι : Type} : Ty ι → Ty ι → Bool
  | .one _, .two _ _ => true
  | .two _ _, .one _ => true
  | .two L R, .two L' R' => (L.isNf != L'.isNf) || (R.isNf != R'.isNf)
  | .one _, .one _ => false

/-- The condition on the type of the second entry `R` of a type `[L, R]`. -/
def easyR {ι : Type} (ty : ι → Ty ι) (tL : Ty ι) : Ty ι → Bool
  | .two _ (.nf _) => true
  | .two (.nf _) (.cls Y) => tL.apart (ty Y)
  | .one Y => tL.apart (ty Y)
  | .two (.cls _) (.cls _) => false

/-- A type whose non-literal members have a small first item, by Lemma SR. -/
def easy {ι : Type} (ty : ι → Ty ι) : Ty ι → Bool
  | .one _ => true
  | .two (.nf _) _ => true
  | .two (.cls _) (.nf _) => true
  | .two (.cls L) (.cls R) => easyR ty (ty L) (ty R)

/-- Membership in a slot. -/
def InS {ι : Type} (M : Nat) (Z : ι → Term → Prop) : Slot ι → Term → Prop
  | .cls Y, a => Z Y a
  | .nf _, a => Normalizing a ∧ sz a ≤ M

/-- `t` has a head normal form of the given type. -/
def TySem {ι : Type} (M : Nat) (Z : ι → Term → Prop) (t : Term) : Ty ι → Prop
  | .one J => ∃ c, Steps t (S ⬝ c) ∧ Z J c
  | .two L R => ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ InS M Z L a ∧ InS M Z R b

/-- A typed system over the scheme `ty` with bound `M`. -/
def Typed {ι : Type} (M : Nat) (ty : ι → Ty ι) (Z : ι → Term → Prop) : Prop :=
  ∀ X t, Z X t → PureS t ∧ TySem M Z t (ty X)

/-- (NN) No member of a typed system in which every type has a class entry is normalizing. -/
theorem typed_nn {ι : Type} {M : Nat} {ty : ι → Ty ι} {Z : ι → Term → Prop} (hT : Typed M ty Z)
    (hc : ∀ X, (ty X).hasCls = true) :
    ∀ (k : Nat) (X : ι) (v n : Term), sz n ≤ k → Z X v → WSteps v n → Normal n → False := by
  intro k
  induction k with
  | zero =>
    intro X v n h _ _ _
    have := sz_pos n
    omega
  | succ k ih =>
    intro X v n hsz hv hvn nf
    obtain ⟨hp, hsem⟩ := hT X v hv
    have hcX := hc X
    cases hty : ty X with
    | one J =>
      rw [hty] at hsem
      obtain ⟨c, hs, hcZ⟩ := hsem
      obtain ⟨c', e, hcc⟩ := hnf1_wsteps (steps_pure hp hs) (wsteps_to_normal hs.weak hvn nf)
      rw [e] at nf hsz
      have h1 : sz c' < sz (S ⬝ c') := sz_arg_lt S c'
      exact ih J c c' (by omega) hcZ hcc nf.app_inv.2
    | two L R =>
      rw [hty] at hsem hcX
      obtain ⟨a, b, hs, hLa, hRb⟩ := hsem
      obtain ⟨a', b', e, haa, hbb⟩ := hnf2_wsteps (steps_pure hp hs) (wsteps_to_normal hs.weak hvn nf)
      rw [e] at nf hsz
      have h1 : sz a' < sz (S ⬝ a' ⬝ b') := Nat.lt_trans (sz_arg_lt S a') (sz_fun_lt _ b')
      have h2 : sz b' < sz (S ⬝ a' ⬝ b') := sz_arg_lt _ b'
      cases L with
      | cls Y => exact ih Y a a' (by omega) hLa haa nf.app_inv.1.app_inv.2
      | nf m =>
        cases R with
        | cls Y => exact ih Y b b' (by omega) hRb hbb nf.app_inv.2
        | nf m' => exact Bool.false_ne_true hcX

theorem typed_not_normalizing {ι : Type} {M : Nat} {ty : ι → Ty ι} {Z : ι → Term → Prop}
    (hT : Typed M ty Z) (hc : ∀ X, (ty X).hasCls = true) {X : ι} {v : Term} (hv : Z X v) :
    ¬ Normalizing v :=
  fun ⟨n, hvn, nf⟩ => typed_nn hT hc (sz n) X v n (Nat.le_refl _) hv hvn nf

theorem slot_mism {ι : Type} {M : Nat} {ty : ι → Ty ι} {Z : ι → Term → Prop} (hT : Typed M ty Z)
    (hc : ∀ X, (ty X).hasCls = true) {L L' : Slot ι} {a : Term}
    (h : (L.isNf != L'.isNf) = true) (h1 : InS M Z L a) (h2 : InS M Z L' a) : False := by
  cases L with
  | cls Y =>
    cases L' with
    | cls Y' => exact Bool.false_ne_true h
    | nf m => exact typed_not_normalizing hT hc h1 h2.1
  | nf m =>
    cases L' with
    | cls Y' => exact typed_not_normalizing hT hc h2 h1.1
    | nf m' => exact Bool.false_ne_true h

/-- Classes with types that are apart are disjoint. -/
theorem typed_apart {ι : Type} {M : Nat} {ty : ι → Ty ι} {Z : ι → Term → Prop} (hT : Typed M ty Z)
    (hc : ∀ X, (ty X).hasCls = true) {X Y : ι} {t : Term} (h : (ty X).apart (ty Y) = true)
    (hX : Z X t) (hY : Z Y t) : False := by
  obtain ⟨_, hsX⟩ := hT X t hX
  obtain ⟨_, hsY⟩ := hT Y t hY
  cases hx : ty X with
  | one J =>
    cases hy : ty Y with
    | one J' =>
      rw [hx, hy] at h
      exact Bool.false_ne_true h
    | two L' R' =>
      rw [hx] at hsX
      rw [hy] at hsY
      obtain ⟨c, hs, _⟩ := hsX
      obtain ⟨a, b, hs', _, _⟩ := hsY
      have e := run_hnf_hnf (.inr (.inl ⟨c, rfl⟩)) (.inr (.inr ⟨a, b, rfl⟩)) hs hs'
      injection e with e1 _
      cases e1
  | two L R =>
    cases hy : ty Y with
    | one J' =>
      rw [hx] at hsX
      rw [hy] at hsY
      obtain ⟨a, b, hs, _, _⟩ := hsX
      obtain ⟨c, hs', _⟩ := hsY
      have e := run_hnf_hnf (.inr (.inl ⟨c, rfl⟩)) (.inr (.inr ⟨a, b, rfl⟩)) hs' hs
      injection e with e1 _
      cases e1
    | two L' R' =>
      rw [hx] at hsX
      rw [hy] at hsY
      rw [hx, hy] at h
      obtain ⟨a, b, hs, hLa, hRb⟩ := hsX
      obtain ⟨a', b', hs', hLa', hRb'⟩ := hsY
      have e := run_hnf_hnf (.inr (.inr ⟨a, b, rfl⟩)) (.inr (.inr ⟨a', b', rfl⟩)) hs hs'
      injection e with e1 e2
      injection e1 with _ e3
      rw [← e3] at hLa'
      rw [← e2] at hRb'
      have h' : ((L.isNf != L'.isNf) || (R.isNf != R'.isNf)) = true := h
      cases h1 : (L.isNf != L'.isNf) with
      | true => exact slot_mism hT hc h1 hLa hLa'
      | false =>
        rw [h1] at h'
        exact slot_mism hT hc h' hRb hRb'

/-- **Theorem T at distance 0.**  There is no typed system over a scheme in which every type has
a class entry and every type is `easy`: all sets `Z X` are empty.  (By Theorem X: Lemma SR gives
every non-literal member a first item of leaf count at most `M`.) -/
theorem thm_T0 {ι : Type} {M : Nat} {ty : ι → Ty ι} {Z : ι → Term → Prop} (hT : Typed M ty Z)
    (hc : ∀ X, (ty X).hasCls = true) (he : ∀ X, easy ty (ty X) = true) : ∀ X t, ¬ Z X t := by
  intro X₀ t₀ hZ₀
  refine thm_X (M := M) (Z := fun t => ∃ X, Z X t) ?_ t₀ ⟨X₀, hZ₀⟩
  rintro t ⟨X, hZ⟩
  obtain ⟨hp, hsem⟩ := hT X t hZ
  refine ⟨hp, ?_⟩
  have heX := he X
  have hcX := hc X
  cases hty : ty X with
  | one J =>
    rw [hty] at hsem
    obtain ⟨c, hs, hcZ⟩ := hsem
    exact .inl ⟨c, hs, J, hcZ⟩
  | two L R =>
    rw [hty] at hsem heX hcX
    obtain ⟨a, b, hs, hLa, hRb⟩ := hsem
    have slotU : ∀ (L : Slot ι) (a : Term), InS M Z L a → (∃ X, Z X a) ∨ sz a ≤ M := by
      intro L a h
      cases L with
      | cls Y => exact .inl ⟨Y, h⟩
      | nf m => exact .inr h.2
    have hone : (∃ X, Z X a) ∨ ∃ X, Z X b := by
      cases L with
      | cls Y => exact .inl ⟨Y, hLa⟩
      | nf m =>
        cases R with
        | cls Y => exact .inr ⟨Y, hRb⟩
        | nf m' => exact (Bool.false_ne_true hcX).elim
    refine .inr ⟨a, b, hs, slotU L a hLa, slotU R b hRb, hone, ?_⟩
    intro ne
    obtain ⟨y, _, eb⟩ := lemma_L' hp hs ne
    cases L with
    | nf m => exact hLa.2
    | cls L' =>
      have h0 := sz_arg_lt y a
      rw [← eb] at h0
      cases R with
      | nf m =>
        have := hRb.2
        omega
      | cls R' =>
        have heX' : easyR ty (ty L') (ty R') = true := heX
        obtain ⟨hpb, hsemb⟩ := hT R' b hRb
        have haS : a ≠ S := by
          intro e
          rw [e] at hLa
          exact typed_not_normalizing hT hc hLa ⟨S, .refl _, normal_S⟩
        cases hR : ty R' with
        | one Y =>
          rw [hR] at heX' hsemb
          obtain ⟨c, hsb, hcY⟩ := hsemb
          have e := hnf1_literal hpb hsb
          rw [eb] at e
          injection e with _ e2
          rw [← e2] at hcY
          exact (typed_apart hT hc heX' hLa hcY).elim
        | two L2 R2 =>
          rw [hR] at heX' hsemb
          obtain ⟨h1, h2, hsb, hL2, hR2⟩ := hsemb
          rw [eb] at hpb hsb
          obtain ⟨hsr1, hsr2⟩ := lemma_SR hpb hsb
          cases R2 with
          | nf m2 => exact Nat.le_trans hsr1 hR2.2
          | cls Y =>
            cases L2 with
            | nf m1 =>
              rcases hsr2 haS with e | ⟨h3, _⟩
              · injection e with _ e2
                rw [← e2] at hR2
                exact (typed_apart hT hc heX' hLa hR2).elim
              · exact Nat.le_trans h3 hL2.2
            | cls Y' => exact (Bool.false_ne_true heX').elim

/-! ## Conversion classes given by representatives -/

def slotTm {ι : Type} (rep : ι → Term) : Slot ι → Term
  | .cls i => rep i
  | .nf n => n

/-- The literal head normal form that a type prescribes for the representatives. -/
def tyTm {ι : Type} (rep : ι → Term) : Ty ι → Term
  | .one i => S ⬝ rep i
  | .two L R => S ⬝ slotTm rep L ⬝ slotTm rep R

/-- A normalizing slot holds a closed term with a normal form of leaf count at most `M`. -/
def SlotOk {ι : Type} (M : Nat) : Slot ι → Prop
  | .cls _ => True
  | .nf n => PureS n ∧ ∃ m, WSteps n m ∧ Normal m ∧ sz m ≤ M

def TyOk {ι : Type} (M : Nat) : Ty ι → Prop
  | .one _ => True
  | .two L R => SlotOk M L ∧ SlotOk M R

theorem slotok_cls {ι : Type} {M : Nat} {i : ι} : SlotOk M (Slot.cls i) := trivial

theorem slotok_nf {ι : Type} {M : Nat} {n m : Term} (hn : PureS n) (h1 : WSteps n m)
    (h2 : Normal m) (h3 : sz m ≤ M) : SlotOk (ι := ι) M (Slot.nf n) := ⟨hn, m, h1, h2, h3⟩

theorem tyok_one {ι : Type} {M : Nat} {i : ι} : TyOk M (Ty.one i) := trivial

theorem tyok_two {ι : Type} {M : Nat} {L R : Slot ι} (hL : SlotOk M L) (hR : SlotOk M R) :
    TyOk M (Ty.two L R) := ⟨hL, hR⟩

/-- The conversion classes of representatives that are convertible to the literal head normal
forms prescribed by their types form a typed system (S6 Lemma 4, proof; Church–Rosser; size). -/
theorem typed_of_reps {ι : Type} {M : Nat} (ty : ι → Ty ι) (rep : ι → Term)
    (hrep : ∀ X, PureS (rep X)) (hok : ∀ X, TyOk M (ty X))
    (hconv : ∀ X, Convertible (rep X) (tyTm rep (ty X))) :
    Typed M ty (fun X t => PureS t ∧ Convertible t (rep X)) := by
  have slot_pure : ∀ L : Slot ι, SlotOk M L → PureS (slotTm rep L) := by
    intro L h
    cases L with
    | cls i => exact hrep i
    | nf n => exact h.1
  have slot_in : ∀ (L : Slot ι) (a : Term), SlotOk M L → PureS a →
      Convertible a (slotTm rep L) →
      InS M (fun X t => PureS t ∧ Convertible t (rep X)) L a := by
    intro L a h hpa hca
    cases L with
    | cls i => exact ⟨hpa, hca⟩
    | nf n =>
      obtain ⟨_, m, h1, h2, h3⟩ := h
      have hca' : Convertible a n := hca
      obtain ⟨c, h4, h5⟩ := conv_iff_join.mp hca'
      have hm : WSteps a m := h4.trans (wsteps_to_normal h5 h1 h2)
      exact ⟨⟨m, hm, h2⟩, Nat.le_trans (sz_wsteps hpa hm) h3⟩
  rintro X t ⟨ht, hc⟩
  refine ⟨ht, ?_⟩
  have h1 := hconv X
  have h2 := hok X
  cases hty : ty X with
  | one J =>
    rw [hty] at h1
    have h1' : Convertible (rep X) (S ⬝ rep J) := h1
    obtain ⟨c, e, cc⟩ := hnf1_conv ht (hrep J) (hc.trans h1')
    have hpc : PureS c := by
      rw [e] at ht
      exact ht.app_inv.2
    show ∃ c, Steps t (S ⬝ c) ∧ (PureS c ∧ Convertible c (rep J))
    exact ⟨c, by rw [e]; exact .refl _, hpc, cc⟩
  | two L R =>
    rw [hty] at h1 h2
    have h1' : Convertible (rep X) (S ⬝ slotTm rep L ⬝ slotTm rep R) := h1
    have h2' : SlotOk M L ∧ SlotOk M R := h2
    obtain ⟨a, b, hs, ca, cb⟩ :=
      hnf2_conv ht (slot_pure L h2'.1) (slot_pure R h2'.2) (hc.trans h1')
    have hpab := steps_pure ht hs
    show ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ InS M _ L a ∧ InS M _ R b
    exact ⟨a, b, hs, slot_in L a h2'.1 hpab.app_inv.1.app_inv.2 ca,
      slot_in R b h2'.2 hpab.app_inv.2 cb⟩

/-- No family of closed S-terms `rep X` satisfies the conversions prescribed by an easy scheme in
which every type has a class entry. -/
theorem ncfp_scheme {ι : Type} {M : Nat} (ty : ι → Ty ι) (rep : ι → Term)
    (hrep : ∀ X, PureS (rep X)) (hok : ∀ X, TyOk M (ty X))
    (hconv : ∀ X, Convertible (rep X) (tyTm rep (ty X)))
    (hc : ∀ X, (ty X).hasCls = true) (he : ∀ X, easy ty (ty X) = true) (X₀ : ι) : False :=
  thm_T0 (typed_of_reps ty rep hrep hok hconv) hc he X₀ (rep X₀) ⟨hrep X₀, .refl _⟩

/-! ## The two-hole shapes of depth 2 (N6–N10) -/

/-- Three class symbols. -/
inductive C3 where
  | A | B | C

/-- Theorem N6, the equation: `p` is not convertible to `S (S p p) n`. -/
theorem no_S_Spp_n {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ p) ⬝ n) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  refine ncfp_scheme (ι := Bool) (M := sz nfn)
    (fun X => match X with | true => .two (.cls false) (.nf n) | false => .two (.cls true) (.cls true))
    (fun X => match X with | true => p | false => S ⬝ p ⬝ p)
    ?_ ?_ ?_ ?_ ?_ true
  · intro X
    cases X
    · exact (.app (.app .S hp) hp)
    · exact hp
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two slotok_cls (slotok_nf hn hn1 hn2 (Nat.le_refl _))
  · intro X
    cases X
    · exact Convertible.refl _
    · exact hc
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N7, the equation: `p` is not convertible to `S n (S p p)`. -/
theorem no_S_n_Spp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ n ⬝ (S ⬝ p ⬝ p)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  refine ncfp_scheme (ι := Bool) (M := sz nfn)
    (fun X => match X with | true => .two (.nf n) (.cls false) | false => .two (.cls true) (.cls true))
    (fun X => match X with | true => p | false => S ⬝ p ⬝ p)
    ?_ ?_ ?_ ?_ ?_ true
  · intro X
    cases X
    · exact (.app (.app .S hp) hp)
    · exact hp
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two (slotok_nf hn hn1 hn2 (Nat.le_refl _)) slotok_cls
  · intro X
    cases X
    · exact Convertible.refl _
    · exact hc
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N8, the equation: `p` is not convertible to `S (S p) (S n p)`. -/
theorem no_S_Sp_Snp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p) ⬝ (S ⬝ n ⬝ p)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  refine ncfp_scheme (ι := C3) (M := sz nfn)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .one .A | .C => .two (.nf n) (.cls .A))
    (fun X => match X with | .A => p | .B => S ⬝ p | .C => S ⬝ n ⬝ p)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app .S hp)
    · exact (.app (.app .S hn) hp)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_one
    · exact tyok_two (slotok_nf hn hn1 hn2 (Nat.le_refl _)) slotok_cls
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N9, the equation: `p` is not convertible to `S (S n p) (S p m)`. -/
theorem no_S_Snp_Spm {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ p ⬝ m)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  obtain ⟨nfm, hm1, hm2⟩ := hmm
  refine ncfp_scheme (ι := C3) (M := sz nfn + sz nfm)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .two (.nf n) (.cls .A) | .C => .two (.cls .A) (.nf m))
    (fun X => match X with | .A => p | .B => S ⬝ n ⬝ p | .C => S ⬝ p ⬝ m)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app (.app .S hn) hp)
    · exact (.app (.app .S hp) hm)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two (slotok_nf hn hn1 hn2 (Nat.le_add_right _ _)) slotok_cls
    · exact tyok_two slotok_cls (slotok_nf hm hm1 hm2 (Nat.le_add_left _ _))
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N10 (1), the equation: `p` is not convertible to `S (S p) (S p n)`. -/
theorem no_S_Sp_Spn {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p) ⬝ (S ⬝ p ⬝ n)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  refine ncfp_scheme (ι := C3) (M := sz nfn)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .one .A | .C => .two (.cls .A) (.nf n))
    (fun X => match X with | .A => p | .B => S ⬝ p | .C => S ⬝ p ⬝ n)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app .S hp)
    · exact (.app (.app .S hp) hn)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_one
    · exact tyok_two slotok_cls (slotok_nf hn hn1 hn2 (Nat.le_refl _))
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N10 (2), the equation: `p` is not convertible to `S (S n p) (S p)`. -/
theorem no_S_Snp_Sp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ p)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  refine ncfp_scheme (ι := C3) (M := sz nfn)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .two (.nf n) (.cls .A) | .C => .one .A)
    (fun X => match X with | .A => p | .B => S ⬝ n ⬝ p | .C => S ⬝ p)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app (.app .S hn) hp)
    · exact (.app .S hp)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two (slotok_nf hn hn1 hn2 (Nat.le_refl _)) slotok_cls
    · exact tyok_one
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N10 (3), the equation: `p` is not convertible to `S (S p n) (S p)`. -/
theorem no_S_Spn_Sp {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ p)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  refine ncfp_scheme (ι := C3) (M := sz nfn)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .two (.cls .A) (.nf n) | .C => .one .A)
    (fun X => match X with | .A => p | .B => S ⬝ p ⬝ n | .C => S ⬝ p)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app (.app .S hp) hn)
    · exact (.app .S hp)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two slotok_cls (slotok_nf hn hn1 hn2 (Nat.le_refl _))
    · exact tyok_one
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N10 (4), the equation: `p` is not convertible to `S (S n p) (S m p)`. -/
theorem no_S_Snp_Smp {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ n ⬝ p) ⬝ (S ⬝ m ⬝ p)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  obtain ⟨nfm, hm1, hm2⟩ := hmm
  refine ncfp_scheme (ι := C3) (M := sz nfn + sz nfm)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .two (.nf n) (.cls .A) | .C => .two (.nf m) (.cls .A))
    (fun X => match X with | .A => p | .B => S ⬝ n ⬝ p | .C => S ⬝ m ⬝ p)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app (.app .S hn) hp)
    · exact (.app (.app .S hm) hp)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two (slotok_nf hn hn1 hn2 (Nat.le_add_right _ _)) slotok_cls
    · exact tyok_two (slotok_nf hm hm1 hm2 (Nat.le_add_left _ _)) slotok_cls
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N10 (5), the equation: `p` is not convertible to `S (S p n) (S m p)`. -/
theorem no_S_Spn_Smp {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ m ⬝ p)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  obtain ⟨nfm, hm1, hm2⟩ := hmm
  refine ncfp_scheme (ι := C3) (M := sz nfn + sz nfm)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .two (.cls .A) (.nf n) | .C => .two (.nf m) (.cls .A))
    (fun X => match X with | .A => p | .B => S ⬝ p ⬝ n | .C => S ⬝ m ⬝ p)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app (.app .S hp) hn)
    · exact (.app (.app .S hm) hp)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two slotok_cls (slotok_nf hn hn1 hn2 (Nat.le_add_right _ _))
    · exact tyok_two (slotok_nf hm hm1 hm2 (Nat.le_add_left _ _)) slotok_cls
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-- Theorem N10 (6), the equation: `p` is not convertible to `S (S p n) (S p m)`. -/
theorem no_S_Spn_Spm {p n m : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) (hm : PureS m) (hmm : Normalizing m) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ n) ⬝ (S ⬝ p ⬝ m)) := by
  intro hc
  obtain ⟨nfn, hn1, hn2⟩ := hnn
  obtain ⟨nfm, hm1, hm2⟩ := hmm
  refine ncfp_scheme (ι := C3) (M := sz nfn + sz nfm)
    (fun X => match X with | .A => .two (.cls .B) (.cls .C) | .B => .two (.cls .A) (.nf n) | .C => .two (.cls .A) (.nf m))
    (fun X => match X with | .A => p | .B => S ⬝ p ⬝ n | .C => S ⬝ p ⬝ m)
    ?_ ?_ ?_ ?_ ?_ .A
  · intro X
    cases X
    · exact hp
    · exact (.app (.app .S hp) hn)
    · exact (.app (.app .S hp) hm)
  · intro X
    cases X
    · exact tyok_two slotok_cls slotok_cls
    · exact tyok_two slotok_cls (slotok_nf hn hn1 hn2 (Nat.le_add_right _ _))
    · exact tyok_two slotok_cls (slotok_nf hm hm1 hm2 (Nat.le_add_left _ _))
  · intro X
    cases X
    · exact hc
    · exact Convertible.refl _
    · exact Convertible.refl _
  · intro X
    cases X <;> rfl
  · intro X
    cases X <;> rfl

/-! ## Theorem N11 -/

/-- **Theorem N11.**  Let `A`, `B`, `C` be sets of closed S-terms such that every member of `A`
has, on its head run, a two-item head normal form `S a b` with `a ∈ B` and `b` normalizing of leaf
count at most `M`; every member of `B` a two-item head normal form `S a b` with `a ∈ A`, `b ∈ C`;
and every member of `C` is `S c` with `c ∈ A`.  Then `A` is empty.  (Its scheme is not easy: the
exception in `B` is handled by the predecessor-free frame `S (S S) (S c) S`.)  Uses
`HeadRec.no_ground_loop` through the pigeonhole. -/
theorem thm_N11 {M : Nat} {A B C : Term → Prop}
    (hA : ∀ t, A t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ B a ∧ Normalizing b ∧ sz b ≤ M)
    (hB : ∀ t, B t → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧ A a ∧ C b)
    (hC : ∀ t, C t → ∃ c, t = S ⬝ c ∧ A c) : ∀ t, ¬ A t := by
  have notBSS : ¬ B (S ⬝ S) := by
    intro h
    obtain ⟨_, a, b, hs, _, _⟩ := hB _ h
    have e := InfNF.steps_from_hnf (.inr (.inl ⟨S, rfl⟩)) hs
    injection e with e1 _
    cases e1
  have hdesc : ∀ {t a b : Term}, Steps t (S ⬝ a ⬝ b) → Desc t a :=
    fun hs => ⟨_, hs.weak, .left _ (.right S .refl)⟩
  have key : ∀ (k : Nat) (t : Term), sz t ≤ k → (A t ∨ B t) →
      (∀ t₃, (A t₃ ∨ B t₃) → Desc t t₃ → M < sz t₃) → False := by
    intro k
    induction k with
    | zero =>
      intro t h _ _
      have := sz_pos t
      omega
    | succ k ih =>
      intro t hsz hU hbig
      rcases hU with hAt | hBt
      · obtain ⟨ht, a, b, hs, ha, _, hbM⟩ := hA t hAt
        have hDa := hdesc hs
        have hbiga := hbig a (.inr ha) hDa
        rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
        · have hlt : sz a < sz t := by
            rw [e]
            exact Nat.lt_trans (sz_arg_lt S a) (sz_fun_lt _ b)
          exact ih a (by omega) (.inr ha) (fun t₃ h1 h2 => hbig t₃ h1 (hDa.trans h2))
        · obtain ⟨y, _, eb⟩ := lemma_L' ht hs ne
          have h1 := sz_arg_lt y a
          rw [← eb] at h1
          omega
      · obtain ⟨ht, a, b, hs, ha, hb⟩ := hB t hBt
        obtain ⟨c, ec, _⟩ := hC b hb
        have hDa := hdesc hs
        have down : sz a < sz t → False := fun hlt =>
          ih a (by omega) (.inl ha) (fun t₃ h1 h2 => hbig t₃ h1 (hDa.trans h2))
        rcases Decidable.em (t = S ⬝ a ⬝ b) with e | ne
        · exact down (by rw [e]; exact Nat.lt_trans (sz_arg_lt S a) (sz_fun_lt _ b))
        · obtain ⟨y, eR, _, hcase⟩ := lemma_TD ht (plus_of_steps_ne hs ne)
          have ey : y = S := by
            rw [ec] at eR
            injection eR with e1 _
            exact e1.symm
          rcases hcase with ⟨tm, e, _⟩ | ⟨x, p, q, hfr, _, ea, hφ⟩
          · exact down (by rw [e]; exact sz_arg_lt tm a)
          · rw [ey] at hφ
            have hpfr := steps_pure ht hfr
            have hpxq : PureS (x ⬝ q) := .app hpfr.app_inv.1.app_inv.1.app_inv.2 hpfr.app_inv.2
            rcases Decidable.em (x ⬝ q = S ⬝ S ⬝ S) with e' | ne'
            · injection e' with e1 e2
              rw [e1, e2] at hfr
              rw [e2] at ea
              -- `a = p S` is a member of `A`; it is literal, or it has a small first item
              obtain ⟨hpa, a₁, b₁, hs1, ha₁, _, hb₁⟩ := hA a ha
              have hDa₁ : Desc t a₁ := hDa.trans (hdesc hs1)
              have hbig₁ := hbig a₁ (.inr ha₁) hDa₁
              rcases Decidable.em (a = S ⬝ a₁ ⬝ b₁) with el | nl
              · rw [ea] at el
                injection el with e3 _
                rw [e3] at hfr
                have hlit : t = S ⬝ (S ⬝ S) ⬝ (S ⬝ a₁) ⬝ S := by
                  rcases steps_last hfr with e | ⟨t'', h1, s⟩
                  · exact e
                  · exfalso
                    obtain ⟨u, l, eu⟩ := step_app s
                    have hpu := steps_pure ht h1
                    rw [eu] at s hpu
                    rcases step_inv hpu.app_inv.1 s with ⟨u', s', e⟩ | ⟨f, g, _, e⟩
                    · injection e with e4 _
                      rw [← e4] at s'
                      obtain ⟨y₀, _, e5⟩ := step_to_S2 hpu.app_inv.1 s'
                      injection e5 with e6 e7
                      rw [e7] at ha₁
                      exact notBSS ha₁
                    · injection e with _ e4
                      cases e4
                have hlt : sz a₁ < sz t := by
                  rw [hlit]
                  have h1 : sz (S ⬝ (S ⬝ S) ⬝ (S ⬝ a₁) ⬝ S) = 1 + (1 + 1) + (1 + sz a₁) + 1 := rfl
                  omega
                exact ih a₁ (by omega) (.inr ha₁) (fun t₃ h1 h2 => hbig t₃ h1 (hDa₁.trans h2))
              · obtain ⟨y₁, _, eb₁⟩ := lemma_L' hpa hs1 nl
                have h1 := sz_arg_lt y₁ a₁
                rw [← eb₁] at h1
                omega
            · obtain ⟨y'', _, e'⟩ := lemma_L' hpxq hφ ne'
              cases e'
  have none : ∀ t, ¬ (A t ∨ B t) := by
    refine finite_descent_nn (B := M) (D := Desc) ?_ (fun h1 h2 => Desc.trans h1 h2) ?_ ?_
    · rintro t (h | h)
      · exact (hA t h).1
      · exact (hB t h).1
    · rintro t (h | h)
      · exact Desc.irrefl (hA t h).1
      · exact Desc.irrefl (hB t h).1
    · intro t hU hno
      refine key (sz t) t (Nat.le_refl _) hU (fun t₃ h1 h2 => ?_)
      rcases Nat.lt_or_ge M (sz t₃) with h | h
      · exact h
      · exact absurd ⟨t₃, h1, h2, h⟩ hno
  exact fun t h => none t (.inl h)

/-- Theorem N11, the equation: `p` is not convertible to `S (S p (S p)) n`, for every closed
normalizing `n`. -/
theorem no_S_SpSp_n {p n : Term} (hp : PureS p) (hn : PureS n) (hnn : Normalizing n) :
    ¬ Convertible p (S ⬝ (S ⬝ p ⬝ (S ⬝ p)) ⬝ n) := by
  intro hc
  obtain ⟨nf, hnnf, hnf⟩ := hnn
  have hpB : PureS (S ⬝ p ⬝ (S ⬝ p)) := .app (.app .S hp) (.app .S hp)
  have hA : ∀ t, (PureS t ∧ Convertible t p) → PureS t ∧ ∃ a b, Steps t (S ⬝ a ⬝ b) ∧
      (PureS a ∧ Convertible a (S ⬝ p ⬝ (S ⬝ p))) ∧ Normalizing b ∧ sz b ≤ sz nf := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, m, hs, hpa, ca, hm, hsz⟩ := hnf2_conv_right ht hpB hn hnnf hnf (hct.trans hc)
    exact ⟨ht, a, m, hs, ⟨hpa, ca⟩, hm, hsz⟩
  have hB : ∀ t, (PureS t ∧ Convertible t (S ⬝ p ⬝ (S ⬝ p))) → PureS t ∧ ∃ a b,
      Steps t (S ⬝ a ⬝ b) ∧ (PureS a ∧ Convertible a p) ∧ (PureS b ∧ Convertible b (S ⬝ p)) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨a, b, hs, ca, cb⟩ := hnf2_conv ht hp (.app .S hp) hct
    have hpab := steps_pure ht hs
    exact ⟨ht, a, b, hs, ⟨hpab.app_inv.1.app_inv.2, ca⟩, ⟨hpab.app_inv.2, cb⟩⟩
  have hC : ∀ t, (PureS t ∧ Convertible t (S ⬝ p)) → ∃ c, t = S ⬝ c ∧
      (PureS c ∧ Convertible c p) := by
    rintro t ⟨ht, hct⟩
    obtain ⟨c, e, cc⟩ := hnf1_conv ht hp hct
    have hpc : PureS c := by
      rw [e] at ht
      exact ht.app_inv.2
    exact ⟨c, e, hpc, cc⟩
  exact thm_N11 (M := sz nf) (A := fun t => PureS t ∧ Convertible t p)
    (B := fun t => PureS t ∧ Convertible t (S ⬝ p ⬝ (S ⬝ p)))
    (C := fun t => PureS t ∧ Convertible t (S ⬝ p)) hA hB hC p ⟨hp, Convertible.refl p⟩

end Ncfp
