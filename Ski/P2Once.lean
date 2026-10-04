import Ski.P2Complete

/-!
# The verifiers with the Poseidon2 jet call it exactly once

The proof's public level table counts the jet's calls (`Circuit.idxPub`),
so the count must not depend on the witness.  For `p2pre h` and
`p2commit c pat` it does not: every accepted table has exactly one jet row
(`p2pre_once`, `p2commit_once`).

The argument is about the terms the rows read back as.  The verifier is
`S (K K) g`, `g = J ⬝ CHECK_h` or `S (J ⬝ CHECK_c) PAT`; the run starts from
`S (K K) g ⬝ β ⬝ w` and passes through the frame
`S (K K) g b w → K K b u w → K u w → u`, `u` the jet's part `g ⬝ b` as it
reduces (`Outer`).  Every plain step keeps the term in the frame, every
term in it holds `J`, and a jet row in it fires the jet with a continuation
and remaining arguments free of `J`; the jet's result is then free of `J`,
and stays so.  The run ends at `K`, free of `J`: so it fired the jet once.
-/

open Term Compose CompM ComposedPText Poseidon2SKI

namespace P2Once

open Mach Stmt Wit

/-- `J` does not occur. -/
def Free (J : Nat) (t : OTerm) : Prop := ¬ Occ J t

theorem free_app {J : Nat} {f a : OTerm} (hf : Free J f) (ha : Free J a) : Free J (f ⬝ₒ a) := fun h => by
  cases h with
  | left _ h => exact hf h
  | right _ h => exact ha h

theorem free_left {J : Nat} {f a : OTerm} (h : Free J (f ⬝ₒ a)) : Free J f := fun h' => h (.left a h')
theorem free_right {J : Nat} {f a : OTerm} (h : Free J (f ⬝ₒ a)) : Free J a := fun h' => h (.right f h')

theorem free_K (J : Nat) : Free J .K := fun h => nomatch h

theorem free_toO (J : Nat) (t : Term) : Free J t.toO := fun h => Nat.not_lt_zero _ (fresh_toO t 0 J h)

theorem free_step {J : Nat} {t u : OTerm} (ht : Free J t) (h : OWStep t u) : Free J u := fun hu => ht (h.occ hu)

theorem free_steps {J : Nat} {t u : OTerm} (ht : Free J t) (h : OWSteps t u) : Free J u := by
  induction h with
  | refl _ => exact ht
  | step h _ ih => exact ih (free_step ht h)

theorem free_appL {J : Nat} : ∀ {t : OTerm} {as : List OTerm}, Free J t → (∀ x ∈ as, Free J x) → Free J (appL t as)
  | _, [], ht, _ => ht
  | t, a :: as, ht, ha => free_appL (t := t ⬝ₒ a) (as := as) (free_app ht (ha a List.mem_cons_self))
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-- The head of an application. -/
def headO : OTerm → OTerm
  | .app f _ => headO f
  | t => t

/-- The number of arguments at the head. -/
def nargs : OTerm → Nat
  | .app f _ => nargs f + 1
  | _ => 0

theorem headO_appL : ∀ (t : OTerm) (as : List OTerm), headO (appL t as) = headO t
  | _, [] => rfl
  | t, a :: as => headO_appL (t ⬝ₒ a) as

theorem nargs_appL : ∀ (t : OTerm) (as : List OTerm), nargs (appL t as) = nargs t + as.length
  | _, [] => rfl
  | t, a :: as => by
    show nargs (appL (t ⬝ₒ a) as) = _
    rw [nargs_appL (t ⬝ₒ a) as, List.length_cons]
    show nargs t + 1 + as.length = _
    omega

theorem occ_head {J : Nat} : ∀ {t : OTerm}, headO t = .var J → Occ J t
  | .var _, h => by cases h; exact .var _
  | .app f a, h => .left a (occ_head (t := f) h)
  | .S, h => nomatch h
  | .K, h => nomatch h
  | .I, h => nomatch h

/-- **The frame**: `S (K K) g b w`, `K K b u w`, `K u w`, `u`, the free
    parts free of `J`, `g` a jet's part `G` and `u` its applied form `U`. -/
inductive Outer (J : Nat) (G U : OTerm → Prop) : OTerm → Prop
  | o0 {g b w : OTerm} : G g → Free J b → Free J w → Outer J G U (.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g ⬝ₒ b ⬝ₒ w)
  | o1 {b u w : OTerm} : Free J b → U u → Free J w → Outer J G U (.K ⬝ₒ .K ⬝ₒ b ⬝ₒ u ⬝ₒ w)
  | o2 {u w : OTerm} : U u → Free J w → Outer J G U (.K ⬝ₒ u ⬝ₒ w)
  | o3 {u : OTerm} : U u → Outer J G U u

/-- What a jet's part must satisfy for the frame to call the jet once. -/
structure Part (J : Nat) (G U : OTerm → Prop) : Prop where
  gstep : ∀ {g g'}, G g → OWStep g g' → G g'
  gapp : ∀ {g b}, G g → Free J b → U (g ⬝ₒ b)
  ustep : ∀ {u u'}, U u → OWStep u u' → U u'
  gocc : ∀ {g}, G g → Occ J g
  uocc : ∀ {u}, U u → Occ J u
  ujet : ∀ {k β R}, U (appL (.var J) (k :: β :: R)) → Free J k ∧ ∀ x ∈ R, Free J x

theorem owstep_KK {u : OTerm} (h : OWStep (.K ⬝ₒ .K) u) : False := by
  cases h with
  | left _ h => nomatch h
  | right _ h => nomatch h

section
variable {J : Nat} {G U : OTerm → Prop} (hp : Part J G U)
include hp

theorem outer_step {t u : OTerm} (ht : Outer J G U t) (hs : OWStep t u) : Outer J G U u := by
  cases ht with
  | o0 hg hb hw =>
    cases hs with
    | left _ hs =>
      cases hs with
      | S => exact .o1 hb (hp.gapp hg hb) hw
      | left _ hs =>
        cases hs with
        | left _ hs =>
          cases hs with
          | left _ hs => nomatch hs
          | right _ hs => exact (owstep_KK hs).elim
        | right _ hs => exact .o0 (hp.gstep hg hs) hb hw
      | right _ hs => exact .o0 hg (free_step hb hs) hw
    | right _ hs => exact .o0 hg hb (free_step hw hs)
  | o1 hb hu hw =>
    cases hs with
    | left _ hs =>
      cases hs with
      | left _ hs =>
        cases hs with
        | K => exact .o2 hu hw
        | left _ hs => exact (owstep_KK hs).elim
        | right _ hs => exact .o1 (free_step hb hs) hu hw
      | right _ hs => exact .o1 hb (hp.ustep hu hs) hw
    | right _ hs => exact .o1 hb hu (free_step hw hs)
  | o2 hu hw =>
    cases hs with
    | K => exact .o3 hu
    | left _ hs =>
      cases hs with
      | left _ hs => nomatch hs
      | right _ hs => exact .o2 (hp.ustep hu hs) hw
    | right _ hs => exact .o2 hu (free_step hw hs)
  | o3 hu => exact .o3 (hp.ustep hu hs)

theorem outer_steps {t u : OTerm} (ht : Outer J G U t) (hs : OWSteps t u) : Outer J G U u := by
  induction hs with
  | refl _ => exact ht
  | step h _ ih => exact ih (outer_step hp ht h)

theorem outer_occ {t : OTerm} (ht : Outer J G U t) : Occ J t := by
  cases ht with
  | o0 hg _ _ => exact .left _ (.left _ (.right _ (hp.gocc hg)))
  | o1 _ hu _ => exact .left _ (.right _ (hp.uocc hu))
  | o2 hu _ => exact .left _ (.right _ (hp.uocc hu))
  | o3 hu => exact hp.uocc hu

/-- **A jet row in the frame**: the continuation and the remaining
    arguments are free of `J`. -/
theorem outer_jet {k β : OTerm} {R : List OTerm} (ht : Outer J G U (appL (.var J) (k :: β :: R))) :
    Free J k ∧ ∀ x ∈ R, Free J x := by
  have hh := headO_appL (.var J) (k :: β :: R)
  generalize e : appL (.var J) (k :: β :: R) = t at ht hh
  cases ht with
  | o0 => nomatch hh
  | o1 => nomatch hh
  | o2 => nomatch hh
  | o3 hu => subst e; exact hp.ujet hu

end

-- ---------------------------------------------------------------------------
-- The two statements' jet parts
-- ---------------------------------------------------------------------------

theorem mem_false_of_free {x : Nat} : ∀ {t : OTerm}, Free x t → t.mem x = false
  | .S, _ => rfl
  | .K, _ => rfl
  | .I, _ => rfl
  | .var y, h => by
    show (y == x) = false
    cases hyx : y == x
    · rfl
    · exact absurd (by rw [beq_iff_eq.1 hyx]; exact Occ.var x) h
  | .app f a, h => by
    show (f.mem x || a.mem x) = false
    rw [mem_false_of_free (free_left h), mem_false_of_free (free_right h)]; rfl

/-- `p2pre`'s: `g = J ⬝ c`, applied `J ⬝ c ⬝ b`. -/
def GP (J : Nat) (g : OTerm) : Prop := ∃ c, Free J c ∧ g = .var J ⬝ₒ c
def UP (J : Nat) (u : OTerm) : Prop := ∃ c b, Free J c ∧ Free J b ∧ u = .var J ⬝ₒ c ⬝ₒ b

theorem partP (J : Nat) : Part J (GP J) (UP J) where
  gstep := by
    rintro _ _ ⟨c, hc, rfl⟩ hs
    cases hs with
    | left _ hs => nomatch hs
    | right _ hs => exact ⟨_, free_step hc hs, rfl⟩
  gapp := by
    rintro _ b ⟨c, hc, rfl⟩ hb
    exact ⟨c, b, hc, hb, rfl⟩
  ustep := by
    rintro _ _ ⟨c, b, hc, hb, rfl⟩ hs
    cases hs with
    | left _ hs =>
      cases hs with
      | left _ hs => nomatch hs
      | right _ hs => exact ⟨_, b, free_step hc hs, hb, rfl⟩
    | right _ hs => exact ⟨c, _, hc, free_step hb hs, rfl⟩
  gocc := by
    rintro _ ⟨c, _, rfl⟩
    exact .left _ (.var _)
  uocc := by
    rintro _ ⟨c, b, _, _, rfl⟩
    exact .left _ (.left _ (.var _))
  ujet := by
    rintro k β R ⟨c, b, hc, _, e⟩
    have hn := congrArg nargs e
    rw [nargs_appL] at hn
    match R, hn with
    | [], _ =>
      have e' : OTerm.var J ⬝ₒ k ⬝ₒ β = .var J ⬝ₒ c ⬝ₒ b := e
      injection e' with e1 _
      injection e1 with _ e2
      exact ⟨e2 ▸ hc, fun _ hx => nomatch hx⟩
    | _ :: R, hn =>
      have : nargs (OTerm.var J) + (R.length + 3) = 2 := hn
      exact absurd this (by omega)

/-- `p2commit`'s: `g = S (J ⬝ c) p`, applied `S (J ⬝ c) p b`, which
    reduces to `J ⬝ c ⬝ b ⬝ (p ⬝ b)`. -/
def GC (J : Nat) (g : OTerm) : Prop := ∃ c p, Free J c ∧ Free J p ∧ g = .S ⬝ₒ (.var J ⬝ₒ c) ⬝ₒ p
def UC (J : Nat) (u : OTerm) : Prop :=
  (∃ c p b, Free J c ∧ Free J p ∧ Free J b ∧ u = .S ⬝ₒ (.var J ⬝ₒ c) ⬝ₒ p ⬝ₒ b) ∨
    (∃ c b x, Free J c ∧ Free J b ∧ Free J x ∧ u = .var J ⬝ₒ c ⬝ₒ b ⬝ₒ x)

theorem partC (J : Nat) : Part J (GC J) (UC J) where
  gstep := by
    rintro _ _ ⟨c, p, hc, hp, rfl⟩ hs
    cases hs with
    | left _ hs =>
      cases hs with
      | left _ hs => nomatch hs
      | right _ hs =>
        cases hs with
        | left _ hs => nomatch hs
        | right _ hs => exact ⟨_, p, free_step hc hs, hp, rfl⟩
    | right _ hs => exact ⟨c, _, hc, free_step hp hs, rfl⟩
  gapp := by
    rintro _ b ⟨c, p, hc, hp, rfl⟩ hb
    exact .inl ⟨c, p, b, hc, hp, hb, rfl⟩
  ustep := by
    rintro _ _ (⟨c, p, b, hc, hp, hb, rfl⟩ | ⟨c, b, x, hc, hb, hx, rfl⟩) hs
    · cases hs with
      | S => exact .inr ⟨c, b, p ⬝ₒ b, hc, hb, free_app hp hb, rfl⟩
      | left _ hs =>
        cases hs with
        | left _ hs =>
          cases hs with
          | left _ hs => nomatch hs
          | right _ hs =>
            cases hs with
            | left _ hs => nomatch hs
            | right _ hs => exact .inl ⟨_, p, b, free_step hc hs, hp, hb, rfl⟩
        | right _ hs => exact .inl ⟨c, _, b, hc, free_step hp hs, hb, rfl⟩
      | right _ hs => exact .inl ⟨c, p, _, hc, hp, free_step hb hs, rfl⟩
    · cases hs with
      | left _ hs =>
        cases hs with
        | left _ hs =>
          cases hs with
          | left _ hs => nomatch hs
          | right _ hs => exact .inr ⟨_, b, x, free_step hc hs, hb, hx, rfl⟩
        | right _ hs => exact .inr ⟨c, _, x, hc, free_step hb hs, hx, rfl⟩
      | right _ hs => exact .inr ⟨c, b, _, hc, hb, free_step hx hs, rfl⟩
  gocc := by
    rintro _ ⟨c, p, _, _, rfl⟩
    exact .left _ (.right _ (.left _ (.var _)))
  uocc := by
    rintro _ (⟨c, p, b, _, _, _, rfl⟩ | ⟨c, b, x, _, _, _, rfl⟩)
    · exact .left _ (.left _ (.right _ (.left _ (.var _))))
    · exact .left _ (.left _ (.left _ (.var _)))
  ujet := by
    rintro k β R (⟨c, p, b, _, _, _, e⟩ | ⟨c, b, x, hc, _, hx, e⟩)
    · have hh := congrArg headO e
      rw [headO_appL] at hh
      nomatch hh
    · have hn := congrArg nargs e
      rw [nargs_appL] at hn
      match R, hn with
      | [y], _ =>
        have e' : OTerm.var J ⬝ₒ k ⬝ₒ β ⬝ₒ y = .var J ⬝ₒ c ⬝ₒ b ⬝ₒ x := e
        injection e' with e1 e3
        injection e1 with e1 _
        injection e1 with _ e2
        refine ⟨e2 ▸ hc, fun z hz => ?_⟩
        rw [List.mem_singleton] at hz
        rw [hz, e3]; exact hx
      | [], hn => exact absurd hn (by show ¬ (0 + 2 + 0 = 0 + 1 + 1 + 1); omega)
      | _ :: _ :: R, hn =>
        have : nargs (OTerm.var J) + (R.length + 4) = 3 := hn
        exact absurd this (by omega)

theorem checkO_free (h x : Nat) : Free x (checkO h) := Circuit.chkO_closed _ _ x

/-- **`p2pre`'s verifier, abstracted**: `S (K K) (J ⬝ CHECK_h)`. -/
theorem verifierO_eq (h : Nat) : verifierO h = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.var JP2 ⬝ₒ checkO h) := by
  have hc : ∀ x, (checkO h).mem x = false := fun x => mem_false_of_free (checkO_free h x)
  show abs 0 (abs 1 (.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0)) = _
  have m1 : (OTerm.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0).mem 1 = false := by
    show ((JP2 == 1 || (checkO h).mem 1) || (0 == 1)) = false
    rw [hc]; rfl
  rw [abs_of_not_mem m1, abs_app, if_neg (by
    show ¬ ((OTerm.K.mem 0 || ((JP2 == 0 || (checkO h).mem 0) || (0 == 0))) = false)
    rw [hc]; decide), if_neg (fun e => nomatch e.1)]
  show OTerm.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ abs 0 (.var JP2 ⬝ₒ checkO h ⬝ₒ .var 0) = _
  rw [abs_app, if_neg (by
    show ¬ (((JP2 == 0 || (checkO h).mem 0) || (0 == 0)) = false)
    rw [hc]; decide), if_pos ⟨rfl, by show (JP2 == 0 || (checkO h).mem 0) = false; rw [hc]; rfl⟩]

/-- **`p2commit`'s verifier, abstracted**: `S (K K) (S (J ⬝ CHECK_c) PAT)`. -/
theorem verifierC_eq (c : List Nat) (pat : List (Option Bool)) :
    verifierC c pat = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ (.S ⬝ₒ (.var JP2 ⬝ₒ checkC c) ⬝ₒ patO pat) := by
  have hc : ∀ x, (checkC c).mem x = false := fun x => mem_false_of_free (P2Commit.checkC_closed c x)
  have hp : ∀ x, (patO pat).mem x = false := fun x => mem_false_of_free (P2Commit.patO_closed x pat)
  show abs 100 (abs 101 (.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100))) = _
  have m1 : (OTerm.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100)).mem 101 = false := by
    show (((JP2 == 101 || (checkC c).mem 101) || (100 == 101)) || ((patO pat).mem 101 || (100 == 101))) = false
    rw [hc, hp]; rfl
  rw [abs_of_not_mem m1, abs_app, if_neg (by
    show ¬ ((OTerm.K.mem 100 || (((JP2 == 100 || (checkC c).mem 100) || (100 == 100)) ||
      ((patO pat).mem 100 || (100 == 100)))) = false)
    rw [hc, hp]; decide), if_neg (fun e => nomatch e.1)]
  show OTerm.S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ abs 100 (.var JP2 ⬝ₒ checkC c ⬝ₒ .var 100 ⬝ₒ (patO pat ⬝ₒ .var 100)) = _
  rw [abs_app, if_neg (by
    show ¬ ((((JP2 == 100 || (checkC c).mem 100) || (100 == 100)) ||
      ((patO pat).mem 100 || (100 == 100))) = false)
    rw [hc, hp]; decide), if_neg (fun e => nomatch e.1), abs_app, if_neg (by
    show ¬ (((JP2 == 100 || (checkC c).mem 100) || (100 == 100)) = false)
    rw [hc]; decide), if_pos ⟨rfl, by show (JP2 == 100 || (checkC c).mem 100) = false; rw [hc]; rfl⟩,
    abs_app, if_neg (by show ¬ (((patO pat).mem 100 || (100 == 100)) = false); rw [hp]; decide),
    if_pos ⟨rfl, hp 100⟩]

-- ---------------------------------------------------------------------------
-- The run
-- ---------------------------------------------------------------------------

theorem not_outer_K {J : Nat} {G U : OTerm → Prop} (hp : Part J G U) : ¬ Outer J G U .K :=
  fun h => nomatch outer_occ hp h

/-- **A run of one verifier in the frame calls the jet once**: of the rows
    before its end, each a plain row (`sel` false) or a jet row (`sel`
    true), exactly one is a jet row. -/
theorem once_of {ρ : Nat → Bool} {shp : BT} {region : List Cell} {V : OTerm} {J root : Nat}
    {G U : OTerm → Prop} (hp : Part J G U) {g : OTerm} (hg : G g) (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g)
    {bs₀ : List Bool} (hb0 : P2Jet.bitsAt (cMachineO ρ shp region [V]).heap P2Jet.slotAddrs = some bs₀)
    (ho0 : otermAt (cMachineO ρ shp region [V]).heap ((cMachineO ρ shp region [V]).heap.length + 1) root =
      some (combT bs₀).toO)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shp + 3 + i) c = true)
    {M : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (h : AcceptsCP M (cMachineO ρ shp region [V]) [] [] J root (cHeapO ρ shp region [V]).2
      (cHeapO ρ shp region [V]).1.length 1 e row)
    (sel : Nat → Bool)
    (hsel : ∀ i, i < e 0 → (sel i = false ∧ Air.NormRow M [] [] (row i) (row (i + 1))) ∨
      (sel i = true ∧ P2Jet.p2Row M J root (row i) = some (row (i + 1)))) :
    ∃ r0, r0 < e 0 ∧ sel r0 = true ∧ ∀ r, r < e 0 → sel r = true → r = r0 := by
  let N := BT.nleaves shp
  let m0 := cMachineO ρ shp region [V]
  obtain ⟨w, hw⟩ := witnessOf_some (slots_wf ρ N hr) (by simp [slotHeap_length]; omega)
  obtain ⟨_, hdecV⟩ := cMachineO_decode (Vs := [V]) hw
  have hroot := hdecV 0 V rfl
  have hroots : Air.RootsOK m0.heap [] [] := fun _ _ h' => absurd h' List.not_mem_nil
  obtain ⟨hc, hm, _, _⟩ := h.runs hroots 0 Nat.zero_lt_one
  replace hc : (row 0).ctr ≤ M.length := hc
  have hm0 : m0.heap = M.take (row 0).ctr := h.heap0.symm
  have hc0 : (row 0).ctr = m0.heap.length := h.ctr0
  have hr0 : Air.RootsOK (M.take (row 0).ctr) [] [] := fun _ _ h' => absurd h' List.not_mem_nil
  have hlen : (Air.st M (row 0)).heap.length = (row 0).ctr := by
    simp [Air.st, Air.take_length hc]
  have hstart : odecode (Air.st M (row 0)) = some (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) := by
    have e1 : V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO = appL (V ⬝ₒ (fillB shp ρ 0).enc.toO ⬝ₒ w.toO) [] := rfl
    rw [e1]
    apply odecode_of
    · show otermAt (M.take (row 0).ctr) (_ + 1) (row 0).hd = _
      rw [h.hd0]
      rw [hm0] at hroot
      refine Air.otermAt_take (Nat.le_refl _) ?_ hroot
      rw [← hm0, hlen, hc0]
      exact Nat.le_refl _
    · show ostackAt (M.take (row 0).ctr) (_ + 1) (row 0).stk = _
      rw [h.stk0]
      have hn : (M.take (row 0).ctr)[(cHeapO ρ shp region [V]).1.length]? = some .nil := by
        rw [← hm0]; simp [m0, cMachineO]
      unfold ostackAt
      rw [hn]
  have hcombs : ∀ c, (row 0).ctr ≤ c → P2Jet.CombAt (M.take c) root := fun c hcc => by
    have hb' : P2Jet.bitsAt (M.take (row 0).ctr) P2Jet.slotAddrs = some bs₀ := by rw [← hm0]; exact hb0
    have ho' : otermAt (M.take (row 0).ctr) ((M.take (row 0).ctr).length + 1) root = some (combT bs₀).toO := by
      rw [← hm0]; exact ho0
    exact combAt_take hb' ho' hcc
  -- the claim, row by row
  have claim : ∀ b, b ≤ e 0 → ∃ t, odecode (Air.st M (row b)) = some t ∧ (row 0).ctr ≤ (row b).ctr ∧
      (row b).ctr ≤ M.length ∧
      ((Outer J G U t ∧ ∀ i, i < b → sel i = false) ∨
        (Free J t ∧ ∃ r0, r0 < b ∧ sel r0 = true ∧ ∀ i, i < b → sel i = true → i = r0)) := by
    intro b
    induction b with
    | zero =>
      intro _
      refine ⟨_, hstart, Nat.le_refl _, hc, .inl ⟨?_, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩⟩
      rw [hV]
      exact .o0 hg (free_toO J _) (free_toO J _)
    | succ b ih =>
      intro hb
      obtain ⟨t, hdec, hcl, hcu, hph⟩ := ih (Nat.le_of_succ_le hb)
      rcases hsel b hb with ⟨hs, hn⟩ | ⟨hs, hj⟩
      · obtain ⟨h1, h2, hJ, _⟩ := Air.normRow_spec hr0 hcl hcu hn
        obtain ⟨u, hu, hwu⟩ := ojsteps_owsteps hdec hJ
        refine ⟨u, hu, Nat.le_trans hcl h1, h2, ?_⟩
        rcases hph with ⟨ho, hall⟩ | ⟨hf, r0, hr0b, hsr, huniq⟩
        · refine .inl ⟨outer_steps hp ho hwu, fun i hi => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
          · exact hall i hi
          · exact hs
        · refine .inr ⟨free_steps hf hwu, r0, Nat.lt_succ_of_lt hr0b, hsr, fun i hi hsi => ?_⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
          · exact huniq i hi hsi
          · rw [hs] at hsi; cases hsi
      · obtain ⟨a1, a2⟩ := P2Jet.p2Row_ctr_len hj hcu
        obtain ⟨_, Nk, bs, R, _, rfl, hd⟩ := P2Jet.p2Row_step hj hcu (hcombs _ hcl) hdec
        refine ⟨_, hd, Nat.le_trans hcl a1, a2, ?_⟩
        rcases hph with ⟨ho, hall⟩ | ⟨hf, _, _, _, _⟩
        · obtain ⟨hk, hR⟩ := outer_jet hp ho
          refine .inr ⟨free_appL hk (fun x hx => ?_), b, Nat.lt_succ_self _, hs, fun i hi hsi => ?_⟩
          · rcases List.mem_append.1 hx with hx | hx
            · obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
              exact free_toO J _
            · exact hR x hx
          · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
            · rw [hall i hi] at hsi; cases hsi
            · rfl
        · exact absurd (occ_head (headO_appL _ _)) hf
  obtain ⟨t, hdec, _, _, hph⟩ := claim (e 0) (Nat.le_refl _)
  have hK : t = .K := by
    refine odecode_K hdec ?_ ?_
    · rw [← (h.ends 0 Nat.zero_lt_one).1, Air.rd_eq]; rfl
    · rw [← (h.ends 0 Nat.zero_lt_one).2, Air.rd_eq]; rfl
  rcases hph with ⟨ho, _⟩ | ⟨_, r0, hr, hs, hu⟩
  · rw [hK] at ho; exact absurd ho (not_outer_K hp)
  · exact ⟨r0, hr, hs, hu⟩

end P2Once

namespace Circuit

open B Air Compose CompM Stmt Mach Wit P2Once

/-- **An accepted proof of one verifier in the frame has exactly one jet
    row**: its CPU table has exactly one row with `P2SEL = 1`, and `0` on
    every other. -/
theorem compP_once {V : OTerm} {G U : OTerm → Prop} (hp : Part JP2 G U) {g : OTerm} (hg : G g)
    (hV : V = .S ⬝ₒ (.K ⬝ₒ .K) ⬝ₒ g) (hocc : ∀ x, Occ x V → x = JP2)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirsG [V]) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      ∃ r0, r0 < C.h ∧ C.main r0 P2SEL = 1 ∧ ∀ r, r < C.h → r ≠ r0 → C.main r P2SEL = 0 := by
  have hacc' := accepted_transfer hs ((acceptedP_iff_of (compPG_guarded [V]) hs ts).1 hacc)
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ok⟩ := compPOK_ofG hacc'
  refine ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ?_⟩
  have hv : ∀ V' ∈ [V], ∀ x, Occ x V' → x < JP2 + 1 := fun V' hV' x hx => by
    rw [List.mem_singleton.1 hV'] at hx
    rw [hocc x hx]; exact Nat.lt_succ_self _
  have hP : JP2 + 1 < P := by decide
  have hroot : rootP < P := by
    have := ok.heap_lt
    have hfit := cMachineO_fitsB (JP2 + 1) (fun _ => false) shpP (List.replicate 1 .S) [V]
      (fun i c h' => blank_region 1 i c h' _) hv
    have : rootP < (blankMO shpP 1 [V]).heap.length := hfit.2.2
    omega
  have h499 : 499 ≤ (blankMO shpP 1 [V]).heap.length := by
    have := blankO_prefix shpP 1 [V]
    rw [shpP_nleaves] at this
    omega
  have hJ : JP2 < P := by decide
  have hcp := ok.acceptsCP hv (Nat.zero_lt_succ _) hP hJ hroot h499
  have hl : (regionM (memOf Mm) (BT.nleaves shpP) 1).length = (List.replicate 1 Cell.S).length := by
    rw [List.length_replicate]; exact ok.region_len
  obtain ⟨_, hstk, hR, _, _, _⟩ := cMachineO_public (bitsM (memOf Mm)) (fun _ => false) shpP
    (regionM (memOf Mm) (BT.nleaves shpP) 1) (List.replicate 1 .S) [V] hl
  have hroot' : rootP = combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) :=
    combRoot_public _ _ shpP (by rw [hl]; rfl)
  have hroots : blankRootsO shpP 1 [V] = (cHeapO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).2 :=
    hR.symm
  have hnil : (blankMO shpP 1 [V]).stk =
      (cHeapO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).1.length := hstk.symm
  rw [hroot', hroots, hnil] at hcp
  have hwf := ok.regionWF
  obtain ⟨hb0, ho0⟩ := comb_heap (bitsM (memOf Mm)) (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]
  have hend : endRow (rsF C) (C.h - 1) [V].length 0 = C.h - 1 := endRow_last _ _ _ (Nat.zero_lt_succ _)
  have hc := ok.cnt_last
  rw [blankRootsO_length] at hc
  -- the rows before the end: plain, or the jet's
  have hsel : ∀ i, i < endRow (rsF C) (C.h - 1) [V].length 0 →
      (decide (C.main i P2SEL = 1) = false ∧ Air.NormRow (memOf Mm) [] [] (rowOf C i) (rowOf C (i + 1))) ∨
      (decide (C.main i P2SEL = 1) = true ∧
        P2Jet.p2Row (memOf Mm) JP2 (combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1))
          (rowOf C i) = some (rowOf C (i + 1))) := by
    intro i hi
    rw [hend] at hi
    have hrs : rsF C i = 0 := by
      rcases Nat.lt_or_ge (rsF C i) 1 with h1 | h1
      · omega
      · obtain ⟨j, hj, _⟩ := endRow_of_one _ ok.rs_le hc hi (by have := ok.rs_le i; omega)
        exact absurd hj (by show ¬ (j + 1 < 1); omega)
    have hrs' : C.main i RS = 0 := by
      rw [rsF_eq (by omega)] at hrs
      rw [← ofN_val (C.main i RS), hrs]; rfl
    rw [← hroot']
    rcases ok.normRowSel (by omega) hrs' hJ hroot h499 with ⟨h0, hn⟩ | ⟨h1, hj⟩
    · exact .inl ⟨by rw [h0]; decide, hn⟩
    · exact .inr ⟨by rw [h1]; decide, hj⟩
  have hb0' : P2Jet.bitsAt (cMachineO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).heap
      P2Jet.slotAddrs = some ((List.range' 0 496).map (bitsM (memOf Mm))) := hb0
  have ho0' : otermAt (cMachineO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).heap
      ((cMachineO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) [V]).heap.length + 1)
      (combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1)) =
      some (combT ((List.range' 0 496).map (bitsM (memOf Mm)))).toO := ho0
  have hwf' : ∀ i c, (regionM (memOf Mm) (BT.nleaves shpP) 1)[i]? = some c →
      cellOK (BT.nleaves shpP + 3 + i) c = true := hwf
  obtain ⟨r0, hr0, hs0, huniq⟩ := once_of (shp := shpP) hp hg hV hb0' ho0' hwf' hcp _ hsel
  rw [hend] at hr0 huniq
  have huniq' : ∀ r, r < C.h → C.main r P2SEL = 1 → r = r0 := by
    intro r hr hr1
    rcases Nat.lt_or_ge r (C.h - 1) with hlt | hge
    · exact huniq r hlt (decide_eq_true hr1)
    · -- the last row reads `K` at its head, not the jet
      exfalso
      have hrl : r = C.h - 1 := by omega
      have ends := (hcp.ends 0 (Nat.zero_lt_succ _)).1
      rw [hend, ← hrl] at ends
      have hjr := (ok.jetReads hr hr1 hJ hroot).1
      have : rd (memOf Mm) (rowOf C r).ctr (rowOf C r).hd = rd (memOf Mm) (C.main r CTR).val (C.main r HD).val := rfl
      rw [this, hjr] at ends
      cases ends
  refine ⟨r0, by omega, of_decide_eq_true hs0, fun r hr hne => ?_⟩
  -- every other row's selector is clear: it is `0` or `1` by its kind
  obtain ⟨k, hk⟩ := kind_ofP2 ok.cpu hr
  rw [hk.2.2.2]
  split
  · next h12 => exact absurd (huniq' r hr (by rw [hk.2.2.2, if_pos h12])) hne
  · rfl

/-- **A proof of `p2pre h` calls the jet once**: every accepted table has
    exactly one jet row. -/
theorem p2pre_once {h : Nat} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirs h) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      ∃ r0, r0 < C.h ∧ C.main r0 P2SEL = 1 ∧ ∀ r, r < C.h → r ≠ r0 → C.main r P2SEL = 0 :=
  compP_once (partP JP2) ⟨checkO h, checkO_free h JP2, rfl⟩ (verifierO_eq h) (verifierO_occ h) hs hacc

/-- **A proof of `p2commit c pat` calls the jet once.** -/
theorem p2commit_once {c : List Nat} {pat : List (Option Bool)} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirsG [verifierC c pat]) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      ∃ r0, r0 < C.h ∧ C.main r0 P2SEL = 1 ∧ ∀ r, r < C.h → r ≠ r0 → C.main r P2SEL = 0 :=
  compP_once (partC JP2) ⟨checkC c, patO pat, P2Commit.checkC_closed c JP2, P2Commit.patO_closed JP2 pat, rfl⟩
    (verifierC_eq c pat) (P2Commit.verifierC_occ c pat) hs hacc

end Circuit
