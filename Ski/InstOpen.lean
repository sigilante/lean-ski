import Ski.Inst
import Ski.HeapOpen

open Term

/-!
# Supercombinator jets on open terms

`Ski/Inst.lean` licenses an instantiation on closed terms: a state that
reads back as a term steps to one that reads back as a weak reduct.  A
probe runs a term applied to atom markers, which `odecode` reads back as
an open term, its markers variables.  This module carries the licence
over.

**The theorems.**
- `oinst_sound_g`: when the head reads back as `absN xs body`
  substituted by the globals' meanings `ρ`, and each global points to a
  cell reading back as its meaning, an instantiation leaves a state that
  reads back, as an open term, as a weak reduct of the state before.
- `ojsteps_owsteps`: a jetted run (`Mach.JSteps`, whose instantiations
  are licensed on closed cells) from a state that reads back as an open
  term reaches one that reads back as a weak reduct of it.  So a jetted
  probe run is an open weak reduction, which `Probe.owsteps_spine` turns
  into the head reduction the decode relation asks for.
-/

namespace Mach

theorem override_notin : ∀ (ρ : Nat → OTerm) (xs : List Nat) (Ns : List OTerm) (x : Nat),
    x ∉ xs → override ρ xs Ns x = ρ x
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, _ => rfl
  | ρ, y :: ys, N :: Ns, x, hx => by
    show override (upd ρ y N) ys Ns x = ρ x
    rw [override_notin _ ys Ns x (fun h => hx (.tail _ h))]
    unfold upd
    rw [if_neg (fun h => hx (by rw [h]; exact .head _))]

/-- Pointers `ps` hold the open terms `Ns`, one for one. -/
def OPtrsOK (heap : List Cell) (F : Nat) : List Nat → List OTerm → Prop
  | [], [] => True
  | p :: ps, N :: Ns => otermAt heap F p = some N ∧ OPtrsOK heap F ps Ns
  | _, _ => False

theorem override_optr {heap : List Cell} {F : Nat} :
    ∀ (xs : List Nat) (e : Nat → Nat) (ρ : Nat → OTerm) (ps : List Nat) (Ns : List OTerm) (x : Nat),
      x ∈ xs → OPtrsOK heap F ps Ns → ps.length = xs.length →
      otermAt heap F (overrideN e xs ps x) = some (override ρ xs Ns x)
  | [], _, _, _, _, _, hx, _, _ => by cases hx
  | _ :: _, _, _, [], _, _, _, _, hl => by cases hl
  | _ :: _, _, _, _ :: _, [], _, _, hok, _ => by cases hok
  | y :: ys, e, ρ, p :: ps, N :: Ns, x, hx, hok, hl => by
    show otermAt heap F (overrideN (updN e y p) ys ps x) = some (override (upd ρ y N) ys Ns x)
    by_cases hin : x ∈ ys
    · exact override_optr ys _ _ ps Ns x hin hok.2 (Nat.succ.inj hl)
    · rw [overrideN_notin _ ys ps x hin, override_notin _ ys Ns x hin]
      have hxy : x = y := by
        cases hx with
        | head => rfl
        | tail _ h => exact absurd h hin
      subst hxy
      unfold updN upd
      rw [if_pos rfl, if_pos rfl]
      exact hok.1

theorem OPtrsOK.mono {heap : List Cell} {F G : Nat} (hFG : F ≤ G) :
    ∀ {ps : List Nat} {Ns : List OTerm}, OPtrsOK heap F ps Ns → OPtrsOK heap G ps Ns
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨otermAt_mono h.1 hFG, OPtrsOK.mono hFG h.2⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem popN_ospec {heap : List Cell} : ∀ (k : Nat) {s F : Nat} {args : List OTerm} {ps : List Nat}
    {r : Nat}, popN heap k s = some (ps, r) → ostackAt heap F s = some args →
    ∃ Ns rest G, G ≤ F ∧ args = Ns ++ rest ∧ Ns.length = k ∧ ps.length = k ∧
      OPtrsOK heap F ps Ns ∧ ostackAt heap G r = some rest
  | 0, s, F, args, ps, r, hp, hs => by
    cases hp
    exact ⟨[], args, F, Nat.le_refl F, rfl, rfl, rfl, trivial, hs⟩
  | k + 1, s, F, args, ps, r, hp, hs => by
    unfold popN at hp
    cases hc : heap[s]? with
    | none => rw [hc] at hp; cases hp
    | some c =>
      rw [hc] at hp
      cases c with
      | cons x r0 =>
        dsimp only at hp
        cases hq : popN heap k r0 with
        | none => rw [hq] at hp; cases hp
        | some q =>
          obtain ⟨ps0, r1⟩ := q
          rw [hq] at hp
          cases hp
          cases F with
          | zero => unfold ostackAt at hs; cases hs
          | succ f =>
            unfold ostackAt at hs
            rw [hc] at hs
            dsimp only at hs
            cases hx : otermAt heap (f + 1) x with
            | none => rw [hx] at hs; cases hs
            | some tx =>
              cases hr : ostackAt heap f r0 with
              | none => rw [hx, hr] at hs; cases hs
              | some rest0 =>
                rw [hx, hr] at hs
                cases hs
                obtain ⟨Ns, rest, G, hG, he, hlN, hlp, hok, hrest⟩ := popN_ospec k hq hr
                refine ⟨tx :: Ns, rest, G, by omega, by rw [he]; rfl, by simp [hlN], by simp [hlp],
                  ⟨hx, hok.mono (Nat.le_succ f)⟩, hrest⟩
      | _ => cases hp

theorem ibuild_ospec (env : Nat → Nat) (σ : Nat → OTerm) : ∀ (t : OTerm) (h : List Cell),
    (∀ x, Occ x t → otermAt h (h.length + 1) (env x) = some (σ x)) →
    ∃ cs, (ibuild env h t).1 = h ++ cs ∧
      otermAt (ibuild env h t).1 ((ibuild env h t).1.length + 1) (ibuild env h t).2 = some (t.subst σ)
  | .S, h, _ => ⟨[.S], rfl, by simp [ibuild, alloc, otermAt, OTerm.subst]⟩
  | .K, h, _ => ⟨[.K], rfl, by simp [ibuild, alloc, otermAt, OTerm.subst]⟩
  | .I, h, _ => ⟨[.I], rfl, by simp [ibuild, alloc, otermAt, OTerm.subst]⟩
  | .var x, h, henv => ⟨[], by simp [ibuild], by
      show otermAt h (h.length + 1) (env x) = some (σ x)
      exact henv x (Occ.var x)⟩
  | .app f a, h, henv => by
    obtain ⟨cs1, e1, t1⟩ := ibuild_ospec env σ f h (fun x hx => henv x (Occ.left a hx))
    have henv2 : ∀ x, Occ x a →
        otermAt (ibuild env h f).1 ((ibuild env h f).1.length + 1) (env x) = some (σ x) := by
      intro x hx
      rw [e1]
      exact otermAt_grow (henv x (.right f hx)) (by simp)
    obtain ⟨cs2, e2, t2⟩ := ibuild_ospec env σ a (ibuild env h f).1 henv2
    refine ⟨cs1 ++ cs2 ++ [.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2], ?_, ?_⟩
    · show (ibuild env (ibuild env h f).1 a).1 ++ [_] = _
      rw [e2, e1]; simp
    · show otermAt ((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2])
          (((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2]).length + 1)
          (ibuild env (ibuild env h f).1 a).1.length = some ((f.subst σ) ⬝ₒ (a.subst σ))
      rw [length_concat]
      unfold otermAt
      rw [getElem?_concat]
      dsimp only
      have ef : otermAt ((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2])
          ((ibuild env (ibuild env h f).1 a).1.length + 1) (ibuild env h f).2 = some (f.subst σ) := by
        rw [e2, List.append_assoc]
        refine otermAt_grow t1 ?_
        simp
      have ea : otermAt ((ibuild env (ibuild env h f).1 a).1 ++
          [Cell.app (ibuild env h f).2 (ibuild env (ibuild env h f).1 a).2])
          ((ibuild env (ibuild env h f).1 a).1.length + 1) (ibuild env (ibuild env h f).1 a).2 =
          some (a.subst σ) :=
        otermAt_grow t2 (Nat.le_refl _)
      rw [ef, ea]

theorem appL_app : ∀ (t : OTerm) (as bs : List OTerm), appL t (as ++ bs) = appL (appL t as) bs
  | _, [], _ => rfl
  | t, a :: as, bs => appL_app (t ⬝ₒ a) as bs

/-- **Instantiation with globals, on open terms, is weak reduction.** -/
theorem oinst_sound_g {xs : List Nat} {body : OTerm} {genv : Nat → Nat} {ρ : Nat → OTerm}
    {m m' : Mach} {t : OTerm}
    (hglob : ∀ x, Occ x body → x ∉ xs → otermAt m.heap (m.heap.length + 1) (genv x) = some (ρ x))
    (hhd : otermAt m.heap (m.heap.length + 1) m.hd = some ((absN xs body).subst ρ))
    (hdec : odecode m = some t) (hstep : instStepG xs body genv m = some m') :
    ∃ t', odecode m' = some t' ∧ OWSteps t t' := by
  obtain ⟨hdT, args, h1, h2, ht⟩ := odecode_eq hdec
  rw [hhd] at h1
  cases h1
  unfold instStepG at hstep
  cases hp : popN m.heap xs.length m.stk with
  | none => rw [hp] at hstep; cases hstep
  | some q =>
    obtain ⟨ps, r⟩ := q
    rw [hp] at hstep
    dsimp only at hstep
    cases hstep
    obtain ⟨Ns, rest, G, hG, hargs, hlN, hlp, hok, hrest⟩ := popN_ospec xs.length hp h2
    let σ := override ρ xs Ns
    let env := overrideN genv xs ps
    have henv : ∀ x, Occ x body → otermAt m.heap (m.heap.length + 1) (env x) = some (σ x) := by
      intro x hx
      by_cases hin : x ∈ xs
      · exact override_optr xs _ _ ps Ns x hin hok hlp
      · show otermAt _ _ (overrideN genv xs ps x) = some (override ρ xs Ns x)
        rw [overrideN_notin _ xs ps x hin, override_notin _ xs Ns x hin]
        exact hglob x hx hin
    obtain ⟨cs, e, hroot⟩ := ibuild_ospec env σ body m.heap henv
    refine ⟨appL (body.subst σ) rest, ?_, ?_⟩
    · apply odecode_of hroot
      show ostackAt (ibuild env m.heap body).1 ((ibuild env m.heap body).1.length + 1) r = some rest
      rw [e]
      exact ostackAt_grow hrest (by simp; omega)
    · rw [ht, hargs, appL_app]
      exact OWSteps.appL (absN_beta_subst xs body ρ Ns (by rw [hlN])) rest

/-- A closed cell reads back, as an open term, as its closed term. -/
theorem otermAt_of_termAt {heap : List Cell} : ∀ {F a : Nat} {u : Term},
    termAt heap F a = some u → otermAt heap F a = some u.toO
  | 0, _, _, h => by cases h
  | F + 1, a, u, h => by
    unfold termAt at h
    unfold otermAt
    cases hc : heap[a]? with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      cases c with
      | S => cases h; rfl
      | K => cases h; rfl
      | I => cases h; rfl
      | app g x =>
        dsimp only at h ⊢
        cases hg : termAt heap F g with
        | none => rw [hg] at h; cases h
        | some tg =>
          cases hx : termAt heap F x with
          | none => rw [hg, hx] at h; cases h
          | some tx =>
            rw [hg, hx] at h
            cases h
            rw [otermAt_of_termAt hg, otermAt_of_termAt hx]
            rfl
      | _ => cases h

/-- **A jetted run is open weak reduction.** -/
theorem ojsteps_owsteps {m m' : Mach} {t : OTerm} (hdec : odecode m = some t) (h : JSteps m m') :
    ∃ u, odecode m' = some u ∧ OWSteps t u := by
  induction h generalizing t with
  | refl _ => exact ⟨t, hdec, .refl t⟩
  | step hs _ ih =>
    cases hs with
    | mach hm =>
      rcases omstep_some hdec hm with hd1 | ⟨u1, hu1, hd1⟩
      · exact ih hd1
      · obtain ⟨u, hu, hw⟩ := ih hd1
        exact ⟨u, hu, (OSteps.single hu1).weak.trans hw⟩
    | inst xs body genv γ hglob hhd hi =>
      have hhd' := otermAt_of_termAt hhd
      rw [toO_close] at hhd'
      have hglob' : ∀ x, Occ x body → x ∉ xs →
          otermAt _ (_ + 1) (genv x) = some ((fun i => (γ i).toO) x) :=
        fun x hx hn => otermAt_of_termAt (hglob x hx hn)
      obtain ⟨u1, hd1, hw1⟩ := oinst_sound_g hglob' hhd' hdec hi
      obtain ⟨u, hu, hw⟩ := ih hd1
      exact ⟨u, hu, hw1.trans hw⟩

end Mach
