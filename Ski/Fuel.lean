import Ski.Basic
open Term

/-!
# The fuel interpreter

`step?` is the computable contraction; `evalF k t` runs at most `k`
step-attempts, the last of which must be the no-redex check, so a run of
`s` contractions needs fuel `s + 1` and times out at `s` — SKIjack's fuel
rule (SPEC §6).  `runF` also returns the contraction count, which is what
the conformance corpus pins.

`step?` recurses into the function position first, exactly as `progress`
does: a term steps at the head of its spine if the spine's function steps,
and otherwise only if the function is a saturated combinator.
-/

/-- The computable contraction. -/
def step? : Term → Option Term
  | S => none
  | K => none
  | I => none
  | app f x =>
    match step? f with
    | some f' => some (app f' x)
    | none =>
      match f with
      | I => some x
      | app K y => some y
      | app (app S y) z => some (app (app y x) (app z x))
      | _ => none

theorem step?_none {t : Term} (h : step? t = none) : Whnf t := by
  induction t with
  | S => exact .S
  | K => exact .K
  | I => exact .I
  | app f x ihf _ =>
    simp only [step?] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hf
      have hw := ihf hf
      cases hw with
      | S => exact .S1 x
      | K => exact .K1 x
      | I => simp at h
      | S1 y => exact .S2 y x
      | S2 y z => simp at h
      | K1 y => simp at h

theorem step?_sound {t u : Term} (h : step? t = some u) : Step t u := by
  induction t generalizing u with
  | S => simp [step?] at h
  | K => simp [step?] at h
  | I => simp [step?] at h
  | app f x ihf _ =>
    simp only [step?] at h
    split at h
    · rename_i f' hf
      cases h
      exact .left x (ihf hf)
    · rename_i hf
      have hw := step?_none hf
      cases hw with
      | S => simp at h
      | K => simp at h
      | I => cases h; exact .I x
      | S1 y => simp at h
      | S2 _ _ => cases h; exact .S _ _ x
      | K1 _ => cases h; exact .K _ x

theorem step?_complete {t u : Term} (h : Step t u) : step? t = some u := by
  induction h with
  | S f g x => rfl
  | K x y => rfl
  | I x => rfl
  | left x _ ih => simp [step?, ih]

theorem step?_iff {t u : Term} : step? t = some u ↔ Step t u :=
  ⟨step?_sound, step?_complete⟩

theorem whnf_iff_step?_none {t : Term} : Whnf t ↔ step? t = none := by
  constructor
  · intro hw
    cases hs : step? t with
    | none => rfl
    | some u => exact (hw.no_step (step?_sound hs)).elim
  · exact step?_none

/-- Exactly `k` contractions, if they exist. -/
def iter : Nat → Term → Option Term
  | 0, t => some t
  | k + 1, t => (step? t).bind (iter k)

theorem iter_sound : ∀ {k : Nat} {t u : Term}, iter k t = some u → Steps t u
  | 0, t, u, h => by cases h; exact .refl t
  | k + 1, t, u, h => by
    simp only [iter] at h
    cases hs : step? t with
    | none => simp [hs] at h
    | some t' =>
      rw [hs] at h
      exact .step (step?_sound hs) (iter_sound h)

/-- `k` step-attempts; `none` is the timeout. -/
def evalF : Nat → Term → Option Term
  | 0, _ => none
  | k + 1, t =>
    match step? t with
    | none => some t
    | some t' => evalF k t'

/-- As `evalF`, with the contraction count. -/
def runF : Nat → Term → Option (Term × Nat)
  | 0, _ => none
  | k + 1, t =>
    match step? t with
    | none => some (t, 0)
    | some t' => (runF k t').map (fun p => (p.1, p.2 + 1))

theorem evalF_sound : ∀ {k : Nat} {t u : Term}, evalF k t = some u → Eval t u
  | 0, _, _, h => by simp [evalF] at h
  | k + 1, t, u, h => by
    simp only [evalF] at h
    cases hs : step? t with
    | none => (try rw [hs] at h); cases h; exact ⟨.refl t, step?_none hs⟩
    | some t' =>
      (try rw [hs] at h)
      have ⟨hst, hw⟩ := evalF_sound h
      exact ⟨.step (step?_sound hs) hst, hw⟩

theorem evalF_mono : ∀ {k k' : Nat} {t u : Term}, evalF k t = some u → k ≤ k' → evalF k' t = some u
  | 0, _, _, _, h, _ => by simp [evalF] at h
  | k + 1, 0, _, _, _, hle => by omega
  | k + 1, k' + 1, t, u, h, hle => by
    simp only [evalF] at h ⊢
    cases hs : step? t with
    | none => rw [hs] at h; exact h
    | some t' => rw [hs] at h; exact evalF_mono h (by omega)

theorem evalF_complete {t u : Term} (h : Eval t u) : ∃ k, evalF k t = some u := by
  obtain ⟨hs, hw⟩ := h
  induction hs with
  | refl t =>
    refine ⟨1, ?_⟩
    simp [evalF, whnf_iff_step?_none.mp hw]
  | step h _ ih =>
    obtain ⟨k, hk⟩ := ih hw
    refine ⟨k + 1, ?_⟩
    simp [evalF, step?_complete h, hk]

/-- Divergence is "timeout at every fuel". -/
theorem diverges_iff_fuel (t : Term) : Diverges t ↔ ∀ k, evalF k t = none := by
  constructor
  · intro hd k
    cases h : evalF k t with
    | none => rfl
    | some u => exact (hd u (evalF_sound h)).elim
  · intro hf u he
    obtain ⟨k, hk⟩ := evalF_complete he
    rw [hf k] at hk
    cases hk

theorem runF_evalF : ∀ {k : Nat} {t : Term}, (runF k t).map Prod.fst = evalF k t
  | 0, _ => rfl
  | k + 1, t => by
    simp only [runF, evalF]
    cases step? t with
    | none => rfl
    | some t' => simp [Option.map_map, ← runF_evalF (k := k) (t := t')]; rfl
