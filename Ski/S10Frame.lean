import Ski.HnfSound
import Ski.Fuel
open Term HnfS

/-!
# S10 (Clock Closure), milestone M0: frames, firing, locality, and the term bridge

Plan: `notes/S10-CLOCK-PLAN.md` §1.2, with the Wizard repairs W10.2 and W10.6.

* **Frames.** The frame of a term is its argument list `args t = HnfSound.spine t`
  (`spine (S u₁ ⋯ uₘ) = [u₁, …, uₘ]`).  One head step pops `x y z` and pushes
  `args x ++ [z, y z]` (`fstep`); `frun n` is `n` such steps.
* **Firing.** A step fires when its x-seat is the marker `F = S tw8 tw8`.  `FiresAt l n`: the
  first firing is after exactly `n` steps (0-based; the paper's firing index is `n + 1`).
  `Silent`: never fires.  `Eternal`: never halts.  `Quiet n a b`: `a` runs to `b` in `n`
  steps without firing, for every tail.
* **Locality** (`frun_append`): a run that succeeds on `l` succeeds on `l ++ R`, with `R`
  carried along.  No length side condition is needed: a successful step already has a window.
* **Checked runs.** `qrun` is `frun` that refuses to step on an `F` seat; `Quiet.of_qrun` and
  `firesAt_of_qrun` turn one kernel evaluation (`rfl`, free variables allowed) into a quiet
  segment or a firing.  The `F` test `isF` is a pattern match, so it never inspects a free
  variable below the depth of the marker's shape.
* **Bridge** (W10.6): `iter_eq_frun : PureS t → iter n t = (frun n (args t)).map (·.foldl app S)`,
  an equation (it covers `none`), and `TFiresAt.of_firesAt`: on a pure-S term, frame-level
  firing is firing of the head reduction `Ski.Fuel.iter`.
-/

namespace S10

/-! ## Frames, the marker, the step -/

/-- The frame (argument list) of a term. -/
def args (t : Term) : List Term := HnfSound.spine t

/-- `tw n = S (S (⋯ S))` with `n` leaves (`tw 0 = tw 1 = S`). -/
def tw : Nat → Term
  | 0 => S
  | 1 => S
  | n + 2 => S ⬝ tw (n + 1)

/-- The marker `F = S tw8 tw8` (17 leaves, normal). -/
def F : Term := S ⬝ tw 8 ⬝ tw 8

/-- One head step on a frame: pop `x y z`, push `args x ++ [z, y z]`. -/
def fstep : List Term → Option (List Term)
  | x :: y :: z :: r => some (args x ++ z :: (y ⬝ z) :: r)
  | _ => none

/-- Exactly `n` frame steps. -/
def frun : Nat → List Term → Option (List Term)
  | 0, l => some l
  | n + 1, l => (fstep l).bind (frun n)

/-- The x-seat, when a step is possible. -/
def seat : List Term → Option Term
  | x :: _ :: _ :: _ => some x
  | _ => none

/-- `l` first fires after exactly `n` steps (0-based). -/
def FiresAt (l : List Term) (n : Nat) : Prop :=
  (∃ l', frun n l = some l' ∧ seat l' = some F) ∧
  ∀ k, k < n → ∀ l', frun k l = some l' → seat l' ≠ some F

/-- Never fires (a halted frame never fires). -/
def Silent (l : List Term) : Prop := ∀ k l', frun k l = some l' → seat l' ≠ some F

/-- Never halts: every frame on the run has a window. -/
def Eternal (l : List Term) : Prop := ∀ k, ∃ l', frun k l = some l' ∧ 3 ≤ l'.length

/-- A quiet segment: from `a` to `b` in exactly `n` steps, no firing, for every tail. -/
def Quiet (n : Nat) (a b : List Term) : Prop :=
  ∀ R, frun n (a ++ R) = some (b ++ R) ∧
       ∀ k, k < n → ∀ l', frun k (a ++ R) = some l' → seat l' ≠ some F

/-- `psum f g = Σ_{c<g} f c`. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | g + 1 => psum f g + f g

theorem psum_const (k : Nat) : ∀ g, psum (fun _ => k) g = k * g
  | 0 => by simp [psum]
  | g + 1 => by rw [psum, psum_const k g, Nat.mul_succ]

/-! ## Basic run facts -/

theorem fstep_append {l l' : List Term} (R : List Term) (h : fstep l = some l') :
    fstep (l ++ R) = some (l' ++ R) := by
  match l, h with
  | x :: y :: z :: r, h =>
    simp only [fstep, Option.some.injEq] at h
    subst h
    simp [fstep]

/-- Locality: a successful run carries any tail along. -/
theorem frun_append : ∀ {n : Nat} {l l' : List Term} (R : List Term),
    frun n l = some l' → frun n (l ++ R) = some (l' ++ R)
  | 0, l, l', R, h => by
    simp only [frun, Option.some.injEq] at h
    subst h; rfl
  | n + 1, l, l', R, h => by
    simp only [frun] at h ⊢
    cases hs : fstep l with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      rw [fstep_append R hs]
      exact frun_append R h

theorem frun_add : ∀ (n m : Nat) (l : List Term),
    frun (n + m) l = (frun n l).bind (frun m)
  | 0, m, l => by simp [frun]
  | n + 1, m, l => by
    rw [Nat.succ_add]
    simp only [frun]
    cases fstep l with
    | none => rfl
    | some l₁ => exact frun_add n m l₁

theorem fstep_len {l l' : List Term} (h : fstep l = some l') : 3 ≤ l.length := by
  match l, h with
  | _ :: _ :: _ :: r, _ => simp

theorem frun_succ_len {n : Nat} {l b : List Term} (h : frun (n + 1) l = some b) :
    3 ≤ l.length := by
  simp only [frun] at h
  cases hs : fstep l with
  | none => rw [hs] at h; cases h
  | some _ => exact fstep_len hs

theorem seat_append {l : List Term} (R : List Term) (h : 3 ≤ l.length) :
    seat (l ++ R) = seat l := by
  match l, h with
  | _ :: _ :: _ :: r, _ => rfl

theorem seat_len {l : List Term} {x : Term} (h : seat l = some x) : 3 ≤ l.length := by
  match l, h with
  | _ :: _ :: _ :: r, _ => simp

/-- An intermediate frame of a successful run. -/
theorem frun_le {n k : Nat} {l b : List Term} (h : frun n l = some b) (hk : k ≤ n) :
    ∃ l', frun k l = some l' ∧ frun (n - k) l' = some b := by
  have e : n = k + (n - k) := by omega
  rw [e, frun_add] at h
  cases hl : frun k l with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h
    exact ⟨l', rfl, h⟩

/-- Frames strictly before the end of a successful run have a window. -/
theorem frun_lt_len {n k : Nat} {l b : List Term} (h : frun n l = some b) (hk : k < n) :
    ∃ l', frun k l = some l' ∧ 3 ≤ l'.length := by
  obtain ⟨l', h1, h2⟩ := frun_le h (Nat.le_of_lt hk)
  obtain ⟨j, hj⟩ : ∃ j, n - k = j + 1 := ⟨n - k - 1, by omega⟩
  rw [hj] at h2
  exact ⟨l', h1, frun_succ_len h2⟩

/-! ## Quiet segments -/

/-- A quiet run with the empty tail is quiet for every tail (locality). -/
theorem Quiet.of_nil {n : Nat} {a b : List Term} (h : frun n a = some b)
    (hq : ∀ k, k < n → ∀ l', frun k a = some l' → seat l' ≠ some F) : Quiet n a b := by
  intro R
  refine ⟨frun_append R h, ?_⟩
  intro k hk l'' hl''
  obtain ⟨l', h1, h3⟩ := frun_lt_len h hk
  rw [frun_append R h1] at hl''
  cases hl''
  rw [seat_append R h3]
  exact hq k hk l' h1

theorem Quiet.nil {n : Nat} {a b : List Term} (h : Quiet n a b) :
    frun n a = some b ∧ ∀ k, k < n → ∀ l', frun k a = some l' → seat l' ≠ some F := by
  have := h []
  simpa using this

theorem Quiet.refl (a : List Term) : Quiet 0 a a := by
  intro R
  exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

/-- Chain two quiet segments; the first segment's deposit `J` stays behind. -/
theorem Quiet.trans {n m : Nat} {a b c J : List Term} (h₁ : Quiet n a (b ++ J))
    (h₂ : Quiet m b c) : Quiet (n + m) a (c ++ J) := by
  intro R
  obtain ⟨r₁, q₁⟩ := h₁ R
  obtain ⟨r₂, q₂⟩ := h₂ (J ++ R)
  refine ⟨?_, ?_⟩
  · rw [frun_add, r₁]
    simp only [Option.bind_some, List.append_assoc]
    exact r₂
  · intro k hk l' hl'
    cases Nat.lt_or_ge k n with
    | inl hlt => exact q₁ k hlt l' hl'
    | inr hge =>
      have e : k = n + (k - n) := by omega
      rw [e, frun_add, r₁] at hl'
      simp only [Option.bind_some, List.append_assoc] at hl'
      exact q₂ (k - n) (by omega) l' hl'

/-- A quiet segment followed by a firing. -/
theorem Quiet.fires {n m : Nat} {a b : List Term} {R : List Term} (h : Quiet n a b)
    (hf : FiresAt (b ++ R) m) : FiresAt (a ++ R) (n + m) := by
  obtain ⟨r, q⟩ := h R
  obtain ⟨⟨l', hl', hs⟩, hq⟩ := hf
  refine ⟨⟨l', ?_, hs⟩, ?_⟩
  · rw [frun_add, r]; exact hl'
  · intro k hk l'' hl''
    cases Nat.lt_or_ge k n with
    | inl hlt => exact q k hlt l'' hl''
    | inr hge =>
      have e : k = n + (k - n) := by omega
      rw [e, frun_add, r] at hl''
      exact hq (k - n) (by omega) l'' hl''

/-- A quiet segment whose end is silent and eternal starts silent and eternal. -/
theorem Quiet.silent_eternal {n : Nat} {a b : List Term} (h : Quiet n a b)
    (hb : Silent b ∧ Eternal b) : Silent a ∧ Eternal a := by
  obtain ⟨r, q⟩ := h.nil
  refine ⟨?_, ?_⟩
  · intro k l' hl'
    cases Nat.lt_or_ge k n with
    | inl hlt => exact q k hlt l' hl'
    | inr hge =>
      have e : k = n + (k - n) := by omega
      rw [e, frun_add, r] at hl'
      exact hb.1 (k - n) l' hl'
  · intro k
    cases Nat.lt_or_ge k n with
    | inl hlt => exact frun_lt_len r hlt
    | inr hge =>
      have e : k = n + (k - n) := by omega
      rw [e, frun_add, r]
      exact hb.2 (k - n)

/-- Silence and eternity survive appending a tail (locality). -/
theorem silent_eternal_append {l : List Term} (J : List Term) (h : Silent l ∧ Eternal l) :
    Silent (l ++ J) ∧ Eternal (l ++ J) := by
  refine ⟨?_, ?_⟩
  · intro k l'' hl''
    obtain ⟨l', h1, h3⟩ := h.2 k
    rw [frun_append J h1] at hl''
    cases hl''
    rw [seat_append J h3]
    exact h.1 k l' h1
  · intro k
    obtain ⟨l', h1, h3⟩ := h.2 k
    refine ⟨l' ++ J, frun_append J h1, ?_⟩
    simp only [List.length_append]; omega

/-- A firing frame is not silent. -/
theorem FiresAt.not_silent {l : List Term} {n : Nat} (h : FiresAt l n) (hs : Silent l) : False := by
  obtain ⟨⟨l', hl', hF⟩, _⟩ := h
  exact hs n l' hl' hF

/-- The first firing is unique. -/
theorem FiresAt.unique {l : List Term} {n m : Nat} (h₁ : FiresAt l n) (h₂ : FiresAt l m) :
    n = m := by
  obtain ⟨⟨l₁, r₁, s₁⟩, q₁⟩ := h₁
  obtain ⟨⟨l₂, r₂, s₂⟩, q₂⟩ := h₂
  cases Nat.lt_or_ge n m with
  | inl hlt => exact absurd s₁ (q₂ n hlt l₁ r₁)
  | inr hge =>
    cases Nat.lt_or_ge m n with
    | inl hlt => exact absurd s₂ (q₁ m hlt l₂ r₂)
    | inr hge' => exact Nat.le_antisymm hge' hge

/-- Firing is tail-independent (W10.5). -/
theorem FiresAt.append {l : List Term} {n : Nat} (R : List Term) (h : FiresAt l n) :
    FiresAt (l ++ R) n := by
  obtain ⟨⟨l', r, s⟩, q⟩ := h
  have hq : Quiet n l l' := Quiet.of_nil r q
  have hf : FiresAt (l' ++ R) 0 := by
    refine ⟨⟨l' ++ R, rfl, ?_⟩, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    rw [seat_append R (seat_len s)]; exact s
  have := hq.fires hf
  simpa using this

/-! ## Checked runs (`qrun`) -/

/-- `tw 8` by its shape. -/
def isTw8 : Term → Bool
  | S ⬝ (S ⬝ (S ⬝ (S ⬝ (S ⬝ (S ⬝ (S ⬝ S)))))) => true
  | _ => false

/-- The marker test, by shape: `isF x = true ↔ x = F`; only the soundness half is used. -/
def isF : Term → Bool
  | S ⬝ a ⬝ b => isTw8 a && isTw8 b
  | _ => false

theorem isF_F : isF F = true := rfl

theorem ne_F_of_isF {x : Term} (h : isF x = false) : x ≠ F := by
  intro e; subst e; exact Bool.noConfusion (isF_F.symm.trans h)

/-- `frun` that stops (with `none`) instead of stepping on an `F` seat. -/
def qrun : Nat → List Term → Option (List Term)
  | 0, l => some l
  | n + 1, x :: y :: z :: r =>
    match isF x with
    | true => none
    | false => qrun n (args x ++ z :: (y ⬝ z) :: r)
  | _ + 1, _ => none

theorem qrun_sound : ∀ {n : Nat} {a b : List Term}, qrun n a = some b →
    frun n a = some b ∧ ∀ k, k < n → ∀ l', frun k a = some l' → seat l' ≠ some F
  | 0, a, b, h => by
    simp only [qrun, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | n + 1, a, b, h => by
    match a, h with
    | x :: y :: z :: r, h =>
      simp only [qrun] at h
      cases hx : isF x with
      | true => rw [hx] at h; cases h
      | false =>
        rw [hx] at h
        obtain ⟨r₁, q₁⟩ := qrun_sound h
        refine ⟨r₁, ?_⟩
        intro k hk l' hl'
        cases k with
        | zero =>
          simp only [frun, Option.some.injEq] at hl'
          subst hl'
          simp only [seat, ne_eq, Option.some.injEq]
          exact ne_F_of_isF hx
        | succ j =>
          exact q₁ j (Nat.lt_of_succ_lt_succ hk) l' hl'
    | [], h => simp [qrun] at h
    | [_], h => simp [qrun] at h
    | [_, _], h => simp [qrun] at h

/-- One kernel evaluation of `qrun` is a quiet segment. -/
theorem Quiet.of_qrun {n : Nat} {a b : List Term} (h : qrun n a = some b) : Quiet n a b :=
  Quiet.of_nil (qrun_sound h).1 (qrun_sound h).2

/-- A quiet segment whose deposit is left implicit: the first `k` entries of the end frame. -/
theorem Quiet.of_qrun_take {n k : Nat} {a b : List Term}
    (h : (qrun n a).map (List.take k) = some b) : ∃ J, Quiet n a (b ++ J) := by
  cases hq : qrun n a with
  | none => rw [hq] at h; cases h
  | some l =>
    rw [hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨l.drop k, ?_⟩
    rw [← h, List.take_append_drop]
    exact Quiet.of_qrun hq

/-- One kernel evaluation of `qrun` ending on an `F` seat is a firing, for every tail. -/
theorem firesAt_of_qrun {n : Nat} {a : List Term} (h : (qrun n a).bind seat = some F) :
    ∀ R, FiresAt (a ++ R) n := by
  cases hq : qrun n a with
  | none => rw [hq] at h; cases h
  | some b =>
    rw [hq] at h
    simp only [Option.bind_some] at h
    intro R
    have hf : FiresAt (b ++ R) 0 := by
      refine ⟨⟨b ++ R, rfl, ?_⟩, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      rw [seat_append R (seat_len h)]; exact h
    have := (Quiet.of_qrun hq).fires hf
    simpa using this

/-! ## Quiet segments with implicit deposits -/

/-- `a` runs quietly in `n` steps to `b` followed by some deposit. -/
def QuietD (n : Nat) (a b : List Term) : Prop := ∃ J, Quiet n a (b ++ J)

theorem QuietD.trans {n m : Nat} {a b c : List Term} (h₁ : QuietD n a b) (h₂ : QuietD m b c) :
    QuietD (n + m) a c := by
  obtain ⟨J, q₁⟩ := h₁
  obtain ⟨J', q₂⟩ := h₂
  refine ⟨J' ++ J, ?_⟩
  have := q₁.trans q₂
  simpa using this

theorem QuietD.fires {n m : Nat} {a b : List Term} (h : QuietD n a b)
    (hf : ∀ R, FiresAt (b ++ R) m) : ∀ R, FiresAt (a ++ R) (n + m) := by
  obtain ⟨J, q⟩ := h
  intro R
  have := hf (J ++ R)
  rw [← List.append_assoc] at this
  exact q.fires this

theorem QuietD.cast {n n' : Nat} {a b : List Term} (h : QuietD n a b) (e : n = n') :
    QuietD n' a b := e ▸ h

/-! ## The bridge to head reduction (W10.6) -/

theorem step?_foldl {h h' : Term} (hs : step? h = some h') :
    ∀ r : List Term, step? (r.foldl Term.app h) = some (r.foldl Term.app h') := by
  intro r
  induction r generalizing h h' with
  | nil => exact hs
  | cons x r ih =>
    simp only [List.foldl]
    apply ih
    simp [step?, hs]

/-- The head step of a pure-S spine is the frame step. -/
theorem step?_frame (l : List Term) (hl : ∀ u ∈ l, PureS u) :
    step? (l.foldl Term.app S) = (fstep l).map (fun l' => l'.foldl Term.app S) := by
  match l with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | x :: y :: z :: r =>
    have hx : PureS x := hl x (by simp)
    have h0 : step? (S ⬝ x ⬝ y ⬝ z) = some (x ⬝ z ⬝ (y ⬝ z)) := rfl
    have := step?_foldl h0 r
    simp only [List.foldl] at this ⊢
    rw [this]
    simp only [fstep, Option.map_some, List.foldl_append, List.foldl]
    have e : x = (args x).foldl Term.app S := HnfSound.pure_eq_foldl hx
    rw [← e]

/-- `fstep` preserves pure-S frames. -/
theorem fstep_pure {l l' : List Term} (hl : ∀ u ∈ l, PureS u) (h : fstep l = some l') :
    ∀ u ∈ l', PureS u := by
  match l, h with
  | x :: y :: z :: r, h =>
    simp only [fstep, Option.some.injEq] at h
    subst h
    have hx : PureS x := hl x (by simp)
    have hy : PureS y := hl y (by simp)
    have hz : PureS z := hl z (by simp)
    intro u hu
    simp only [List.mem_append, List.mem_cons] at hu
    rcases hu with hu | rfl | rfl | hu
    · exact HnfSound.spine_pure hx u hu
    · exact hz
    · exact PureS.app hy hz
    · exact hl u (by simp [hu])

theorem frun_pure : ∀ {n : Nat} {l l' : List Term}, (∀ u ∈ l, PureS u) →
    frun n l = some l' → ∀ u ∈ l', PureS u
  | 0, l, l', hl, h => by
    simp only [frun, Option.some.injEq] at h
    subst h; exact hl
  | n + 1, l, l', hl, h => by
    simp only [frun] at h
    cases hs : fstep l with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      exact frun_pure (fstep_pure hl hs) h

theorem iter_foldl : ∀ (n : Nat) (l : List Term), (∀ u ∈ l, PureS u) →
    iter n (l.foldl Term.app S) = (frun n l).map (fun l' => l'.foldl Term.app S)
  | 0, l, _ => rfl
  | n + 1, l, hl => by
    simp only [iter, frun, step?_frame l hl]
    cases hs : fstep l with
    | none => rfl
    | some l' =>
      simp only [Option.map_some, Option.bind_some]
      exact iter_foldl n l' (fstep_pure hl hs)

/-- **Bridge (W10.6).** On a pure-S term, `n` head steps are `n` frame steps, as an equation. -/
theorem iter_eq_frun {t : Term} (ht : PureS t) (n : Nat) :
    iter n t = (frun n (args t)).map (fun l => l.foldl Term.app S) := by
  have h := iter_foldl n (args t) (HnfSound.spine_pure ht)
  have e : (args t).foldl Term.app S = t := (HnfSound.pure_eq_foldl ht).symm
  rw [e] at h
  exact h

/-- The frame of a folded spine. -/
theorem args_foldl (l : List Term) : args (l.foldl Term.app S) = l := by
  have := HnfSound.spine_foldl S l
  simpa [args, HnfSound.spine] using this

/-- **Term-level firing.** `t` is a pure-`S` term, its `n`-th head reduct exists and has
x-seat `F` (it is `S F y z ⋯`), and no earlier head reduct has x-seat `F`.  The `PureS`
conjunct is what makes the reading "`S F y z ⋯`" literal: `args` drops the head symbol. -/
def TFiresAt (t : Term) (n : Nat) : Prop :=
  PureS t ∧
  (∃ u, iter n t = some u ∧ seat (args u) = some F) ∧
  ∀ k, k < n → ∀ u, iter k t = some u → seat (args u) ≠ some F

theorem TFiresAt.of_firesAt {t : Term} {n : Nat} (ht : PureS t) (h : FiresAt (args t) n) :
    TFiresAt t n := by
  obtain ⟨⟨l', hl', hs⟩, hq⟩ := h
  refine ⟨ht, ⟨l'.foldl Term.app S, ?_, ?_⟩, ?_⟩
  · rw [iter_eq_frun ht, hl']; rfl
  · rw [args_foldl]; exact hs
  · intro k hk u hu
    rw [iter_eq_frun ht] at hu
    cases hr : frun k (args t) with
    | none => rw [hr] at hu; cases hu
    | some l =>
      rw [hr] at hu
      simp only [Option.map_some, Option.some.injEq] at hu
      subst hu
      rw [args_foldl]
      exact hq k hk l hr

end S10
