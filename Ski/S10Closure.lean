import Ski.S10Frame
open Term

/-!
# S10 (Clock Closure), milestone M1: clocks and their closure

Plan: `notes/S10-CLOCK-PLAN.md` §§1.3, 1.4, 2.1, with the Wizard repairs W10.3–W10.5.

A `Clock P` is a parametric family of frames with its schedule as **data**: `H p` says whether
the frame fires, `T p` when.  The quiet side demands `Silent` *and* `Eternal` (W10.3): this is
stricter than the source's Def 2′; a halting silent family (e.g. the empty frame) is not a
clock.

The operators act on head runs: **Seq** (a quiet prefix, then a clock), **Iter** (a family of
boundary frames, each running quietly to the next one down, with a firing exit at the bottom),
**Loop** (an infinite chain of quiet segments, each of at least one step: silent and eternal),
**Cond** (a sum of clocks), **Reindex** (pulling a clock back along a map).  Quiet segments
are stated with deposits `J` that stay behind the window.  Each closure lemma is proved for
the existential-deposit form `QuietD` and specialised to explicit deposits in
`clock_closure`, whose statement is the plan's §2.1.

`Clock.fires_iff` (the corollary of §2.1, W10.4) says only that `H` is the firing predicate:
`(∃ n, FiresAt (C.frame p) n) ↔ C.H p = true`.  It claims no decidability beyond the fact that
`H` is a field; computability is claimed only for named instances in the audit gate.
-/

namespace S10

/-- A clock: frames with their schedule `(T, H)` as data. -/
structure Clock (P : Type) where
  frame : P → List Term
  H : P → Bool
  T : P → Nat
  fire : ∀ p, H p = true → ∀ R, FiresAt (frame p ++ R) (T p)
  quiet : ∀ p, H p = false → Silent (frame p) ∧ Eternal (frame p)

/-- The corollary: `H` is exactly the firing predicate, and `T` the first firing. -/
theorem Clock.fires_iff {P : Type} (C : Clock P) (p : P) :
    (∃ n, FiresAt (C.frame p) n) ↔ C.H p = true := by
  constructor
  · intro ⟨n, hn⟩
    cases hH : C.H p with
    | true => rfl
    | false => exact (hn.not_silent (C.quiet p hH).1).elim
  · intro hH
    refine ⟨C.T p, ?_⟩
    have := C.fire p hH []
    simpa using this

theorem Clock.firesAt_T {P : Type} (C : Clock P) {p : P} {n : Nat}
    (h : FiresAt (C.frame p) n) : n = C.T p := by
  have hH := (C.fires_iff p).1 ⟨n, h⟩
  have h' := C.fire p hH []
  simp only [List.append_nil] at h'
  exact h.unique h'

/-! ## Seq -/

theorem seq_fires {n m : Nat} {a b : List Term} (h : QuietD n a b)
    (hf : ∀ R, FiresAt (b ++ R) m) : ∀ R, FiresAt (a ++ R) (n + m) := h.fires hf

theorem seq_quiet {n : Nat} {a b : List Term} (h : QuietD n a b)
    (hb : Silent b ∧ Eternal b) : Silent a ∧ Eternal a := by
  obtain ⟨J, q⟩ := h
  exact q.silent_eternal (silent_eternal_append J hb)

/-- **Seq**: a quiet prefix handing off to a clock. -/
def Clock.seq {P Q : Type} (C : Clock Q) (a : P → List Term) (o : P → Q) (c : P → Nat)
    (h : ∀ p, QuietD (c p) (a p) (C.frame (o p))) : Clock P where
  frame := a
  H p := C.H (o p)
  T p := c p + C.T (o p)
  fire p hH := seq_fires (h p) (C.fire (o p) hH)
  quiet p hH := seq_quiet (h p) (C.quiet (o p) hH)

/-! ## Iter -/

/-- **Iter**: boundary frames running quietly downward, firing at the bottom. -/
theorem iter_fires (bnd : Nat → List Term) (per : Nat → Nat) (e : Nat)
    (h : ∀ c, QuietD (per c) (bnd (c + 1)) (bnd c))
    (hx : ∀ R, FiresAt (bnd 0 ++ R) e) : ∀ g R, FiresAt (bnd g ++ R) (e + psum per g) := by
  intro g
  induction g with
  | zero => simpa [psum] using hx
  | succ g ih =>
    intro R
    have := (h g).fires ih R
    have e' : per g + (e + psum per g) = e + psum per (g + 1) := by
      simp only [psum]; omega
    rw [← e']; exact this

def Clock.iter (bnd : Nat → List Term) (per : Nat → Nat) (e : Nat)
    (h : ∀ c, QuietD (per c) (bnd (c + 1)) (bnd c))
    (hx : ∀ R, FiresAt (bnd 0 ++ R) e) : Clock Nat where
  frame := bnd
  H _ := true
  T g := e + psum per g
  fire g _ := iter_fires bnd per e h hx g
  quiet _ hH := Bool.noConfusion hH

/-! ## Loop -/

/-- The invariant of a loop: every frame on the run from `cfg k ++ R` has a window and a
non-`F` seat. -/
theorem loop_frames (cfg : Nat → List Term) (per : Nat → Nat)
    (h : ∀ k, QuietD (per k + 1) (cfg k) (cfg (k + 1))) :
    ∀ j k R, ∃ l', frun j (cfg k ++ R) = some l' ∧ 3 ≤ l'.length ∧ seat l' ≠ some F := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro k R
    obtain ⟨J, q⟩ := h k
    obtain ⟨r, qq⟩ := q R
    cases Nat.lt_or_ge j (per k + 1) with
    | inl hlt =>
      obtain ⟨l', h1, h3⟩ := frun_lt_len r hlt
      exact ⟨l', h1, h3, qq j hlt l' h1⟩
    | inr hge =>
      have e : j = (per k + 1) + (j - (per k + 1)) := by omega
      obtain ⟨l', h1, h3, h4⟩ := ih (j - (per k + 1)) (by omega) (k + 1) (J ++ R)
      refine ⟨l', ?_, h3, h4⟩
      rw [e, frun_add, r]
      simp only [Option.bind_some, List.append_assoc]
      exact h1

/-- **Loop**: an infinite chain of nonempty quiet segments is silent and eternal. -/
theorem loop_silent_eternal (cfg : Nat → List Term) (per : Nat → Nat)
    (h : ∀ k, QuietD (per k + 1) (cfg k) (cfg (k + 1))) :
    Silent (cfg 0) ∧ Eternal (cfg 0) := by
  have hf := loop_frames cfg per h
  refine ⟨?_, ?_⟩
  · intro j l' hl'
    obtain ⟨l'', h1, _, h4⟩ := hf j 0 []
    simp only [List.append_nil] at h1
    rw [hl'] at h1; cases h1
    exact h4
  · intro j
    obtain ⟨l'', h1, h3, _⟩ := hf j 0 []
    simp only [List.append_nil] at h1
    exact ⟨l'', h1, h3⟩

/-! ## Cond and Reindex -/

/-- **Cond**: the sum of two clocks. -/
def Clock.cond {P₁ P₂ : Type} (C₁ : Clock P₁) (C₂ : Clock P₂) : Clock (P₁ ⊕ P₂) where
  frame p := match p with
    | .inl p => C₁.frame p
    | .inr p => C₂.frame p
  H p := match p with
    | .inl p => C₁.H p
    | .inr p => C₂.H p
  T p := match p with
    | .inl p => C₁.T p
    | .inr p => C₂.T p
  fire p := match p with
    | .inl p => C₁.fire p
    | .inr p => C₂.fire p
  quiet p := match p with
    | .inl p => C₁.quiet p
    | .inr p => C₂.quiet p

/-- **Reindex**: pull a clock back along `f`. -/
def Clock.reindex {P Q : Type} (C : Clock Q) (f : P → Q) : Clock P where
  frame p := C.frame (f p)
  H p := C.H (f p)
  T p := C.T (f p)
  fire p := C.fire (f p)
  quiet p := C.quiet (f p)

/-! ## The closure theorem (plan §2.1, explicit deposits) -/

theorem clock_closure :
    -- Seq
    (∀ {P Q : Type} (C : Clock Q) (a J : P → List Term) (o : P → Q) (c : P → Nat),
       (∀ p, Quiet (c p) (a p) (C.frame (o p) ++ J p)) →
       ∀ p, (C.H (o p) = true → ∀ R, FiresAt (a p ++ R) (c p + C.T (o p))) ∧
            (C.H (o p) = false → Silent (a p) ∧ Eternal (a p))) ∧
    -- Iter
    (∀ (bnd J : Nat → List Term) (per : Nat → Nat) (e : Nat),
       (∀ c, Quiet (per c) (bnd (c + 1)) (bnd c ++ J c)) →
       (∀ R, FiresAt (bnd 0 ++ R) e) →
       ∀ g R, FiresAt (bnd g ++ R) (e + psum per g)) ∧
    -- Loop
    (∀ (cfg J : Nat → List Term) (per : Nat → Nat),
       (∀ k, Quiet (per k + 1) (cfg k) (cfg (k + 1) ++ J k)) →
       Silent (cfg 0) ∧ Eternal (cfg 0)) ∧
    -- Cond
    (∀ {P₁ P₂ : Type} (C₁ : Clock P₁) (C₂ : Clock P₂), ∃ C : Clock (P₁ ⊕ P₂),
       (∀ p, C.frame (.inl p) = C₁.frame p ∧ C.T (.inl p) = C₁.T p ∧ C.H (.inl p) = C₁.H p) ∧
       (∀ p, C.frame (.inr p) = C₂.frame p ∧ C.T (.inr p) = C₂.T p ∧ C.H (.inr p) = C₂.H p)) ∧
    -- Reindex
    (∀ {P Q : Type} (C : Clock Q) (f : P → Q), ∃ C' : Clock P,
       C'.frame = C.frame ∘ f ∧ C'.T = C.T ∘ f ∧ C'.H = C.H ∘ f) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P Q C a J o c h p
    have hd : QuietD (c p) (a p) (C.frame (o p)) := ⟨J p, h p⟩
    exact ⟨fun hH => seq_fires hd (C.fire (o p) hH),
           fun hH => seq_quiet hd (C.quiet (o p) hH)⟩
  · intro bnd J per e h hx
    exact iter_fires bnd per e (fun c => ⟨J c, h c⟩) hx
  · intro cfg J per h
    exact loop_silent_eternal cfg per (fun k => ⟨J k, h k⟩)
  · intro P₁ P₂ C₁ C₂
    exact ⟨Clock.cond C₁ C₂, fun _ => ⟨rfl, rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl⟩⟩
  · intro P Q C f
    exact ⟨Clock.reindex C f, rfl, rfl, rfl⟩

end S10
