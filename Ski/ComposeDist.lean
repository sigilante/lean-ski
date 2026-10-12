import Ski.Chain

/-!
# Part II's interface with an additive distance

`Compose.EvalPS` and `Chain.PS` state zero knowledge as an abstract
equivalence `indist`, so `compose` and `chain2` only reindex it.  Here the
distance is a number.  A proof system draws its randomness from an
explicit list of draws (`draws`); honest proving and simulating are
functions of the draw, `none` when the prover aborts; and zero knowledge
is `CloseD`: for every event of the view, the counts of the draws on which
the real and the simulated views meet it differ by at most `err`, that is
a statistical distance of at most `err / draws.length`.

Knowledge soundness stays an assumed field, as it is the STARK's.  The
zero-knowledge field has the form the circuits' transcript theorems prove
(`Ski/ZK/ComposeZK.lean` turns `transcript_zkG` into `CloseD`), and
`Ski/ZK/CompPSD.lean` builds the composed circuit's instance (`compPSD`),
its relation an accepted run of the composed machine.

- `composeD`: over such a system, a formula's statement is complete,
  knowledge-sound, zero knowledge within `err`, and witness
  indistinguishable within `2 · err`: the errors add.
- `chain2D`: a two-stage chain, the stages drawing independently (the
  product of their draws), is zero knowledge within
  `|draws₂| · err₁ + |draws₁| · err₂` of `|draws₁| · |draws₂|` draws, a
  distance of `err₁ / |draws₁| + err₂ / |draws₂|`: the hybrid argument,
  proved (`closeD_prod`).
-/

namespace Compose

/-- A sum over a list. -/
def lsum {α : Type} (l : List α) (f : α → Nat) : Nat := (l.map f).sum

theorem lsum_nil {α : Type} (f : α → Nat) : lsum [] f = 0 := rfl

theorem lsum_cons {α : Type} (a : α) (l : List α) (f : α → Nat) : lsum (a :: l) f = f a + lsum l f := by
  simp [lsum]

theorem lsum_le {α : Type} {f g : α → Nat} : ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → lsum l f ≤ lsum l g
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    rw [lsum_cons, lsum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (lsum_le l fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem lsum_add {α : Type} (f g : α → Nat) : ∀ l : List α, lsum l (fun x => f x + g x) = lsum l f + lsum l g
  | [] => rfl
  | a :: l => by
    rw [lsum_cons, lsum_cons, lsum_cons, lsum_add f g l]
    omega

theorem lsum_const {α : Type} (c : Nat) : ∀ l : List α, lsum l (fun _ => c) = l.length * c
  | [] => by simp [lsum]
  | a :: l => by rw [lsum_cons, lsum_const c l, List.length_cons, Nat.succ_mul]; omega

theorem lsum_comm {α β : Type} (f : α → β → Nat) (l₂ : List β) :
    ∀ l₁ : List α, lsum l₁ (fun a => lsum l₂ (fun b => f a b)) = lsum l₂ (fun b => lsum l₁ (fun a => f a b))
  | [] => by
    show 0 = lsum l₂ (fun _ => 0)
    rw [lsum_const 0 l₂, Nat.mul_zero]
  | a :: l₁ => by
    rw [lsum_cons, lsum_comm f l₂ l₁]
    have : lsum l₂ (fun b => lsum (a :: l₁) (fun a => f a b)) = lsum l₂ (fun b => f a b + lsum l₁ (fun a => f a b)) :=
      congrArg (lsum l₂) (funext fun b => lsum_cons a l₁ _)
    rw [this, lsum_add]

/-- The product of two lists of draws. -/
def lprod {α β : Type} (l₁ : List α) (l₂ : List β) : List (α × β) := l₁.flatMap fun a => l₂.map fun b => (a, b)

theorem lsum_prod {α β : Type} (f : α × β → Nat) (l₂ : List β) :
    ∀ l₁ : List α, lsum (lprod l₁ l₂) f = lsum l₁ (fun a => lsum l₂ (fun b => f (a, b)))
  | [] => rfl
  | a :: l₁ => by
    rw [lsum_cons, ← lsum_prod f l₂ l₁]
    simp [lprod, lsum, List.flatMap_cons, List.map_append, List.sum_append, Function.comp_def]

theorem lprod_length {α β : Type} (l₁ : List α) (l₂ : List β) : (lprod l₁ l₂).length = l₁.length * l₂.length := by
  induction l₁ with
  | nil => simp [lprod]
  | cons a l ih => simp [lprod, List.flatMap_cons, List.length_append, Nat.succ_mul, Nat.add_comm] at ih ⊢; omega

-- ---------------------------------------------------------------------------
-- Closeness
-- ---------------------------------------------------------------------------

/-- The number of draws on which the view meets the event. -/
def cnt {D V : Type} (ds : List D) (f : D → V) (E : V → Bool) : Nat := lsum ds fun d => if E (f d) then 1 else 0

/-- **Two views within `e` draws**: for every event, the counts of the
    draws on which they meet it differ by at most `e`. -/
def CloseD {D V : Type} (ds : List D) (e : Nat) (f g : D → V) : Prop :=
  ∀ E : V → Bool, cnt ds f E ≤ cnt ds g E + e ∧ cnt ds g E ≤ cnt ds f E + e

namespace CloseD

variable {D V : Type} {ds : List D} {f g h : D → V} {e e' : Nat}

theorem refl : CloseD ds 0 f f := fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem symm (hc : CloseD ds e f g) : CloseD ds e g f := fun E => ⟨(hc E).2, (hc E).1⟩

/-- **The errors add.** -/
theorem trans (h₁ : CloseD ds e f g) (h₂ : CloseD ds e' g h) : CloseD ds (e + e') f h := fun E =>
  ⟨by have := (h₁ E).1; have := (h₂ E).1; omega, by have := (h₁ E).2; have := (h₂ E).2; omega⟩

theorem mono (he : e ≤ e') (hc : CloseD ds e f g) : CloseD ds e' f g := fun E =>
  ⟨by have := (hc E).1; omega, by have := (hc E).2; omega⟩

end CloseD

/-- **The hybrid argument.**  Two independent stages, each within its own
    error: any function of the pair of views is within
    `|ds₂| · e₁ + |ds₁| · e₂` over the product of the draws. -/
theorem closeD_prod {D₁ D₂ V₁ V₂ V : Type} {ds₁ : List D₁} {ds₂ : List D₂} {e₁ e₂ : Nat}
    {f₁ g₁ : D₁ → V₁} {f₂ g₂ : D₂ → V₂} (h₁ : CloseD ds₁ e₁ f₁ g₁) (h₂ : CloseD ds₂ e₂ f₂ g₂)
    (c : V₁ → V₂ → V) :
    CloseD (lprod ds₁ ds₂) (ds₂.length * e₁ + ds₁.length * e₂)
      (fun p => c (f₁ p.1) (f₂ p.2)) (fun p => c (g₁ p.1) (g₂ p.2)) := by
  intro E
  let ind := fun (v₁ : V₁) (v₂ : V₂) => if E (c v₁ v₂) then 1 else 0
  have ex : ∀ (a : D₁ → V₁) (b : D₂ → V₂), cnt (lprod ds₁ ds₂) (fun p => c (a p.1) (b p.2)) E =
      lsum ds₁ (fun x => lsum ds₂ (fun y => ind (a x) (b y))) :=
    fun a b => lsum_prod (fun p => if E (c (a p.1) (b p.2)) then 1 else 0) ds₂ ds₁
  -- the second stage, for each first draw
  have s2 : ∀ (a : D₁ → V₁) x, (lsum ds₂ fun y => ind (a x) (f₂ y)) ≤ (lsum ds₂ fun y => ind (a x) (g₂ y)) + e₂ ∧
      (lsum ds₂ fun y => ind (a x) (g₂ y)) ≤ (lsum ds₂ fun y => ind (a x) (f₂ y)) + e₂ :=
    fun a x => h₂ (fun v₂ => E (c (a x) v₂))
  -- the first stage, for each second draw
  have s1 : ∀ (b : D₂ → V₂) y, (lsum ds₁ fun x => ind (f₁ x) (b y)) ≤ (lsum ds₁ fun x => ind (g₁ x) (b y)) + e₁ ∧
      (lsum ds₁ fun x => ind (g₁ x) (b y)) ≤ (lsum ds₁ fun x => ind (f₁ x) (b y)) + e₁ :=
    fun b y => h₁ (fun v₁ => E (c v₁ (b y)))
  have A : ∀ (a : D₁ → V₁), (lsum ds₁ fun x => lsum ds₂ fun y => ind (a x) (f₂ y)) ≤
      (lsum ds₁ fun x => lsum ds₂ fun y => ind (a x) (g₂ y)) + ds₁.length * e₂ ∧
      (lsum ds₁ fun x => lsum ds₂ fun y => ind (a x) (g₂ y)) ≤
      (lsum ds₁ fun x => lsum ds₂ fun y => ind (a x) (f₂ y)) + ds₁.length * e₂ := by
    intro a
    rw [← lsum_const e₂ ds₁, ← lsum_add, ← lsum_add]
    exact ⟨lsum_le ds₁ fun x _ => (s2 a x).1, lsum_le ds₁ fun x _ => (s2 a x).2⟩
  have B : ∀ (b : D₂ → V₂), (lsum ds₁ fun x => lsum ds₂ fun y => ind (f₁ x) (b y)) ≤
      (lsum ds₁ fun x => lsum ds₂ fun y => ind (g₁ x) (b y)) + ds₂.length * e₁ ∧
      (lsum ds₁ fun x => lsum ds₂ fun y => ind (g₁ x) (b y)) ≤
      (lsum ds₁ fun x => lsum ds₂ fun y => ind (f₁ x) (b y)) + ds₂.length * e₁ := by
    intro b
    rw [lsum_comm (fun x y => ind (f₁ x) (b y)), lsum_comm (fun x y => ind (g₁ x) (b y)), ← lsum_const e₁ ds₂,
      ← lsum_add, ← lsum_add]
    exact ⟨lsum_le ds₂ fun y _ => (s1 b y).1, lsum_le ds₂ fun y _ => (s1 b y).2⟩
  rw [ex, ex]
  have a1 := (A f₁).1; have a2 := (A f₁).2; have b1 := (B g₂).1; have b2 := (B g₂).2
  exact ⟨by omega, by omega⟩

-- ---------------------------------------------------------------------------
-- The interface
-- ---------------------------------------------------------------------------

/-- **The interface with a distance**: a proof system for a relation over
    statements `T` and witnesses `W`.  The prover and the simulator are
    functions of a draw from `draws`, a nonempty list, the prover's
    `none` an abort; the simulator never aborts.  Completeness (every
    proof the prover outputs verifies) and knowledge soundness are
    assumed, the STARK's; zero knowledge is `CloseD` within `err`, so the
    prover aborts on at most `err` draws (`PSD.aborts_le`). -/
structure PSD (T W : Type) (R : T → W → Prop) where
  Proof : Type
  Draw : Type
  draws : List Draw
  prove : T → W → Draw → Option Proof
  sim : T → Draw → Option Proof
  verify : T → Proof → Prop
  ext : T → Proof → W
  err : T → Nat
  draws_ne : draws ≠ []
  sim_some : ∀ t d, (sim t d).isSome = true
  complete : ∀ t w, R t w → ∀ d π, prove t w d = some π → verify t π
  knowledge : ∀ t π, verify t π → R t (ext t π)
  zk : ∀ t w, R t w → CloseD draws (err t) (prove t w) (sim t)

/-- **The prover aborts on at most `err` draws**: the simulator never
    does, and the two views are within `err`. -/
theorem PSD.aborts_le {T W : Type} {R : T → W → Prop} (ps : PSD T W R) {t : T} {w : W} (h : R t w) :
    cnt ps.draws (ps.prove t w) (fun o => o.isNone) ≤ ps.err t := by
  have hz := (ps.zk t w h (fun o => o.isNone)).1
  have h0 : cnt ps.draws (ps.sim t) (fun o => o.isNone) = 0 := by
    unfold cnt
    rw [show (fun d => if (ps.sim t d).isNone = true then 1 else 0) = fun _ => 0 from funext fun d => by
      have := ps.sim_some t d
      cases hs : ps.sim t d with
      | none => rw [hs] at this; cases this
      | some _ => rfl, lsum_const, Nat.mul_zero]
  omega

/-- The interface for evaluation statements, the witness bits and a term. -/
abbrev EvalPSD (Stmt : Type) (Rel : Stmt → BT → Term → Prop) := PSD Stmt (BT × Term) (fun s w => Rel s w.1 w.2)

/-- **The composition theorem, with a distance.**  Over a proof system for
    evaluation statements, the statement of a formula of atoms under `∧`
    and `∨`: complete, knowledge-sound, zero knowledge within `err`, and
    witness-indistinguishable within `2 · err`: proofs from two accepted
    witnesses, for instance two sides of an `∨`, differ by at most twice
    the error. -/
theorem composeD (ps : EvalPSD EvalStmt EvalRel) (M : MF) :
    (∀ r, Real M.toForm r → ∃ β w, Accepts M β w ∧
      (∀ d π, ps.prove (evalStmtOf M) (β, w) d = some π → ps.verify (evalStmtOf M) π) ∧
      cnt ps.draws (ps.prove (evalStmtOf M) (β, w)) (fun o => o.isNone) ≤ ps.err (evalStmtOf M)) ∧
    (∀ π, ps.verify (evalStmtOf M) π →
      Real M.toForm (readBack M (ps.ext (evalStmtOf M) π).1 (ps.ext (evalStmtOf M) π).2 [])) ∧
    (∀ β w, Accepts M β w →
      CloseD ps.draws (ps.err (evalStmtOf M)) (ps.prove (evalStmtOf M) (β, w)) (ps.sim (evalStmtOf M))) ∧
    (∀ β w β' w', Accepts M β w → Accepts M β' w' →
      CloseD ps.draws (2 * ps.err (evalStmtOf M)) (ps.prove (evalStmtOf M) (β, w))
        (ps.prove (evalStmtOf M) (β', w'))) := by
  refine ⟨fun r hr => ?_, fun π hv => ?_, fun β w h => ps.zk _ (β, w) h, fun β w β' w' h h' => ?_⟩
  · obtain ⟨β, w, hacc⟩ := accepted_of_real hr
    exact ⟨β, w, hacc, ps.complete _ (β, w) hacc, ps.aborts_le hacc⟩
  · exact real_of_accepted (ps.knowledge _ π hv)
  · rw [Nat.two_mul]
    exact (ps.zk _ (β, w) h).trans (ps.zk _ (β', w') h').symm

/-- The pair of two stages' outputs, `none` when either aborts. -/
def pairO {A B : Type} (a : Option A) (b : Option B) : Option (A × B) :=
  match a, b with
  | some x, some y => some (x, y)
  | _, _ => none

/-- **A two-stage chain, with a distance.**  The stages draw independently,
    the chain from the product of their draws; its error is the hybrid
    argument's, `|draws₂| · err₁ + |draws₁| · err₂`. -/
def chain2D {T₁ T₂ W₁ W₂ : Type} {R₁ : T₁ → W₁ → Prop} {R₂ : T₂ → W₂ → Prop}
    (ps₁ : PSD T₁ W₁ R₁) (ps₂ : PSD T₂ W₂ R₂) (link : T₁ → T₂) :
    PSD T₁ (W₁ × W₂) (fun t w => R₁ t w.1 ∧ R₂ (link t) w.2) where
  Proof := ps₁.Proof × ps₂.Proof
  Draw := ps₁.Draw × ps₂.Draw
  draws := lprod ps₁.draws ps₂.draws
  prove t w d := pairO (ps₁.prove t w.1 d.1) (ps₂.prove (link t) w.2 d.2)
  sim t d := pairO (ps₁.sim t d.1) (ps₂.sim (link t) d.2)
  verify t π := ps₁.verify t π.1 ∧ ps₂.verify (link t) π.2
  ext t π := (ps₁.ext t π.1, ps₂.ext (link t) π.2)
  err t := ps₂.draws.length * ps₁.err t + ps₁.draws.length * ps₂.err (link t)
  draws_ne := by
    cases h₁ : ps₁.draws with
    | nil => exact absurd h₁ ps₁.draws_ne
    | cons a l₁ =>
      cases h₂ : ps₂.draws with
      | nil => exact absurd h₂ ps₂.draws_ne
      | cons b l₂ => simp [lprod]
  sim_some t d := by
    have h₁ := ps₁.sim_some t d.1
    have h₂ := ps₂.sim_some (link t) d.2
    cases e₁ : ps₁.sim t d.1 with
    | none => rw [e₁] at h₁; cases h₁
    | some x =>
      cases e₂ : ps₂.sim (link t) d.2 with
      | none => rw [e₂] at h₂; cases h₂
      | some y => simp [pairO]
  complete t w h d π hp := by
    unfold pairO at hp
    split at hp
    · next x y h1 h2 =>
      cases hp
      exact ⟨ps₁.complete t w.1 h.1 d.1 x h1, ps₂.complete (link t) w.2 h.2 d.2 y h2⟩
    · cases hp
  knowledge t π h := ⟨ps₁.knowledge t π.1 h.1, ps₂.knowledge (link t) π.2 h.2⟩
  zk t w h := closeD_prod (ps₁.zk t w.1 h.1) (ps₂.zk (link t) w.2 h.2) pairO

/-- The chain's draws: the product of the stages'. -/
theorem chain2D_draws {T₁ T₂ W₁ W₂ : Type} {R₁ : T₁ → W₁ → Prop} {R₂ : T₂ → W₂ → Prop}
    (ps₁ : PSD T₁ W₁ R₁) (ps₂ : PSD T₂ W₂ R₂) (link : T₁ → T₂) :
    (chain2D ps₁ ps₂ link).draws.length = ps₁.draws.length * ps₂.draws.length :=
  lprod_length _ _

end Compose
