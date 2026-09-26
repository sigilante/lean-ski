import Ski.Converse
open Term

/-!
# Without static quotations, nothing diverges

No closed `{S, K, I}` term turns a live term into data (Jay and
Given-Wilson; Proposition `prop:quote` of the ski-in-ski manuscript), so
a quotation's code can enter a program only at compile time: SKIlark
defunctionalizes each static quotation into a constructor of a closed
sum, whose body is that quotation's compiled code.  The kernel formalized
here has no static quotations, so a quotation built at run time by
`cons`, `unit` and `cat` carries data and `i` and nothing else.

Such a quotation cannot loop.  Running `q` on `S` never produces a stack
larger than `q` and `S` together (`apply_total`, measured by `qsz` and
`ssz`): `cons` moves part of the quotation onto the stack, `unit` pushes
and stops, and `then` runs a quotation popped from the stack and then its
own remainder, each on less.  So `ApplyRel` derives an outcome for every
quotation and stack, every compiled program converges
(`program_converges`), and `composition_diverges` holds with both sides
false.  Divergence enters with the compile-time line: a static quotation
body can hold `dup`, and so Joy's `y`.
-/

mutual
  def isz : Item → Nat
    | .num _ => 1
    | .quot q => 1 + qsz q
  def qsz : Quotation → Nat
    | .cons x r => 1 + isz x + qsz r
    | .unit x => 1 + isz x
    | .then b => 1 + qsz b
end

def ssz : Stack → Nat
  | [] => 0
  | a :: s => isz a + ssz s

/-- `ApplyRel` derives an outcome for every quotation and stack, and a
    value is never larger than the quotation and stack it came from. -/
theorem apply_total_bound : ∀ (B : Nat) (q : Quotation) (S : Stack), qsz q + ssz S < B →
    ∃ o, ApplyRel q S o ∧ ∀ S', o = .val S' → ssz S' ≤ qsz q + ssz S := by
  intro B
  induction B with
  | zero => intro q S h; exact absurd h (Nat.not_lt_zero _)
  | succ B ih =>
    intro q S hB
    cases q with
    | unit x =>
      refine ⟨_, .unit, fun S' e => ?_⟩
      cases e
      simp only [ssz, qsz]
      omega
    | cons x r =>
      have hlt : qsz r + ssz (x :: S) < B := by simp only [ssz, qsz] at hB ⊢; omega
      cases ih r (x :: S) hlt with
      | intro o ho =>
        refine ⟨o, .cons ho.1, fun S' e => ?_⟩
        have := ho.2 S' e
        simp only [ssz, qsz] at this ⊢
        omega
    | «then» b =>
      cases S with
      | nil => exact ⟨_, .then_bad (fun _ _ e => by cases e), fun _ e => by cases e⟩
      | cons a t =>
        cases a with
        | num n => exact ⟨_, .then_bad (fun _ _ e => by cases e), fun _ e => by cases e⟩
        | quot r =>
          have h1 : qsz r + ssz t < B := by simp only [ssz, qsz, isz] at hB ⊢; omega
          cases ih r t h1 with
          | intro o1 ho1 =>
            cases o1 with
            | err => exact ⟨_, .then_err ho1.1, fun _ e => by cases e⟩
            | val S1 =>
              have hS1 := ho1.2 S1 rfl
              have h2 : qsz b + ssz S1 < B := by simp only [ssz, qsz, isz] at hB hS1 ⊢; omega
              cases ih b S1 h2 with
              | intro o2 ho2 =>
                refine ⟨o2, .then_val ho1.1 ho2.1, fun S' e => ?_⟩
                have := ho2.2 S' e
                simp only [ssz, qsz, isz] at this hS1 ⊢
                omega

theorem apply_total (q : Quotation) (S : Stack) : ∃ o, ApplyRel q S o :=
  match apply_total_bound _ q S (Nat.lt_succ_self _) with
  | ⟨o, ho, _⟩ => ⟨o, ho⟩

/-- Every word has a relational outcome. -/
theorem word_total (w : Word) (S : Stack) : ∃ o, CwR ApplyRel w S o := by
  cases w with
  | dup => exact ⟨_, .plain rfl⟩
  | swap => exact ⟨_, .plain rfl⟩
  | pop => exact ⟨_, .plain rfl⟩
  | cons => exact ⟨_, .plain rfl⟩
  | cat => exact ⟨_, .plain rfl⟩
  | unit => exact ⟨_, .plain rfl⟩
  | lit n => exact ⟨_, .plain rfl⟩
  | quote q => exact ⟨_, .plain rfl⟩
  | add => exact ⟨_, .plain rfl⟩
  | i =>
    cases S with
    | nil => exact ⟨_, .i_bad (fun _ _ e => by cases e)⟩
    | cons a t =>
      cases a with
      | num n => exact ⟨_, .i_bad (fun _ _ e => by cases e)⟩
      | quot r =>
        cases apply_total r t with
        | intro o ho => exact ⟨o, .i_run ho⟩
  | dip =>
    cases S with
    | nil => exact ⟨_, .dip_bad (fun _ _ _ e => by cases e)⟩
    | cons a t =>
      cases a with
      | num n => exact ⟨_, .dip_bad (fun _ _ _ e => by cases e)⟩
      | quot r =>
        cases t with
        | nil => exact ⟨_, .dip_bad (fun _ _ _ e => by cases e)⟩
        | cons b u =>
          cases apply_total r u with
          | intro o ho => exact ⟨_, .dip_run ho⟩
  | ifz =>
    cases S with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | cons a t =>
    cases a with
    | num n => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | quot sc =>
    cases t with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | cons b u =>
    cases b with
    | num n => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | quot z =>
    cases u with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | cons c v =>
    cases c with
    | quot q => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | num k =>
    cases k with
    | zero =>
      cases apply_total z v with
      | intro o ho => exact ⟨o, .ifz_zero ho⟩
    | succ m =>
      cases apply_total sc (.num m :: v) with
      | intro o ho => exact ⟨o, .ifz_succ ho⟩

/-- Every word list has a relational outcome. -/
theorem program_total : ∀ (p : List Word) (S : Stack), ∃ o, CsemR ApplyRel p S o
  | [], st => ⟨_, .nil st⟩
  | w :: p, st =>
    match word_total w st with
    | ⟨.err, hw⟩ => ⟨_, .err hw⟩
    | ⟨.val S', hw⟩ =>
      match program_total p S' with
      | ⟨o, hp⟩ => ⟨o, .val hw hp⟩

/-- **No compiled program without static quotations diverges.** -/
theorem program_converges (p : List Word) (S : Stack) {s : Term} (hs : DecStack s S) :
    ∃ o u, Eval (N Scott.applyU p ⬝ s) u ∧ Decodes u o ∧ CsemR ApplyRel p S o :=
  match program_total p S with
  | ⟨o, hp⟩ =>
    match composition_apply hp hs with
    | ⟨u, he, hd⟩ => ⟨o, u, he, hd, hp⟩

theorem program_not_diverges (p : List Word) (S : Stack) {s : Term} (hs : DecStack s S) :
    ¬ Diverges (N Scott.applyU p ⬝ s) :=
  fun hd => match program_converges p S hs with
    | ⟨_, u, he, _, _⟩ => hd u he
