import Ski.Converse
open Term

set_option linter.unusedSectionVars false

/-!
# Without static quotations, nothing diverges

No closed `{S, K, I}` term turns a live term into data (Jay and
Given-Wilson; Proposition `prop:quote` of the ski-in-ski manuscript), so
a quotation's code can enter a program only at compile time: SKIlark
defunctionalizes each static quotation into a constructor of a closed
sum, whose body is that quotation's compiled code.  The kernel formalized
here is any table with no static quotations (`Kit.n = 0`, as for the
kernel of `Ski/Scott.lean`), so a quotation built at run time by `cons`,
`unit` and `cat` carries data and `i` and nothing else.

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
    | .stat _ => 1
    | .cons x r => 1 + isz x + qsz r
    | .unit x => 1 + isz x
    | .then b => 1 + qsz b
end

def ssz : Stack → Nat
  | [] => 0
  | a :: s => isz a + ssz s

variable [Kit] [KitElim] [KitWords] [KitApply]

/-- The plain words take valid stacks to valid stacks. -/
theorem cw_ok {n : Nat} {w : Word} {S S' : Stack} (hho : w.ho = false) (hw : w.ok n = true)
    (hS : S.all (Item.ok n) = true) (h : cw (fun _ _ => .err) w S = .val S') :
    S'.all (Item.ok n) = true := by
  cases w with
  | dup =>
    cases S with
    | nil => cases h
    | cons a t => cases h; simp_all [List.all_cons]
  | swap =>
    cases S with
    | nil => cases h
    | cons a t =>
      cases t with
      | nil => cases h
      | cons b u => cases h; simp_all [List.all_cons]
  | pop =>
    cases S with
    | nil => cases h
    | cons a t => cases h; simp_all [List.all_cons]
  | cons =>
    cases S with
    | nil => cases h
    | cons a t =>
      cases a with
      | num k => cases h
      | quot r =>
        cases t with
        | nil => cases h
        | cons b u => cases h; simp_all [List.all_cons, Item.ok, Quotation.ok]
  | cat =>
    cases S with
    | nil => cases h
    | cons a t =>
      cases a with
      | num k => cases h
      | quot r =>
        cases t with
        | nil => cases h
        | cons b u =>
          cases b with
          | num k => cases h
          | quot l => cases h; simp_all [List.all_cons, Item.ok, Quotation.ok]
  | unit =>
    cases S with
    | nil => cases h
    | cons a t => cases h; simp_all [List.all_cons, Item.ok, Quotation.ok]
  | dip => cases hho
  | i => cases hho
  | ifz => cases hho
  | lit k => cases h; simp_all [List.all_cons, Item.ok]
  | quote q => cases h; simp_all [List.all_cons, Item.ok, Word.ok]
  | add =>
    cases S with
    | nil => cases h
    | cons a t =>
      cases a with
      | quot q => cases t <;> cases h
      | num m =>
        cases t with
        | nil => cases h
        | cons b u =>
          cases b with
          | quot q => cases h
          | num k => cases h; simp_all [List.all_cons, Item.ok]

/-- In a table with no static quotations, `ApplyRel` derives an outcome for
    every valid quotation and stack, and a value is valid and never larger
    than the quotation and stack it came from. -/
theorem apply_total_bound (h0 : Kit.n = 0) : ∀ (B : Nat) (q : Quotation) (S : Stack),
    q.ok Kit.n = true → S.all (Item.ok Kit.n) = true → qsz q + ssz S < B →
    ∃ o, ApplyRel q S o ∧ ∀ S', o = .val S' → S'.all (Item.ok Kit.n) = true ∧
      ssz S' ≤ qsz q + ssz S := by
  intro B
  induction B with
  | zero => intro q S _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ B ih =>
    intro q S hq hS hB
    cases q with
    | stat k =>
      simp only [Quotation.ok, h0, decide_eq_true_eq] at hq
      exact absurd hq (Nat.not_lt_zero k)
    | unit x =>
      refine ⟨_, Run.unit, fun S' e => ?_⟩
      cases e
      simp only [Quotation.ok] at hq
      refine ⟨by simp only [List.all_cons, Bool.and_eq_true]; exact ⟨hq, hS⟩, ?_⟩
      simp only [ssz, qsz]
      omega
    | cons x r =>
      simp only [Quotation.ok, Bool.and_eq_true] at hq
      have hlt : qsz r + ssz (x :: S) < B := by simp only [ssz, qsz] at hB ⊢; omega
      cases ih r (x :: S) hq.2 (by simp only [List.all_cons, Bool.and_eq_true]; exact ⟨hq.1, hS⟩)
          hlt with
      | intro o ho =>
        refine ⟨o, Run.cons ho.1, fun S' e => ⟨(ho.2 S' e).1, ?_⟩⟩
        have := (ho.2 S' e).2
        simp only [ssz, qsz] at this ⊢
        omega
    | «then» b =>
      cases S with
      | nil => exact ⟨_, Run.then_bad (fun _ _ e => by cases e), fun _ e => by cases e⟩
      | cons a t =>
        cases a with
        | num n => exact ⟨_, Run.then_bad (fun _ _ e => by cases e), fun _ e => by cases e⟩
        | quot r =>
          simp only [Quotation.ok] at hq
          simp only [List.all_cons, Bool.and_eq_true, Item.ok] at hS
          have h1 : qsz r + ssz t < B := by simp only [ssz, qsz, isz] at hB ⊢; omega
          cases ih r t hS.1 hS.2 h1 with
          | intro o1 ho1 =>
            cases o1 with
            | err => exact ⟨_, Run.then_err ho1.1, fun _ e => by cases e⟩
            | val S1 =>
              have hS1 := ho1.2 S1 rfl
              have h2 : qsz b + ssz S1 < B := by
                have := hS1.2
                simp only [ssz, qsz, isz] at hB this ⊢; omega
              cases ih b S1 hq hS1.1 h2 with
              | intro o2 ho2 =>
                refine ⟨o2, Run.then_val ho1.1 ho2.1, fun S' e => ⟨(ho2.2 S' e).1, ?_⟩⟩
                have := (ho2.2 S' e).2
                have := hS1.2
                simp only [ssz, qsz, isz] at *
                omega

theorem apply_total (h0 : Kit.n = 0) (q : Quotation) (S : Stack) (hq : q.ok Kit.n = true)
    (hS : S.all (Item.ok Kit.n) = true) :
    ∃ o, ApplyRel q S o ∧ ∀ S', o = .val S' → S'.all (Item.ok Kit.n) = true :=
  match apply_total_bound h0 _ q S hq hS (Nat.lt_succ_self _) with
  | ⟨o, ho, hb⟩ => ⟨o, ho, fun S' e => (hb S' e).1⟩

/-- Every valid word, on a valid stack, has an outcome, and its value is valid. -/
theorem word_total (h0 : Kit.n = 0) (w : Word) (S : Stack) (hw : w.ok Kit.n = true)
    (hS : S.all (Item.ok Kit.n) = true) :
    ∃ o, Run (.word w) S o ∧ ∀ S', o = .val S' → S'.all (Item.ok Kit.n) = true := by
  have plain : w.ho = false → ∃ o, Run (.word w) S o ∧
      ∀ S', o = .val S' → S'.all (Item.ok Kit.n) = true :=
    fun hho => ⟨_, .plain hho, fun S' e => cw_ok hho hw hS e⟩
  cases w with
  | dup => exact plain rfl
  | swap => exact plain rfl
  | pop => exact plain rfl
  | cons => exact plain rfl
  | cat => exact plain rfl
  | unit => exact plain rfl
  | lit n => exact plain rfl
  | quote q => exact plain rfl
  | add => exact plain rfl
  | i =>
    cases S with
    | nil => exact ⟨_, .i_bad (fun _ _ e => by cases e), fun _ e => by cases e⟩
    | cons a t =>
      cases a with
      | num n => exact ⟨_, .i_bad (fun _ _ e => by cases e), fun _ e => by cases e⟩
      | quot r =>
        simp only [List.all_cons, Bool.and_eq_true, Item.ok] at hS
        cases apply_total h0 r t hS.1 hS.2 with
        | intro o ho => exact ⟨o, .i_run ho.1, ho.2⟩
  | dip =>
    cases S with
    | nil => exact ⟨_, .dip_bad (fun _ _ _ e => by cases e), fun _ e => by cases e⟩
    | cons a t =>
      cases a with
      | num n => exact ⟨_, .dip_bad (fun _ _ _ e => by cases e), fun _ e => by cases e⟩
      | quot r =>
        cases t with
        | nil => exact ⟨_, .dip_bad (fun _ _ _ e => by cases e), fun _ e => by cases e⟩
        | cons b u =>
          simp only [List.all_cons, Bool.and_eq_true, Item.ok] at hS
          cases apply_total h0 r u hS.1 hS.2.2 with
          | intro o ho =>
            refine ⟨_, .dip_run ho.1, fun S' e => ?_⟩
            cases o with
            | err => cases e
            | val v =>
              cases e
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨hS.2.1, ho.2 v rfl⟩
  | ifz =>
    cases S with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e), fun _ e => by cases e⟩
    | cons a t =>
    cases a with
    | num n => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e), fun _ e => by cases e⟩
    | quot sc =>
    cases t with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e), fun _ e => by cases e⟩
    | cons b u =>
    cases b with
    | num n => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e), fun _ e => by cases e⟩
    | quot z =>
    cases u with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e), fun _ e => by cases e⟩
    | cons c v =>
    cases c with
    | quot q => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e), fun _ e => by cases e⟩
    | num k =>
    simp only [List.all_cons, Bool.and_eq_true, Item.ok] at hS
    cases k with
    | zero =>
      cases apply_total h0 z v hS.2.1 hS.2.2.2 with
      | intro o ho => exact ⟨o, .ifz_zero ho.1, ho.2⟩
    | succ m =>
      cases apply_total h0 sc (.num m :: v) hS.1
          (by simp only [List.all_cons, Bool.and_eq_true, Item.ok]; exact ⟨trivial, hS.2.2.2⟩) with
      | intro o ho => exact ⟨o, .ifz_succ ho.1, ho.2⟩

/-- Every valid program, on a valid stack, has an outcome. -/
theorem program_total (h0 : Kit.n = 0) : ∀ (p : List Word) (S : Stack),
    p.all (Word.ok Kit.n) = true → S.all (Item.ok Kit.n) = true → ∃ o, Run (.prog p) S o
  | [], st, _, _ => ⟨_, .nil st⟩
  | w :: p, st, hp, hS => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    cases word_total h0 w st hp.1 hS with
    | intro o ho =>
      cases o with
      | err => exact ⟨_, .seq_err ho.1⟩
      | val S' =>
        cases program_total h0 p S' hp.2 (ho.2 S' rfl) with
        | intro o' ho' => exact ⟨o', .seq_val ho.1 ho'⟩

/-- **No compiled program over a table without static quotations diverges.** -/
theorem program_converges (h0 : Kit.n = 0) (p : List Word) (S : Stack)
    (hp : p.all (Word.ok Kit.n) = true) (hS : S.all (Item.ok Kit.n) = true) {t s : Term}
    (ht : Compiles Kit.applyU p t) (hs : DecStack s S) :
    ∃ o u, Eval (t ⬝ s) u ∧ Decodes u o ∧ Run (.prog p) S o :=
  match program_total h0 p S hp hS with
  | ⟨o, h⟩ =>
    match composition_apply h hp ht hs with
    | ⟨u, he, hd⟩ => ⟨o, u, he, hd, h⟩

theorem program_not_diverges (h0 : Kit.n = 0) (p : List Word) (S : Stack)
    (hp : p.all (Word.ok Kit.n) = true) (hS : S.all (Item.ok Kit.n) = true) {t s : Term}
    (ht : Compiles Kit.applyU p t) (hs : DecStack s S) : ¬ Diverges (t ⬝ s) :=
  fun hd => match program_converges h0 p S hp hS ht hs with
    | ⟨_, u, he, _, _⟩ => hd u he
