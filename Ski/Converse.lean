import Ski.Apply
open Term

set_option linter.unusedSectionVars false

/-!
# The converse, and the divergence biconditional

`composition_apply` says a derivation of the relational C model gives a
run of the compiled term.  This file proves the converse: a run of the
compiled term that reaches a weak head normal form gives a derivation.
Together they give `composition_diverges`, the jet paper's third outcome
in mechanized form: the compiled program diverges exactly when the C
model derives no outcome, as a biconditional between two
absence-of-derivation propositions.

## The measure

`ApplyRel`'s recursion is not structural: `QThen` runs a quotation popped
from the stack, which is no part of the quotation being run.  So the
converse for `apply` is a strong induction on the number of contractions
to normal form, `StepsN`, as `lean-nock`'s backward simulation is on
fuel.  Two facts about a normalizing run carry it.  Every term the run
passes through normalizes in no more steps (`StepsN.tail`), and in
strictly fewer after the first contraction (`StepsN.tail_lt`), because
reduction is deterministic.  And if `t ⬝ a` normalizes, so does `t`, in
no more steps (`StepsN.app_left`), because normal order reduces the head
first.

A recursive call of `applyU` is always reached after the first
contraction of the call that makes it, so the measure falls.  In the
`QThen` branch, the popped quotation's call sits under `seq`'s three
continuations; `app_left` extracts its normalization, the induction
hypothesis gives its derivation, the forward theorem gives the stack its
result decodes to, and the run continues from `seq`'s continuation into
the call for the rest.

## Both sides occur

Over a table with no static quotations a quotation's code is only pushes
and `i`, and `Ski/Total.lean` proves no program diverges, so both sides
of `composition_diverges` are false there.  A static quotation's body is
code: over the table of `[dup i] dup i`, `LoopTable.cloop_diverges` makes
both sides true for the compiled program itself.
-/

-- ---------------------------------------------------------------------------
-- Counted reduction
-- ---------------------------------------------------------------------------

/-- Exactly `n` contractions. -/
inductive StepsN : Nat → Term → Term → Prop
  | refl (t : Term) : StepsN 0 t t
  | step {n : Nat} {t t' u : Term} (h : Step t t') (hs : StepsN n t' u) : StepsN (n + 1) t u

theorem StepsN.steps {n : Nat} {t u : Term} (h : StepsN n t u) : Steps t u := by
  induction h with
  | refl t => exact .refl t
  | step h _ ih => exact .step h ih

theorem Steps.counted {t u : Term} (h : Steps t u) : ∃ n, StepsN n t u := by
  induction h with
  | refl t => exact ⟨0, .refl t⟩
  | step h _ ih =>
    cases ih with
    | intro n hn => exact ⟨n + 1, .step h hn⟩

/-- Every term a normalizing run passes through normalizes, in no more steps. -/
theorem StepsN.tail {t u w : Term} {n : Nat} (h : Steps t u) (hw : StepsN n t w) (ww : Whnf w) :
    ∃ m, m ≤ n ∧ StepsN m u w := by
  induction h generalizing n with
  | refl _ => exact ⟨n, Nat.le_refl n, hw⟩
  | step s _ ih =>
    cases hw with
    | refl _ => exact (ww.no_step s).elim
    | step s' hw' =>
      have e := Step.det s' s
      subst e
      cases ih hw' with
      | intro m hm => exact ⟨m, Nat.le_succ_of_le hm.1, hm.2⟩

theorem StepsN.after_step {t t' w : Term} {n : Nat} (s : Step t t') (hw : StepsN n t w)
    (ww : Whnf w) : ∃ m, n = m + 1 ∧ StepsN m t' w := by
  cases hw with
  | refl _ => exact (ww.no_step s).elim
  | step s' hw' =>
    have e := Step.det s' s
    subst e
    exact ⟨_, rfl, hw'⟩

/-- After a first contraction, strictly fewer steps remain. -/
theorem StepsN.tail_lt {t t1 u w : Term} {n : Nat} (s : Step t t1) (h : Steps t1 u)
    (hw : StepsN n t w) (ww : Whnf w) : ∃ m, m < n ∧ StepsN m u w := by
  cases StepsN.after_step s hw ww with
  | intro m hm =>
    cases StepsN.tail h hm.2 ww with
    | intro m' hm' =>
      rw [hm.1]
      exact ⟨m', Nat.lt_succ_of_le hm'.1, hm'.2⟩

theorem Whnf.fn {t a : Term} (h : Whnf (t ⬝ a)) : Whnf t := by
  cases h with
  | S1 _ => exact .S
  | S2 x _ => exact .S1 x
  | K1 _ => exact .K

/-- If `t ⬝ a` normalizes, so does `t`: normal order reduces the head first. -/
theorem StepsN.app_left : ∀ {n : Nat} {t a w : Term}, StepsN n (t ⬝ a) w → Whnf w →
    ∃ m v, m ≤ n ∧ StepsN m t v ∧ Whnf v := by
  intro n
  induction n with
  | zero =>
    intro t a w hw ww
    cases hw
    exact ⟨0, t, Nat.le_refl 0, .refl t, ww.fn⟩
  | succ n ih =>
    intro t a w hw ww
    cases progress t with
    | inl ht => exact ⟨0, t, Nat.zero_le _, .refl t, ht⟩
    | inr hs =>
      cases hs with
      | intro t' s =>
        cases hw with
        | step s' hw' =>
          have e := Step.det s' (Step.left a s)
          subst e
          cases ih hw' ww with
          | intro m hm =>
            cases hm with
            | intro v hv => exact ⟨m + 1, v, Nat.succ_le_succ hv.1, .step s hv.2.1, hv.2.2⟩

/-- `t` reaches a weak head normal form. -/
def Converges (t : Term) : Prop := ∃ u, Eval t u

theorem Converges.of_steps {t u : Term} (h : Steps t u) (hc : Converges t) : Converges u := by
  cases hc with
  | intro w hw =>
    cases hw.1.counted with
    | intro n hn =>
      cases StepsN.tail h hn hw.2 with
      | intro m hm => exact ⟨w, hm.2.steps, hw.2⟩

theorem Converges.app_left {t a : Term} (hc : Converges (t ⬝ a)) : Converges t := by
  cases hc with
  | intro w hw =>
    cases hw.1.counted with
    | intro n hn =>
      cases StepsN.app_left hn hw.2 with
      | intro m hm =>
        cases hm with
        | intro v hv => exact ⟨v, hv.2.1.steps, hv.2.2⟩

theorem Converges.app3_left {t a b c : Term} (hc : Converges (t ⬝ a ⬝ b ⬝ c)) : Converges t :=
  hc.app_left.app_left.app_left

theorem StepsN.app3_left {n : Nat} {t a b c w : Term} (hw : StepsN n (t ⬝ a ⬝ b ⬝ c) w)
    (ww : Whnf w) : ∃ m v, m ≤ n ∧ StepsN m t v ∧ Whnf v := by
  cases StepsN.app_left hw ww with | intro m1 h1 => cases h1 with | intro v1 h1 =>
  cases StepsN.app_left h1.2.1 h1.2.2 with | intro m2 h2 => cases h2 with | intro v2 h2 =>
  cases StepsN.app_left h2.2.1 h2.2.2 with | intro m3 h3 => cases h3 with | intro v3 h3 =>
  exact ⟨m3, v3, Nat.le_trans h3.1 (Nat.le_trans h2.1 h1.1), h3.2.1, h3.2.2⟩

variable [Kit] [KitElim] [KitWords]

-- ---------------------------------------------------------------------------
-- The paths a word takes to its quotation eliminator
-- ---------------------------------------------------------------------------

theorem path_i (apT : Term) {s : Term} {r : Quotation} {t : Stack}
    (hs : DecStack s (.quot r :: t)) :
    ∃ x th, Steps (phi .i ⬝ apT ⬝ s) (apT ⬝ x ⬝ th) ∧ DecQuot x r ∧ DecStack th t := by
  cases wDo_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  exact ⟨x, _, h3.1.trans (h2.2.2 x), h3.2, DecStack.of_steps (steps_thunk2 _ _ _) h1.2.2⟩

theorem path_dip (apT : Term) {s : Term} {r : Quotation} {b : Item} {u : Stack}
    (hs : DecStack s (.quot r :: b :: u)) :
    ∃ x g2 k0 k1 k2, Steps (phi .dip ⬝ apT ⬝ s) (apT ⬝ x ⬝ g2 ⬝ k0 ⬝ k1 ⬝ k2) ∧
      DecQuot x r ∧ DecStack g2 u := by
  cases wDip_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
  cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 => cases h5 with | intro g2 h5 =>
  cases h4.2.2 f2 g2 with | intro k0 h6 => cases h6 with | intro k1 h6 =>
  cases h6 with | intro k2 h6 =>
  exact ⟨x, g2, k0, k1, k2, h5.1.trans h6.1, h3.2, h5.2.2⟩

/-- `ifz`'s path on a well-shaped stack, to the branch it runs. -/
theorem path_ifz (apT : Term) {s : Term} {sc z : Quotation} {k : Nat} {v : Stack}
    (hs : DecStack s (.quot sc :: .quot z :: .num k :: v)) :
    (k = 0 → ∃ y g3, Steps (phi .ifz ⬝ apT ⬝ s) (apT ⬝ y ⬝ g3) ∧ DecQuot y z ∧ DecStack g3 v) ∧
    (∀ m, k = m + 1 → ∃ x p, Steps (phi .ifz ⬝ apT ⬝ s) (apT ⬝ x ⬝ p) ∧ DecQuot x sc ∧
      DecStack p (.num m :: v)) := by
  cases wIfz_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
  cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 => cases h5 with | intro g2 h5 =>
  cases h4.2.2 f2 g2 with | intro e0' h6 => cases h6 with | intro e1' h6 =>
  cases item_quot h5.2.1 (h5.1.trans h6.1) with | intro y h7 =>
  cases h6.2.2 y with | intro d0' h8 => cases h8 with | intro d1' h8 =>
  cases stack_push h5.2.2 (h7.1.trans h8.1) with | intro f3 h9 => cases h9 with | intro g3 h9 =>
  cases h8.2.2 f3 g3 with | intro E0 h10 => cases h10 with | intro E1 h10 =>
  cases item_num h9.2.1 (h9.1.trans h10.1) with | intro fn h11 =>
  cases h10.2.2 fn with | intro N0 h12 => cases h12 with | intro N1 h12 =>
  constructor
  · intro hk
    subst hk
    exact ⟨y, g3, (nat_zero h11.2 (h11.1.trans h12.1)).trans h12.2.1, h7.2, h9.2.2⟩
  · intro m hk
    subst hk
    cases nat_succ h11.2 (h11.1.trans h12.1) with | intro fm h13 =>
    cases h12.2.2 fm with | intro p h14 =>
    exact ⟨x, p, h13.1.trans h14.1, h3.2,
      DecStack.of_steps h14.2
        (dec_push (dec_num h13.2) (DecStack.of_steps (steps_thunk1 _ _) h9.2.2))⟩

-- ---------------------------------------------------------------------------
-- The converse for `apply`
-- ---------------------------------------------------------------------------

theorem fixSelf_first (F z a b : Term) :
    Step (fixSelf F z ⬝ a ⬝ b) (S ⬝ I ⬝ I ⬝ z ⬝ a ⬝ b) :=
  .left b (.left a (.left z (.K _ _)))

theorem fixSelf_rest {F z : Term} (hz : Steps z (fixB F)) (a b : Term) :
    Steps (S ⬝ I ⬝ I ⬝ z ⬝ a ⬝ b) (F ⬝ fixSelf F (I ⬝ z) ⬝ a ⬝ b) :=
  (Steps.left b (iter_sound (k := 2) rfl : Steps (S ⬝ I ⬝ I ⬝ z ⬝ a) (z ⬝ (I ⬝ z) ⬝ a))).trans
    ((Steps.app2 a b (Steps.left (I ⬝ z) hz)).trans (Steps.app2 a b (fixB_unfold F _)))

variable [KitApply]

/-- A normalizing self-reference of `applyU` has a derivation. -/
def ApplyClaim (n : Nat) : Prop :=
  ∀ {z fq fs w : Term} {q : Quotation} {S : Stack}, Steps z (fixB applyF) →
    DecQuot fq q → DecStack fs S → StepsN n (fixSelf applyF z ⬝ fq ⬝ fs) w → Whnf w →
    ∃ o, ApplyRel q S o

/-- Whenever the eliminator `apT` normalizes on decoding inputs within `n`
    contractions, `ApplyRel` derives an outcome. -/
def ElimClaim (apT : Term) (n : Nat) : Prop :=
  ∀ {fq fs w : Term} {q : Quotation} {S : Stack}, DecQuot fq q → DecStack fs S →
    StepsN n (apT ⬝ fq ⬝ fs) w → Whnf w → ∃ o, ApplyRel q S o

/-- A normalizing word has a derivation, given its eliminator's claim up to
    the word's count. -/
theorem word_complete_at {apT : Term} {n : Nat} (hE : ∀ m, m ≤ n → ElimClaim apT m) :
    ∀ {s w' : Term} {w : Word} {S : Stack}, DecStack s S →
      StepsN n (wordTerm apT w ⬝ s) w' → Whnf w' → ∃ o, Run (.word w) S o := by
  intro s w' w S hs hw ww
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
        cases path_i apT hs with | intro x h => cases h with | intro th h =>
        cases StepsN.tail h.1 hw ww with | intro m hm =>
        cases hE m hm.1 h.2.1 h.2.2 hm.2 ww with
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
          cases path_dip apT hs with | intro x h => cases h with | intro g2 h =>
          cases h with | intro k0 h => cases h with | intro k1 h => cases h with | intro k2 h =>
          cases StepsN.tail h.1 hw ww with | intro m hm =>
          cases StepsN.app3_left hm.2 ww with | intro m' h' => cases h' with | intro v h' =>
          cases hE m' (Nat.le_trans h'.1 hm.1) h.2.1 h.2.2 h'.2.1 h'.2.2 with
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
    | quot z' =>
    cases u with
    | nil => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | cons c v =>
    cases c with
    | quot q => exact ⟨_, .ifz_bad (fun _ _ _ _ e => by cases e)⟩
    | num k =>
    have hp := path_ifz apT hs
    cases k with
    | zero =>
      cases hp.1 rfl with | intro y h => cases h with | intro g3 h =>
      cases StepsN.tail h.1 hw ww with | intro m hm =>
      cases hE m hm.1 h.2.1 h.2.2 hm.2 ww with
      | intro o ho => exact ⟨o, .ifz_zero ho⟩
    | succ m =>
      cases hp.2 m rfl with | intro x h => cases h with | intro p h =>
      cases StepsN.tail h.1 hw ww with | intro m' hm =>
      cases hE m' hm.1 h.2.1 h.2.2 hm.2 ww with
      | intro o ho => exact ⟨o, .ifz_succ ho⟩

/-- A normalizing compiled program has a derivation: by recursion on the
    program, given a sound eliminator and its claim up to the program's
    count. -/
theorem prog_complete_at {apT : Term} {n : Nat} (hS : ApSoundR apT ApplyRel)
    (hE : ∀ m, m ≤ n → ElimClaim apT m) :
    ∀ (p : List Word) {t s w' : Term} {st : Stack}, p.all (Word.ok Kit.n) = true →
      Compiles apT p t → DecStack s st → StepsN n (t ⬝ s) w' → Whnf w' →
      ∃ o, Run (.prog p) st o
  | [], _, _, _, st, _, _, _, _, _ => ⟨_, .nil st⟩
  | [w], _, s, _, _, _, ht, hs, hw, ww => by
    cases StepsN.tail (Steps.left s ht) hw ww with
    | intro m hm =>
      cases word_complete_at (fun m' hm' => hE m' (Nat.le_trans hm' hm.1)) hs hm.2 ww with
      | intro o ho =>
        cases o with
        | val S' => exact ⟨_, .seq_val ho (.nil S')⟩
        | err => exact ⟨_, .seq_err ho⟩
  | w :: w' :: p, _, s, _, _, hok, ht, hs, hw, ww => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases ht with
    | intro g hg =>
    cases seq_stages (wordTerm apT w) g s with
    | intro j0 h => cases h with | intro j1 h => cases h with | intro j2 h =>
    have toWord := (Steps.left s hg.1).trans h.1
    cases StepsN.tail toWord hw ww with | intro m hm =>
    cases StepsN.app3_left hm.2 ww with | intro m' h' => cases h' with | intro v h' =>
    cases word_complete_at (fun m'' hm'' => hE m'' (Nat.le_trans hm'' (Nat.le_trans h'.1 hm.1)))
        hs h'.2.1 h'.2.2 with
    | intro o1 ho1 =>
      cases o1 with
      | err => exact ⟨_, .seq_err ho1⟩
      | val S' =>
        cases leafR hS hok.1 hs ho1.word_cwR with | intro u hu =>
        cases hu.2.probe_val j0 j1 j2 with | intro fv hv =>
        cases StepsN.tail
            (toWord.trans ((Steps.app3 j0 j1 j2 hu.1.1).trans (hv.1.trans (h.2.1 fv)))) hw ww with
        | intro m2 hm2 =>
          cases prog_complete_at hS (fun m'' hm'' => hE m'' (Nat.le_trans hm'' hm2.1)) (w' :: p)
              (by simp only [List.all_cons, Bool.and_eq_true]; exact hok.2) hg.2 hv.2 hm2.2 ww with
          | intro o ho => exact ⟨o, .seq_val ho1 ho⟩

theorem applySelf_soundR {z : Term} (hz : Steps z (fixB applyF)) :
    ApSoundR (fixSelf applyF z) ApplyRel :=
  fun _ _ _ h _ _ hr hu => applySelf_sound h hz hr hu

/-- A normalizing self-reference of `applyU` has a derivation, from the
    claim at every smaller count. -/
theorem apply_complete_at {n : Nat} (hA : ∀ m, m < n → ApplyClaim m) : ApplyClaim n := by
  intro z fq fs w q S hz hq hs hw ww
  have reach : ∀ {u : Term},
      Steps (applyF ⬝ fixSelf applyF (I ⬝ z) ⬝ fq ⬝ fs) u → ∃ m, m < n ∧ StepsN m u w :=
    fun hu => StepsN.tail_lt (fixSelf_first applyF z fq fs) ((fixSelf_rest hz fq fs).trans hu) hw ww
  have hz' := fixSelf_inv hz
  cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
  cases q with
  | stat k =>
    cases reach (h.1.trans ((hq.probe_stat.2 ks).trans (h.2.1 k hq.1))) with
    | intro m hm =>
      cases prog_complete_at (applySelf_soundR hz')
          (fun m' hm' _ _ _ _ _ hq' hs' hw' ww' => hA m' (Nat.lt_of_le_of_lt hm' hm.1) hz' hq' hs' hw' ww')
          (Kit.body k) (KitApply.body_ok k hq.1) (KitApply.body_compiles k hq.1 _) hs hm.2 ww with
      | intro o ho => exact ⟨o, .stat hq.1 ho⟩
  | unit x => exact ⟨_, .unit⟩
  | cons x r =>
    cases hq.probe_cons ks with | intro f hf => cases hf with | intro g hg =>
    cases h.2.2.1 f g with | intro P hP =>
    cases reach (h.1.trans (hg.1.trans hP.1)) with | intro m hm =>
    cases hA m hm.1 hz' hg.2.2
        (DecStack.of_steps hP.2 (dec_push hg.2.1 (DecStack.of_steps (steps_thunk1 _ _) hs)))
        hm.2 ww with
    | intro o ho => exact ⟨o, .cons ho⟩
  | «then» b =>
    cases S with
    | nil => exact ⟨_, .then_bad (fun _ _ e => by cases e)⟩
    | cons a t =>
      cases a with
      | num k => exact ⟨_, .then_bad (fun _ _ e => by cases e)⟩
      | quot r =>
        cases hq.probe_then ks with | intro fb hb =>
        have hs' := DecStack.of_steps (steps_thunk2 (fixSelf applyF (I ⬝ z)) fs fb) hs
        have toSeq := h.1.trans (hb.1.trans (h.2.2.2.2 fb))
        cases seq_stages (Scott.wDo ⬝ fixSelf applyF (I ⬝ z))
            (I ⬝ fixSelf applyF (I ⬝ z) ⬝ fb) (K ⬝ K ⬝ fixSelf applyF (I ⬝ z) ⬝ fs ⬝ fb) with
        | intro j0 hj => cases hj with | intro j1 hj => cases hj with | intro j2 hj =>
        cases path_i (fixSelf applyF (I ⬝ z)) hs' with | intro x hx => cases hx with
        | intro th hx =>
        have toCall := toSeq.trans (hj.1.trans (Steps.app3 j0 j1 j2 hx.1))
        cases reach toCall with | intro m1 hm1 =>
        cases StepsN.app3_left hm1.2 ww with | intro m2 h2 => cases h2 with | intro v h2 =>
        cases hA m2 (Nat.lt_of_le_of_lt h2.1 hm1.1) hz' hx.2.1 hx.2.2 h2.2.1 h2.2.2 with
        | intro o1 ho1 =>
          cases o1 with
          | err => exact ⟨_, .then_err ho1⟩
          | val S' =>
            cases applySelf_sound ho1 hz' hx.2.1 hx.2.2 with | intro u hu =>
            cases hu.2.probe_val j0 j1 j2 with | intro fv hv =>
            have toRest := toCall.trans ((Steps.app3 j0 j1 j2 hu.1.1).trans
              (hv.1.trans ((hj.2.1 fv).trans (.single (.left fv (.left fb (.I _)))))))
            cases reach toRest with | intro m3 hm3 =>
            cases hA m3 hm3.1 hz' hb.2 hv.2 hm3.2 ww with
            | intro o2 ho2 => exact ⟨o2, .then_val ho1 ho2⟩

theorem apply_complete_all : ∀ n, ApplyClaim n := by
  have h : ∀ B n, n < B → ApplyClaim n := by
    intro B
    induction B with
    | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
    | succ B ih =>
      intro n hn
      exact apply_complete_at fun m hm => ih m (Nat.lt_of_lt_of_le hm (Nat.le_of_lt_succ hn))
  exact fun n => h (n + 1) n (Nat.lt_succ_self n)

/-- **The converse for `apply`.**  If the table's compiled `applyU`
    normalizes on terms that decode to `q` and `S`, `ApplyRel` derives an
    outcome. -/
theorem apply_complete {fq fs : Term} {q : Quotation} {S : Stack}
    (hc : Converges (Kit.applyU ⬝ fq ⬝ fs)) (hq : DecQuot fq q) (hs : DecStack fs S) :
    ∃ o, ApplyRel q S o := by
  cases hc with
  | intro w hw =>
    cases hw.1.counted with
    | intro n hn =>
      cases StepsN.tail (KitApply.applyU_unfold fq fs) hn hw.2 with
      | intro m hm => exact apply_complete_all m (.refl _) hq hs hm.2 hw.2

/-- **`apply` diverges exactly when `ApplyRel` derives nothing.** -/
theorem apply_diverges {fq fs : Term} {q : Quotation} {S : Stack}
    (hq : DecQuot fq q) (hs : DecStack fs S) :
    Diverges (Kit.applyU ⬝ fq ⬝ fs) ↔ ∀ o, ¬ ApplyRel q S o := by
  constructor
  · intro hd o h
    cases apply_sound _ _ _ h _ _ hq hs with
    | intro u hu => exact hd u hu.1
  · intro hno u he
    cases apply_complete ⟨u, he⟩ hq hs with
    | intro o ho => exact hno o ho

-- ---------------------------------------------------------------------------
-- Programs
-- ---------------------------------------------------------------------------

theorem applyU_claim (n : Nat) : ElimClaim Kit.applyU n := by
  intro fq fs w q S hq hs hw ww
  cases StepsN.tail (KitApply.applyU_unfold fq fs) hw ww with
  | intro m hm => exact apply_complete_all m (.refl _) hq hs hm.2 ww

/-- **The converse of `composition_apply`.**  If a compiled program
    normalizes on a term that decodes to `S`, `Run` derives an outcome. -/
theorem composition_complete {p : List Word} {S : Stack} {t s : Term}
    (hp : p.all (Word.ok Kit.n) = true) (ht : Compiles Kit.applyU p t) (hs : DecStack s S)
    (hc : Converges (t ⬝ s)) : ∃ o, Run (.prog p) S o := by
  cases hc with
  | intro w hw =>
    cases hw.1.counted with
    | intro n hn =>
      exact prog_complete_at apply_sound (fun m _ => applyU_claim m) p hp ht hs hn hw.2

/-- **The divergence biconditional.**  A compiled program diverges on a
    term that decodes to `S` exactly when `Run` derives no outcome: two
    absence-of-derivation propositions, equivalent. -/
theorem composition_diverges {p : List Word} {S : Stack} {t s : Term}
    (hp : p.all (Word.ok Kit.n) = true) (ht : Compiles Kit.applyU p t) (hs : DecStack s S) :
    Diverges (t ⬝ s) ↔ ∀ o, ¬ Run (.prog p) S o := by
  constructor
  · intro hd o h
    cases composition_apply h hp ht hs with
    | intro u hu => exact hd u hu.1
  · intro hno u he
    cases composition_complete hp ht hs ⟨u, he⟩ with
    | intro o ho => exact hno o ho

/-- **Agreement, both ways.**  Whatever a compiled program normalizes to
    decodes to an outcome `Run` derives. -/
theorem composition_exact {p : List Word} {S : Stack} {t s u : Term} {o : Outcome}
    (hp : p.all (Word.ok Kit.n) = true) (ht : Compiles Kit.applyU p t) (hs : DecStack s S)
    (he : Eval (t ⬝ s) u) (hd : Decodes u o) : Run (.prog p) S o := by
  cases composition_complete hp ht hs ⟨u, he⟩ with
  | intro o' ho' =>
    cases composition_apply ho' hp ht hs with
    | intro u' hu' =>
      have e := Eval.deterministic he hu'.1
      rw [← e] at hu'
      rw [Decodes.functional hd hu'.2]
      exact ho'
