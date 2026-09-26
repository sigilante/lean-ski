import Ski.Composition
open Term

/-!
# `apply`: running quotations

SKIlark defunctionalizes quotations, and the compiled kernel runs one with

    applyU q s = q |> { QCons x r (applyU r (Push x s)); QUnit x (RVal (Push x s));
                        QThen b (seq (wDo applyU) (applyU b) s) }

so Joy's `i` is `wDo applyU`, a case over the constructors plus `seq`.
`ApplyRel q S o` is its big-step semantics: `QCons` pushes and continues,
`QUnit` pushes and stops, `QThen b` pops a quotation, runs it, then runs
`b`, strictly.  A run that never returns has no derivation.

## The relational word semantics

With `apply` a relation, the words that run quotations get a relational
model: `CwR R w S o` is `cw` with the quotation's meaning given by a
relation `R`, and `CsemR R` threads it through a word list.
`ApSoundR apT R` says the eliminator term meets `R` wherever `R` derives.
`composition_rel` is `composition` over this semantics: it needs only
the leaves' pointwise forms (`leafD_i_run`, `leafD_dip_run`), since each
use of `R` supplies the one `(r, u)` it is needed at.

## The theorem

`apply_sound : ApSoundR Scott.applyU ApplyRel`.  `applyU` is `Y` applied
to its body, as `add` is, and the recursion is proved over every
self-reference `fixSelf applyF z` with `z ⟶* fixB applyF`, by induction on
the `ApplyRel` derivation.  `composition_apply` follows: every compiled
program over the no-static-quotation kernel, run with the compiled
`applyU`, meets the relational C model wherever it derives an outcome.
`ApplyRel.det` falls out: the relation is a function.

This is the forward direction.  The converse (a compiled run that
reaches a decodable normal form has a derivation), and with it the
divergence biconditional, is not proved here.
-/

-- ---------------------------------------------------------------------------
-- The fixpoint combinator, generically
-- ---------------------------------------------------------------------------

/-- `Y = S (K (S I I)) (S (S (K S) K) (K (S I I)))`, as `skijack` emits it. -/
def fixY : Term := S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)))

/-- `λ x. F (x x)`, the self-application `Y F` unrolls through. -/
def fixB (F : Term) : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ F

/-- A self-reference of `Y F`, as the unrolling produces it. -/
def fixSelf (F z : Term) : Term := K ⬝ (S ⬝ I ⬝ I) ⬝ F ⬝ z

theorem fix_unfold (F a : Term) : Steps (fixY ⬝ F ⬝ a) (fixSelf F (fixB F) ⬝ a) :=
  iter_sound (k := 1) rfl

theorem fixB_unfold (F y : Term) : Steps (fixB F ⬝ y) (F ⬝ fixSelf F y) :=
  iter_sound (k := 5) rfl

/-- Each unrolling wraps the self-application in one more `I`; the loop
    invariant is that it still reduces to `fixB F`. -/
theorem fixSelf_step {F z : Term} (hz : Steps z (fixB F)) (a : Term) :
    Steps (fixSelf F z ⬝ a) (F ⬝ fixSelf F (I ⬝ z) ⬝ a) :=
  (iter_sound (k := 3) rfl : Steps (fixSelf F z ⬝ a) (z ⬝ (I ⬝ z) ⬝ a)).trans
    ((Steps.left a (Steps.left (I ⬝ z) hz)).trans (Steps.left a (fixB_unfold F _)))

theorem fixSelf_inv {F z : Term} (hz : Steps z (fixB F)) : Steps (I ⬝ z) (fixB F) :=
  .step (.I z) hz

-- ---------------------------------------------------------------------------
-- The relational word semantics
-- ---------------------------------------------------------------------------

/-- The words that run a quotation. -/
def Word.ho : Word → Bool
  | .dip | .i | .ifz => true
  | _ => false

/-- `cw`, with the quotation's meaning a relation. -/
inductive CwR (R : Quotation → Stack → Outcome → Prop) : Word → Stack → Outcome → Prop
  | plain {w S} : w.ho = false → CwR R w S (cw (fun _ _ => .err) w S)
  | i_run {r t o} : R r t o → CwR R .i (.quot r :: t) o
  | i_bad {S} : (∀ r t, S ≠ .quot r :: t) → CwR R .i S .err
  | dip_run {r b u o} : R r u o → CwR R .dip (.quot r :: b :: u) (dipOut b o)
  | dip_bad {S} : (∀ r b u, S ≠ .quot r :: b :: u) → CwR R .dip S .err
  | ifz_zero {sc z v o} : R z v o → CwR R .ifz (.quot sc :: .quot z :: .num 0 :: v) o
  | ifz_succ {sc z m v o} :
      R sc (.num m :: v) o → CwR R .ifz (.quot sc :: .quot z :: .num (m + 1) :: v) o
  | ifz_bad {S} : (∀ sc z n v, S ≠ .quot sc :: .quot z :: .num n :: v) → CwR R .ifz S .err

/-- A word list, threading the stack strictly. -/
inductive CsemR (R : Quotation → Stack → Outcome → Prop) : List Word → Stack → Outcome → Prop
  | nil (S) : CsemR R [] S (.val S)
  | val {w p S S' o} : CwR R w S (.val S') → CsemR R p S' o → CsemR R (w :: p) S o
  | err {w p S} : CwR R w S .err → CsemR R (w :: p) S .err

/-- The eliminator term meets the relation wherever the relation derives. -/
def ApSoundR (apT : Term) (R : Quotation → Stack → Outcome → Prop) : Prop :=
  ∀ r u o, R r u o → ∀ fr fu, DecQuot fr r → DecStack fu u → Contract (apT ⬝ fr ⬝ fu) o

/-- The empty relation is met by every eliminator. -/
theorem apSoundR_empty (apT : Term) : ApSoundR apT (fun _ _ _ => False) :=
  fun _ _ _ h => h.elim

-- ---------------------------------------------------------------------------
-- Relational leaves for `i`, `dip`, `ifz`
-- ---------------------------------------------------------------------------

theorem leafR_i {apT : Term} {R : Quotation → Stack → Outcome → Prop} (hR : ApSoundR apT R)
    {S : Stack} {s : Term} {o : Outcome} (hs : DecStack s S) (hc : CwR R .i S o) :
    Contract (phi .i ⬝ apT ⬝ s) o := by
  cases wDo_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil =>
    cases hc with
    | plain hw => cases hw
    | i_bad _ => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n =>
      cases hc with
      | plain hw => cases hw
      | i_bad _ => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot r =>
      cases hc with
      | plain hw => cases hw
      | i_run hr => exact leafD_i_run apT r t o hs (hR r t o hr)
      | i_bad hb => exact absurd rfl (hb r t)

theorem leafR_dip {apT : Term} {R : Quotation → Stack → Outcome → Prop} (hR : ApSoundR apT R)
    {S : Stack} {s : Term} {o : Outcome} (hs : DecStack s S) (hc : CwR R .dip S o) :
    Contract (phi .dip ⬝ apT ⬝ s) o := by
  cases wDip_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil =>
    cases hc with
    | plain hw => cases hw
    | dip_bad _ => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n =>
      cases hc with
      | plain hw => cases hw
      | dip_bad _ => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot r =>
      cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
      cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
      cases t with
      | nil =>
        cases hc with
        | plain hw => cases hw
        | dip_bad _ => exact stack_err h1.2.2 (h3.1.trans h4.1) h4.2.1
      | cons b u =>
        cases hc with
        | plain hw => cases hw
        | dip_run hr =>
          exact leafD_dip_run apT r b u _ hs fun fr fu hfr hfu =>
            match hR r u _ hr fr fu hfr hfu with
            | ⟨_, he, hd⟩ => Decodes.of_steps he.1 hd
        | dip_bad hb => exact absurd rfl (hb r b u)

theorem leafR_ifz {apT : Term} {R : Quotation → Stack → Outcome → Prop} (hR : ApSoundR apT R)
    {S : Stack} {s : Term} {o : Outcome} (hs : DecStack s S) (hc : CwR R .ifz S o) :
    Contract (phi .ifz ⬝ apT ⬝ s) o := by
  cases wIfz_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil =>
    cases hc with
    | plain hw => cases hw
    | ifz_bad _ => exact stack_err hs h.1 h.2.1
  | cons a t =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases a with
  | num k =>
    cases hc with
    | plain hw => cases hw
    | ifz_bad _ => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
  | quot sc =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
  cases t with
  | nil =>
    cases hc with
    | plain hw => cases hw
    | ifz_bad _ => exact stack_err h1.2.2 (h3.1.trans h4.1) h4.2.1
  | cons b u =>
  cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 => cases h5 with | intro g2 h5 =>
  cases h4.2.2 f2 g2 with | intro e0' h6 => cases h6 with | intro e1' h6 =>
  cases b with
  | num k =>
    cases hc with
    | plain hw => cases hw
    | ifz_bad _ => exact item_num_err h5.2.1 (h5.1.trans h6.1) h6.2.1
  | quot z =>
  cases item_quot h5.2.1 (h5.1.trans h6.1) with | intro y h7 =>
  cases h6.2.2 y with | intro d0' h8 => cases h8 with | intro d1' h8 =>
  cases u with
  | nil =>
    cases hc with
    | plain hw => cases hw
    | ifz_bad _ => exact stack_err h5.2.2 (h7.1.trans h8.1) h8.2.1
  | cons c v =>
  cases stack_push h5.2.2 (h7.1.trans h8.1) with | intro f3 h9 => cases h9 with | intro g3 h9 =>
  cases h8.2.2 f3 g3 with | intro E0 h10 => cases h10 with | intro E1 h10 =>
  cases c with
  | quot q =>
    cases hc with
    | plain hw => cases hw
    | ifz_bad _ => exact item_quot_err h9.2.1 (h9.1.trans h10.1) h10.2.1
  | num k =>
  cases item_num h9.2.1 (h9.1.trans h10.1) with | intro fn h11 =>
  cases h10.2.2 fn with | intro N0 h12 => cases h12 with | intro N1 h12 =>
  cases k with
  | zero =>
    cases hc with
    | plain hw => cases hw
    | ifz_zero hr =>
      exact Contract.of_steps ((nat_zero h11.2 (h11.1.trans h12.1)).trans h12.2.1)
        (hR z v o hr y g3 h7.2 h9.2.2)
    | ifz_bad hb => exact absurd rfl (hb sc z 0 v)
  | succ m =>
    cases nat_succ h11.2 (h11.1.trans h12.1) with | intro fm h13 =>
    cases h12.2.2 fm with | intro p h14 =>
    cases hc with
    | plain hw => cases hw
    | ifz_succ hr =>
      exact Contract.of_steps (h13.1.trans h14.1)
        (hR sc (.num m :: v) o hr x p h3.2
          (DecStack.of_steps h14.2
            (dec_push (dec_num h13.2) (DecStack.of_steps (steps_thunk1 _ _) h9.2.2))))
    | ifz_bad hb => exact absurd rfl (hb sc z (m + 1) v)

/-- **Every word meets its relational contract.** -/
theorem leafR {apT : Term} {R : Quotation → Stack → Outcome → Prop} (hR : ApSoundR apT R)
    {w : Word} {S : Stack} {s : Term} {o : Outcome} (hs : DecStack s S) (hc : CwR R w S o) :
    Contract (wordTerm apT w ⬝ s) o := by
  cases w with
  | dip => exact leafR_dip hR hs hc
  | i => exact leafR_i hR hs hc
  | ifz => exact leafR_ifz hR hs hc
  | dup => cases hc with | plain _ => exact leafD_dup _ S hs
  | swap => cases hc with | plain _ => exact leafD_swap _ S hs
  | pop => cases hc with | plain _ => exact leafD_pop _ S hs
  | cons => cases hc with | plain _ => exact leafD_cons _ S hs
  | cat => cases hc with | plain _ => exact leafD_cat _ S hs
  | unit => cases hc with | plain _ => exact leafD_unit _ S hs
  | lit n => cases hc with | plain _ => exact leafD_lit _ n S hs
  | quote q => cases hc with | plain _ => exact leafD_quote _ q S hs
  | add => cases hc with | plain _ => exact leafD_add _ S hs

/-- **Composition, relationally.** -/
theorem composition_rel {apT : Term} {R : Quotation → Stack → Outcome → Prop}
    (hR : ApSoundR apT R) {p : List Word} {S : Stack} {o : Outcome} (h : CsemR R p S o) :
    ∀ {s : Term}, DecStack s S → Contract (N apT p ⬝ s) o := by
  induction h with
  | nil S => exact fun hs => idW_contract hs
  | @val w p S S' o hw hp ih =>
    intro s hs
    cases p with
    | nil =>
      cases hp
      exact leafR hR hs hw
    | cons w' p' =>
      exact seq_contract (k := fun _ => o) (leafR hR hs hw)
        (fun _ _ he ht => by cases he; exact ih ht)
  | @err w p S hw =>
    intro s hs
    cases p with
    | nil => exact leafR hR hs hw
    | cons w' p' =>
      exact seq_contract (k := fun _ => Outcome.err) (leafR hR hs hw)
        (fun _ _ he _ => by cases he)

-- ---------------------------------------------------------------------------
-- `ApplyRel` and the compiled `applyU`
-- ---------------------------------------------------------------------------

/-- The big-step semantics of `applyU`.  `then b` is `i` followed by `b`. -/
inductive ApplyRel : Quotation → Stack → Outcome → Prop
  | cons {x r S o} : ApplyRel r (x :: S) o → ApplyRel (.cons x r) S o
  | unit {x S} : ApplyRel (.unit x) S (.val (x :: S))
  | then_val {b r t S' o} :
      ApplyRel r t (.val S') → ApplyRel b S' o → ApplyRel (.then b) (.quot r :: t) o
  | then_err {b r t} : ApplyRel r t .err → ApplyRel (.then b) (.quot r :: t) .err
  | then_bad {b S} : (∀ r t, S ≠ .quot r :: t) → ApplyRel (.then b) S .err

/-- The argument of an application. -/
def Term.argOf : Term → Term
  | app _ x => x
  | t => t

/-- The body of `applyU`: `Scott.applyU` is `fixY ⬝ applyF`. -/
def applyF : Term := Scott.applyU.argOf

theorem applyU_unfold (fq fs : Term) :
    Steps (Scott.applyU ⬝ fq ⬝ fs) (fixSelf applyF (fixB applyF) ⬝ fq ⬝ fs) :=
  iter_sound (k := 1) rfl

theorem applyF_stages (R q s : Term) : ∃ k0 k1 k2,
    Steps (applyF ⬝ R ⬝ q ⬝ s) (q ⬝ k0 ⬝ k1 ⬝ k2) ∧
    (∀ x r, ∃ P, Steps (k0 ⬝ x ⬝ r) (R ⬝ r ⬝ P) ∧
      Steps P (Scott.Push ⬝ x ⬝ (K ⬝ s ⬝ x))) ∧
    (∀ x, ∃ G, Steps (k1 ⬝ x) (Scott.RVal ⬝ G) ∧ Steps G (Scott.Push ⬝ x ⬝ (K ⬝ s ⬝ x))) ∧
    (∀ b, Steps (k2 ⬝ b)
      (Scott.seq ⬝ (Scott.wDo ⬝ R) ⬝ (I ⬝ R ⬝ b) ⬝ (K ⬝ K ⬝ R ⬝ s ⬝ b))) :=
  ⟨_, _, _, iter_sound (k := 25) rfl,
    fun _ _ => ⟨_, iter_sound (k := 17) rfl, iter_sound (k := 9) rfl⟩,
    fun _ => ⟨_, iter_sound (k := 6) rfl, iter_sound (k := 3) rfl⟩,
    fun _ => iter_sound (k := 22) rfl⟩

/-- The recursion, over every self-reference of `applyU`. -/
theorem applySelf_sound {q : Quotation} {S : Stack} {o : Outcome} (h : ApplyRel q S o) :
    ∀ {z fq fs : Term}, Steps z (fixB applyF) → DecQuot fq q → DecStack fs S →
      Contract (fixSelf applyF z ⬝ fq ⬝ fs) o := by
  induction h with
  | @cons x r S o _ ih =>
    intro z fq fs hz hq hs
    cases applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro k0 h => cases h with
    | intro k1 h => cases h with | intro k2 h =>
    cases hq k0 k1 k2 with | intro f hf => cases hf with | intro g hg =>
    cases h.2.1 f g with | intro P hP =>
    exact Contract.of_steps
      ((Steps.left fs (fixSelf_step hz fq)).trans (h.1.trans (hg.1.trans hP.1)))
      (ih (fixSelf_inv hz) hg.2.2
        (DecStack.of_steps hP.2 (dec_push hg.2.1 (DecStack.of_steps (steps_thunk1 _ _) hs))))
  | @unit x S =>
    intro z fq fs hz hq hs
    cases applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro k0 h => cases h with
    | intro k1 h => cases h with | intro k2 h =>
    cases hq k0 k1 k2 with | intro f hf =>
    cases h.2.2.1 f with | intro G hG =>
    exact contract_val
      ((Steps.left fs (fixSelf_step hz fq)).trans (h.1.trans (hf.1.trans hG.1)))
      (DecStack.of_steps hG.2 (dec_push hf.2 (DecStack.of_steps (steps_thunk1 _ _) hs)))
  | @then_val b r t S' o _ _ ih1 ih2 =>
    intro z fq fs hz hq hs
    cases applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro k0 h => cases h with
    | intro k1 h => cases h with | intro k2 h =>
    cases hq k0 k1 k2 with | intro fb hb =>
    have hs' := DecStack.of_steps (steps_thunk2 (fixSelf applyF (I ⬝ z)) fs fb) hs
    exact Contract.of_steps
      ((Steps.left fs (fixSelf_step hz fq)).trans (h.1.trans (hb.1.trans (h.2.2.2 fb))))
      (seq_contract (k := fun _ => o)
        (leafD_i_run _ r t _ hs' fun _ _ hr hu => ih1 (fixSelf_inv hz) hr hu)
        (fun _ t' he ht => by
          cases he
          exact Contract.of_steps (.single (.left t' (.left fb (.I _))))
            (ih2 (fixSelf_inv hz) hb.2 ht)))
  | @then_err b r t _ ih1 =>
    intro z fq fs hz hq hs
    cases applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro k0 h => cases h with
    | intro k1 h => cases h with | intro k2 h =>
    cases hq k0 k1 k2 with | intro fb hb =>
    have hs' := DecStack.of_steps (steps_thunk2 (fixSelf applyF (I ⬝ z)) fs fb) hs
    exact Contract.of_steps
      ((Steps.left fs (fixSelf_step hz fq)).trans (h.1.trans (hb.1.trans (h.2.2.2 fb))))
      (seq_contract (k := fun _ => Outcome.err)
        (leafD_i_run _ r t _ hs' fun _ _ hr hu => ih1 (fixSelf_inv hz) hr hu)
        (fun _ _ he _ => by cases he))
  | @then_bad b S hbad =>
    intro z fq fs hz hq hs
    cases applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro k0 h => cases h with
    | intro k1 h => cases h with | intro k2 h =>
    cases hq k0 k1 k2 with | intro fb hb =>
    have hs' := DecStack.of_steps (steps_thunk2 (fixSelf applyF (I ⬝ z)) fs fb) hs
    exact Contract.of_steps
      ((Steps.left fs (fixSelf_step hz fq)).trans (h.1.trans (hb.1.trans (h.2.2.2 fb))))
      (seq_contract (k := fun _ => Outcome.err)
        (leafR_i (apSoundR_empty _) hs' (CwR.i_bad hbad))
        (fun _ _ he _ => by cases he))

/-- **The compiled `applyU` realizes `ApplyRel`.** -/
theorem apply_sound : ApSoundR Scott.applyU ApplyRel :=
  fun _ _ _ h fr fu hr hu =>
    Contract.of_steps (applyU_unfold fr fu) (applySelf_sound h (.refl _) hr hu)

/-- **Composition with `apply`.**  A compiled program over the kernel, run
    with the compiled `applyU`, meets the relational C model wherever the
    model derives an outcome. -/
theorem composition_apply {p : List Word} {S : Stack} {o : Outcome}
    (h : CsemR ApplyRel p S o) {s : Term} (hs : DecStack s S) :
    Contract (N Scott.applyU p ⬝ s) o :=
  composition_rel apply_sound h hs

/-- `ApplyRel` is a function: the compiled term decides it. -/
theorem ApplyRel.det {q : Quotation} {S : Stack} {o o' : Outcome}
    (h : ApplyRel q S o) (h' : ApplyRel q S o') : o = o' := by
  cases apply_sound _ _ _ h _ _ (encQuot_dec q) (encStack_dec S) with
  | intro u hu =>
    cases apply_sound _ _ _ h' _ _ (encQuot_dec q) (encStack_dec S) with
    | intro u' hu' =>
      have e := Eval.deterministic hu.1 hu'.1
      rw [← e] at hu'
      exact Decodes.functional hu.2 hu'.2
