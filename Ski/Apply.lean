import Ski.Composition
open Term

set_option linter.unusedSectionVars false

/-!
# `apply`: running quotations

SKIlark defunctionalizes quotations, and the compiled kernel runs one with

    applyU q s = q |> { Q_k (b_k applyU s); QCons x r (applyU r (Push x s));
                        QUnit x (RVal (Push x s)); QThen b (seq (wDo applyU) (applyU b) s) }

so Joy's `i` is `wDo applyU`, a case over the table's constructors plus
`seq`: a static quotation runs its compiled body `b_k`, `QCons` pushes and
continues, `QUnit` pushes and stops, and `QThen b` pops a quotation, runs
it, then runs `b`, strictly.

## `Run`

`Run` is the big-step semantics of quotations, programs and words
together, so that a static quotation can run its body, a program, and the
words of that program can run quotations again.  A run that never returns
has no derivation.  `ApplyRel q S o` is `Run (.quot q) S o`.

## The relational word semantics

The words that run quotations also get a relational model on their own:
`CwR R w S o` is `cw` with the quotation's meaning given by a relation
`R`, and `CsemR R` threads it through a word list.  `ApSoundR apT R` says
the eliminator term meets `R` wherever `R` derives.  `composition_rel` is
`composition` over this semantics, for any compiled form of the program.

## The theorem

`apply_sound : ApSoundR Kit.applyU ApplyRel`.  The table's `applyU` is
`Y` applied to its body, as `add` is, and `run_sound` proves every `Run`
derivation realized by every self-reference `fixSelf applyF z` with
`z ⟶* fixB applyF`, by induction on the derivation; each `i`, `dip` or
`ifz` step uses the relational leaves at the singleton relation `only`
its induction hypothesis supplies.  `composition_apply` follows: every
compiled program over the table, run with its compiled `applyU`, meets
`Run` wherever `Run` derives an outcome.  The converse, and with it the
divergence biconditional, is `Ski/Converse.lean`.
-/

variable [Kit] [KitElim] [KitWords]

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
    {w : Word} (hw : w.ok Kit.n = true) {S : Stack} {s : Term} {o : Outcome}
    (hs : DecStack s S) (hc : CwR R w S o) : Contract (wordTerm apT w ⬝ s) o := by
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
  | quote q => cases hc with | plain _ => exact leafD_quote _ q hw S hs
  | add => cases hc with | plain _ => exact leafD_add _ S hs

/-- **Composition, relationally**, for any compiled form of the program. -/
theorem composition_rel {apT : Term} {R : Quotation → Stack → Outcome → Prop}
    (hR : ApSoundR apT R) {p : List Word} {S : Stack} {o : Outcome} (h : CsemR R p S o) :
    p.all (Word.ok Kit.n) = true → ∀ {t s : Term}, Compiles apT p t → DecStack s S →
      Contract (t ⬝ s) o := by
  induction h with
  | nil S => exact fun _ _ s ht hs => Contract.of_steps (Steps.left s ht) (idW_contract hs)
  | @val w p S S' o hw hp ih =>
    intro hok t s ht hs
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases p with
    | nil =>
      cases hp
      exact Contract.of_steps (Steps.left s ht) (leafR hR hok.1 hs hw)
    | cons w' p' =>
      cases ht with
      | intro g hg =>
        exact Contract.of_steps (Steps.left s hg.1)
          (seq_contract (k := fun _ => o) (leafR hR hok.1 hs hw)
            (fun _ _ he ht' => by cases he; exact ih hok.2 hg.2 ht'))
  | @err w p S hw =>
    intro hok t s ht hs
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases p with
    | nil => exact Contract.of_steps (Steps.left s ht) (leafR hR hok.1 hs hw)
    | cons w' p' =>
      cases ht with
      | intro g hg =>
        exact Contract.of_steps (Steps.left s hg.1)
          (seq_contract (k := fun _ => Outcome.err) (leafR hR hok.1 hs hw)
            (fun _ _ he _ => by cases he))

/-- The relation that holds at one `(q, u, o)` only. -/
def only (q : Quotation) (u : Stack) (o : Outcome) : Quotation → Stack → Outcome → Prop :=
  fun q' u' o' => q' = q ∧ u' = u ∧ o' = o

theorem apSoundR_only {apT : Term} {q : Quotation} {u : Stack} {o : Outcome}
    (h : ∀ fr fu, DecQuot fr q → DecStack fu u → Contract (apT ⬝ fr ⬝ fu) o) :
    ApSoundR apT (only q u o) := by
  intro q' u' o' hq
  cases hq with
  | intro e1 h2 =>
    cases h2 with
    | intro e2 e3 =>
      subst e1 e2 e3
      exact h

-- ---------------------------------------------------------------------------
-- `Run`: quotations, programs and words, together
-- ---------------------------------------------------------------------------

/-- What `Run` runs: a quotation, a program, or one word. -/
inductive Job
  | quot (q : Quotation)
  | prog (p : List Word)
  | word (w : Word)

/-- The big-step semantics of the compiled kernel with its table: a static
    quotation runs its body, `then b` is `i` followed by `b`, a program
    threads its words strictly, and the words that run a quotation run it
    here.  A run that never returns has no derivation. -/
inductive Run : Job → Stack → Outcome → Prop
  | stat {k S o} : k < Kit.n → Run (.prog (Kit.body k)) S o → Run (.quot (.stat k)) S o
  | cons {x r S o} : Run (.quot r) (x :: S) o → Run (.quot (.cons x r)) S o
  | unit {x S} : Run (.quot (.unit x)) S (.val (x :: S))
  | then_val {b r t S' o} :
      Run (.quot r) t (.val S') → Run (.quot b) S' o → Run (.quot (.then b)) (.quot r :: t) o
  | then_err {b r t} : Run (.quot r) t .err → Run (.quot (.then b)) (.quot r :: t) .err
  | then_bad {b S} : (∀ r t, S ≠ .quot r :: t) → Run (.quot (.then b)) S .err
  | nil (S) : Run (.prog []) S (.val S)
  | seq_val {w p S S' o} : Run (.word w) S (.val S') → Run (.prog p) S' o → Run (.prog (w :: p)) S o
  | seq_err {w p S} : Run (.word w) S .err → Run (.prog (w :: p)) S .err
  | plain {w S} : w.ho = false → Run (.word w) S (cw (fun _ _ => .err) w S)
  | i_run {r t o} : Run (.quot r) t o → Run (.word .i) (.quot r :: t) o
  | i_bad {S} : (∀ r t, S ≠ .quot r :: t) → Run (.word .i) S .err
  | dip_run {r b u o} : Run (.quot r) u o → Run (.word .dip) (.quot r :: b :: u) (dipOut b o)
  | dip_bad {S} : (∀ r b u, S ≠ .quot r :: b :: u) → Run (.word .dip) S .err
  | ifz_zero {sc z v o} : Run (.quot z) v o → Run (.word .ifz) (.quot sc :: .quot z :: .num 0 :: v) o
  | ifz_succ {sc z m v o} :
      Run (.quot sc) (.num m :: v) o → Run (.word .ifz) (.quot sc :: .quot z :: .num (m + 1) :: v) o
  | ifz_bad {S} : (∀ sc z n v, S ≠ .quot sc :: .quot z :: .num n :: v) → Run (.word .ifz) S .err

/-- Running a quotation. -/
def ApplyRel (q : Quotation) (S : Stack) (o : Outcome) : Prop := Run (.quot q) S o

theorem Run.word_cwR {w : Word} {S : Stack} {o : Outcome} (h : Run (.word w) S o) :
    CwR ApplyRel w S o := by
  cases h with
  | plain hw => exact .plain hw
  | i_run hr => exact .i_run hr
  | i_bad hb => exact .i_bad hb
  | dip_run hr => exact .dip_run hr
  | dip_bad hb => exact .dip_bad hb
  | ifz_zero hr => exact .ifz_zero hr
  | ifz_succ hr => exact .ifz_succ hr
  | ifz_bad hb => exact .ifz_bad hb

theorem CwR.run {w : Word} {S : Stack} {o : Outcome} (h : CwR ApplyRel w S o) :
    Run (.word w) S o := by
  cases h with
  | plain hw => exact .plain hw
  | i_run hr => exact .i_run hr
  | i_bad hb => exact .i_bad hb
  | dip_run hr => exact .dip_run hr
  | dip_bad hb => exact .dip_bad hb
  | ifz_zero hr => exact .ifz_zero hr
  | ifz_succ hr => exact .ifz_succ hr
  | ifz_bad hb => exact .ifz_bad hb

/-- A program's `Run` is its `CsemR` over `ApplyRel`. -/
theorem Run.prog_csemR {t : Job} {S : Stack} {o : Outcome} (h : Run t S o) :
    ∀ p, t = .prog p → CsemR ApplyRel p S o := by
  induction h with
  | nil S => intro p e; cases e; exact .nil S
  | seq_val hw _ _ ih => intro p e; cases e; exact .val hw.word_cwR (ih _ rfl)
  | seq_err hw => intro p e; cases e; exact .err hw.word_cwR
  | _ => intro p e; cases e

theorem CsemR.run {p : List Word} {S : Stack} {o : Outcome} (h : CsemR ApplyRel p S o) :
    Run (.prog p) S o := by
  induction h with
  | nil S => exact .nil S
  | val hw _ ih => exact .seq_val hw.run ih
  | err hw => exact .seq_err hw.run

-- ---------------------------------------------------------------------------
-- The table's `applyU`
-- ---------------------------------------------------------------------------

/-- The argument of an application. -/
def Term.argOf : Term → Term
  | app _ x => x
  | t => t

/-- The body of the table's `applyU`, which is `fixY ⬝ applyF`. -/
def applyF : Term := Kit.applyU.argOf

/-- The table's `applyU` unrolls and runs to its cases, and each static
    quotation's compiled term runs to its body's compiled form; the runs
    after the unrolling are up to weak reduction.  Bracket abstraction
    gives exactly these for every valid table (`Table.kit_apply`,
    `Ski/Laws.lean`). -/
class KitApply [Kit] [KitElim] [KitWords] : Prop where
  applyU_unfold : ∀ fq fs,
    Steps (Kit.applyU ⬝ fq ⬝ fs) (fixSelf applyF (fixB applyF) ⬝ fq ⬝ fs)
  applyF_stages : ∀ R q s, ∃ ks : Nat → Term,
    WSteps (applyF ⬝ R ⬝ q ⬝ s) (appF q ks (Kit.n + 3)) ∧
    (∀ k, k < Kit.n → WSteps (ks k) (Kit.bodyT k ⬝ R ⬝ s)) ∧
    (∀ x r, WSteps (ks Kit.n ⬝ x ⬝ r) (R ⬝ r ⬝ (Scott.Push ⬝ x ⬝ s))) ∧
    (∀ x, WSteps (ks (Kit.n + 1) ⬝ x) (Scott.RVal ⬝ (Scott.Push ⬝ x ⬝ s))) ∧
    (∀ b, WSteps (ks (Kit.n + 2) ⬝ b) (Scott.seq ⬝ (Scott.wDo ⬝ R) ⬝ (R ⬝ b) ⬝ s))
  body_compiles : ∀ k, k < Kit.n → ∀ R, WSteps (Kit.bodyT k ⬝ R) (N R (Kit.body k))
  body_ok : ∀ k, k < Kit.n → (Kit.body k).all (Word.ok Kit.n) = true

variable [KitApply]

/-- What a derivation promises of the compiled self-references of `applyU`. -/
def Sound : Job → Stack → Outcome → Prop
  | .quot q, st, o => ∀ {z fq fs : Term}, Steps z (fixB applyF) → DecQuot fq q → DecStack fs st →
      Contract (fixSelf applyF z ⬝ fq ⬝ fs) o
  | .prog p, st, o => p.all (Word.ok Kit.n) = true → ∀ {z t s : Term}, Steps z (fixB applyF) →
      Compiles (fixSelf applyF z) p t → DecStack s st → Contract (t ⬝ s) o
  | .word w, st, o => w.ok Kit.n = true → ∀ {z s : Term}, Steps z (fixB applyF) →
      DecStack s st → Contract (wordTerm (fixSelf applyF z) w ⬝ s) o

/-- The run of a self-reference to its cases. -/
theorem applySelf_cases {z fq fs : Term} (hz : Steps z (fixB applyF)) (ks : Nat → Term)
    (h : WSteps (applyF ⬝ fixSelf applyF (I ⬝ z) ⬝ fq ⬝ fs) (appF fq ks (Kit.n + 3))) :
    WSteps (fixSelf applyF z ⬝ fq ⬝ fs) (appF fq ks (Kit.n + 3)) :=
  (Steps.left fs (fixSelf_step hz fq)).weak.trans h

/-- **Every derivation is realized by the compiled terms.** -/
theorem run_sound {t : Job} {S : Stack} {o : Outcome} (h : Run t S o) : Sound t S o := by
  induction h with
  | @stat k S o hk _ ih =>
    unfold Sound
    intro z fq fs hz hq hs
    cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
    exact Contract.of_wsteps
      ((applySelf_cases hz ks h.1).trans ((hq.probe_stat.2 ks).weak.trans
        ((h.2.1 k hk).trans (WSteps.left fs (KitApply.body_compiles k hk _)))))
      (ih (KitApply.body_ok k hk) (fixSelf_inv hz) (compiles_N _ _) hs)
  | @cons x r S o _ ih =>
    unfold Sound
    intro z fq fs hz hq hs
    cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
    cases hq.probe_cons ks with | intro f hf => cases hf with | intro g hg =>
    exact Contract.of_wsteps ((applySelf_cases hz ks h.1).trans (hg.1.weak.trans (h.2.2.1 f g)))
      (ih (fixSelf_inv hz) hg.2.2 (dec_push hg.2.1 hs))
  | @unit x S =>
    unfold Sound
    intro z fq fs hz hq hs
    cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
    cases hq.probe_unit ks with | intro f hf =>
    exact contract_valW ((applySelf_cases hz ks h.1).trans (hf.1.weak.trans (h.2.2.2.1 f)))
      (dec_push hf.2 hs)
  | @then_val b r t S' o _ _ ih1 ih2 =>
    unfold Sound
    intro z fq fs hz hq hs
    cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
    cases hq.probe_then ks with | intro fb hb =>
    exact Contract.of_wsteps
      ((applySelf_cases hz ks h.1).trans (hb.1.weak.trans (h.2.2.2.2 fb)))
      (seq_contract (k := fun _ => o)
        (leafD_i_run _ r t _ hs fun _ _ hr hu => ih1 (fixSelf_inv hz) hr hu)
        (fun _ _ he ht => by
          cases he
          exact ih2 (fixSelf_inv hz) hb.2 ht))
  | @then_err b r t _ ih1 =>
    unfold Sound
    intro z fq fs hz hq hs
    cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
    cases hq.probe_then ks with | intro fb hb =>
    exact Contract.of_wsteps
      ((applySelf_cases hz ks h.1).trans (hb.1.weak.trans (h.2.2.2.2 fb)))
      (seq_contract (k := fun _ => Outcome.err)
        (leafD_i_run _ r t _ hs fun _ _ hr hu => ih1 (fixSelf_inv hz) hr hu)
        (fun _ _ he _ => by cases he))
  | @then_bad b S hbad =>
    unfold Sound
    intro z fq fs hz hq hs
    cases KitApply.applyF_stages (fixSelf applyF (I ⬝ z)) fq fs with | intro ks h =>
    cases hq.probe_then ks with | intro fb hb =>
    exact Contract.of_wsteps
      ((applySelf_cases hz ks h.1).trans (hb.1.weak.trans (h.2.2.2.2 fb)))
      (seq_contract (k := fun _ => Outcome.err)
        (leafR_i (apSoundR_empty _) hs (CwR.i_bad hbad))
        (fun _ _ he _ => by cases he))
  | nil S =>
    exact fun _ _ _ s _ ht hs => Contract.of_steps (Steps.left s ht) (idW_contract hs)
  | @seq_val w p S S' o _ hp ihw ihp =>
    unfold Sound
    intro hok z t s hz ht hs
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases p with
    | nil =>
      cases hp
      exact Contract.of_steps (Steps.left s ht) (ihw hok.1 hz hs)
    | cons w' p' =>
      cases ht with
      | intro g hg =>
        exact Contract.of_steps (Steps.left s hg.1)
          (seq_contract (k := fun _ => o) (ihw hok.1 hz hs)
            (fun _ _ he ht' => by cases he; exact ihp hok.2 hz hg.2 ht'))
  | @seq_err w p S _ ihw =>
    unfold Sound
    intro hok z t s hz ht hs
    simp only [List.all_cons, Bool.and_eq_true] at hok
    cases p with
    | nil => exact Contract.of_steps (Steps.left s ht) (ihw hok.1 hz hs)
    | cons w' p' =>
      cases ht with
      | intro g hg =>
        exact Contract.of_steps (Steps.left s hg.1)
          (seq_contract (k := fun _ => Outcome.err) (ihw hok.1 hz hs)
            (fun _ _ he _ => by cases he))
  | plain hw => exact fun hok _ _ _ hs => leafR (apSoundR_empty _) hok hs (.plain hw)
  | @i_run r t o _ ih =>
    exact fun _ _ _ hz hs =>
      leafR_i (apSoundR_only fun _ _ hr hu => ih hz hr hu) hs (.i_run ⟨rfl, rfl, rfl⟩)
  | i_bad hb => exact fun _ _ _ _ hs => leafR_i (apSoundR_empty _) hs (.i_bad hb)
  | @dip_run r b u o _ ih =>
    exact fun _ _ _ hz hs =>
      leafR_dip (apSoundR_only fun _ _ hr hu => ih hz hr hu) hs (.dip_run ⟨rfl, rfl, rfl⟩)
  | dip_bad hb => exact fun _ _ _ _ hs => leafR_dip (apSoundR_empty _) hs (.dip_bad hb)
  | @ifz_zero sc z v o _ ih =>
    exact fun _ _ _ hz hs =>
      leafR_ifz (apSoundR_only fun _ _ hr hu => ih hz hr hu) hs (.ifz_zero ⟨rfl, rfl, rfl⟩)
  | @ifz_succ sc z m v o _ ih =>
    exact fun _ _ _ hz hs =>
      leafR_ifz (apSoundR_only fun _ _ hr hu => ih hz hr hu) hs (.ifz_succ ⟨rfl, rfl, rfl⟩)
  | ifz_bad hb => exact fun _ _ _ _ hs => leafR_ifz (apSoundR_empty _) hs (.ifz_bad hb)

theorem applySelf_sound {q : Quotation} {S : Stack} {o : Outcome} (h : ApplyRel q S o)
    {z fq fs : Term} (hz : Steps z (fixB applyF)) (hq : DecQuot fq q) (hs : DecStack fs S) :
    Contract (fixSelf applyF z ⬝ fq ⬝ fs) o :=
  run_sound h hz hq hs

/-- **The table's compiled `applyU` realizes `ApplyRel`.** -/
theorem apply_sound : ApSoundR Kit.applyU ApplyRel :=
  fun _ _ _ h fr fu hr hu =>
    Contract.of_steps (KitApply.applyU_unfold fr fu) (applySelf_sound h (.refl _) hr hu)

/-- **Composition with `apply`.**  Any compiled form of a program over the
    table, run with its compiled `applyU`, meets `Run` wherever `Run`
    derives an outcome. -/
theorem composition_apply {p : List Word} {S : Stack} {o : Outcome}
    (h : Run (.prog p) S o) (hp : p.all (Word.ok Kit.n) = true) {t s : Term}
    (ht : Compiles Kit.applyU p t) (hs : DecStack s S) : Contract (t ⬝ s) o :=
  composition_rel apply_sound (h.prog_csemR p rfl) hp ht hs

/-- `ApplyRel` is a function on valid inputs: the compiled term decides it. -/
theorem ApplyRel.det {q : Quotation} {S : Stack} {o o' : Outcome}
    (hq : q.ok Kit.n = true) (hS : S.all (Item.ok Kit.n) = true)
    (h : ApplyRel q S o) (h' : ApplyRel q S o') : o = o' := by
  cases apply_sound _ _ _ h _ _ (encQuot_dec q hq) (encStack_dec S hS) with
  | intro u hu =>
    cases apply_sound _ _ _ h' _ _ (encQuot_dec q hq) (encStack_dec S hS) with
    | intro u' hu' =>
      have e := Eval.deterministic hu.1 hu'.1
      rw [← e] at hu'
      exact Decodes.functional hu.2 hu'.2
