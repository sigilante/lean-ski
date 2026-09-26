import Ski.Decode
open Term

set_option linter.unusedSectionVars false

/-!
# Leaf contracts

`Contract t o` says `t` reduces to a weak head normal form that decodes to
`o`.  The leaf contract of word `w` is

    DecStack s S → Contract (phi w ⬝ s) (cw ap w S)

for **every** term `s` that decodes to `S`, not only for `encStack S`: in a
composed program a word receives its predecessor's result stack, which is
a thunk, not an encoding.  `leaf_w` is the special case `s = encStack S`,
in the form `Steps (phi w ⬝ encStack S) t ∧ Decodes t (cw ap w S)`
strengthened to `Eval`.

## Stages

A compiled word cases on its input by applying it to two continuations.
Normal order then stops with the input at the head, and the input's
decoding says where it goes next: to the first continuation if the stack
is empty, to the second, applied to the top and the rest, if not.  A stage
lemma (`wSwap_stages` and the rest) chains these stops: each clause is a
run by `iter_sound rfl` on symbolic terms, down to the next input at the
head, to `RErr`, or to `RVal` of a result skeleton.  The continuations
are existentials, hundreds of atoms long, which the kernel's `rfl`
supplies; nothing in a leaf proof looks inside them.  The skeleton lemmas
reduce each result to Scott constructors, and the constructor lemmas of
`Ski/Decode.lean` decode it.

The table's words `unit`, `cons` and `cat` differ between tables, so
their stages are the class `KitWords`, stated up to weak reduction and
proved for every table from source (`Ski/Laws.lean`).  Their results are
the table's constructors applied to the fields, with no skeleton; the
shared steps take weak runs in their `*W` forms, through
`Contract.of_wsteps`.

## Words that run a quotation

`dip` and `i` stop with the quotation eliminator `apT` at the head,
applied to the quotation and the rest of the stack.  `ApSound apT ap` is
the contract they assume of it: `apT`, applied to anything that decodes
to `r` and `u`, meets `Contract` for `ap r u`.  The `*_run` lemmas assume
it only at the one `(r, u)` the stack supplies, so they apply to an
eliminator that diverges elsewhere.
-/

variable [Kit] [KitElim]

-- ---------------------------------------------------------------------------
-- Contracts, and the steps every leaf shares
-- ---------------------------------------------------------------------------

/-- `t` reduces to a weak head normal form that decodes to `o`. -/
def Contract (t : Term) (o : Outcome) : Prop := ∃ u, Eval t u ∧ Decodes u o

theorem Contract.of_steps {t t' : Term} {o : Outcome} (h : Steps t t') (h' : Contract t' o) :
    Contract t o := by
  cases h' with
  | intro u hu => exact ⟨u, ⟨h.trans hu.1.1, hu.1.2⟩, hu.2⟩

/-- **Contracts are closed under backward weak reduction.**  If `t` weakly
    reduces to `t'` and `t'` meets the contract, so does `t`: `t` reaches a
    weak head normal form that weakly reduces to `t'`'s (`eval_back`), and
    decoding is closed under backward weak reduction. -/
theorem Contract.of_wsteps {t t' : Term} {o : Outcome} (h : WSteps t t') (h' : Contract t' o) :
    Contract t o := by
  cases h' with
  | intro u hu =>
    cases eval_back h hu.1 with
    | intro v hv => exact ⟨v, hv.1, Decodes.of_wsteps hv.2 hu.2⟩

/-- The quotation eliminator `apT` realizes the model `ap`. -/
def ApSound (apT : Term) (ap : Quotation → Stack → Outcome) : Prop :=
  ∀ r u fr fu, DecQuot fr r → DecStack fu u → Contract (apT ⬝ fr ⬝ fu) (ap r u)

/-- The weak head normal form of `RVal ⬝ g`. -/
def rvalW (g : Term) : Term :=
  S ⬝ (K ⬝ K) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K) ⬝ g)

theorem eval_rval (g : Term) : Eval (Scott.RVal ⬝ g) (rvalW g) :=
  ⟨iter_sound (k := 2) rfl, .S2 _ _⟩

theorem dec_rvalW {g : Term} {s : Stack} (h : DecStack g s) : Decodes (rvalW g) (.val s) :=
  fun _ _ => ⟨_, oiter_sound (k := 12) rfl, DecStackO.of_owsteps (owsteps_thunk1 _ _) h⟩

theorem contract_val {t g : Term} {s : Stack} (ht : Steps t (Scott.RVal ⬝ g))
    (hg : DecStack g s) : Contract t (.val s) :=
  ⟨rvalW g, ⟨ht.trans (eval_rval g).1, (eval_rval g).2⟩, dec_rvalW hg⟩

theorem contract_err {t : Term} (ht : Steps t Scott.RErr) : Contract t .err :=
  ⟨Scott.RErr, ⟨ht, .K1 K⟩, dec_rerr⟩

/-- An empty input stack takes the first continuation. -/
theorem stack_err {s c0 c1 t : Term} (hs : DecStack s []) (h : Steps t (s ⬝ c0 ⬝ c1))
    (h0 : Steps c0 Scott.RErr) : Contract t .err :=
  contract_err (h.trans ((hs.probe_nil c0 c1).trans h0))

/-- A non-empty input stack takes the second, with its top and rest. -/
theorem stack_push {s c0 c1 t : Term} {a : Item} {S : Stack} (hs : DecStack s (a :: S))
    (h : Steps t (s ⬝ c0 ⬝ c1)) :
    ∃ f g, Steps t (c1 ⬝ f ⬝ g) ∧ DecItem f a ∧ DecStack g S := by
  cases hs.probe_cons c0 c1 with
  | intro f hf =>
    cases hf with
    | intro g hg => exact ⟨f, g, h.trans hg.1, hg.2⟩

/-- A number where a quotation is wanted takes the first continuation. -/
theorem item_num_err {x e0 e1 t : Term} {n : Nat} (hx : DecItem x (.num n))
    (h : Steps t (x ⬝ e0 ⬝ e1)) (he : ∀ f, Steps (e0 ⬝ f) Scott.RErr) : Contract t .err := by
  cases hx.probe_num e0 e1 with
  | intro f hf => exact contract_err (h.trans (hf.1.trans (he f)))

/-- A quotation takes the second continuation, with its body. -/
theorem item_quot {x e0 e1 t : Term} {q : Quotation} (hx : DecItem x (.quot q))
    (h : Steps t (x ⬝ e0 ⬝ e1)) : ∃ f, Steps t (e1 ⬝ f) ∧ DecQuot f q := by
  cases hx.probe_quot e0 e1 with
  | intro f hf => exact ⟨f, h.trans hf.1, hf.2⟩

-- ---------------------------------------------------------------------------
-- The same, up to weak reduction
-- ---------------------------------------------------------------------------

theorem contract_valW {t g : Term} {s : Stack} (ht : WSteps t (Scott.RVal ⬝ g))
    (hg : DecStack g s) : Contract t (.val s) :=
  Contract.of_wsteps ht (contract_val (.refl _) hg)

theorem contract_errW {t : Term} (ht : WSteps t Scott.RErr) : Contract t .err :=
  Contract.of_wsteps ht (contract_err (.refl _))

theorem stack_errW {s c1 t : Term} (hs : DecStack s []) (h : WSteps t (s ⬝ Scott.RErr ⬝ c1)) :
    Contract t .err :=
  Contract.of_wsteps h (contract_err (hs.probe_nil _ _))

theorem stack_pushW {s c0 c1 t : Term} {a : Item} {S : Stack} (hs : DecStack s (a :: S))
    (h : WSteps t (s ⬝ c0 ⬝ c1)) :
    ∃ f g, WSteps t (c1 ⬝ f ⬝ g) ∧ DecItem f a ∧ DecStack g S := by
  cases hs.probe_cons c0 c1 with
  | intro f hf =>
    cases hf with
    | intro g hg => exact ⟨f, g, h.trans hg.1.weak, hg.2⟩

theorem item_num_errW {x e0 e1 t : Term} {n : Nat} (hx : DecItem x (.num n))
    (h : WSteps t (x ⬝ e0 ⬝ e1)) (he : ∀ f, WSteps (e0 ⬝ f) Scott.RErr) : Contract t .err := by
  cases hx.probe_num e0 e1 with
  | intro f hf => exact contract_errW (h.trans (hf.1.weak.trans (he f)))

theorem item_quotW {x e0 e1 t : Term} {q : Quotation} (hx : DecItem x (.quot q))
    (h : WSteps t (x ⬝ e0 ⬝ e1)) : ∃ f, WSteps t (e1 ⬝ f) ∧ DecQuot f q := by
  cases hx.probe_quot e0 e1 with
  | intro f hf => exact ⟨f, h.trans hf.1.weak, hf.2⟩

-- ---------------------------------------------------------------------------
-- The table's words: `unit`, `cons` and `cat` build `quot` values, so their
-- terms are the table's.  Each runs, up to weak reduction, to the next
-- input at the head, to `RErr`, or to `RVal` of its result built from the
-- table's constructors; bracket abstraction gives exactly these runs for
-- every table (`Table.kit_words`, `Ski/Laws.lean`).
-- ---------------------------------------------------------------------------

/-- The table's `unit`, `cons` and `cat` run to their results, up to weak
    reduction. -/
class KitWords [Kit] : Prop where
  wUnit_stages : ∀ s : Term, ∃ c1,
    WSteps (Kit.wUnit ⬝ s) (s ⬝ Scott.RErr ⬝ c1) ∧
    ∀ f g, WSteps (c1 ⬝ f ⬝ g) (Scott.RVal ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ (Kit.QUnit ⬝ f)) ⬝ g))
  wQcons_stages : ∀ s : Term, ∃ c1,
    WSteps (Kit.wQcons ⬝ s) (s ⬝ Scott.RErr ⬝ c1) ∧
    ∀ f g, ∃ e0 e1, WSteps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, WSteps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d1, WSteps (e1 ⬝ x) (g ⬝ Scott.RErr ⬝ d1) ∧
        ∀ f2 g2, WSteps (d1 ⬝ f2 ⬝ g2)
          (Scott.RVal ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ (Kit.QCons ⬝ f2 ⬝ x)) ⬝ g2))
  wCat_stages : ∀ s : Term, ∃ c1,
    WSteps (Kit.wCat ⬝ s) (s ⬝ Scott.RErr ⬝ c1) ∧
    ∀ f g, ∃ e0 e1, WSteps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, WSteps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d1, WSteps (e1 ⬝ x) (g ⬝ Scott.RErr ⬝ d1) ∧
        ∀ f2 g2, ∃ e0' e1', WSteps (d1 ⬝ f2 ⬝ g2) (f2 ⬝ e0' ⬝ e1') ∧
          (∀ n, WSteps (e0' ⬝ n) Scott.RErr) ∧
          ∀ y, WSteps (e1' ⬝ y) (Scott.RVal ⬝ (Scott.Push ⬝
            (Scott.Quot ⬝ (Kit.QCons ⬝ (Scott.Quot ⬝ y) ⬝ (Kit.QThen ⬝ x))) ⬝ g2))

variable [KitWords]

-- ---------------------------------------------------------------------------
-- pop   ( a — )
-- ---------------------------------------------------------------------------

theorem wPop_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wPop ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, Steps (c1 ⬝ f ⬝ g) (Scott.RVal ⬝ g) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ => iter_sound (k := 2) rfl⟩

theorem leafD_pop (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .pop ⬝ s) (cw ap .pop S) := by
  cases wPop_stages s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    exact contract_val (h1.1.trans (h.2.2 f g)) h1.2.2

theorem leaf_pop (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .pop ⬝ encStack S) t ∧ Decodes t (cw ap .pop S) :=
  leafD_pop ap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- dup   ( a — a a )
-- ---------------------------------------------------------------------------

/-- `λ a t. Push a (Push a t)`, as bracket abstraction leaves it. -/
def dupD : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ Scott.Push)) ⬝ Scott.Push

theorem dupD_push (a t : Term) :
    Steps (dupD ⬝ a ⬝ t) (Scott.Push ⬝ a ⬝ (Scott.Push ⬝ a ⬝ t)) :=
  iter_sound (k := 7) rfl

theorem wDup_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wDup ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, Steps (c1 ⬝ f ⬝ g) (Scott.RVal ⬝ (dupD ⬝ f ⬝ g)) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ => iter_sound (k := 5) rfl⟩

theorem leafD_dup (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .dup ⬝ s) (cw ap .dup S) := by
  cases wDup_stages s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    exact contract_val (h1.1.trans (h.2.2 f g))
      (DecStack.of_steps (dupD_push _ _) (dec_push h1.2.1 (dec_push h1.2.1 h1.2.2)))

theorem leaf_dup (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .dup ⬝ encStack S) t ∧ Decodes t (cw ap .dup S) :=
  leafD_dup ap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- swap   ( a b — b a )
-- ---------------------------------------------------------------------------

/-- `λ a b t. Push a t`, the inner push of `swap`. -/
def swapT : Term := S ⬝ (K ⬝ K) ⬝ Scott.Push

/-- `λ a b t. Push b (Push a t)`. -/
def swapC : Term := S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ swapT))) ⬝ swapT

theorem swapC_push (f0 f1 f2 : Term) :
    Steps (swapC ⬝ f0 ⬝ f1 ⬝ f2) (Scott.Push ⬝ f1 ⬝ (swapT ⬝ f0 ⬝ f1 ⬝ f2)) :=
  iter_sound (k := 9) rfl

theorem swapT_push (f0 f1 f2 : Term) :
    Steps (swapT ⬝ f0 ⬝ f1 ⬝ f2) (Scott.Push ⬝ f0 ⬝ f2) :=
  iter_sound (k := 3) rfl

theorem wSwap_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wSwap ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ d0 d1, Steps (c1 ⬝ f ⬝ g) (g ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
      ∀ f2 g2, Steps (d1 ⬝ f2 ⬝ g2) (Scott.RVal ⬝ (swapC ⬝ f ⬝ f2 ⬝ g2)) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 6) rfl, iter_sound (k := 1) rfl, fun _ _ => iter_sound (k := 9) rfl⟩⟩

theorem leafD_swap (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .swap ⬝ s) (cw ap .swap S) := by
  cases wSwap_stages s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2.2 f g with | intro d0 h2 => cases h2 with | intro d1 h2 =>
    cases t with
    | nil => exact stack_err h1.2.2 (h1.1.trans h2.1) h2.2.1
    | cons b u =>
      cases stack_push h1.2.2 (h1.1.trans h2.1) with | intro f2 h3 =>
      cases h3 with | intro g2 h3 =>
      exact contract_val (h3.1.trans (h2.2.2 f2 g2))
        (DecStack.of_steps (swapC_push _ _ _)
          (dec_push h3.2.1 (DecStack.of_steps (swapT_push _ _ _) (dec_push h1.2.1 h3.2.2))))

theorem leaf_swap (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .swap ⬝ encStack S) t ∧ Decodes t (cw ap .swap S) :=
  leafD_swap ap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- unit   ( a — [a] )
-- ---------------------------------------------------------------------------

theorem leafD_unit (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .unit ⬝ s) (cw ap .unit S) := by
  cases KitWords.wUnit_stages s with | intro c1 h =>
  cases S with
  | nil => exact stack_errW hs h.1
  | cons a t =>
    cases stack_pushW hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    exact contract_valW (h1.1.trans (h.2 f g)) (dec_push (dec_quot (dec_qunit h1.2.1)) h1.2.2)

theorem leaf_unit (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .unit ⬝ encStack S) t ∧ Decodes t (cw ap .unit S) :=
  leafD_unit ap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- cons   ( b [r] — [b r] )
-- ---------------------------------------------------------------------------

theorem leafD_cons (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .cons ⬝ s) (cw ap .cons S) := by
  cases KitWords.wQcons_stages s with | intro c1 h =>
  cases S with
  | nil => exact stack_errW hs h.1
  | cons a t =>
    cases stack_pushW hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n => exact item_num_errW h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot q =>
      cases item_quotW h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
      cases h2.2.2 x with | intro d1 h4 =>
      cases t with
      | nil => exact stack_errW h1.2.2 (h3.1.trans h4.1)
      | cons b u =>
        cases stack_pushW h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 =>
        cases h5 with | intro g2 h5 =>
        exact contract_valW (h5.1.trans (h4.2 f2 g2))
          (dec_push (dec_quot (dec_qcons h5.2.1 h3.2)) h5.2.2)

theorem leaf_cons (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .cons ⬝ encStack S) t ∧ Decodes t (cw ap .cons S) :=
  leafD_cons ap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- cat   ( [l] [r] — [[l] i r] )
-- ---------------------------------------------------------------------------

theorem leafD_cat (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .cat ⬝ s) (cw ap .cat S) := by
  cases KitWords.wCat_stages s with | intro c1 h =>
  cases S with
  | nil => exact stack_errW hs h.1
  | cons a t =>
    cases stack_pushW hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n => exact item_num_errW h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot r =>
      cases item_quotW h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
      cases h2.2.2 x with | intro d1 h4 =>
      cases t with
      | nil => exact stack_errW h1.2.2 (h3.1.trans h4.1)
      | cons b u =>
        cases stack_pushW h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 =>
        cases h5 with | intro g2 h5 =>
        cases h4.2 f2 g2 with | intro e0' h6 => cases h6 with | intro e1' h6 =>
        cases b with
        | num m => exact item_num_errW h5.2.1 (h5.1.trans h6.1) h6.2.1
        | quot l =>
          cases item_quotW h5.2.1 (h5.1.trans h6.1) with | intro y h7 =>
          exact contract_valW (h7.1.trans (h6.2.2 y))
            (dec_push (dec_quot (dec_qcons (dec_quot h7.2) (dec_qthen h3.2))) h5.2.2)

theorem leaf_cat (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .cat ⬝ encStack S) t ∧ Decodes t (cw ap .cat S) :=
  leafD_cat ap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- dip   ( b [r] — r b )   with `apT` running `r`
--
-- `wDip` runs until `apT` is at the head, applied to the quotation, the
-- rest of the stack and three continuations.  What `apT` does there is
-- known only through `Decodes`, whose closed probes hold at every
-- continuation (`Decodes.probe_val`), and `dip`'s own continuations are the
-- ones it is probed at.
-- ---------------------------------------------------------------------------

theorem wDip_stages (apT s : Term) : ∃ c0 c1,
    Steps (Scott.wDip ⬝ apT ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ e0 e1, Steps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, Steps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d0 d1, Steps (e1 ⬝ x) (g ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
        ∀ f2 g2, ∃ k0 k1 k2, Steps (d1 ⬝ f2 ⬝ g2) (apT ⬝ x ⬝ g2 ⬝ k0 ⬝ k1 ⬝ k2) ∧
          (∀ v, Steps (k0 ⬝ v) (Scott.RVal ⬝ (Scott.Push ⬝ f2 ⬝ v))) ∧
          Steps k1 Scott.RErr :=
  ⟨_, _, iter_sound (k := 5) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 14) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
      ⟨_, _, iter_sound (k := 14) rfl, iter_sound (k := 1) rfl, fun _ _ =>
        ⟨_, _, _, iter_sound (k := 52) rfl, fun _ => iter_sound (k := 9) rfl,
          iter_sound (k := 4) rfl⟩⟩⟩⟩

/-- `dip`'s outcome once `ap r u` has returned `o`. -/
def dipOut (b : Item) : Outcome → Outcome
  | .val v => .val (b :: v)
  | .err => .err

theorem cw_dip (ap : Quotation → Stack → Outcome) (r : Quotation) (b : Item) (u : Stack) :
    cw ap .dip (.quot r :: b :: u) = dipOut b (ap r u) := by
  simp only [cw]
  cases ap r u <;> rfl

/-- `dip` on a well-shaped stack, assuming `apT` only at the `(r, u)` it
    supplies.  `dip` needs `ap`'s result only up to `Decodes`. -/
theorem leafD_dip_run (apT : Term) (r : Quotation) (b : Item) (u : Stack) (o : Outcome)
    {s : Term} (hs : DecStack s (.quot r :: b :: u))
    (hap : ∀ fr fu, DecQuot fr r → DecStack fu u → Decodes (apT ⬝ fr ⬝ fu) o) :
    Contract (phi .dip ⬝ apT ⬝ s) (dipOut b o) := by
  cases wDip_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
  cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 => cases h5 with | intro g2 h5 =>
  cases h4.2.2 f2 g2 with | intro k0 h6 => cases h6 with | intro k1 h6 =>
  cases h6 with | intro k2 h6 =>
  have run := h5.1.trans h6.1
  have ho := hap x g2 h3.2 h5.2.2
  cases o with
  | val v =>
    cases ho.probe_val k0 k1 k2 with
    | intro fv hv =>
      exact contract_val (run.trans (hv.1.trans (h6.2.1 fv))) (dec_push h5.2.1 hv.2)
  | err => exact contract_err (run.trans ((ho.probe_err k0 k1 k2).trans h6.2.2))

theorem leafD_dip (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (S : Stack) {s : Term} (hs : DecStack s S) :
    Contract (phi .dip ⬝ apT ⬝ s) (cw ap .dip S) := by
  cases wDip_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot r =>
      cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
      cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
      cases t with
      | nil => exact stack_err h1.2.2 (h3.1.trans h4.1) h4.2.1
      | cons b u =>
        rw [cw_dip]
        exact leafD_dip_run apT r b u (ap r u) hs fun fr fu hr hu =>
          match hap r u fr fu hr hu with
          | ⟨_, he, hd⟩ => Decodes.of_steps he.1 hd

theorem leaf_dip (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .dip ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .dip S) :=
  leafD_dip apT ap hap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- i   ( [r] — r )   with `apT` running `r`
-- ---------------------------------------------------------------------------

theorem wDo_stages (apT s : Term) : ∃ c0 c1,
    Steps (Scott.wDo ⬝ apT ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ e0 e1, Steps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, Steps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, Steps (e1 ⬝ x) (apT ⬝ x ⬝ (K ⬝ K ⬝ apT ⬝ g ⬝ x)) :=
  ⟨_, _, iter_sound (k := 5) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 14) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
      iter_sound (k := 11) rfl⟩⟩

theorem leafD_i_run (apT : Term) (r : Quotation) (t : Stack) (o : Outcome)
    {s : Term} (hs : DecStack s (.quot r :: t))
    (hap : ∀ fr fu, DecQuot fr r → DecStack fu t → Contract (apT ⬝ fr ⬝ fu) o) :
    Contract (phi .i ⬝ apT ⬝ s) o := by
  cases wDo_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  exact Contract.of_steps (h3.1.trans (h2.2.2 x))
    (hap x _ h3.2 (DecStack.of_steps (steps_thunk2 _ _ _) h1.2.2))

theorem leafD_i (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (S : Stack) {s : Term} (hs : DecStack s S) :
    Contract (phi .i ⬝ apT ⬝ s) (cw ap .i S) := by
  cases wDo_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot r => exact leafD_i_run apT r t (ap r t) hs (hap r t)

theorem leaf_i (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .i ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .i S) :=
  leafD_i apT ap hap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- lit n   ( — n )   and   quote q   ( — [q] )
-- ---------------------------------------------------------------------------

/-- `λ n s. Push (Num n) s`. -/
def litC : Term := S ⬝ (K ⬝ Scott.Push) ⬝ Scott.Num

/-- `λ q s. Push (Quot q) s`. -/
def quoteC : Term := S ⬝ (K ⬝ Scott.Push) ⬝ Scott.Quot

theorem litC_push (n s : Term) : Steps (litC ⬝ n ⬝ s) (Scott.Push ⬝ (Scott.Num ⬝ n) ⬝ s) :=
  iter_sound (k := 2) rfl

theorem quoteC_push (q s : Term) : Steps (quoteC ⬝ q ⬝ s) (Scott.Push ⬝ (Scott.Quot ⬝ q) ⬝ s) :=
  iter_sound (k := 2) rfl

theorem wLit_run (n s : Term) : Steps (Scott.wLit ⬝ n ⬝ s) (Scott.RVal ⬝ (litC ⬝ n ⬝ s)) :=
  iter_sound (k := 4) rfl

theorem wQuote_run (q s : Term) : Steps (Scott.wQuote ⬝ q ⬝ s) (Scott.RVal ⬝ (quoteC ⬝ q ⬝ s)) :=
  iter_sound (k := 4) rfl

theorem leafD_lit (ap : Quotation → Stack → Outcome) (n : Nat) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi (.lit n) ⬝ s) (cw ap (.lit n) S) :=
  contract_val (wLit_run _ _)
    (DecStack.of_steps (litC_push _ _) (dec_push (dec_num (encNat_dec n)) hs))

theorem leafD_quote (ap : Quotation → Stack → Outcome) (q : Quotation) (hq : q.ok Kit.n = true)
    (S : Stack) {s : Term} (hs : DecStack s S) :
    Contract (phi (.quote q) ⬝ s) (cw ap (.quote q) S) :=
  contract_val (wQuote_run _ _)
    (DecStack.of_steps (quoteC_push _ _) (dec_push (dec_quot (encQuot_dec q hq)) hs))

-- ---------------------------------------------------------------------------
-- ifz   ( n [z] [s] — … )   runs `z` on the rest if `n = 0`, else `s` on `n-1`
-- ---------------------------------------------------------------------------

/-- A quotation where a number is wanted takes the second continuation. -/
theorem item_quot_err {x e0 e1 t : Term} {q : Quotation} (hx : DecItem x (.quot q))
    (h : Steps t (x ⬝ e0 ⬝ e1)) (he : ∀ f, Steps (e1 ⬝ f) Scott.RErr) : Contract t .err := by
  cases hx.probe_quot e0 e1 with
  | intro f hf => exact contract_err (h.trans (hf.1.trans (he f)))

/-- A number takes the first continuation, with its numeral. -/
theorem item_num {x e0 e1 t : Term} {n : Nat} (hx : DecItem x (.num n))
    (h : Steps t (x ⬝ e0 ⬝ e1)) : ∃ f, Steps t (e0 ⬝ f) ∧ DecNat f n := by
  cases hx.probe_num e0 e1 with
  | intro f hf => exact ⟨f, h.trans hf.1, hf.2⟩

theorem nat_zero {x n0 n1 t : Term} (hx : DecNat x 0) (h : Steps t (x ⬝ n0 ⬝ n1)) :
    Steps t n0 :=
  h.trans (hx.probe_zero n0 n1)

theorem nat_succ {x n0 n1 t : Term} {m : Nat} (hx : DecNat x (m + 1))
    (h : Steps t (x ⬝ n0 ⬝ n1)) : ∃ f, Steps t (n1 ⬝ f) ∧ DecNat f m := by
  cases hx.probe_succ n0 n1 with
  | intro f hf => exact ⟨f, h.trans hf.1, hf.2⟩

theorem wIfz_stages (apT s : Term) : ∃ c0 c1,
    Steps (Scott.wIfz ⬝ apT ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ e0 e1, Steps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, Steps (e0 ⬝ n) Scott.RErr) ∧
    ∀ x, ∃ d0 d1, Steps (e1 ⬝ x) (g ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
    ∀ f2 g2, ∃ e0 e1, Steps (d1 ⬝ f2 ⬝ g2) (f2 ⬝ e0 ⬝ e1) ∧ (∀ n, Steps (e0 ⬝ n) Scott.RErr) ∧
    ∀ y, ∃ d0 d1, Steps (e1 ⬝ y) (g2 ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
    ∀ f3 g3, ∃ e0 e1, Steps (d1 ⬝ f3 ⬝ g3) (f3 ⬝ e0 ⬝ e1) ∧ (∀ q, Steps (e1 ⬝ q) Scott.RErr) ∧
    ∀ n, ∃ n0 n1, Steps (e0 ⬝ n) (n ⬝ n0 ⬝ n1) ∧ Steps n0 (apT ⬝ y ⬝ g3) ∧
    ∀ m, ∃ p, Steps (n1 ⬝ m) (apT ⬝ x ⬝ p) ∧
      Steps p (Scott.Push ⬝ (Scott.Num ⬝ m) ⬝ (K ⬝ g3 ⬝ m)) :=
  ⟨_, _, iter_sound (k := 5) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 14) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
    ⟨_, _, iter_sound (k := 14) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 16) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
    ⟨_, _, iter_sound (k := 18) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 41) rfl, fun _ => iter_sound (k := 6) rfl, fun _ =>
    ⟨_, _, iter_sound (k := 37) rfl, iter_sound (k := 5) rfl, fun _ =>
    ⟨_, iter_sound (k := 34) rfl, iter_sound (k := 7) rfl⟩⟩⟩⟩⟩⟩⟩⟩

theorem leafD_ifz (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (S : Stack) {s : Term} (hs : DecStack s S) :
    Contract (phi .ifz ⬝ apT ⬝ s) (cw ap .ifz S) := by
  cases wIfz_stages apT s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
  cases a with
  | num k => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
  | quot sc =>
  cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
  cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
  cases t with
  | nil => exact stack_err h1.2.2 (h3.1.trans h4.1) h4.2.1
  | cons b u =>
  cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 => cases h5 with | intro g2 h5 =>
  cases h4.2.2 f2 g2 with | intro e0' h6 => cases h6 with | intro e1' h6 =>
  cases b with
  | num k => exact item_num_err h5.2.1 (h5.1.trans h6.1) h6.2.1
  | quot z =>
  cases item_quot h5.2.1 (h5.1.trans h6.1) with | intro y h7 =>
  cases h6.2.2 y with | intro d0' h8 => cases h8 with | intro d1' h8 =>
  cases u with
  | nil => exact stack_err h5.2.2 (h7.1.trans h8.1) h8.2.1
  | cons c v =>
  cases stack_push h5.2.2 (h7.1.trans h8.1) with | intro f3 h9 => cases h9 with | intro g3 h9 =>
  cases h8.2.2 f3 g3 with | intro E0 h10 => cases h10 with | intro E1 h10 =>
  cases c with
  | quot q => exact item_quot_err h9.2.1 (h9.1.trans h10.1) h10.2.1
  | num k =>
  cases item_num h9.2.1 (h9.1.trans h10.1) with | intro fn h11 =>
  cases h10.2.2 fn with | intro N0 h12 => cases h12 with | intro N1 h12 =>
  cases k with
  | zero =>
    exact Contract.of_steps ((nat_zero h11.2 (h11.1.trans h12.1)).trans h12.2.1)
      (hap z v y g3 h7.2 h9.2.2)
  | succ m =>
    cases nat_succ h11.2 (h11.1.trans h12.1) with | intro fm h13 =>
    cases h12.2.2 fm with | intro p h14 =>
    exact Contract.of_steps (h13.1.trans h14.1)
      (hap sc (.num m :: v) x p h3.2
        (DecStack.of_steps h14.2
          (dec_push (dec_num h13.2) (DecStack.of_steps (steps_thunk1 _ _) h9.2.2))))

theorem leaf_ifz (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .ifz ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .ifz S) :=
  leafD_ifz apT ap hap S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- add   ( n m — m+n )   Class C: the compiled `add` recurses on its numeral
--
-- `Scott.add` is `Y ⬝ addF` for the fixpoint combinator
-- `Y = S (K (S I I)) (S (S (K S) K) (K (S I I)))`.  Unrolling never returns
-- to a syntactically equal term: each round wraps the self-application in
-- one more `I`, and normal order does not reduce arguments.  So the loop
-- invariant is semantic: `addSelf z` behaves as `add` whenever `z` reduces
-- to `addB`, and `I ⬝ z` reduces to `addB` again (`addSelf_step`).
-- `add_dec` is then an induction on the second numeral.
-- ---------------------------------------------------------------------------

/-- `λ self m n. n |> { Zero m; Suc k (Suc (self m k)) }`, compiled. -/
def addF : Term :=
  S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ I)) ⬝ K))))
    ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ K))) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Suc)))))

/-- The fixpoint's self-application, `λ x. addF (x x)`. -/
def addB : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ addF

/-- A self-reference of `add`, as the unrolling produces it. -/
def addSelf (z : Term) : Term := K ⬝ (S ⬝ I ⬝ I) ⬝ addF ⬝ z

theorem add_self (m n : Term) : Steps (Scott.add ⬝ m ⬝ n) (addSelf addB ⬝ m ⬝ n) :=
  iter_sound (k := 1) rfl

theorem addB_unfold (y : Term) : Steps (addB ⬝ y) (addF ⬝ addSelf y) :=
  iter_sound (k := 5) rfl

theorem addSelf_step {z : Term} (hz : Steps z addB) (m n : Term) :
    Steps (addSelf z ⬝ m ⬝ n) (addF ⬝ addSelf (I ⬝ z) ⬝ m ⬝ n) :=
  (iter_sound (k := 3) rfl : Steps (addSelf z ⬝ m ⬝ n) (z ⬝ (I ⬝ z) ⬝ m ⬝ n)).trans
    ((Steps.app2 m n (Steps.left (I ⬝ z) hz)).trans (Steps.app2 m n (addB_unfold _)))

theorem addF_stages (R fm fn : Term) : ∃ c1,
    Steps (addF ⬝ R ⬝ fm ⬝ fn) (fn ⬝ (K ⬝ fm ⬝ fn) ⬝ c1) ∧
    ∀ f1, Steps (c1 ⬝ f1) (Scott.Suc ⬝ (R ⬝ fm ⬝ f1)) :=
  ⟨_, iter_sound (k := 10) rfl, fun _ => iter_sound (k := 9) rfl⟩

theorem addSelf_dec (n : Nat) : ∀ {z fm fn : Term} {m : Nat}, Steps z addB →
    DecNat fm m → DecNat fn n → DecNat (addSelf z ⬝ fm ⬝ fn) (m + n) := by
  induction n with
  | zero =>
    intro z fm fn m hz hm hn
    cases addF_stages (addSelf (I ⬝ z)) fm fn with
    | intro c1 h =>
      exact DecNat.of_steps
        ((addSelf_step hz fm fn).trans ((nat_zero hn h.1).trans (steps_thunk1 fm fn))) hm
  | succ n ih =>
    intro z fm fn m hz hm hn
    cases addF_stages (addSelf (I ⬝ z)) fm fn with
    | intro c1 h =>
      cases nat_succ hn ((addSelf_step hz fm fn).trans h.1) with
      | intro f1 h1 =>
        show DecNat _ ((m + n) + 1)
        exact DecNat.of_steps (h1.1.trans (h.2 f1))
          (dec_suc (ih (Steps.step (.I z) hz) hm h1.2))

/-- **The compiled `add` adds.**  Class C's leaf lemma. -/
theorem add_dec {fm fn : Term} {m n : Nat} (hm : DecNat fm m) (hn : DecNat fn n) :
    DecNat (Scott.add ⬝ fm ⬝ fn) (m + n) :=
  DecNat.of_steps (add_self fm fn) (addSelf_dec n (.refl _) hm hn)

/-- `λ m n. Num (add m n)`. -/
def addN : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Num))) ⬝ Scott.add

/-- `λ u m n. u`. -/
def addT : Term := S ⬝ (K ⬝ K) ⬝ K

/-- `λ u m n. Push (Num (add m n)) u`. -/
def addC : Term :=
  S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Push))) ⬝ addN)))) ⬝ addT

theorem addC_push (u m n : Term) :
    Steps (addC ⬝ u ⬝ m ⬝ n) (Scott.Push ⬝ (addN ⬝ m ⬝ n) ⬝ (addT ⬝ u ⬝ m ⬝ n)) :=
  iter_sound (k := 10) rfl

theorem addN_num (m n : Term) : Steps (addN ⬝ m ⬝ n) (Scott.Num ⬝ (Scott.add ⬝ m ⬝ n)) :=
  iter_sound (k := 4) rfl

theorem addT_tail (u m n : Term) : Steps (addT ⬝ u ⬝ m ⬝ n) u :=
  iter_sound (k := 4) rfl

theorem wAdd_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wAdd ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ d0 d1, Steps (c1 ⬝ f ⬝ g) (g ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
    ∀ f2 g2, ∃ e0 e1, Steps (d1 ⬝ f2 ⬝ g2) (f ⬝ e0 ⬝ e1) ∧ (∀ q, Steps (e1 ⬝ q) Scott.RErr) ∧
    ∀ m, ∃ e2 e3, Steps (e0 ⬝ m) (f2 ⬝ e2 ⬝ e3) ∧ (∀ q, Steps (e3 ⬝ q) Scott.RErr) ∧
    ∀ n, Steps (e2 ⬝ n) (Scott.RVal ⬝ (addC ⬝ g2 ⬝ m ⬝ n)) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 6) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 23) rfl, fun _ => iter_sound (k := 4) rfl, fun _ =>
    ⟨_, _, iter_sound (k := 21) rfl, fun _ => iter_sound (k := 4) rfl, fun _ =>
      iter_sound (k := 7) rfl⟩⟩⟩⟩

theorem leafD_add (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .add ⬝ s) (cw ap .add S) := by
  cases wAdd_stages s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
  cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
  cases h.2.2 f g with | intro d0 h2 => cases h2 with | intro d1 h2 =>
  cases t with
  | nil => cases a <;> exact stack_err h1.2.2 (h1.1.trans h2.1) h2.2.1
  | cons b u =>
  cases stack_push h1.2.2 (h1.1.trans h2.1) with | intro f2 h3 => cases h3 with | intro g2 h3 =>
  cases h2.2.2 f2 g2 with | intro e0 h4 => cases h4 with | intro e1 h4 =>
  cases a with
  | quot q => exact item_quot_err h1.2.1 (h3.1.trans h4.1) h4.2.1
  | num m =>
  cases item_num h1.2.1 (h3.1.trans h4.1) with | intro x h5 =>
  cases h4.2.2 x with | intro e0' h6 => cases h6 with | intro e1' h6 =>
  cases b with
  | quot q => exact item_quot_err h3.2.1 (h5.1.trans h6.1) h6.2.1
  | num n =>
  cases item_num h3.2.1 (h5.1.trans h6.1) with | intro y h7 =>
  exact contract_val (h7.1.trans (h6.2.2 y))
    (DecStack.of_steps (addC_push _ _ _)
      (dec_push (DecItem.of_steps (addN_num _ _) (dec_num (add_dec h5.2 h7.2)))
        (DecStack.of_steps (addT_tail _ _ _) h3.2.2)))

theorem leaf_add (ap : Quotation → Stack → Outcome) (S : Stack) (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (phi .add ⬝ encStack S) t ∧ Decodes t (cw ap .add S) :=
  leafD_add ap S (encStack_dec S hS)
