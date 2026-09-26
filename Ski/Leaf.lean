import Ski.Decode
open Term

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

## Words that run a quotation

`dip` and `i` stop with the quotation eliminator `apT` at the head,
applied to the quotation and the rest of the stack.  `ApSound apT ap` is
the contract they assume of it: `apT`, applied to anything that decodes
to `r` and `u`, meets `Contract` for `ap r u`.  The `*_run` lemmas assume
it only at the one `(r, u)` the stack supplies, so they apply to an
eliminator that diverges elsewhere.
-/

-- ---------------------------------------------------------------------------
-- Contracts, and the steps every leaf shares
-- ---------------------------------------------------------------------------

/-- `t` reduces to a weak head normal form that decodes to `o`. -/
def Contract (t : Term) (o : Outcome) : Prop := ∃ u, Eval t u ∧ Decodes u o

theorem Contract.of_steps {t t' : Term} {o : Outcome} (h : Steps t t') (h' : Contract t' o) :
    Contract t o := by
  cases h' with
  | intro u hu => exact ⟨u, ⟨h.trans hu.1.1, hu.1.2⟩, hu.2⟩

/-- The quotation eliminator `apT` realizes the model `ap`. -/
def ApSound (apT : Term) (ap : Quotation → Stack → Outcome) : Prop :=
  ∀ r u fr fu, DecQuot fr r → DecStack fu u → Contract (apT ⬝ fr ⬝ fu) (ap r u)

/-- The weak head normal form of `RVal ⬝ g`. -/
def rvalW (g : Term) : Term :=
  S ⬝ (K ⬝ K) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K) ⬝ g)

theorem eval_rval (g : Term) : Eval (Scott.RVal ⬝ g) (rvalW g) :=
  ⟨iter_sound (k := 2) rfl, .S2 _ _⟩

theorem dec_rvalW {g : Term} {s : Stack} (h : DecStack g s) : Decodes (rvalW g) (.val s) :=
  fun k0 _ _ => ⟨_, iter_sound (k := 12) rfl, DecStack.of_steps (steps_thunk1 g k0) h⟩

theorem contract_val {t g : Term} {s : Stack} (ht : Steps t (Scott.RVal ⬝ g))
    (hg : DecStack g s) : Contract t (.val s) :=
  ⟨rvalW g, ⟨ht.trans (eval_rval g).1, (eval_rval g).2⟩, dec_rvalW hg⟩

theorem contract_err {t : Term} (ht : Steps t Scott.RErr) : Contract t .err :=
  ⟨Scott.RErr, ⟨ht, .K1 K⟩, dec_rerr⟩

/-- An empty input stack takes the first continuation. -/
theorem stack_err {s c0 c1 t : Term} (hs : DecStack s []) (h : Steps t (s ⬝ c0 ⬝ c1))
    (h0 : Steps c0 Scott.RErr) : Contract t .err :=
  contract_err (h.trans ((hs c0 c1).trans h0))

/-- A non-empty input stack takes the second, with its top and rest. -/
theorem stack_push {s c0 c1 t : Term} {a : Item} {S : Stack} (hs : DecStack s (a :: S))
    (h : Steps t (s ⬝ c0 ⬝ c1)) :
    ∃ f g, Steps t (c1 ⬝ f ⬝ g) ∧ DecItem f a ∧ DecStack g S := by
  cases hs c0 c1 with
  | intro f hf =>
    cases hf with
    | intro g hg => exact ⟨f, g, h.trans hg.1, hg.2⟩

/-- A number where a quotation is wanted takes the first continuation. -/
theorem item_num_err {x e0 e1 t : Term} {n : Nat} (hx : DecItem x (.num n))
    (h : Steps t (x ⬝ e0 ⬝ e1)) (he : ∀ f, Steps (e0 ⬝ f) Scott.RErr) : Contract t .err := by
  cases hx e0 e1 with
  | intro f hf => exact contract_err (h.trans (hf.1.trans (he f)))

/-- A quotation takes the second continuation, with its body. -/
theorem item_quot {x e0 e1 t : Term} {q : Quotation} (hx : DecItem x (.quot q))
    (h : Steps t (x ⬝ e0 ⬝ e1)) : ∃ f, Steps t (e1 ⬝ f) ∧ DecQuot f q := by
  cases hx e0 e1 with
  | intro f hf => exact ⟨f, h.trans hf.1, hf.2⟩

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

theorem leaf_pop (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .pop ⬝ encStack S) t ∧ Decodes t (cw ap .pop S) :=
  leafD_pop ap S (encStack_dec S)

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

theorem leaf_dup (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .dup ⬝ encStack S) t ∧ Decodes t (cw ap .dup S) :=
  leafD_dup ap S (encStack_dec S)

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

theorem leaf_swap (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .swap ⬝ encStack S) t ∧ Decodes t (cw ap .swap S) :=
  leafD_swap ap S (encStack_dec S)

-- ---------------------------------------------------------------------------
-- unit   ( a — [a] )
-- ---------------------------------------------------------------------------

/-- `λ a. Quot (QUnit a)`. -/
def unitQ : Term := S ⬝ (K ⬝ Scott.Quot) ⬝ Scott.QUnit

/-- `λ a t. Push (Quot (QUnit a)) t`. -/
def unitC : Term := S ⬝ (K ⬝ Scott.Push) ⬝ unitQ

theorem unitC_push (f0 f1 : Term) :
    Steps (unitC ⬝ f0 ⬝ f1) (Scott.Push ⬝ (unitQ ⬝ f0) ⬝ f1) :=
  iter_sound (k := 2) rfl

theorem unitQ_quot (f0 : Term) :
    Steps (unitQ ⬝ f0) (Scott.Quot ⬝ (Scott.QUnit ⬝ f0)) :=
  iter_sound (k := 2) rfl

theorem wUnit_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wUnit ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, Steps (c1 ⬝ f ⬝ g) (Scott.RVal ⬝ (unitC ⬝ f ⬝ g)) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ => iter_sound (k := 5) rfl⟩

theorem leafD_unit (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .unit ⬝ s) (cw ap .unit S) := by
  cases wUnit_stages s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    exact contract_val (h1.1.trans (h.2.2 f g))
      (DecStack.of_steps (unitC_push _ _)
        (dec_push (DecItem.of_steps (unitQ_quot _) (dec_quot (dec_qunit h1.2.1))) h1.2.2))

theorem leaf_unit (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .unit ⬝ encStack S) t ∧ Decodes t (cw ap .unit S) :=
  leafD_unit ap S (encStack_dec S)

-- ---------------------------------------------------------------------------
-- cons   ( b [r] — [b r] )
-- ---------------------------------------------------------------------------

/-- `λ r b. QCons b r`, with `r` passed back as a thunk. -/
def consR : Term := S ⬝ (K ⬝ (S ⬝ Scott.QCons)) ⬝ K

/-- `λ r b. Quot (QCons b r)`. -/
def consQ : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Quot))) ⬝ consR

/-- `λ r b u. Push (Quot (QCons b r)) u`. -/
def consC : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Push))) ⬝ consQ

theorem consC_push (f0 f1 f2 : Term) :
    Steps (consC ⬝ f0 ⬝ f1 ⬝ f2) (Scott.Push ⬝ (consQ ⬝ f0 ⬝ f1) ⬝ f2) :=
  iter_sound (k := 4) rfl

theorem consQ_quot (f0 f1 : Term) :
    Steps (consQ ⬝ f0 ⬝ f1) (Scott.Quot ⬝ (consR ⬝ f0 ⬝ f1)) :=
  iter_sound (k := 4) rfl

theorem consR_qcons (f0 f1 : Term) :
    Steps (consR ⬝ f0 ⬝ f1) (Scott.QCons ⬝ f1 ⬝ (K ⬝ f0 ⬝ f1)) :=
  iter_sound (k := 3) rfl

theorem wQcons_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wQcons ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ e0 e1, Steps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, Steps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d0 d1, Steps (e1 ⬝ x) (g ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
        ∀ f2 g2, Steps (d1 ⬝ f2 ⬝ g2) (Scott.RVal ⬝ (consC ⬝ x ⬝ f2 ⬝ g2)) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 10) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
      ⟨_, _, iter_sound (k := 10) rfl, iter_sound (k := 1) rfl, fun _ _ =>
        iter_sound (k := 7) rfl⟩⟩⟩

theorem leafD_cons (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .cons ⬝ s) (cw ap .cons S) := by
  cases wQcons_stages s with | intro c0 h => cases h with | intro c1 h =>
  cases S with
  | nil => exact stack_err hs h.1 h.2.1
  | cons a t =>
    cases stack_push hs h.1 with | intro f h1 => cases h1 with | intro g h1 =>
    cases h.2.2 f g with | intro e0 h2 => cases h2 with | intro e1 h2 =>
    cases a with
    | num n => exact item_num_err h1.2.1 (h1.1.trans h2.1) h2.2.1
    | quot q =>
      cases item_quot h1.2.1 (h1.1.trans h2.1) with | intro x h3 =>
      cases h2.2.2 x with | intro d0 h4 => cases h4 with | intro d1 h4 =>
      cases t with
      | nil => exact stack_err h1.2.2 (h3.1.trans h4.1) h4.2.1
      | cons b u =>
        cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 =>
        cases h5 with | intro g2 h5 =>
        have hr := DecQuot.of_steps (consR_qcons _ _)
          (dec_qcons h5.2.1 (DecQuot.of_steps (steps_thunk1 _ _) h3.2))
        exact contract_val (h5.1.trans (h4.2.2 f2 g2))
          (DecStack.of_steps (consC_push _ _ _)
            (dec_push (DecItem.of_steps (consQ_quot _ _) (dec_quot hr)) h5.2.2))

theorem leaf_cons (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .cons ⬝ encStack S) t ∧ Decodes t (cw ap .cons S) :=
  leafD_cons ap S (encStack_dec S)

-- ---------------------------------------------------------------------------
-- cat   ( [l] [r] — [[l] i r] )
-- ---------------------------------------------------------------------------

/-- `λ r l. QThen r`. -/
def catThen : Term := S ⬝ (K ⬝ K) ⬝ Scott.QThen

/-- `λ r l. QCons (Quot l) (QThen r)`. -/
def catR : Term := S ⬝ (K ⬝ (S ⬝ (S ⬝ (K ⬝ Scott.QCons) ⬝ Scott.Quot))) ⬝ catThen

/-- `λ r l. Quot (QCons (Quot l) (QThen r))`. -/
def catQ : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Quot))) ⬝ catR

/-- `λ r u l. Push (Quot (QCons (Quot l) (QThen r))) u`. -/
def catC : Term :=
  S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.Push))) ⬝ catQ))))
    ⬝ (K ⬝ K)

theorem catC_push (f0 f1 f2 : Term) :
    Steps (catC ⬝ f0 ⬝ f1 ⬝ f2) (Scott.Push ⬝ (catQ ⬝ f0 ⬝ f2) ⬝ (K ⬝ K ⬝ f0 ⬝ f1 ⬝ f2)) :=
  iter_sound (k := 14) rfl

theorem catQ_quot (f0 f2 : Term) :
    Steps (catQ ⬝ f0 ⬝ f2) (Scott.Quot ⬝ (catR ⬝ f0 ⬝ f2)) :=
  iter_sound (k := 4) rfl

theorem catR_qcons (f0 f2 : Term) :
    Steps (catR ⬝ f0 ⬝ f2) (Scott.QCons ⬝ (Scott.Quot ⬝ f2) ⬝ (catThen ⬝ f0 ⬝ f2)) :=
  iter_sound (k := 5) rfl

theorem catThen_qthen (f0 f2 : Term) :
    Steps (catThen ⬝ f0 ⬝ f2) (Scott.QThen ⬝ f0) :=
  iter_sound (k := 3) rfl

theorem wCat_stages (s : Term) : ∃ c0 c1,
    Steps (Scott.wCat ⬝ s) (s ⬝ c0 ⬝ c1) ∧ Steps c0 Scott.RErr ∧
    ∀ f g, ∃ e0 e1, Steps (c1 ⬝ f ⬝ g) (f ⬝ e0 ⬝ e1) ∧ (∀ n, Steps (e0 ⬝ n) Scott.RErr) ∧
      ∀ x, ∃ d0 d1, Steps (e1 ⬝ x) (g ⬝ d0 ⬝ d1) ∧ Steps d0 Scott.RErr ∧
        ∀ f2 g2, ∃ e0' e1', Steps (d1 ⬝ f2 ⬝ g2) (f2 ⬝ e0' ⬝ e1') ∧
          (∀ n, Steps (e0' ⬝ n) Scott.RErr) ∧
          ∀ y, Steps (e1' ⬝ y) (Scott.RVal ⬝ (catC ⬝ x ⬝ g2 ⬝ y)) :=
  ⟨_, _, iter_sound (k := 3) rfl, iter_sound (k := 1) rfl, fun _ _ =>
    ⟨_, _, iter_sound (k := 10) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
      ⟨_, _, iter_sound (k := 10) rfl, iter_sound (k := 1) rfl, fun _ _ =>
        ⟨_, _, iter_sound (k := 12) rfl, fun _ => iter_sound (k := 2) rfl, fun _ =>
          iter_sound (k := 9) rfl⟩⟩⟩⟩

theorem leafD_cat (ap : Quotation → Stack → Outcome) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi .cat ⬝ s) (cw ap .cat S) := by
  cases wCat_stages s with | intro c0 h => cases h with | intro c1 h =>
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
        cases stack_push h1.2.2 (h3.1.trans h4.1) with | intro f2 h5 =>
        cases h5 with | intro g2 h5 =>
        cases h4.2.2 f2 g2 with | intro e0' h6 => cases h6 with | intro e1' h6 =>
        cases b with
        | num m => exact item_num_err h5.2.1 (h5.1.trans h6.1) h6.2.1
        | quot l =>
          cases item_quot h5.2.1 (h5.1.trans h6.1) with | intro y h7 =>
          have hq := DecQuot.of_steps (catR_qcons _ _)
            (dec_qcons (dec_quot h7.2) (DecQuot.of_steps (catThen_qthen _ _) (dec_qthen h3.2)))
          exact contract_val (h7.1.trans (h6.2.2 y))
            (DecStack.of_steps (catC_push _ _ _)
              (dec_push (DecItem.of_steps (catQ_quot _ _) (dec_quot hq))
                (DecStack.of_steps (steps_thunk2 _ _ _) h5.2.2)))

theorem leaf_cat (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .cat ⬝ encStack S) t ∧ Decodes t (cw ap .cat S) :=
  leafD_cat ap S (encStack_dec S)

-- ---------------------------------------------------------------------------
-- dip   ( b [r] — r b )   with `apT` running `r`
--
-- `wDip` runs until `apT` is at the head, applied to the quotation, the
-- rest of the stack and three continuations.  What `apT` does there is
-- known only through `Decodes`, which probes at every continuation, and
-- `dip`'s own continuations are the ones it is probed at.
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
    cases ho k0 k1 k2 with
    | intro fv hv =>
      exact contract_val (run.trans (hv.1.trans (h6.2.1 fv))) (dec_push h5.2.1 hv.2)
  | err => exact contract_err (run.trans ((ho k0 k1 k2).trans h6.2.2))

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
    (S : Stack) :
    ∃ t, Eval (phi .dip ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .dip S) :=
  leafD_dip apT ap hap S (encStack_dec S)

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
    (S : Stack) :
    ∃ t, Eval (phi .i ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .i S) :=
  leafD_i apT ap hap S (encStack_dec S)

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

theorem leafD_quote (ap : Quotation → Stack → Outcome) (q : Quotation) (S : Stack) {s : Term}
    (hs : DecStack s S) : Contract (phi (.quote q) ⬝ s) (cw ap (.quote q) S) :=
  contract_val (wQuote_run _ _)
    (DecStack.of_steps (quoteC_push _ _) (dec_push (dec_quot (encQuot_dec q)) hs))

-- ---------------------------------------------------------------------------
-- ifz   ( n [z] [s] — … )   runs `z` on the rest if `n = 0`, else `s` on `n-1`
-- ---------------------------------------------------------------------------

/-- A quotation where a number is wanted takes the second continuation. -/
theorem item_quot_err {x e0 e1 t : Term} {q : Quotation} (hx : DecItem x (.quot q))
    (h : Steps t (x ⬝ e0 ⬝ e1)) (he : ∀ f, Steps (e1 ⬝ f) Scott.RErr) : Contract t .err := by
  cases hx e0 e1 with
  | intro f hf => exact contract_err (h.trans (hf.1.trans (he f)))

/-- A number takes the first continuation, with its numeral. -/
theorem item_num {x e0 e1 t : Term} {n : Nat} (hx : DecItem x (.num n))
    (h : Steps t (x ⬝ e0 ⬝ e1)) : ∃ f, Steps t (e0 ⬝ f) ∧ DecNat f n := by
  cases hx e0 e1 with
  | intro f hf => exact ⟨f, h.trans hf.1, hf.2⟩

theorem nat_zero {x n0 n1 t : Term} (hx : DecNat x 0) (h : Steps t (x ⬝ n0 ⬝ n1)) :
    Steps t n0 :=
  h.trans (hx n0 n1)

theorem nat_succ {x n0 n1 t : Term} {m : Nat} (hx : DecNat x (m + 1))
    (h : Steps t (x ⬝ n0 ⬝ n1)) : ∃ f, Steps t (n1 ⬝ f) ∧ DecNat f m := by
  cases hx n0 n1 with
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
    (S : Stack) :
    ∃ t, Eval (phi .ifz ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .ifz S) :=
  leafD_ifz apT ap hap S (encStack_dec S)
