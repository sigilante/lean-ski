import Ski.Decode
open Term

/-!
# Leaf contracts

`leaf_w ap S` says the compiled word `phi w`, applied to the encoding of
`S`, reduces to a weak head normal form that decodes to `cw ap w S`.
This is the requested form `Steps (phi w ⬝ encStack S) t ∧ Decodes t …`,
strengthened from `Steps` to `Eval`: the word also terminates at `t`.
Every word except `dip`, `i` and `ifz` ignores `ap`.

Each proof has the same three parts.  The kernel re-runs the word on a
symbolic stack (`iter_sound rfl`, as for the `*_elim` lemmas), down to
`RErr` or to `RVal` applied to a result stack; normal order stops there,
because the result stack is an argument.  `contract_err` and
`contract_val` finish the outer layer once and for all.  What remains is
that the result stack decodes, which the constructor lemmas of
`Ski/Decode.lean` give once its combinator reduces to `Push`
applications (`dupD_push` for `dup`).
-/

-- ---------------------------------------------------------------------------
-- The outer layer: `RVal ⬝ g` and `RErr`
-- ---------------------------------------------------------------------------

/-- The weak head normal form of `RVal ⬝ g`. -/
def rvalW (g : Term) : Term :=
  S ⬝ (K ⬝ K) ⬝ ((S ⬝ (K ⬝ (S ⬝ (K ⬝ K)))) ⬝ ((S ⬝ (K ⬝ (S ⬝ I))) ⬝ K) ⬝ g)

theorem eval_rval (g : Term) : Eval (Scott.RVal ⬝ g) (rvalW g) :=
  ⟨iter_sound (k := 2) rfl, .S2 _ _⟩

theorem dec_rvalW {g : Term} {s : Stack} (h : DecStack g s) : Decodes (rvalW g) (.val s) :=
  fun k0 _ _ => ⟨_, iter_sound (k := 12) rfl, DecStack.of_steps (steps_thunk1 g k0) h⟩

theorem contract_val {t g : Term} {s : Stack} (ht : Steps t (Scott.RVal ⬝ g))
    (hg : DecStack g s) : ∃ u, Eval t u ∧ Decodes u (.val s) :=
  ⟨rvalW g, ⟨ht.trans (eval_rval g).1, (eval_rval g).2⟩, dec_rvalW hg⟩

theorem contract_err {t : Term} (ht : Steps t Scott.RErr) : ∃ u, Eval t u ∧ Decodes u .err :=
  ⟨Scott.RErr, ⟨ht, .K1 K⟩, dec_rerr⟩

-- ---------------------------------------------------------------------------
-- pop   ( a — )
-- ---------------------------------------------------------------------------

theorem wPop_empty : Steps (Scott.wPop ⬝ Scott.Empty) Scott.RErr := iter_sound (k := 5) rfl

theorem wPop_push (x y : Term) :
    Steps (Scott.wPop ⬝ (Scott.Push ⬝ x ⬝ y))
      (Scott.RVal ⬝ (K ⬝ K ⬝ x ⬝ y ⬝ (K ⬝ (K ⬝ Scott.RVal) ⬝ (Scott.Push ⬝ x ⬝ y)))) :=
  iter_sound (k := 24) rfl

theorem leaf_pop (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .pop ⬝ encStack S) t ∧ Decodes t (cw ap .pop S) := by
  cases S with
  | nil => exact contract_err wPop_empty
  | cons a s =>
    exact contract_val (wPop_push _ _)
      (DecStack.of_steps (steps_thunk2 _ _ _) (encStack_dec s))

-- ---------------------------------------------------------------------------
-- dup   ( a — a a )
-- ---------------------------------------------------------------------------

/-- `λ a t. Push a (Push a t)`, as bracket abstraction leaves it. -/
def dupD : Term := S ⬝ (S ⬝ (K ⬝ S) ⬝ (S ⬝ (K ⬝ K) ⬝ Scott.Push)) ⬝ Scott.Push

/-- The continuation `wDup` hands a non-empty stack. -/
def dupK : Term := S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.RVal))) ⬝ dupD

theorem dupD_push (a t : Term) :
    Steps (dupD ⬝ a ⬝ t) (Scott.Push ⬝ a ⬝ (Scott.Push ⬝ a ⬝ t)) :=
  iter_sound (k := 7) rfl

theorem wDup_empty : Steps (Scott.wDup ⬝ Scott.Empty) Scott.RErr := iter_sound (k := 5) rfl

theorem wDup_push (x y : Term) :
    Steps (Scott.wDup ⬝ (Scott.Push ⬝ x ⬝ y))
      (Scott.RVal ⬝ (dupD ⬝ (K ⬝ x ⬝ (K ⬝ dupK ⬝ (Scott.Push ⬝ x ⬝ y)))
                          ⬝ (K ⬝ K ⬝ x ⬝ y ⬝ (K ⬝ dupK ⬝ (Scott.Push ⬝ x ⬝ y))))) :=
  iter_sound (k := 27) rfl

theorem leaf_dup (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .dup ⬝ encStack S) t ∧ Decodes t (cw ap .dup S) := by
  cases S with
  | nil => exact contract_err wDup_empty
  | cons a s =>
    let k := K ⬝ dupK ⬝ encStack (a :: s)
    have ha := DecItem.of_steps (steps_thunk1 (encItem a) k) (encItem_dec a)
    have hs := DecStack.of_steps (steps_thunk2 (encItem a) (encStack s) k) (encStack_dec s)
    exact contract_val (wDup_push _ _)
      (DecStack.of_steps (dupD_push _ _) (dec_push ha (dec_push ha hs)))

/-!
## Longer runs: junk continuations

From `swap` on, a word's run leaves each field of its result as a thunk
`K ⬝ x ⬝ j` or `K ⬝ K ⬝ x ⬝ y ⬝ j`, where the junk `j` is a continuation
built from the word's own body, hundreds of atoms long and never
inspected again.  The run lemmas quantify it away (`∃ j0 j1 …`), and the
kernel's `rfl` supplies it.  What stays in the statement is the result's
skeleton — a small combinator applied to the thunks — and the skeleton
lemmas reduce each one to Scott constructors.
-/

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

theorem wSwap_empty : Steps (Scott.wSwap ⬝ Scott.Empty) Scott.RErr := iter_sound (k := 5) rfl

theorem wSwap_one (x : Term) :
    Steps (Scott.wSwap ⬝ (Scott.Push ⬝ x ⬝ Scott.Empty)) Scott.RErr :=
  iter_sound (k := 32) rfl

theorem wSwap_two (x x2 y2 : Term) : ∃ j0 j1 j2,
    Steps (Scott.wSwap ⬝ (Scott.Push ⬝ x ⬝ (Scott.Push ⬝ x2 ⬝ y2)))
      (Scott.RVal ⬝ (swapC ⬝ (K ⬝ x ⬝ j0) ⬝ (K ⬝ x2 ⬝ j1) ⬝ (K ⬝ K ⬝ x2 ⬝ y2 ⬝ j2))) :=
  ⟨_, _, _, iter_sound (k := 58) rfl⟩

theorem leaf_swap (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .swap ⬝ encStack S) t ∧ Decodes t (cw ap .swap S) := by
  cases S with
  | nil => exact contract_err wSwap_empty
  | cons a t =>
    cases t with
    | nil => exact contract_err (wSwap_one _)
    | cons b u =>
      cases wSwap_two (encItem a) (encItem b) (encStack u) with
      | intro j0 h =>
        cases h with
        | intro j1 h =>
          cases h with
          | intro j2 h =>
            have ha := DecItem.of_steps (steps_thunk1 _ j0) (encItem_dec a)
            have hb := DecItem.of_steps (steps_thunk1 _ j1) (encItem_dec b)
            have hu := DecStack.of_steps (steps_thunk2 (encItem b) _ j2) (encStack_dec u)
            exact contract_val h
              (DecStack.of_steps (swapC_push _ _ _)
                (dec_push hb (DecStack.of_steps (swapT_push _ _ _) (dec_push ha hu))))

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

theorem wUnit_empty : Steps (Scott.wUnit ⬝ Scott.Empty) Scott.RErr := iter_sound (k := 5) rfl

theorem wUnit_push (x y : Term) : ∃ j0 j1,
    Steps (Scott.wUnit ⬝ (Scott.Push ⬝ x ⬝ y))
      (Scott.RVal ⬝ (unitC ⬝ (K ⬝ x ⬝ j0) ⬝ (K ⬝ K ⬝ x ⬝ y ⬝ j1))) :=
  ⟨_, _, iter_sound (k := 27) rfl⟩

theorem leaf_unit (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .unit ⬝ encStack S) t ∧ Decodes t (cw ap .unit S) := by
  cases S with
  | nil => exact contract_err wUnit_empty
  | cons a s =>
    cases wUnit_push (encItem a) (encStack s) with
    | intro j0 h =>
      cases h with
      | intro j1 h =>
        have ha := DecItem.of_steps (steps_thunk1 _ j0) (encItem_dec a)
        have hs := DecStack.of_steps (steps_thunk2 (encItem a) _ j1) (encStack_dec s)
        exact contract_val h
          (DecStack.of_steps (unitC_push _ _)
            (dec_push (DecItem.of_steps (unitQ_quot _) (dec_quot (dec_qunit ha))) hs))

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

theorem wQcons_empty : Steps (Scott.wQcons ⬝ Scott.Empty) Scott.RErr := iter_sound (k := 5) rfl

theorem wQcons_num (n y : Term) :
    Steps (Scott.wQcons ⬝ (Scott.Push ⬝ (Scott.Num ⬝ n) ⬝ y)) Scott.RErr :=
  iter_sound (k := 44) rfl

theorem wQcons_one (r : Term) :
    Steps (Scott.wQcons ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ Scott.Empty)) Scott.RErr :=
  iter_sound (k := 54) rfl

theorem wQcons_two (r x2 y2 : Term) : ∃ j0 j1 j2,
    Steps (Scott.wQcons ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ (Scott.Push ⬝ x2 ⬝ y2)))
      (Scott.RVal ⬝ (consC ⬝ (K ⬝ r ⬝ j0) ⬝ (K ⬝ x2 ⬝ j1) ⬝ (K ⬝ K ⬝ x2 ⬝ y2 ⬝ j2))) :=
  ⟨_, _, _, iter_sound (k := 78) rfl⟩

theorem leaf_cons (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .cons ⬝ encStack S) t ∧ Decodes t (cw ap .cons S) := by
  cases S with
  | nil => exact contract_err wQcons_empty
  | cons a t =>
    cases a with
    | num n => exact contract_err (wQcons_num _ _)
    | quot q =>
      cases t with
      | nil => exact contract_err (wQcons_one _)
      | cons b u =>
        cases wQcons_two (encQuot q) (encItem b) (encStack u) with
        | intro j0 h =>
          cases h with
          | intro j1 h =>
            cases h with
            | intro j2 h =>
              have hq := DecQuot.of_steps (steps_thunk1 _ j0) (encQuot_dec q)
              have hb := DecItem.of_steps (steps_thunk1 _ j1) (encItem_dec b)
              have hu := DecStack.of_steps (steps_thunk2 (encItem b) _ j2) (encStack_dec u)
              have hr := DecQuot.of_steps (consR_qcons _ _)
                (dec_qcons hb (DecQuot.of_steps (steps_thunk1 _ _) hq))
              exact contract_val h
                (DecStack.of_steps (consC_push _ _ _)
                  (dec_push (DecItem.of_steps (consQ_quot _ _) (dec_quot hr)) hu))

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

theorem wCat_empty : Steps (Scott.wCat ⬝ Scott.Empty) Scott.RErr := iter_sound (k := 5) rfl

theorem wCat_num (n y : Term) :
    Steps (Scott.wCat ⬝ (Scott.Push ⬝ (Scott.Num ⬝ n) ⬝ y)) Scott.RErr :=
  iter_sound (k := 44) rfl

theorem wCat_one (r : Term) :
    Steps (Scott.wCat ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ Scott.Empty)) Scott.RErr :=
  iter_sound (k := 54) rfl

theorem wCat_quot_num (r m y2 : Term) :
    Steps (Scott.wCat ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ (Scott.Push ⬝ (Scott.Num ⬝ m) ⬝ y2)))
      Scott.RErr :=
  iter_sound (k := 95) rfl

theorem wCat_two (r l y2 : Term) : ∃ j0 j1 j2,
    Steps (Scott.wCat ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ l) ⬝ y2)))
      (Scott.RVal ⬝ (catC ⬝ (K ⬝ r ⬝ j0) ⬝ (K ⬝ K ⬝ (Scott.Quot ⬝ l) ⬝ y2 ⬝ j1) ⬝ (K ⬝ l ⬝ j2))) :=
  ⟨_, _, _, iter_sound (k := 100) rfl⟩

theorem leaf_cat (ap : Quotation → Stack → Outcome) (S : Stack) :
    ∃ t, Eval (phi .cat ⬝ encStack S) t ∧ Decodes t (cw ap .cat S) := by
  cases S with
  | nil => exact contract_err wCat_empty
  | cons a t =>
    cases a with
    | num n => exact contract_err (wCat_num _ _)
    | quot r =>
      cases t with
      | nil => exact contract_err (wCat_one _)
      | cons b u =>
        cases b with
        | num m => exact contract_err (wCat_quot_num _ _ _)
        | quot l =>
          cases wCat_two (encQuot r) (encQuot l) (encStack u) with
          | intro j0 h =>
            cases h with
            | intro j1 h =>
              cases h with
              | intro j2 h =>
                have hr := DecQuot.of_steps (steps_thunk1 _ j0) (encQuot_dec r)
                have hu := DecStack.of_steps (steps_thunk2 (Scott.Quot ⬝ encQuot l) _ j1) (encStack_dec u)
                have hl := DecQuot.of_steps (steps_thunk1 _ j2) (encQuot_dec l)
                have hq := DecQuot.of_steps (catR_qcons _ _)
                  (dec_qcons (dec_quot hl) (DecQuot.of_steps (catThen_qthen _ _) (dec_qthen hr)))
                exact contract_val h
                  (DecStack.of_steps (catC_push _ _ _)
                    (dec_push (DecItem.of_steps (catQ_quot _ _) (dec_quot hq))
                      (DecStack.of_steps (steps_thunk2 _ _ _) hu)))

-- ---------------------------------------------------------------------------
-- dip   ( b [r] — r b )   with `ap` running `r`
--
-- `wDip` runs until the quotation eliminator is at the head, applied to
-- thunks of `r` and `u` and to three continuations.  What `ap` does there
-- is known only through `Decodes`, which is why that relation probes at
-- every continuation: `dip`'s own continuations are the ones it is probed
-- at.  The core lemma is pointwise in `(r, u)`, so it applies to an `ap`
-- that diverges elsewhere; `leaf_dip` is its corollary for a total model.
-- ---------------------------------------------------------------------------

/-- `λ b u v. RVal (Push b v)`. -/
def dipV : Term := S ⬝ (K ⬝ K) ⬝ (S ⬝ (K ⬝ (S ⬝ (K ⬝ Scott.RVal))) ⬝ Scott.Push)

/-- The value continuation `wDip` hands `ap`, applied to its result stack. -/
theorem dipK_val (a1 a2 a3 a4 v : Term) :
    Steps (K ⬝ (K ⬝ dipV) ⬝ a1 ⬝ a2 ⬝ a3 ⬝ a4 ⬝ v) (Scott.RVal ⬝ (Scott.Push ⬝ a3 ⬝ v)) :=
  iter_sound (k := 9) rfl

/-- The error continuation `wDip` hands `ap`. -/
theorem dipK_err (a1 a2 a3 a4 : Term) :
    Steps (K ⬝ (K ⬝ (K ⬝ (K ⬝ (K ⬝ K)))) ⬝ a1 ⬝ a2 ⬝ a3 ⬝ a4) Scott.RErr :=
  iter_sound (k := 4) rfl

theorem wDip_empty (apT : Term) : Steps (Scott.wDip ⬝ apT ⬝ Scott.Empty) Scott.RErr :=
  iter_sound (k := 7) rfl

theorem wDip_num (apT n y : Term) :
    Steps (Scott.wDip ⬝ apT ⬝ (Scott.Push ⬝ (Scott.Num ⬝ n) ⬝ y)) Scott.RErr :=
  iter_sound (k := 50) rfl

theorem wDip_one (apT r : Term) :
    Steps (Scott.wDip ⬝ apT ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ Scott.Empty)) Scott.RErr :=
  iter_sound (k := 64) rfl

theorem wDip_two (apT r x2 y2 : Term) : ∃ j0 j1 j2 a1 a2 a4 e1 e2 e3 e4 k2,
    Steps (Scott.wDip ⬝ apT ⬝ (Scott.Push ⬝ (Scott.Quot ⬝ r) ⬝ (Scott.Push ⬝ x2 ⬝ y2)))
      (apT ⬝ (K ⬝ r ⬝ j0) ⬝ (K ⬝ K ⬝ x2 ⬝ y2 ⬝ j1)
        ⬝ (K ⬝ (K ⬝ dipV) ⬝ a1 ⬝ a2 ⬝ (K ⬝ x2 ⬝ j2) ⬝ a4)
        ⬝ (K ⬝ (K ⬝ (K ⬝ (K ⬝ (K ⬝ K)))) ⬝ e1 ⬝ e2 ⬝ e3 ⬝ e4)
        ⬝ k2) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, iter_sound (k := 133) rfl⟩

/-- `dip`'s outcome once `ap r u` has returned `o`. -/
def dipOut (b : Item) : Outcome → Outcome
  | .val v => .val (b :: v)
  | .err => .err

theorem cw_dip (ap : Quotation → Stack → Outcome) (r : Quotation) (b : Item) (u : Stack) :
    cw ap .dip (.quot r :: b :: u) = dipOut b (ap r u) := by
  simp only [cw]
  cases ap r u <;> rfl

theorem leaf_dip_run (apT : Term) (r : Quotation) (b : Item) (u : Stack) (o : Outcome)
    (hap : ∀ fr fu, DecQuot fr r → DecStack fu u → Decodes (apT ⬝ fr ⬝ fu) o) :
    ∃ t, Eval (phi .dip ⬝ apT ⬝ encStack (.quot r :: b :: u)) t ∧ Decodes t (dipOut b o) := by
  cases wDip_two apT (encQuot r) (encItem b) (encStack u) with
  | intro j0 h => cases h with | intro j1 h => cases h with | intro j2 h =>
  cases h with | intro a1 h => cases h with | intro a2 h => cases h with | intro a4 h =>
  cases h with | intro e1 h => cases h with | intro e2 h => cases h with | intro e3 h =>
  cases h with | intro e4 h => cases h with | intro k2 h =>
    have hr := DecQuot.of_steps (steps_thunk1 _ j0) (encQuot_dec r)
    have hu := DecStack.of_steps (steps_thunk2 (encItem b) _ j1) (encStack_dec u)
    have hb := DecItem.of_steps (steps_thunk1 _ j2) (encItem_dec b)
    have ho := hap _ _ hr hu
    cases o with
    | val v =>
      cases ho (K ⬝ (K ⬝ dipV) ⬝ a1 ⬝ a2 ⬝ (K ⬝ encItem b ⬝ j2) ⬝ a4)
          (K ⬝ (K ⬝ (K ⬝ (K ⬝ (K ⬝ K)))) ⬝ e1 ⬝ e2 ⬝ e3 ⬝ e4) k2 with
      | intro f hf =>
        exact contract_val (h.trans (hf.1.trans (dipK_val _ _ _ _ _))) (dec_push hb hf.2)
    | err =>
      exact contract_err (h.trans ((ho _ _ k2).trans (dipK_err _ _ _ _)))

theorem leaf_dip (apT : Term) (ap : Quotation → Stack → Outcome)
    (hap : ∀ r u fr fu, DecQuot fr r → DecStack fu u → Decodes (apT ⬝ fr ⬝ fu) (ap r u))
    (S : Stack) :
    ∃ t, Eval (phi .dip ⬝ apT ⬝ encStack S) t ∧ Decodes t (cw ap .dip S) := by
  cases S with
  | nil => exact contract_err (wDip_empty apT)
  | cons a t =>
    cases a with
    | num n => exact contract_err (wDip_num _ _ _)
    | quot r =>
      cases t with
      | nil => exact contract_err (wDip_one _ _)
      | cons b u =>
        rw [cw_dip]
        exact leaf_dip_run apT r b u (ap r u) (hap r u)
