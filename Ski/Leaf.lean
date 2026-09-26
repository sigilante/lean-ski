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
