import Ski.Leaf
open Term

set_option linter.unusedSectionVars false

/-!
# Composition

`N apT p` is the term `skilark.joy.compiled` emits for a word list `p`
(`_Compiler.body`): `idW` for the empty program, the word itself for one
word, and `seq w (N rest)` otherwise, with the quotation eliminator `apT`
passed to `dip`, `i` and `ifz`.  `Csem ap p` threads a stack through `cw`,
strictly: an error stops the program.

`composition` is `lean-nock`'s theorem for SKI.  Every leaf holds for any
input that decodes to its stack, so `seq_contract` can hand the second
word the first word's result, a thunk, and the induction goes through
with no further reasoning about terms.  `composition_agree` adds that no
other outcome is derivable: reduction is deterministic and decoding is a
function.

## Scope

`composition` assumes `ApSound apT ap`: the eliminator realizes a *total*
model `ap`.  A table's real `applyU` realizes no total model once some
quotation loops, and in this repository the hypothesis is discharged
only by `apErr`, which fails every quotation.  For programs run with the
real `applyU`, the theorem to use is `composition_apply`
(`Ski/Apply.lean`), over the relational semantics `Run`.
-/

variable [Kit] [KitElim] [KitWords]

/-- The term of a word as a compiled program uses it. -/
def wordTerm (apT : Term) : Word → Term
  | .dip => phi .dip ⬝ apT
  | .i => phi .i ⬝ apT
  | .ifz => phi .ifz ⬝ apT
  | w => phi w

/-- **Every word meets its contract**, at every input that decodes. -/
theorem leaf_correct (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (w : Word) (hw : w.ok Kit.n = true) (S : Stack) {s : Term} (hs : DecStack s S) :
    Contract (wordTerm apT w ⬝ s) (cw ap w S) := by
  cases w with
  | dup => exact leafD_dup ap S hs
  | swap => exact leafD_swap ap S hs
  | pop => exact leafD_pop ap S hs
  | cons => exact leafD_cons ap S hs
  | cat => exact leafD_cat ap S hs
  | unit => exact leafD_unit ap S hs
  | dip => exact leafD_dip apT ap hap S hs
  | i => exact leafD_i apT ap hap S hs
  | ifz => exact leafD_ifz apT ap hap S hs
  | lit n => exact leafD_lit ap n S hs
  | quote q => exact leafD_quote ap q hw S hs
  | add => exact leafD_add ap S hs

/-- Compile a word list, as `_Compiler.body` does. -/
def N (apT : Term) : List Word → Term
  | [] => Scott.idW
  | [w] => wordTerm apT w
  | w :: w' :: p => Scott.seq ⬝ wordTerm apT w ⬝ N apT (w' :: p)

/-- Continue with `k` on a value; stop on an error. -/
def bindO : Outcome → (Stack → Outcome) → Outcome
  | .val S', k => k S'
  | .err, _ => .err

/-- `t` is a compiled form of `p`: it reduces to `seq ⬝ w ⬝ g` with `g` a
    compiled form of the rest, and so on to the last word.  Bracket
    abstraction over the eliminator leaves each continuation of `seq` as an
    unreduced argument, so the compiler's term for a program that passes the
    eliminator on reaches `N` only one `seq` at a time; `N apT p` itself is a
    compiled form of `p` (`compiles_N`). -/
def Compiles (apT : Term) : List Word → Term → Prop
  | [], t => Steps t Scott.idW
  | [w], t => Steps t (wordTerm apT w)
  | w :: w' :: p, t => ∃ g, Steps t (Scott.seq ⬝ wordTerm apT w ⬝ g) ∧ Compiles apT (w' :: p) g

theorem compiles_N (apT : Term) : ∀ p, Compiles apT p (N apT p)
  | [] => .refl _
  | [_] => .refl _
  | _ :: w' :: p => ⟨_, .refl _, compiles_N apT (w' :: p)⟩

/-- Run a word list through the C model, threading the stack. -/
def Csem (ap : Quotation → Stack → Outcome) : List Word → Stack → Outcome
  | [], st => .val st
  | w :: p, st => bindO (cw ap w st) (Csem ap p)

-- ---------------------------------------------------------------------------
-- The two schemas: `idW` and `seq`
-- ---------------------------------------------------------------------------

theorem idW_contract {s : Term} {S : Stack} (hs : DecStack s S) :
    Contract (Scott.idW ⬝ s) (.val S) :=
  contract_val (.refl _) hs

theorem seq_stages (f g s : Term) : ∃ k0 k1 k2,
    Steps (Scott.seq ⬝ f ⬝ g ⬝ s) (f ⬝ s ⬝ k0 ⬝ k1 ⬝ k2) ∧
    (∀ v, Steps (k0 ⬝ v) (g ⬝ v)) ∧ Steps k1 Scott.RErr :=
  ⟨_, _, _, iter_sound (k := 26) rfl, fun _ => iter_sound (k := 5) rfl, iter_sound (k := 3) rfl⟩

/-- `seq f g` follows `f`'s outcome strictly: on a value it runs `g` on the
    result stack, whatever term carries it; on an error it stops. -/
theorem seq_contract {f g s : Term} {o : Outcome} {k : Stack → Outcome}
    (hf : Contract (f ⬝ s) o) (hg : ∀ S' t, o = .val S' → DecStack t S' → Contract (g ⬝ t) (k S')) :
    Contract (Scott.seq ⬝ f ⬝ g ⬝ s) (bindO o k) := by
  cases seq_stages f g s with | intro k0 h => cases h with | intro k1 h =>
  cases h with | intro k2 h =>
  cases hf with
  | intro u hu =>
    have run := h.1.trans (Steps.app3 k0 k1 k2 hu.1.1)
    cases o with
    | val S' =>
      cases hu.2 k0 k1 k2 with
      | intro fv hv =>
        exact Contract.of_steps (run.trans (hv.1.trans (h.2.1 fv))) (hg S' fv rfl hv.2)
    | err => exact contract_err (run.trans ((hu.2 k0 k1 k2).trans h.2.2))

-- ---------------------------------------------------------------------------
-- The composition theorem
-- ---------------------------------------------------------------------------

theorem Csem_single (ap : Quotation → Stack → Outcome) (w : Word) (S : Stack) :
    Csem ap [w] S = cw ap w S := by
  show bindO (cw ap w S) (Csem ap []) = cw ap w S
  cases cw ap w S <;> rfl

/-- **Composition.**  The compiled term of any word list, applied to any
    term that decodes to `S`, reduces to a weak head normal form that
    decodes to the C model's outcome. -/
theorem composition (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap) :
    ∀ (p : List Word), p.all (Word.ok Kit.n) = true →
      ∀ (S : Stack) {s : Term}, DecStack s S → Contract (N apT p ⬝ s) (Csem ap p S)
  | [], _, _, _, hs => idW_contract hs
  | [w], hp, st, _, hs => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at hp
    rw [Csem_single]
    exact leaf_correct apT ap hap w hp st hs
  | w :: w' :: p, hp, st, _, hs => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    exact seq_contract (leaf_correct apT ap hap w hp.1 st hs)
      (fun S' _ _ ht => composition apT ap hap (w' :: p)
        (by simp only [List.all_cons, Bool.and_eq_true]; exact hp.2) S' ht)

/-- **Agreement.**  Any outcome derivable for a compiled program is the C
    model's. -/
theorem composition_agree (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (p : List Word) (hp : p.all (Word.ok Kit.n) = true) (S : Stack) {s u : Term} {o : Outcome}
    (hs : DecStack s S) (he : Eval (N apT p ⬝ s) u) (hd : Decodes u o) : o = Csem ap p S := by
  cases composition apT ap hap p hp S hs with
  | intro u' hu' =>
    have h := Eval.deterministic he hu'.1
    rw [← h] at hu'
    exact Decodes.functional hd hu'.2

/-- The same at the encoding of `S`. -/
theorem composition_enc (apT : Term) (ap : Quotation → Stack → Outcome) (hap : ApSound apT ap)
    (p : List Word) (hp : p.all (Word.ok Kit.n) = true) (S : Stack)
    (hS : S.all (Item.ok Kit.n) = true) :
    ∃ t, Eval (N apT p ⬝ encStack S) t ∧ Decodes t (Csem ap p S) :=
  composition apT ap hap p hp S (encStack_dec S hS)

-- ---------------------------------------------------------------------------
-- An eliminator for programs that run no quotation
-- ---------------------------------------------------------------------------

/-- The eliminator that fails every quotation.  A program without `dip`,
    `i` or `ifz` never calls it, so `composition` holds for such a program
    unconditionally. -/
def apErr : Term := K ⬝ (K ⬝ Scott.RErr)

theorem apErr_sound : ApSound apErr (fun _ _ => .err) :=
  fun _ _ fr fu _ _ => contract_err (iter_sound (k := 2) rfl : Steps (apErr ⬝ fr ⬝ fu) Scott.RErr)
