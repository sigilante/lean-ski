import Ski.Abs
open Term

/-!
# The compilation scheme

How `skijack` compiles, read from `skijack/expand.py` (`_lower_case`,
`_Codegen`, `expand_program`) and `aviary_kernel/abstraction.py`:

1. A case `e |> { C x… body; … }` lowers to `e` applied to one
   continuation per constructor, in declaration order, each the λ over
   that constructor's fields (`desugar`; `Ski/Front.lean`).
2. A λ chain `λ p… . body` is lifted to its own combinator (`_Codegen.lift`):
   its formals are the enclosing binders free in it, in scope order, then
   `p…`; the use site is that combinator applied to those binders.
3. Every combinator is bracket-abstracted over its formals, innermost last
   (`absN`), after its globals are expanded to closed terms.
4. A recursive equation `f xs = body` becomes `Y` applied to the
   abstraction over a fresh self-parameter followed by `xs`.

`Src` is the source after step 1; `comp` does steps 2 and 3, `compDef` a
definition, `compRec` a recursive one.  Globals are closed terms
(`Src.glob`).  `ctorO` is a Scott constructor, `λ fields conts. k_j
fields`, compiled.
-/

inductive Src
  | glob (t : Term)
  | var (x : Nat)
  | app (f a : Src)
  | lam (x : Nat) (b : Src)

infixl:70 " ⬝ₛ " => Src.app

/-- The variable `x` occurs free. -/
def Src.occurs (x : Nat) : Src → Bool
  | .glob _ => false
  | .var y => y == x
  | .app f a => f.occurs x || a.occurs x
  | .lam y b => y != x && b.occurs x

/-- A lifted combinator: `absN` over the captured binders then the
    parameters, applied to the captured binders. -/
def wrapLift (caps ps : List Nat) (body : OTerm) : OTerm :=
  appL (absN (caps ++ ps) body) (caps.map .var)

mutual
  /-- Compile a source term in a scope of binders. -/
  def comp (scope : List Nat) : Src → OTerm
    | .glob t => t.toO
    | .var x => .var x
    | .app f a => comp scope f ⬝ₒ comp scope a
    | .lam x b => compLam (scope.filter fun s => (Src.lam x b).occurs s) [x] b
  /-- Lift a λ chain: collect its parameters, then compile its body in the
      scope of the captured binders and the parameters. -/
  def compLam (caps ps : List Nat) : Src → OTerm
    | .lam y b => compLam caps (ps ++ [y]) b
    | .glob t => wrapLift caps ps t.toO
    | .var x => wrapLift caps ps (.var x)
    | .app f a => wrapLift caps ps (comp (caps ++ ps) f ⬝ₒ comp (caps ++ ps) a)
end

/-- A definition `f xs = body`. -/
def compDef (xs : List Nat) (body : Src) : OTerm := absN xs (comp xs body)

/-- The fixpoint combinator, as `skijack` overrides it. -/
def Ycomb : Term := S ⬝ (K ⬝ (S ⬝ I ⬝ I)) ⬝ (S ⬝ (S ⬝ (K ⬝ S) ⬝ K) ⬝ (K ⬝ (S ⬝ I ⬝ I)))

/-- A recursive definition `f xs = body`, with `self` for `f` in `body`. -/
def compRec (self : Nat) (xs : List Nat) (body : Src) : OTerm :=
  Ycomb.toO ⬝ₒ absN (self :: xs) (comp (self :: xs) body)

/-- A closed compiled term as a `Term`. -/
def toTerm (t : OTerm) : Term := t.close fun _ => K

/-- The constructor at position `j` of a sum with `m` constructors, with `a`
    fields: `λ fields conts. k_j fields`, compiled. -/
def ctorO (a j m : Nat) : OTerm :=
  absN (List.range (a + m)) (appL (.var (a + j)) ((List.range a).map .var))

-- ---------------------------------------------------------------------------
-- The same scheme by `absNF`, for kernel evaluation
-- ---------------------------------------------------------------------------

/-- `wrapLift` by `absNF`. -/
def wrapLiftF (caps ps : List Nat) (body : OTerm) : OTerm :=
  appL (absNF (caps ++ ps) body) (caps.map .var)

mutual
  /-- `comp` by `absNF`. -/
  def compF (scope : List Nat) : Src → OTerm
    | .glob t => t.toO
    | .var x => .var x
    | .app f a => compF scope f ⬝ₒ compF scope a
    | .lam x b => compLamF (scope.filter fun s => (Src.lam x b).occurs s) [x] b
  /-- `compLam` by `absNF`. -/
  def compLamF (caps ps : List Nat) : Src → OTerm
    | .lam y b => compLamF caps (ps ++ [y]) b
    | .glob t => wrapLiftF caps ps t.toO
    | .var x => wrapLiftF caps ps (.var x)
    | .app f a => wrapLiftF caps ps (compF (caps ++ ps) f ⬝ₒ compF (caps ++ ps) a)
end

theorem wrapLiftF_eq (caps ps : List Nat) (body : OTerm) :
    wrapLiftF caps ps body = wrapLift caps ps body := by
  unfold wrapLiftF wrapLift
  rw [absNF_eq]

mutual
  theorem compF_eq (scope : List Nat) : ∀ s, compF scope s = comp scope s
    | .glob _ => by rw [compF, comp]
    | .var _ => by rw [compF, comp]
    | .app f a => by rw [compF, comp, compF_eq scope f, compF_eq scope a]
    | .lam x b => by rw [compF, comp, compLamF_eq]
  theorem compLamF_eq (caps ps : List Nat) : ∀ s, compLamF caps ps s = compLam caps ps s
    | .lam y b => by rw [compLamF, compLam, compLamF_eq]
    | .glob _ => by rw [compLamF, compLam, wrapLiftF_eq]
    | .var _ => by rw [compLamF, compLam, wrapLiftF_eq]
    | .app f a => by
      rw [compLamF, compLam, wrapLiftF_eq, compF_eq (caps ++ ps) f, compF_eq (caps ++ ps) a]
end

/-- `compDef` by `absNF`. -/
def compDefF (xs : List Nat) (body : Src) : OTerm := absNF xs (compF xs body)

theorem compDefF_eq (xs : List Nat) (body : Src) : compDefF xs body = compDef xs body := by
  unfold compDefF compDef
  rw [absNF_eq, compF_eq]

/-- `compRec` by `absNF`. -/
def compRecF (self : Nat) (xs : List Nat) (body : Src) : OTerm :=
  Ycomb.toO ⬝ₒ absNF (self :: xs) (compF (self :: xs) body)

theorem compRecF_eq (self : Nat) (xs : List Nat) (body : Src) :
    compRecF self xs body = compRec self xs body := by
  unfold compRecF compRec
  rw [absNF_eq, compF_eq]

/-- `ctorO` by `absNF`. -/
def ctorOF (a j m : Nat) : OTerm :=
  absNF (List.range (a + m)) (appL (.var (a + j)) ((List.range a).map .var))

theorem ctorOF_eq (a j m : Nat) : ctorOF a j m = ctorO a j m := by
  unfold ctorOF ctorO
  rw [absNF_eq]
