import Ski.Words
import Ski.Abs
open Term

/-!
# The kernel's source, compiled

G3 of `PLAN.md` §3: the compiled kernel as a function of the quotation
table, so that the laws can be proved once (G4) instead of checked per
table.

## How `skijack` compiles

Read from `skijack/expand.py` (`_lower_case`, `_Codegen`,
`expand_program`) and `aviary_kernel/abstraction.py`:

1. A case `e |> { C x… body; … }` lowers to `e` applied to one
   continuation per constructor, in declaration order, each the λ over
   that constructor's fields (`desugar`).
2. A λ chain `λ p… . body` is lifted to its own combinator (`_Codegen.lift`):
   its formals are the enclosing binders free in it, in scope order, then
   `p…`; the use site is that combinator applied to those binders.
3. Every combinator is bracket-abstracted over its formals, innermost last
   (`absN`), after its globals are expanded to closed terms.
4. A recursive equation `f xs = body` becomes `Y` applied to the
   abstraction over a fresh self-parameter followed by `xs`.

`Src` is the source after step 1; `comp` does steps 2 and 3, `compDef` a
definition, `compRec` a recursive one.  Globals are closed terms
(`Src.glob`).

## Fidelity

Every equation of the kernel that does not depend on the table is
compiled here from its source, transcribed from
`skilark.joy.COMPILED_KERNEL` after `skijack`'s desugaring, and checked by
`rfl` against the term `skijack` emitted (`wPop_compiles` through
`add_compiles`).  The table-dependent terms are functions of a `Table`
(`Table.kit`), checked against each generated table in `Ski/Table.lean`
(`table_*` theorems); `Ski/Laws.lean` proves the laws of `Table.kit` for
every valid table.  A binder name reused by sibling λs in the source is
given distinct numbers here; no binder shadows an enclosing one, so the
captures are the same.
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

-- ---------------------------------------------------------------------------
-- The kernel's equations, after desugaring
-- ---------------------------------------------------------------------------

namespace KernelSrc

open Src

abbrev g := Src.glob
abbrev v := Src.var

-- s0 a1 t2 : (s RErr) (λa t. RVal t)
def wPop : Src := v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2 (g Scott.RVal ⬝ₛ v 2))

-- s0 a1 t2 : (s RErr) (λa t. RVal (Push a (Push a t)))
def wDup : Src :=
  v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2
    (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ v 1 ⬝ₛ (g Scott.Push ⬝ₛ v 1 ⬝ₛ v 2))))

-- s0 a1 t2 b3 u4 : (s RErr) (λa t. (t RErr) (λb u. RVal (Push b (Push a u))))
def wSwap : Src :=
  v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2
    (v 2 ⬝ₛ g Scott.RErr ⬝ₛ lam 3 (lam 4
      (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ v 3 ⬝ₛ (g Scott.Push ⬝ₛ v 1 ⬝ₛ v 4))))))

-- s0 a1 t2 n3 r4 b5 u6 :
-- (s RErr) (λa t. (a (λn. RErr)) (λr. (t RErr) (λb u. RVal (Push (Quot (QCons b r)) u))))
def wQcons (qcons : Term) : Src :=
  v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2
    (v 1 ⬝ₛ lam 3 (g Scott.RErr) ⬝ₛ lam 4
      (v 2 ⬝ₛ g Scott.RErr ⬝ₛ lam 5 (lam 6
        (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ (g Scott.Quot ⬝ₛ (g qcons ⬝ₛ v 5 ⬝ₛ v 4)) ⬝ₛ v 6))))))

-- s0 a1 t2 n3 r4 b5 u6 m7 l8 :
-- (s RErr) (λa t. (a (λn. RErr)) (λr. (t RErr) (λb u. (b (λm. RErr))
--   (λl. RVal (Push (Quot (QCons (Quot l) (QThen r))) u)))))
def wCat (qcons qthen : Term) : Src :=
  v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2
    (v 1 ⬝ₛ lam 3 (g Scott.RErr) ⬝ₛ lam 4
      (v 2 ⬝ₛ g Scott.RErr ⬝ₛ lam 5 (lam 6
        (v 5 ⬝ₛ lam 7 (g Scott.RErr) ⬝ₛ lam 8
          (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ
            (g Scott.Quot ⬝ₛ (g qcons ⬝ₛ (g Scott.Quot ⬝ₛ v 8) ⬝ₛ (g qthen ⬝ₛ v 4))) ⬝ₛ v 6)))))))

-- s0 a1 t2 : (s RErr) (λa t. RVal (Push (Quot (QUnit a)) t))
def wUnit (qunit : Term) : Src :=
  v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2
    (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ (g Scott.Quot ⬝ₛ (g qunit ⬝ₛ v 1)) ⬝ₛ v 2)))

-- ap0 s1 a2 t3 n4 r5 b6 u7 v8 :
-- (s RErr) (λa t. (a (λn. RErr)) (λr. (t RErr) (λb u. ap r u (λv. RVal (Push b v)) RErr RTime)))
def wDip : Src :=
  v 1 ⬝ₛ g Scott.RErr ⬝ₛ lam 2 (lam 3
    (v 2 ⬝ₛ lam 4 (g Scott.RErr) ⬝ₛ lam 5
      (v 3 ⬝ₛ g Scott.RErr ⬝ₛ lam 6 (lam 7
        (v 0 ⬝ₛ v 5 ⬝ₛ v 7 ⬝ₛ lam 8 (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ v 6 ⬝ₛ v 8))
          ⬝ₛ g Scott.RErr ⬝ₛ g Scott.RTime)))))

-- ap0 s1 a2 t3 n4 r5 : (s RErr) (λa t. (a (λn. RErr)) (λr. ap r t))
def wDo : Src :=
  v 1 ⬝ₛ g Scott.RErr ⬝ₛ lam 2 (lam 3
    (v 2 ⬝ₛ lam 4 (g Scott.RErr) ⬝ₛ lam 5 (v 0 ⬝ₛ v 5 ⬝ₛ v 3)))

-- ap0 s1 a2 t3 n4 sc5 b6 u7 n8 z9 c10 v11 n12 m13 r14 :
-- (s RErr) (λa t. (a (λn. RErr)) (λsc. (t RErr) (λb u. (b (λn. RErr)) (λz. (u RErr)
--   (λc v. (c (λn. (n (ap z v)) (λm. ap sc (Push (Num m) v)))) (λr. RErr))))))
def wIfz : Src :=
  v 1 ⬝ₛ g Scott.RErr ⬝ₛ lam 2 (lam 3
    (v 2 ⬝ₛ lam 4 (g Scott.RErr) ⬝ₛ lam 5
      (v 3 ⬝ₛ g Scott.RErr ⬝ₛ lam 6 (lam 7
        (v 6 ⬝ₛ lam 8 (g Scott.RErr) ⬝ₛ lam 9
          (v 7 ⬝ₛ g Scott.RErr ⬝ₛ lam 10 (lam 11
            (v 10 ⬝ₛ lam 12
                (v 12 ⬝ₛ (v 0 ⬝ₛ v 9 ⬝ₛ v 11) ⬝ₛ lam 13
                  (v 0 ⬝ₛ v 5 ⬝ₛ (g Scott.Push ⬝ₛ (g Scott.Num ⬝ₛ v 13) ⬝ₛ v 11)))
              ⬝ₛ lam 14 (g Scott.RErr)))))))))

-- n0 s1 : RVal (Push (Num n) s)
def wLit : Src := g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ (g Scott.Num ⬝ₛ v 0) ⬝ₛ v 1)

-- r0 s1 : RVal (Push (Quot r) s)
def wQuote : Src := g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ (g Scott.Quot ⬝ₛ v 0) ⬝ₛ v 1)

-- s0 a1 t2 b3 u4 m5 n6 r7 r8 :
-- (s RErr) (λa t. (t RErr) (λb u. (a (λm. (b (λn. RVal (Push (Num (add m n)) u))) (λr. RErr)))
--   (λr. RErr)))
def wAdd : Src :=
  v 0 ⬝ₛ g Scott.RErr ⬝ₛ lam 1 (lam 2
    (v 2 ⬝ₛ g Scott.RErr ⬝ₛ lam 3 (lam 4
      (v 1 ⬝ₛ lam 5
          (v 3 ⬝ₛ lam 6
              (g Scott.RVal ⬝ₛ
                (g Scott.Push ⬝ₛ (g Scott.Num ⬝ₛ (g Scott.add ⬝ₛ v 5 ⬝ₛ v 6)) ⬝ₛ v 4))
            ⬝ₛ lam 7 (g Scott.RErr))
        ⬝ₛ lam 8 (g Scott.RErr)))))

-- self0 m1 n2 k3 : (n m) (λk. Suc (self m k))
def add : Src := v 2 ⬝ₛ v 1 ⬝ₛ lam 3 (g Scott.Suc ⬝ₛ (v 0 ⬝ₛ v 1 ⬝ₛ v 3))

-- f0 g1 s2 t3 : (f s) (λt. g t) RErr RTime
def seq : Src := v 0 ⬝ₛ v 2 ⬝ₛ lam 3 (v 1 ⬝ₛ v 3) ⬝ₛ g Scott.RErr ⬝ₛ g Scott.RTime

-- s0 : RVal s
def idW : Src := g Scott.RVal ⬝ₛ v 0

-- The table-independent arms of `applyU`'s case, with self0 q1 s2 x3 r4 x5 b6:
-- λx r. self r (Push x s)
def armCons : Src := lam 3 (lam 4 (v 0 ⬝ₛ v 4 ⬝ₛ (g Scott.Push ⬝ₛ v 3 ⬝ₛ v 2)))

-- λx. RVal (Push x s)
def armUnit : Src := lam 5 (g Scott.RVal ⬝ₛ (g Scott.Push ⬝ₛ v 5 ⬝ₛ v 2))

-- λb. seq (wDo self) (self b) s
def armThen : Src := lam 6 (g Scott.seq ⬝ₛ (g Scott.wDo ⬝ₛ v 0) ⬝ₛ (v 0 ⬝ₛ v 6) ⬝ₛ v 2)

end KernelSrc

-- ---------------------------------------------------------------------------
-- The table-independent equations compile to skijack's terms
-- ---------------------------------------------------------------------------

theorem wPop_compiles : toTerm (compDef [0] KernelSrc.wPop) = Scott.wPop := rfl
theorem wDup_compiles : toTerm (compDef [0] KernelSrc.wDup) = Scott.wDup := rfl
theorem wSwap_compiles : toTerm (compDef [0] KernelSrc.wSwap) = Scott.wSwap := rfl
theorem wDip_compiles : toTerm (compDef [0, 1] KernelSrc.wDip) = Scott.wDip := rfl
theorem wDo_compiles : toTerm (compDef [0, 1] KernelSrc.wDo) = Scott.wDo := rfl
theorem wIfz_compiles : toTerm (compDef [0, 1] KernelSrc.wIfz) = Scott.wIfz := rfl
theorem wLit_compiles : toTerm (compDef [0, 1] KernelSrc.wLit) = Scott.wLit := rfl
theorem wQuote_compiles : toTerm (compDef [0, 1] KernelSrc.wQuote) = Scott.wQuote := rfl
theorem wAdd_compiles : toTerm (compDef [0] KernelSrc.wAdd) = Scott.wAdd := rfl
theorem add_compiles : toTerm (compRec 0 [1, 2] KernelSrc.add) = Scott.add := rfl
theorem seq_compiles : toTerm (compDef [0, 1, 2] KernelSrc.seq) = Scott.seq := rfl
theorem idW_compiles : toTerm (compDef [0] KernelSrc.idW) = Scott.idW := rfl
theorem wQcons0_compiles : toTerm (compDef [0] (KernelSrc.wQcons Scott.QCons)) = Scott.wQcons := rfl
theorem wCat0_compiles :
    toTerm (compDef [0] (KernelSrc.wCat Scott.QCons Scott.QThen)) = Scott.wCat := rfl
theorem wUnit0_compiles : toTerm (compDef [0] (KernelSrc.wUnit Scott.QUnit)) = Scott.wUnit := rfl

-- ---------------------------------------------------------------------------
-- A quotation table, compiled
-- ---------------------------------------------------------------------------

/-- The constructor at position `j` of a sum with `m` constructors, with `a`
    fields: `λ fields conts. k_j fields`, compiled. -/
def ctorO (a j m : Nat) : OTerm :=
  absN (List.range (a + m)) (appL (.var (a + j)) ((List.range a).map .var))

/-- A table of static quotations: how many, and each one's code. -/
structure Table where
  n : Nat
  body : Nat → List Word

namespace Table

variable (tb : Table)

def Qs (k : Nat) : Term := toTerm (ctorO 0 k (tb.n + 3))
def QCons : Term := toTerm (ctorO 2 tb.n (tb.n + 3))
def QUnit : Term := toTerm (ctorO 1 (tb.n + 1) (tb.n + 3))
def QThen : Term := toTerm (ctorO 1 (tb.n + 2) (tb.n + 3))

def wQcons : Term := toTerm (compDef [0] (KernelSrc.wQcons tb.QCons))
def wCat : Term := toTerm (compDef [0] (KernelSrc.wCat tb.QCons tb.QThen))
def wUnit : Term := toTerm (compDef [0] (KernelSrc.wUnit tb.QUnit))

mutual
  /-- An item, encoded with this table's constructors. -/
  def encItem : Item → Term
    | .num n => Scott.Num ⬝ encNat n
    | .quot q => Scott.Quot ⬝ encQuot q
  /-- A quotation, encoded with this table's constructors. -/
  def encQuot : Quotation → Term
    | .stat k => tb.Qs k
    | .cons x r => tb.QCons ⬝ encItem x ⬝ encQuot r
    | .unit x => tb.QUnit ⬝ encItem x
    | .then r => tb.QThen ⬝ encQuot r
end

/-- A word in a static quotation's body, the eliminator `ap` being `v 0`:
    `wLit n`, `wQuote q`, `wDo ap` and the rest, as `skilark.joy` writes them. -/
def wordSrc : Word → Src
  | .dup => .glob Scott.wDup
  | .swap => .glob Scott.wSwap
  | .pop => .glob Scott.wPop
  | .cons => .glob tb.wQcons
  | .cat => .glob tb.wCat
  | .unit => .glob tb.wUnit
  | .dip => .glob Scott.wDip ⬝ₛ .var 0
  | .i => .glob Scott.wDo ⬝ₛ .var 0
  | .ifz => .glob Scott.wIfz ⬝ₛ .var 0
  | .lit n => .glob (Scott.wLit ⬝ encNat n)
  | .quote q => .glob (Scott.wQuote ⬝ tb.encQuot q)
  | .add => .glob Scott.wAdd

/-- `b ap = seq w1 (seq w2 … wm)`, or `idW` for the empty quotation. -/
def bodySrc : List Word → Src
  | [] => .glob Scott.idW
  | [w] => tb.wordSrc w
  | w :: w' :: ws => .glob Scott.seq ⬝ₛ tb.wordSrc w ⬝ₛ bodySrc (w' :: ws)

/-- The `k`-th static quotation's compiled term, `b_k`. -/
def bodyT (k : Nat) : Term := toTerm (compDef [0] (tb.bodySrc (tb.body k)))

/-- `applyU q s = q |> { Q_k (b_k applyU s)…; QCons x r (applyU r (Push x s));
    QUnit x (RVal (Push x s)); QThen b (seq (wDo applyU) (applyU b) s) }`,
    with self0 q1 s2 x3 r4 x5 b6. -/
def applySrc : Src :=
  (List.range tb.n).foldl (fun acc k => acc ⬝ₛ (.glob (tb.bodyT k) ⬝ₛ .var 0 ⬝ₛ .var 2)) (.var 1)
    ⬝ₛ KernelSrc.armCons ⬝ₛ KernelSrc.armUnit ⬝ₛ KernelSrc.armThen

def applyU : Term := toTerm (compRec 0 [1, 2] tb.applySrc)

/-- **The table's kit, compiled from source.** -/
def kit : Kit where
  n := tb.n
  Qs := tb.Qs
  QCons := tb.QCons
  QUnit := tb.QUnit
  QThen := tb.QThen
  wQcons := tb.wQcons
  wCat := tb.wCat
  wUnit := tb.wUnit
  applyU := tb.applyU
  body := tb.body
  bodyT := tb.bodyT

end Table
