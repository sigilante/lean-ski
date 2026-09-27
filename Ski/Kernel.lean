import Ski.Words
import Ski.Front
import Ski.Source
open Term

/-!
# The kernel's source, compiled

G3 of `PLAN.md` §3: the compiled kernel as a function of the quotation
table, so that the laws can be proved once (G4) instead of checked per
table.

## The source

The kernel's equations are the front end's (`Ski/Front.lean`) reading of
`kernelText` (`Ski/Source.lean`): the text `skijack` compiled, character
for character.  `KernelSrc.wPop` and the rest are that reading, lowered,
with the globals resolved: constructors and helpers to the terms of
`Ski/Scott.lean`, and the table's `QCons`, `QUnit` and `QThen` to
parameters, so that `Table.kit` can take them from any table.

## Fidelity

Three checks tie this to `skijack`, all by the kernel (`decide +kernel`):

- `kernel_agrees`: the front end compiles the whole of `kernelText`, and
  every term `Ski/Scott.lean` holds is what it gives, word for word;
- `wPop_compiles` through `wUnit0_compiles`: each `KernelSrc` equation,
  compiled with the formals `kernel_formals` records, is `skijack`'s term;
- the per-table checks of `Ski/Table.lean`.

`kernel_wQcons` and its siblings give the lowered equations the proofs of
`Ski/Laws.lean` read, as literals the kernel checks against the front
end's output; `KernelSrc.wQcons_def` and its siblings rewrite by them.
-/

-- ---------------------------------------------------------------------------
-- The kernel's equations, read from their source
-- ---------------------------------------------------------------------------

open Front

/-- An equation of `kernelText`, lowered. -/
def kernelEqn (n : Nm) : FEqn := (fileEqn kernelText n).getD ⟨[], none, .glob []⟩

/-- The globals the kernel's words name, as `skijack` compiled them. -/
def scottEnv : List (Nm × Term) :=
  [(nm! "Zero", Scott.Zero), (nm! "Suc", Scott.Suc), (nm! "Num", Scott.Num),
   (nm! "Quot", Scott.Quot), (nm! "Empty", Scott.Empty), (nm! "Push", Scott.Push),
   (nm! "RVal", Scott.RVal), (nm! "RErr", Scott.RErr), (nm! "RTime", Scott.RTime),
   (nm! "add", Scott.add), (nm! "seq", Scott.seq), (nm! "idW", Scott.idW),
   (nm! "wDo", Scott.wDo)]

/-- The globals, with a table's `quot` constructors. -/
def kernelEnv (qcons qunit qthen : Term) (n : Nm) : Term :=
  if n = nm! "QCons" then qcons
  else if n = nm! "QUnit" then qunit
  else if n = nm! "QThen" then qthen
  else (scottEnv.lookup n).getD K

namespace KernelSrc

/-- An equation's body, lowered and resolved. -/
def of (n : Nm) (qcons qunit qthen : Term) : Src :=
  (kernelEqn n).body.resolve (kernelEnv qcons qunit qthen)

def wPop : Src := of (nm! "wPop") Scott.QCons Scott.QUnit Scott.QThen
def wDup : Src := of (nm! "wDup") Scott.QCons Scott.QUnit Scott.QThen
def wSwap : Src := of (nm! "wSwap") Scott.QCons Scott.QUnit Scott.QThen
def wQcons (qcons : Term) : Src := of (nm! "wQcons") qcons Scott.QUnit Scott.QThen
def wCat (qcons qthen : Term) : Src := of (nm! "wCat") qcons Scott.QUnit qthen
def wUnit (qunit : Term) : Src := of (nm! "wUnit") Scott.QCons qunit Scott.QThen
def wDip : Src := of (nm! "wDip") Scott.QCons Scott.QUnit Scott.QThen
def wDo : Src := of (nm! "wDo") Scott.QCons Scott.QUnit Scott.QThen
def wIfz : Src := of (nm! "wIfz") Scott.QCons Scott.QUnit Scott.QThen
def wLit : Src := of (nm! "wLit") Scott.QCons Scott.QUnit Scott.QThen
def wQuote : Src := of (nm! "wQuote") Scott.QCons Scott.QUnit Scott.QThen
def wAdd : Src := of (nm! "wAdd") Scott.QCons Scott.QUnit Scott.QThen
def add : Src := of (nm! "add") Scott.QCons Scott.QUnit Scott.QThen
def seq : Src := of (nm! "seq") Scott.QCons Scott.QUnit Scott.QThen
def idW : Src := of (nm! "idW") Scott.QCons Scott.QUnit Scott.QThen

/-- The three branches of `applyU`'s case that do not depend on the table:
    `applyU q s = q |> { QCons x r …; QUnit x …; QThen b … }` lowers to
    `q ⬝ armCons ⬝ armUnit ⬝ armThen`. -/
def applyArms : CSrc → List CSrc
  | .app (.app (.app _ a) b) c => [a, b, c]
  | _ => []

def arm (i : Nat) : Src :=
  ((applyArms (kernelEqn (nm! "applyU")).body).getD i (.glob [])).resolve
    (kernelEnv Scott.QCons Scott.QUnit Scott.QThen)

def armCons : Src := arm 0
def armUnit : Src := arm 1
def armThen : Src := arm 2

end KernelSrc

-- ---------------------------------------------------------------------------
-- The front end agrees with `skijack` on the whole kernel
-- ---------------------------------------------------------------------------

/-- **The front end reads and compiles `kernelText` to `skijack`'s terms**:
    every constructor, word and helper of `Ski/Scott.lean`. -/
theorem kernel_agrees :
    [nm! "Zero", nm! "Suc", nm! "Num", nm! "Quot", nm! "Empty", nm! "Push", nm! "QCons",
     nm! "QUnit", nm! "QThen", nm! "RVal", nm! "RErr", nm! "RTime",
     nm! "wDup", nm! "wSwap", nm! "wPop", nm! "wQcons", nm! "wCat", nm! "wUnit", nm! "wDip",
     nm! "wDo", nm! "wIfz", nm! "wLit", nm! "wQuote", nm! "wAdd",
     nm! "add", nm! "seq", nm! "idW", nm! "applyU"].map (termOf (compileFile kernelText)) =
    [some Scott.Zero, some Scott.Suc, some Scott.Num, some Scott.Quot, some Scott.Empty,
     some Scott.Push, some Scott.QCons, some Scott.QUnit, some Scott.QThen, some Scott.RVal,
     some Scott.RErr, some Scott.RTime,
     some Scott.wDup, some Scott.wSwap, some Scott.wPop, some Scott.wQcons, some Scott.wCat,
     some Scott.wUnit, some Scott.wDip, some Scott.wDo, some Scott.wIfz, some Scott.wLit,
     some Scott.wQuote, some Scott.wAdd,
     some Scott.add, some Scott.seq, some Scott.idW, some Scott.applyU] := by
  decide +kernel

/-- The formals of each equation: parameters, then whether it is recursive. -/
theorem kernel_formals :
    [nm! "wPop", nm! "wDup", nm! "wSwap", nm! "wQcons", nm! "wCat", nm! "wUnit", nm! "wDip",
     nm! "wDo", nm! "wIfz", nm! "wLit", nm! "wQuote", nm! "wAdd", nm! "add", nm! "seq",
     nm! "idW", nm! "applyU"].map (fun n => ((kernelEqn n).params, (kernelEqn n).self)) =
    [([0], none), ([0], none), ([0], none), ([0], none), ([0], none), ([0], none),
     ([0, 1], none), ([0, 1], none), ([0, 1], none), ([0, 1], none), ([0, 1], none),
     ([0], none), ([1, 2], some 0), ([0, 1, 2], none), ([0], none), ([1, 2], some 0)] := by
  decide +kernel

-- ---------------------------------------------------------------------------
-- Each lowered equation compiles to `skijack`'s term
-- ---------------------------------------------------------------------------

theorem wPop_compiles : toTerm (compDef [0] KernelSrc.wPop) = Scott.wPop := by decide +kernel
theorem wDup_compiles : toTerm (compDef [0] KernelSrc.wDup) = Scott.wDup := by decide +kernel
theorem wSwap_compiles : toTerm (compDef [0] KernelSrc.wSwap) = Scott.wSwap := by decide +kernel
theorem wDip_compiles : toTerm (compDef [0, 1] KernelSrc.wDip) = Scott.wDip := by decide +kernel
theorem wDo_compiles : toTerm (compDef [0, 1] KernelSrc.wDo) = Scott.wDo := by decide +kernel
theorem wIfz_compiles : toTerm (compDef [0, 1] KernelSrc.wIfz) = Scott.wIfz := by decide +kernel
theorem wLit_compiles : toTerm (compDef [0, 1] KernelSrc.wLit) = Scott.wLit := by decide +kernel
theorem wQuote_compiles : toTerm (compDef [0, 1] KernelSrc.wQuote) = Scott.wQuote := by
  decide +kernel
theorem wAdd_compiles : toTerm (compDef [0] KernelSrc.wAdd) = Scott.wAdd := by decide +kernel
theorem add_compiles : toTerm (compRec 0 [1, 2] KernelSrc.add) = Scott.add := by decide +kernel
theorem seq_compiles : toTerm (compDef [0, 1, 2] KernelSrc.seq) = Scott.seq := by decide +kernel
theorem idW_compiles : toTerm (compDef [0] KernelSrc.idW) = Scott.idW := by decide +kernel
theorem wQcons0_compiles : toTerm (compDef [0] (KernelSrc.wQcons Scott.QCons)) = Scott.wQcons := by
  decide +kernel
theorem wCat0_compiles :
    toTerm (compDef [0] (KernelSrc.wCat Scott.QCons Scott.QThen)) = Scott.wCat := by
  decide +kernel
theorem wUnit0_compiles : toTerm (compDef [0] (KernelSrc.wUnit Scott.QUnit)) = Scott.wUnit := by
  decide +kernel

-- ---------------------------------------------------------------------------
-- The lowered equations the proofs read, checked against the front end
-- ---------------------------------------------------------------------------

section
local macro:max "g! " s:str : term => `(CSrc.glob (nm! $s))
local macro:max "v! " x:num : term => `(CSrc.var $x)
local infixl:70 " ⬝c " => CSrc.app

/-- `wUnit s = s |> { Empty RErr; Push a t (RVal (Push (Quot (QUnit a)) t)) }`,
    lowered: `s0 a1 t2`. -/
theorem kernel_wUnit : kernelEqn (nm! "wUnit") = ⟨[0], none,
    v! 0 ⬝c g! "RErr" ⬝c .lam 1 (.lam 2
      (g! "RVal" ⬝c (g! "Push" ⬝c (g! "Quot" ⬝c (g! "QUnit" ⬝c v! 1)) ⬝c v! 2)))⟩ := by
  decide +kernel

/-- `wQcons`, lowered: `s0 a1 t2 n3 r4 b5 u6`. -/
theorem kernel_wQcons : kernelEqn (nm! "wQcons") = ⟨[0], none,
    v! 0 ⬝c g! "RErr" ⬝c .lam 1 (.lam 2
      (v! 1 ⬝c .lam 3 (g! "RErr") ⬝c .lam 4
        (v! 2 ⬝c g! "RErr" ⬝c .lam 5 (.lam 6
          (g! "RVal" ⬝c (g! "Push" ⬝c (g! "Quot" ⬝c (g! "QCons" ⬝c v! 5 ⬝c v! 4)) ⬝c v! 6))))))⟩ := by
  decide +kernel

/-- `wCat`, lowered: `s0 a1 t2 n3 r4 b5 u6 m7 l8`. -/
theorem kernel_wCat : kernelEqn (nm! "wCat") = ⟨[0], none,
    v! 0 ⬝c g! "RErr" ⬝c .lam 1 (.lam 2
      (v! 1 ⬝c .lam 3 (g! "RErr") ⬝c .lam 4
        (v! 2 ⬝c g! "RErr" ⬝c .lam 5 (.lam 6
          (v! 5 ⬝c .lam 7 (g! "RErr") ⬝c .lam 8
            (g! "RVal" ⬝c (g! "Push" ⬝c
              (g! "Quot" ⬝c (g! "QCons" ⬝c (g! "Quot" ⬝c v! 8) ⬝c (g! "QThen" ⬝c v! 4)))
              ⬝c v! 6)))))))⟩ := by
  decide +kernel

/-- `applyU`, lowered for a table with no static quotations:
    `self0 q1 s2 x3 r4 x5 b6`. -/
theorem kernel_applyU : kernelEqn (nm! "applyU") = ⟨[1, 2], some 0,
    v! 1
      ⬝c .lam 3 (.lam 4 (v! 0 ⬝c v! 4 ⬝c (g! "Push" ⬝c v! 3 ⬝c v! 2)))
      ⬝c .lam 5 (g! "RVal" ⬝c (g! "Push" ⬝c v! 5 ⬝c v! 2))
      ⬝c .lam 6 (g! "seq" ⬝c (g! "wDo" ⬝c v! 0) ⬝c (v! 0 ⬝c v! 6) ⬝c v! 2)⟩ := by
  decide +kernel

theorem KernelSrc.wUnit_def (qunit : Term) : KernelSrc.wUnit qunit =
    (v! 0 ⬝c g! "RErr" ⬝c .lam 1 (.lam 2
      (g! "RVal" ⬝c (g! "Push" ⬝c (g! "Quot" ⬝c (g! "QUnit" ⬝c v! 1)) ⬝c v! 2)))).resolve
      (kernelEnv Scott.QCons qunit Scott.QThen) := by
  unfold KernelSrc.wUnit KernelSrc.of
  rw [kernel_wUnit]

theorem KernelSrc.wQcons_def (qcons : Term) : KernelSrc.wQcons qcons =
    (v! 0 ⬝c g! "RErr" ⬝c .lam 1 (.lam 2
      (v! 1 ⬝c .lam 3 (g! "RErr") ⬝c .lam 4
        (v! 2 ⬝c g! "RErr" ⬝c .lam 5 (.lam 6
          (g! "RVal" ⬝c (g! "Push" ⬝c (g! "Quot" ⬝c (g! "QCons" ⬝c v! 5 ⬝c v! 4)) ⬝c v! 6))))))
      ).resolve (kernelEnv qcons Scott.QUnit Scott.QThen) := by
  unfold KernelSrc.wQcons KernelSrc.of
  rw [kernel_wQcons]

theorem KernelSrc.wCat_def (qcons qthen : Term) : KernelSrc.wCat qcons qthen =
    (v! 0 ⬝c g! "RErr" ⬝c .lam 1 (.lam 2
      (v! 1 ⬝c .lam 3 (g! "RErr") ⬝c .lam 4
        (v! 2 ⬝c g! "RErr" ⬝c .lam 5 (.lam 6
          (v! 5 ⬝c .lam 7 (g! "RErr") ⬝c .lam 8
            (g! "RVal" ⬝c (g! "Push" ⬝c
              (g! "Quot" ⬝c (g! "QCons" ⬝c (g! "Quot" ⬝c v! 8) ⬝c (g! "QThen" ⬝c v! 4)))
              ⬝c v! 6)))))))).resolve (kernelEnv qcons Scott.QUnit qthen) := by
  unfold KernelSrc.wCat KernelSrc.of
  rw [kernel_wCat]

theorem KernelSrc.armCons_def : KernelSrc.armCons =
    (CSrc.lam 3 (.lam 4 (v! 0 ⬝c v! 4 ⬝c (g! "Push" ⬝c v! 3 ⬝c v! 2)))).resolve
      (kernelEnv Scott.QCons Scott.QUnit Scott.QThen) := by
  unfold KernelSrc.armCons KernelSrc.arm
  rw [kernel_applyU]
  rfl

theorem KernelSrc.armUnit_def : KernelSrc.armUnit =
    (CSrc.lam 5 (g! "RVal" ⬝c (g! "Push" ⬝c v! 5 ⬝c v! 2))).resolve
      (kernelEnv Scott.QCons Scott.QUnit Scott.QThen) := by
  unfold KernelSrc.armUnit KernelSrc.arm
  rw [kernel_applyU]
  rfl

theorem KernelSrc.armThen_def : KernelSrc.armThen =
    (CSrc.lam 6 (g! "seq" ⬝c (g! "wDo" ⬝c v! 0) ⬝c (v! 0 ⬝c v! 6) ⬝c v! 2)).resolve
      (kernelEnv Scott.QCons Scott.QUnit Scott.QThen) := by
  unfold KernelSrc.armThen KernelSrc.arm
  rw [kernel_applyU]
  rfl

end

-- ---------------------------------------------------------------------------
-- A quotation table, compiled
-- ---------------------------------------------------------------------------

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

/-- A word list's compiled term, which takes the eliminator first:
    `c ap = seq w1 (seq w2 … wm)`.  A program and a static quotation's body
    compile alike. -/
def progT (p : List Word) : Term := toTerm (compDef [0] (tb.bodySrc p))

/-- The `k`-th static quotation's compiled term, `b_k`. -/
def bodyT (k : Nat) : Term := tb.progT (tb.body k)

/-- `applyU q s = q |> { Q_k (b_k applyU s)…; QCons x r (applyU r (Push x s));
    QUnit x (RVal (Push x s)); QThen b (seq (wDo applyU) (applyU b) s) }`,
    with self0 q1 s2 x3 r4 x5 b6. -/
def applySrc : Src :=
  (List.range tb.n).foldl (fun acc k => acc ⬝ₛ (.glob (tb.bodyT k) ⬝ₛ .var 0 ⬝ₛ .var 2)) (.var 1)
    ⬝ₛ KernelSrc.armCons ⬝ₛ KernelSrc.armUnit ⬝ₛ KernelSrc.armThen

def applyU : Term := toTerm (compRec 0 [1, 2] tb.applySrc)

/-- **The table's kit, compiled from source.** -/
@[reducible] def kit : Kit where
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
