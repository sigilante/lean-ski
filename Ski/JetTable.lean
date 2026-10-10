import Ski.AirJet
import Ski.Table

open Term

/-!
# Which jets to license: the jet table of a loaded term

`Air.AcceptsJ` takes its roots and jets as public data, and
`Air.checkJA` checks them (`Air.rootsOKB`).  This module computes them for
a loaded term; nothing here is trusted, because every root it returns has
passed `Air.rootOKB`.

**The templates** are every combinator the front end's compiler makes by
bracket abstraction, read off the compiler: each equation's `compDef` or
`compRec`, each λ chain `compLam` lifts inside it (`wrapLift`), and each
constructor's `ctorO`, over the sources of `Ski/Source.lean`.

**The jets.**  A template's body names its closed subterms (its maximal
subterms with no formal, leaves included) as globals, each pointing to a
cell of the loaded heap that holds it, so an instantiation writes only
the cells that depend on its arguments and a nested template's root stays
a root.  Three kinds of template are left out: an open one (a variable
outside the formals); an η-template, `λ xs. G xs` with `G` closed,
which compiles to `G` itself, so that instantiating it rewrites `G xs` to
`G xs` and a jetted run could repeat it forever; and one that compiles to
a bare `S`, `K` or `I` (`isComb`), whose jet costs more rows than the
machine's step.

**The roots** are found by hash-consing the loaded heap against the
templates' compiled forms, and kept only when `Air.rootOKB` licenses
them.

**The template rows** the prover reads (`symCells`, written by
`jetText`) are, resolved at a counter and the argument pointers, exactly
the cells and root `Air.instRow` computes with `icells`
(`symCells_icells`), a repeated formal taking its last occurrence as
`overrideN` binds it (`overrideN_argIx`).
-/

namespace JetTable

open Mach Front Air

-- ---------------------------------------------------------------------------
-- Templates, from the compiler
-- ---------------------------------------------------------------------------

mutual
  /-- The templates `comp scope` makes, innermost first. -/
  def tmplComp (scope : List Nat) : Src → List (List Nat × OTerm)
    | .glob _ => []
    | .var _ => []
    | .app f a => tmplComp scope f ++ tmplComp scope a
    | .lam x b => tmplLam (scope.filter fun s => (Src.lam x b).occurs s) [x] b
  /-- The templates `compLam caps ps` makes: those of the body, then its own. -/
  def tmplLam (caps ps : List Nat) : Src → List (List Nat × OTerm)
    | .lam y b => tmplLam caps (ps ++ [y]) b
    | .glob t => [(caps ++ ps, t.toO)]
    | .var x => [(caps ++ ps, .var x)]
    | .app f a =>
      tmplComp (caps ++ ps) f ++ tmplComp (caps ++ ps) a ++
        [(caps ++ ps, compF (caps ++ ps) f ⬝ₒ compF (caps ++ ps) a)]
end

/-- The templates of a source file: equations, the λ chains they lift, and
    constructors, each with at least one formal.  With `eta`, of the file
    compiled with η-lifting (`Front.compileFileEta`): a chain η-lifting
    removes lifts nothing, so it is no template. -/
def fileTemplates (src : List Nat) (eta : Bool := false) : List (List Nat × OTerm) :=
  match readFile src with
  | none => []
  | some ds =>
    match etaFEqns eta (fileFEqns ds), compileDecls ds eta with
    | some fes, some (_, done) =>
      let env := fun g => (resolveIn done g).getD K
      let eqs := fes.flatMap fun (_, e) =>
        let b := e.body.resolve env
        let xs := match e.self with
          | some s => s :: e.params
          | none => e.params
        tmplComp xs b ++ [(xs, compF xs b)]
      let ctors := (types ds).flatMap fun d =>
        (List.range d.ctors.length).zip d.ctors |>.map fun (j, (_, a)) =>
          (List.range (a + d.ctors.length), appL (.var (a + j)) ((List.range a).map .var))
      (eqs ++ ctors).filter fun (xs, _) => !xs.isEmpty
    | _, _ => []

/-- The templates of a SKIlark predicate's source, compiled with
    η-lifting as its statement's term is (`Front.compileFileEta`). -/
def fileTemplatesEta (src : List Nat) : List (List Nat × OTerm) := fileTemplates src true

/-- The templates of every source the corpus compiles from. -/
def allTemplates : List (List Nat × OTerm) :=
  fileTemplates kernelText ++ fileTemplates corpusText ++ fileTemplates sumText ++
    fileTemplates loopText

-- ---------------------------------------------------------------------------
-- Hash-consing
-- ---------------------------------------------------------------------------

/-- Canonical ids: 0, 1, 2 for `S`, `K`, `I`, then one per distinct
    application of ids. -/
structure HC where
  apps : Std.HashMap (Nat × Nat) Nat := {}
  next : Nat := 3

def HC.app (h : HC) (f x : Nat) : HC × Nat :=
  match h.apps[(f, x)]? with
  | some i => (h, i)
  | none => ({ apps := h.apps.insert (f, x) h.next, next := h.next + 1 }, h.next)

def HC.term (h : HC) : Term → HC × Nat
  | .S => (h, 0)
  | .K => (h, 1)
  | .I => (h, 2)
  | .app f x =>
    let (h, i) := h.term f
    let (h, j) := h.term x
    h.app i j

/-- The ids of a heap's cells; `none` for a cell that is no term.  An
    application points to older cells, so one pass names every cell. -/
def heapIds (h : HC) (heap : Array Cell) : HC × Array (Option Nat) := Id.run do
  let mut h := h
  let mut ids : Array (Option Nat) := #[]
  for c in heap do
    match c with
    | .S => ids := ids.push (some 0)
    | .K => ids := ids.push (some 1)
    | .I => ids := ids.push (some 2)
    | .app f x =>
      match ids[f]?.join, ids[x]?.join with
      | some i, some j =>
        let (h', k) := h.app i j
        h := h'
        ids := ids.push (some k)
      | _, _ => ids := ids.push none
    | _ => ids := ids.push none
  return (h, ids)

-- ---------------------------------------------------------------------------
-- Globals
-- ---------------------------------------------------------------------------

def OTerm.closedT : OTerm → Bool
  | .var _ => false
  | .app f x => closedT f && closedT x
  | _ => true

/-- A closed open term as a term. -/
def OTerm.toT : OTerm → Term
  | .S => .S
  | .K => .K
  | .I => .I
  | .var _ => .K
  | .app f x => .app (toT f) (toT x)

/-- Name each maximal closed subterm of a body, leaves included, by a fresh
    variable from `next` on; returns the body and the globals, in order. -/
def globalize : OTerm → Nat → OTerm × List (Nat × Term) × Nat
  | .var x, n => (.var x, [], n)
  | t@(.app f x), n =>
    if OTerm.closedT t then (.var n, [(n, OTerm.toT t)], n + 1)
    else
      let (f', gf, n1) := globalize f n
      let (x', gx, n2) := globalize x n1
      (.app f' x', gf ++ gx, n2)
  | t, n => (.var n, [(n, OTerm.toT t)], n + 1)

-- ---------------------------------------------------------------------------
-- The jet table
-- ---------------------------------------------------------------------------

/-- Which cells have a **public closure**: every cell below them, by
    application, a term cell outside `priv`.  One pass in address order; a
    pointer that is not backward counts as private, which only drops
    candidates (`Air.publicB` is the check). -/
def pubCells (A : Array Cell) (priv : Nat → Bool) : Array Bool := Id.run do
  let mut pub : Array Bool := Array.mkEmpty A.size
  for i in [0:A.size] do
    let ok := !priv i &&
      match A[i]? with
      | some .S => true
      | some .K => true
      | some .I => true
      | some (.app g x) => decide (g < i) && decide (x < i) && pub.getD g false && pub.getD x false
      | _ => false
    pub := pub.push ok
  return pub

/-- A bare combinator.  A template that compiles to one, with `n` formals,
    reaches its body by the combinator's own contraction, its formals
    beyond the combinator's arity left on the stack.  That step costs one
    CPU row and no POP or INSTW row.  The jet costs one CPU row too, then
    a POP row per formal, an INSTW row per body cell, and CPU rows to
    unwind the cells it wrote.  On csplit8, `seq`'s handler `λg t. g t`
    compiles to `I`; each of its 39,459 instantiations took one CPU, two
    POP and one INSTW row more than the machine's step. -/
def isComb : Term → Bool
  | .S => true
  | .K => true
  | .I => true
  | _ => false

/-- **The jet table of a loaded heap**: the licensed roots and the jets they
    name.  Every returned root passes `Air.rootOKB`.  A template whose
    compiled root is a bare combinator (`isComb`) makes no jet.  With
    `globals` off, a body keeps its closed subterms, and an instantiation
    writes them.  With private addresses `priv`, a root or a global is only
    a cell whose closure avoids them (`pubCells`; the rule of
    `Air.publicB`). -/
def jetTable (h0 : List Cell) (tmpls : List (List Nat × OTerm)) (globals : Bool := true)
    (priv : Nat → Bool := fun _ => false) :
    List (Nat × Nat) × List Jet :=
  Id.run do
    let A := h0.toArray
    let (hc0, ids) := heapIds {} A
    let pub := pubCells A priv
    let mut hc := hc0
    let mut firstAt : Std.HashMap Nat Nat := {}
    for i in [0:ids.size] do
      match ids[i]! with
      | some k => if pub.getD i false && !firstAt.contains k then firstAt := firstAt.insert k i
      | none => pure ()
    -- candidate jets, by the id of their compiled root
    let mut jetOf : Std.HashMap Nat Jet := {}
    for (xs, body) in tmpls do
      let root := toTerm (absNF xs body)
      let isEta := body == appL root.toO (xs.map .var)
      let closedIn := body.vars.all fun v => xs.contains v
      if isEta || isComb root || !closedIn then continue
      let (hc1, rk) := hc.term root
      hc := hc1
      if jetOf.contains rk || !firstAt.contains rk then continue
      let base := (xs ++ body.vars).foldl max 0 + 1
      let (body', gs, _) := if globals then globalize body base else (body, [], base)
      let mut glob : List (Nat × Nat) := []
      let mut ok := true
      for (v, u) in gs do
        let (hc2, uk) := hc.term u
        hc := hc2
        match firstAt[uk]? with
        | some a => glob := glob ++ [(v, a)]
        | none => ok := false
      if ok then jetOf := jetOf.insert rk ⟨xs, body', glob⟩
    -- roots, licensed one by one; jets numbered as first used
    let mut jets : Array Jet := #[]
    let mut jetIx : Std.HashMap Nat Nat := {}
    let mut roots : Array (Nat × Nat) := #[]
    for i in [0:ids.size] do
      match (if pub.getD i false then ids[i]! else none) with
      | some k =>
        match jetOf[k]? with
        | some J =>
          let j := (jetIx[k]?).getD jets.size
          let jets' := if jetIx.contains k then jets else jets.push J
          if rootOKB (fun a => A[a]?) (A.size + 1) jets'.toList i j then
            jets := jets'
            jetIx := jetIx.insert k j
            roots := roots.push (i, j)
        | none => pure ()
      | none => pure ()
    return (roots.toList, jets.toList)

-- ---------------------------------------------------------------------------
-- A jet as the template table reads it
-- ---------------------------------------------------------------------------

/-- An operand: a cell this instantiation wrote (by offset), an argument
    (by index), or a public address. -/
inductive Op
  | local_ (j : Nat)
  | arg (i : Nat)
  | glob (a : Nat)

def Op.text : Op → String
  | .local_ j => s!"L {j}"
  | .arg i => s!"A {i}"
  | .glob a => s!"G {a}"

/-- The argument index a formal takes: its last occurrence, as `overrideN`
    binds a repeated formal (`overrideN_argIx`). -/
def argIx : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: xs, y =>
    match argIx xs y with
    | some i => some (i + 1)
    | none => if x == y then some 0 else none

/-- The operand a variable is. -/
def varOp (J : Jet) (x : Nat) : Op :=
  match argIx J.xs x with
  | some i => .arg i
  | none => .glob (J.genv x)

/-- The cells `icells` writes, symbolically, from offset `off`: each cell's
    tag (0, 1, 2, 3 for `S`, `K`, `I`, an application) and operands, and
    the root. -/
def symCells (J : Jet) : OTerm → Nat → List (Nat × Option (Op × Op)) × Op
  | .S, off => ([(0, none)], .local_ off)
  | .K, off => ([(1, none)], .local_ off)
  | .I, off => ([(2, none)], .local_ off)
  | .var x, _ => ([], varOp J x)
  | .app f a, off =>
    let (cf, rf) := symCells J f off
    let (ca, ra) := symCells J a (off + cf.length)
    (cf ++ ca ++ [(3, some (rf, ra))], .local_ (off + cf.length + ca.length))

/-- A jet in the prover's format: `k n root`, then one line per cell. -/
def jetText (J : Jet) : String :=
  let (cs, root) := symCells J J.body 0
  let head := s!"{J.xs.length} {cs.length} {root.text}\n"
  cs.foldl (fun s (tag, ops) =>
    s ++ (match ops with
      | some (a, b) => s!"{tag} {a.text} {b.text}"
      | none => s!"{tag}") ++ "\n") head

/-- **A jet table as text**, the file `jets emit` writes: the roots, then
    each jet as its template rows (`jetText`). -/
def tableText (roots : List (Nat × Nat)) (jets : List Jet) : String := Id.run do
  let mut s := s!"roots {roots.length}\n"
  for (a, g) in roots do
    s := s ++ s!"{a} {g}\n"
  s := s ++ s!"jets {jets.length}\n"
  for J in jets do
    s := s ++ jetText J
  return s

-- ---------------------------------------------------------------------------
-- The template rows are `icells`
-- ---------------------------------------------------------------------------

/-- An operand's value, for an instantiation at counter `c` with argument
    pointers `ps`: what the prover's INSTW and CPU rows compute. -/
def Op.res (c : Nat) (ps : List Nat) : Op → Nat
  | .local_ j => c + j
  | .arg i => ps.getD i 0
  | .glob a => a

/-- A template row's cell, for an instantiation at `c` with `ps`. -/
def cellOf (c : Nat) (ps : List Nat) : Nat × Option (Op × Op) → Cell
  | (_, some (a, b)) => .app (a.res c ps) (b.res c ps)
  | (0, none) => .S
  | (1, none) => .K
  | (_, none) => .I

/-- `overrideN` binds each formal to the pointer at its last occurrence,
    and every other variable as the default does. -/
theorem overrideN_argIx (e : Nat → Nat) : ∀ (xs ps : List Nat) (y : Nat), ps.length = xs.length →
    overrideN e xs ps y = (argIx xs y).elim (e y) (fun i => ps.getD i 0)
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h.symm (Nat.succ_ne_zero _)
  | x :: xs, p :: ps, y, h => by
    show overrideN (updN e x p) xs ps y = _
    rw [overrideN_argIx (updN e x p) xs ps y (Nat.succ.inj h)]
    have hc : argIx (x :: xs) y =
        (match argIx xs y with
         | some i => some (i + 1)
         | none => if x == y then some 0 else none) := rfl
    rw [hc]
    cases argIx xs y with
    | some i => rfl
    | none =>
      show updN e x p y = (if x == y then some 0 else none).elim (e y) fun i => (p :: ps).getD i 0
      unfold updN
      cases Nat.decEq y x with
      | isTrue hy =>
        subst hy
        rw [if_pos rfl, show (y == y) = true from decide_eq_true rfl]
        rfl
      | isFalse hy =>
        rw [if_neg hy, beq_false_of_ne (Ne.symm hy)]
        rfl

/-- **The template rows are `icells`.**  Resolved at counter `c` with the
    arguments `ps`, the cells and root `symCells` gives a jet (and `jetText`
    writes, one row per cell) are the cells and root `Air.instRow` computes
    with `icells` from `c + off`. -/
theorem symCells_icells (J : Jet) (c : Nat) (ps : List Nat) (hl : ps.length = J.xs.length) :
    ∀ (body : OTerm) (off : Nat),
      ((symCells J body off).1.map (cellOf c ps), (symCells J body off).2.res c ps) =
        icells (overrideN J.genv J.xs ps) (c + off) body
  | .S, off => rfl
  | .K, off => rfl
  | .I, off => rfl
  | .var x, off => by
    show ([], (varOp J x).res c ps) = ([], overrideN J.genv J.xs ps x)
    rw [overrideN_argIx J.genv J.xs ps x hl]
    unfold varOp
    cases argIx J.xs x <;> rfl
  | .app f a, off => by
    have hf := symCells_icells J c ps hl f off
    have ha := symCells_icells J c ps hl a (off + (symCells J f off).1.length)
    unfold symCells icells
    dsimp only
    rw [← hf]
    dsimp only
    rw [List.length_map,
      show c + off + (symCells J f off).1.length = c + (off + (symCells J f off).1.length) by omega, ← ha]
    simp only [List.map_append, List.map_cons, List.map_nil, List.length_map, cellOf, Op.res]
    refine Prod.ext rfl ?_
    show c + (off + (symCells J f off).1.length + (symCells J a (off + (symCells J f off).1.length)).1.length) = _
    omega

end JetTable
