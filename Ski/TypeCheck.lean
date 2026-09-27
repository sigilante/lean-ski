import Ski.Check
open Term

/-!
# SKIjack's checker: Stage B

`skijack/typecheck.py`: Hindley–Milner over the declared sum types, with
an oriented, equirecursive unifier in which a datum may be applied (a
Scott datum is its own case analysis) and a function is never a datum.
It runs over the generated program, on macro-expanded bodies, and only
refuses.

The port keeps the Python's object graph.  A type is a node in an arena,
addressed by its index, which is its identity (`id`); an arrow's flags
(`elim`, `nominal`, `datum`, `checked`) are updated in place, and a node
is allocated exactly where the Python allocates an object, so sharing,
and so every flag update, is the Python's.  Every problem refuses the
program, so the first one ends the check: `stageB ds` is `true` when
there is one.

Each walk carries a depth bound, `walkDepth`, the Python's recursion
limit; running out refuses, as the Python's `RecursionError` does.  A walk
the Python completes is shallower than its limit, so the bound refuses
nothing the Python accepts; a walk the Python never completes, such as
the unification that recurses without end on `scripts/coverage.ski`,
runs out and refuses.
-/

namespace Front

/-- A binary trie keyed by `Nat`: the root holds `0`; `2k + 1` is `k` on
    the left, `2k + 2` is `k` on the right. -/
inductive Trie (α : Type) where
  | leaf
  | node (v : Option α) (l r : Trie α)

/-- The depth bound of a trie walk: keys below `2 ^ 64`. -/
def trieDepth : Nat := 64

def Trie.get {α : Type} : Nat → Trie α → Nat → Option α
  | 0, _, _ => none
  | _ + 1, .leaf, _ => none
  | f + 1, .node v l r, k =>
    if k == 0 then v
    else if k % 2 == 1 then Trie.get f l (k / 2) else Trie.get f r (k / 2 - 1)

def Trie.set {α : Type} : Nat → Trie α → Nat → α → Trie α
  | 0, t, _, _ => t
  | f + 1, t, k, a =>
    let (v, l, r) := match t with
      | .leaf => (none, .leaf, .leaf)
      | .node v l r => (v, l, r)
    if k == 0 then .node (some a) l r
    else if k % 2 == 1 then .node v (Trie.set f l (k / 2) a) r
    else .node v l (Trie.set f r (k / 2 - 1) a)

/-- A type (`TVar`, `TCon`, `TArrow`). -/
inductive TNode
  | var (data : Bool) (ref : Option Nat)
  | con (name : Nm) (args : List Nat)
  | arr (param result : Nat) (elim : Bool) (nominal : Option Nm) (datum : Bool)
      (checked : Option Nm)

/-- A type scheme: its quantified variables, those with the data
    constraint, and its type. -/
structure Scheme where
  vars : List Nat
  data : List Nat
  type : Nat

/-- The checker's state: the arena, the program-level schemes, each
    core's, and the names of the group being inferred. -/
structure TS where
  heap : Trie TNode
  next : Nat
  env : List (Nm × Scheme)
  coreEnv : List (Nm × List (Nm × Scheme))
  mono : List (Nm × Nat)

abbrev TM := StateT TS Option

/-- The depth bound of every walk: the Python's recursion limit. -/
def walkDepth : Nat := 1000

def fail {α : Type} : TM α := fun _ => none

def node (i : Nat) : TM TNode := fun s =>
  match s.heap.get trieDepth i with
  | some n => some (n, s)
  | none => none

def setNode (i : Nat) (n : TNode) : TM Unit := fun s =>
  some ((), { s with heap := s.heap.set trieDepth i n })

def alloc (n : TNode) : TM Nat := fun s =>
  some (s.next, { s with heap := s.heap.set trieDepth s.next n, next := s.next + 1 })

def tfresh (data : Bool := false) : TM Nat := alloc (.var data none)

/-- A dictionary assignment. -/
def dput {β : Type} (d : List (Nm × β)) (n : Nm) (b : β) : List (Nm × β) :=
  if d.any (·.1 == n) then d.map fun q => if q.1 == n then (n, b) else q else d ++ [(n, b)]

/-- Follow a variable's binding to its end (`resolve`). -/
def resolveT : Nat → Nat → TM Nat
  | 0, _ => fail
  | f + 1, i => do
    match ← node i with
    | .var _ (some j) => resolveT f j
    | _ => pure i

def res (i : Nat) : TM Nat := do resolveT ((← get).next + 1) i

/-- `_arrows`: `p1 -> … -> pn -> r`, allocated innermost first. -/
def arrows (ps : List Nat) (r : Nat) : TM Nat :=
  ps.reverse.foldlM (fun t p => alloc (.arr p t false none false none)) r

/-- `_scott`: the same with elimination arrows committed to `name`. -/
def scottArrows (cs : List Nat) (r : Nat) (name : Nm) : TM Nat :=
  cs.reverse.foldlM (fun t c => alloc (.arr c t true (some name) false none)) r

/-- The program's declared types, the last declaration of a name winning. -/
abbrev Types := List (Nm × TypeDecl)

/-- `field`: a declared type, as a new constructor node. -/
def field (tys : Types) (n : Nm) : TM Nat :=
  if tys.any (·.1 == n) then alloc (.con n []) else fail

/-- `scott`: what a datum of type `t` is when applied: an elimination
    spine over one continuation per constructor.  `none` for a type with
    no Scott scheme. -/
def scott (tys : Types) (fuelT : Nat) (t : Nat) : TM (Option Nat) := do
  match ← node t with
  | .con name args =>
    let r ← tfresh
    match lastLookup tys name with
    | some d =>
      let cs ← d.ftys.mapM fun c => do
        let fs ← c.2.mapM (field tys)
        arrows fs r
      some <$> scottArrows cs r name
    | none =>
      if name == nm! "fuel" then
        let a ← alloc (.arr fuelT r false none false none)
        some <$> scottArrows [r, a] r name
      else if name == nm! "list" then
        match args with
        | [a] =>
          let l ← alloc (.con (nm! "list") [a])
          let c2 ← arrows [a, l] r
          some <$> scottArrows [r, c2] r name
        | _ => fail
      else if name == nm! "cell" then
        match args with
        | [a, b] =>
          let c1 ← arrows [a, b] r
          some <$> scottArrows [c1] r name
        | _ => fail
      else pure none
  | _ => fail

/-- `bind`: a variable bound to a type; an operand of `EQ` bound to a
    function refuses. -/
def bindV (v t : Nat) : TM Unit := do
  let t ← res t
  if t == v then return
  match ← node v with
  | .var vd _ =>
    if vd then
      match ← node t with
      | .arr p r el nm _ c =>
        if !el then fail
        setNode t (.arr p r el nm true c)
      | .var _ rf => setNode t (.var true rf)
      | _ => pure ()
    setNode v (.var vd (some t))
  | _ => fail

/-- **Unification** (`unify`), oriented: `expected` against `given`,
    equirecursive by the pairs already `seen`, which every call of one
    unification shares. -/
def unify (tys : Types) (fuelT : Nat) : Nat → Nat → Nat → List (Nat × Nat) → TM (List (Nat × Nat))
  | 0, _, _, _ => fail
  | f + 1, exp, giv, seen => do
    let e ← res exp
    let g ← res giv
    if e == g then return seen
    let ne ← node e
    let ng ← node g
    match ne with
    | .var .. => bindV e g; return seen
    | _ =>
    match ng with
    | .var .. => bindV g e; return seen
    | _ =>
    if seen.contains (e, g) then return seen
    let seen := (e, g) :: seen
    match ne, ng with
    | .arr ep er ee en ed ec, .arr gp gr ge gn gd gc =>
      if ge && !ee then pure ()
      else if ee && !ge then
        if en.isSome || ed then fail
        setNode e (.arr ep er false en ed ec)
      else if ee && ge then
        match en, gn with
        | some a, some b => if a != b then fail
        | _, _ => pure ()
        let nm := match en with | some a => some a | none => gn
        let d := ed || gd
        setNode e (.arr ep er ee nm d ec)
        setNode g (.arr gp gr ge nm d gc)
      let seen ← unify tys fuelT f gp ep seen
      unify tys fuelT f er gr seen
    | .arr ep er ee en ed ec, .con gname _ =>
      if ec == some gname then return seen
      if ee && (match en with | some n => n != gname | none => false) then fail
      match ← scott tys fuelT g with
      | none => fail
      | some sc =>
        setNode e (.arr ep er ee (if ee then some gname else en) ed (some gname))
        unify tys fuelT f e sc seen
    | .con ename _, .arr gp gr ge gn gd gc =>
      if !ge then fail
      if (match gn with | some n => n != ename | none => false) then fail
      if gc == some ename then return seen
      match ← scott tys fuelT e with
      | none => fail
      | some sc =>
        setNode g (.arr gp gr ge (some ename) gd (some ename))
        unify tys fuelT f g sc seen
    | .con en ea, .con gn ga =>
      if en != gn || ea.length != ga.length then fail
      (ea.zip ga).foldlM (fun sn p => unify tys fuelT f p.1 p.2 sn) seen
    | _, _ => fail

def unify0 (tys : Types) (fuelT : Nat) (e g : Nat) : TM Unit := do
  let _ ← unify tys fuelT walkDepth e g []

/-- `instantiate`'s copy: variables substituted, every other node with
    arguments copied once (`memo`), through a hole that closes a cycle. -/
def instGo (sub : List (Nat × Nat)) : Nat → List (Nat × Nat) → Nat → TM (Nat × List (Nat × Nat))
  | 0, _, _ => fail
  | f + 1, memo, t0 => do
    let t ← res t0
    let n ← node t
    match n with
    | .var .. => pure ((sub.lookup t).getD t, memo)
    | _ =>
    match memo.lookup t with
    | some h => pure (h, memo)
    | none =>
    match n with
    | .con _ [] => pure (t, memo)
    | .con name args =>
      let hole ← tfresh
      let memo := memo ++ [(t, hole)]
      let (as', memo) ← args.foldlM (fun (acc : List Nat × List (Nat × Nat)) a => do
        let (a', m) ← instGo sub f acc.2 a
        pure (acc.1 ++ [a'], m)) ([], memo)
      let nw ← alloc (.con name as')
      setNode hole (.var false (some nw))
      pure (nw, memo)
    | .arr p r el nm d c =>
      let hole ← tfresh
      let memo := memo ++ [(t, hole)]
      let (p', memo) ← instGo sub f memo p
      let (r', memo) ← instGo sub f memo r
      let nw ← alloc (.arr p' r' el nm d c)
      setNode hole (.var false (some nw))
      pure (nw, memo)
    | .var .. => fail

def instantiate (s : Scheme) : TM Nat :=
  if s.vars.isEmpty then pure s.type
  else do
    let sub ← s.vars.mapM fun v => do pure (v, ← tfresh (s.data.contains v))
    let (t, _) ← instGo sub walkDepth [] s.type
    pure t

/-- `free`: the variables reachable from a type, cycle-safe. -/
def freeT : Nat → Nat → List Nat → List Nat → TM (List Nat × List Nat)
  | 0, _, _, _ => fail
  | f + 1, t0, out, seen => do
    let t ← res t0
    match ← node t with
    | .var .. => pure (if out.contains t then out else out ++ [t], seen)
    | n =>
      if seen.contains t then pure (out, seen)
      else
        let seen := t :: seen
        match n with
        | .con _ args =>
          args.foldlM (fun (acc : List Nat × List Nat) a => freeT f a acc.1 acc.2) (out, seen)
        | .arr p r .. => do
          let (out, seen) ← freeT f p out seen
          freeT f r out seen
        | .var .. => pure (out, seen)

def freeOf (t : Nat) : TM (List Nat) := do pure (← freeT walkDepth t [] []).1

/-- `env_free`: the free variables of the environment. -/
def envFree : TM (List Nat) := do
  let s ← get
  let a ← s.env.foldlM (fun out p => do
    let fv ← freeOf p.2.type
    pure (out ++ fv.filter fun k => !p.2.vars.contains k)) []
  s.mono.foldlM (fun out p => do pure (out ++ (← freeOf p.2))) a

def isData (k : Nat) : TM Bool := do
  match ← node k with
  | .var d _ => pure d
  | _ => pure false

def generalize (t : Nat) : TM Scheme := do
  let fv ← freeOf t
  let efv ← envFree
  let qs := fv.filter fun k => !efv.contains k
  let ds ← qs.filterM isData
  pure ⟨qs, ds, t⟩

def close (t : Nat) : TM Scheme := do pure ⟨← freeOf t, [], t⟩

/-- `builtin`: the ISA, Tier 1 and the prelude. -/
def builtin (fuelT : Nat) (n : Nm) : TM (Option Scheme) := do
  if n == [83] then
    let a ← tfresh; let b ← tfresh; let c ← tfresh
    let x ← arrows [a, b] c
    let y ← alloc (.arr a b false none false none)
    some <$> close (← arrows [x, y, a] c)
  else if n == [75] then
    let a ← tfresh; let b ← tfresh
    some <$> close (← arrows [a, b] a)
  else if n == [73] then
    let a ← tfresh
    some <$> close (← alloc (.arr a a false none false none))
  else if n == [66] then
    let a ← tfresh; let b ← tfresh; let c ← tfresh
    let x ← alloc (.arr b c false none false none)
    let y ← alloc (.arr a b false none false none)
    some <$> close (← arrows [x, y, a] c)
  else if n == [67] then
    let a ← tfresh; let b ← tfresh; let c ← tfresh
    let x ← arrows [a, b] c
    some <$> close (← arrows [x, b, a] c)
  else if n == [87] then
    let a ← tfresh; let b ← tfresh
    let x ← arrows [a, a] b
    some <$> close (← arrows [x, a] b)
  else if n == [89] then
    let a ← tfresh
    let x ← alloc (.arr a a false none false none)
    some <$> close (← alloc (.arr x a false none false none))
  else if n == nm! "pair" then
    let a ← tfresh; let b ← tfresh
    let c ← alloc (.con (nm! "cell") [a, b])
    some <$> close (← arrows [a, b] c)
  else if n == nm! "hd" then
    let a ← tfresh; let b ← tfresh
    let c ← alloc (.con (nm! "cell") [a, b])
    some <$> close (← alloc (.arr c a false none false none))
  else if n == nm! "tl" then
    let a ← tfresh; let b ← tfresh
    let c ← alloc (.con (nm! "cell") [a, b])
    some <$> close (← alloc (.arr c b false none false none))
  else if n == nm! "nil" then
    let a ← tfresh
    some <$> close (← alloc (.con (nm! "list") [a]))
  else if n == nm! "cons" then
    let a ← tfresh
    let l1 ← alloc (.con (nm! "list") [a])
    let l2 ← alloc (.con (nm! "list") [a])
    some <$> close (← arrows [a, l1] l2)
  else if n == nm! "zero" then pure (some ⟨[], [], fuelT⟩)
  else if n == nm! "suc" then
    pure (some ⟨[], [], ← alloc (.arr fuelT fuelT false none false none)⟩)
  else pure none

/-- `lookup`: a binder, the ISA, the group's names, the core's, the
    program's, then the built-ins. -/
def lookupT (fuelT : Nat) (n : Nm) (bound : List (Nm × Nat)) (core : Option Nm) : TM Nat := do
  match bound.lookup n with
  | some t => pure t
  | none =>
  if isISA n then
    match ← builtin fuelT n with
    | some s => instantiate s
    | none => fail
  else
  let s ← get
  let inCore : Option (TM Nat) := match core with
    | some c =>
      match s.mono.lookup (c ++ [46] ++ n) with
      | some t => some (pure t)
      | none =>
        match (s.coreEnv.lookup c).bind (·.lookup n) with
        | some sc => some (instantiate sc)
        | none => none
    | none => none
  match inCore with
  | some m => m
  | none =>
  match s.mono.lookup n with
  | some t => pure t
  | none =>
  match s.env.lookup n with
  | some sc => instantiate sc
  | none =>
  match ← builtin fuelT n with
  | some sc => instantiate sc
  | none => fail

/-- The declared types' constructors: each constructor's type (the last
    declaring it). -/
abbrev CtorOf := List (Nm × TypeDecl)

/-- `infer`, over a macro-expanded body. -/
def infer (tys : Types) (ctorOf : CtorOf) (fuelT : Nat) (core : Option Nm) :
    Nat → Expr → List (Nm × Nat) → TM Nat
  | 0, _, _ => fail
  | f + 1, e, bound =>
    match e with
    | .name n => lookupT fuelT n bound core
    | .lam x b => do
      let p ← tfresh
      let body ← infer tys ctorOf fuelT core f b ((x, p) :: bound)
      alloc (.arr p body false none false none)
    | .app g a => do
      let (h, args) := spine (.app g a)
      let tf ← infer tys ctorOf fuelT core f h bound
      let isEq := match h with | .name n => n == nm! "EQ" | _ => false
      let (tf, _) ← args.foldlM (fun (acc : Nat × Nat) x => do
        let tx ← infer tys ctorOf fuelT core f x bound
        let tx ← if isEq && acc.2 < 2 then do
            let d ← tfresh true
            unify0 tys fuelT d tx
            pure d
          else pure tx
        let r ← tfresh
        let ar ← alloc (.arr tx r true none false none)
        unify0 tys fuelT ar acc.1
        pure (r, acc.2 + 1)) (tf, 0)
      pure tf
    | .cell items => do
      let ts ← (itemsList items).mapM fun x => infer tys ctorOf fuelT core f x bound
      match ts.reverse with
      | [] => tfresh
      | last :: rest => rest.foldlM (fun c t => alloc (.con (nm! "cell") [t, c])) last
    | .pick n x => do
      let t0 ← infer tys ctorOf fuelT core f x bound
      (axisSteps n).foldlM (fun t bit => do
        let a ← tfresh
        let b ← tfresh
        let c ← alloc (.con (nm! "cell") [a, b])
        unify0 tys fuelT c t
        pure (if bit then b else a)) t0
    | .case sc bs => do
      let brs := bs.toList
      match brs with
      | [] => fail
      | (c0, _, _) :: _ =>
      match ctorOf.lookup c0 with
      | none => fail
      | some d =>
      let tc ← alloc (.con d.name [])
      let ts ← infer tys ctorOf fuelT core f sc bound
      unify0 tys fuelT tc ts
      let result ← tfresh
      let fields := d.ftys.reverse
      brs.forM fun (c, xs, body) => do
        match fields.lookup c with
        | none => fail
        | some fs =>
          if xs.length != fs.length then fail
          let fts ← fs.mapM (field tys)
          let inner := (xs.zip fts).reverse ++ bound
          let tb ← infer tys ctorOf fuelT core f body inner
          unify0 tys fuelT result tb
      pure result
    | _ => tfresh
where
  itemsList : Items → List Expr
    | .nil => []
    | .cons x r => x :: itemsList r

mutual
  /-- `_names`: every name an expression mentions, bound or not. -/
  def namesE : Expr → List Nm
    | .name n => [n]
    | .app f a => namesE f ++ namesE a
    | .lam _ b => namesE b
    | .cell items => namesI items
    | .pick _ e => namesE e
    | .case e bs => namesE e ++ namesB bs
    | _ => []
  def namesB : Branches → List Nm
    | .nil => []
    | .cons _ _ b r => namesE b ++ namesB r
  def namesI : Items → List Nm
    | .nil => []
    | .cons e r => namesE e ++ namesI r
end

/-- Names in Python's string order. -/
def nmLt : Nm → Nm → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && nmLt as bs)

def insertNm (x : Nm) : List Nm → List Nm
  | [] => [x]
  | y :: ys => if nmLt x y then x :: y :: ys else y :: insertNm x ys

def sortNm (l : List Nm) : List Nm := l.foldl (fun acc x => insertNm x acc) []

/-- Tarjan's state: indices and low links (newest first), the stack, and
    the groups found. -/
structure TJ where
  index : List (Nm × Nat)
  low : List (Nm × Nat)
  stack : List Nm
  out : List (List Nm)
  counter : Nat

def TJ.lowOf (st : TJ) (v : Nm) : Nat := (st.low.lookup v).getD 0

/-- Pop the stack down to `v`, the top first. -/
def popTo (v : Nm) : List Nm → List Nm → List Nm × List Nm
  | [], g => (g, [])
  | w :: r, g => if w == v then (g ++ [w], r) else popTo v r (g ++ [w])

/-- `_sccs`' `visit`. -/
def visit (deps : List (Nm × List Nm)) : Nat → Nm → TJ → TJ
  | 0, _, st => st
  | f + 1, v, st0 =>
    let st : TJ := { st0 with index := (v, st0.counter) :: st0.index,
                              low := (v, st0.counter) :: st0.low,
                              counter := st0.counter + 1, stack := v :: st0.stack }
    let st := (sortNm ((deps.lookup v).getD [])).foldl (fun st w =>
      match st.index.lookup w with
      | none =>
        let st := visit deps f w st
        { st with low := (v, min (st.lowOf v) (st.lowOf w)) :: st.low }
      | some iw =>
        if st.stack.contains w then { st with low := (v, min (st.lowOf v) iw) :: st.low }
        else st) st
    if st.lowOf v == (st.index.lookup v).getD 0 then
      let (g, rest) := popTo v st.stack []
      { st with stack := rest, out := st.out ++ [g] }
    else st

/-- `_sccs`: the groups in dependency order, callees first. -/
def sccs (keys : List Nm) (deps : List (Nm × List Nm)) : List (List Nm) :=
  ((sortNm keys).foldl (fun st v =>
    if (st.index.lookup v).isSome then st else visit deps (keys.length + 1) v st)
    (⟨[], [], [], [], 0⟩ : TJ)).out

/-- An item to infer: its name, its core, its binders, its expanded body. -/
structure Item where
  name : Nm
  core : Option Nm
  binders : List Nm
  body : Expr

def Item.key (it : Item) : Nm :=
  match it.core with
  | some c => c ++ [46] ++ it.name
  | none => it.name

/-- `infer_group`: one strongly connected group, monomorphic within it,
    then generalized. -/
def inferGroup (tys : Types) (ctorOf : CtorOf) (fuelT : Nat) (items : List (Nm × Item))
    (group : List Nm) : TM Unit := do
  group.forM fun k => do
    let t ← tfresh
    modify fun s => { s with mono := dput s.mono k t }
  let results ← group.mapM fun k => do
    match items.lookup k with
    | none => fail
    | some it =>
      let bound ← it.binders.mapM fun b => do pure (b, ← tfresh)
      let bnd := bound.reverse
      let body ← infer tys ctorOf fuelT it.core walkDepth it.body bnd
      let t ← arrows (it.binders.map fun b => (bnd.lookup b).getD 0) body
      let m ← do pure (((← get).mono.lookup k).getD 0)
      unify0 tys fuelT m t
      pure (k, it, t)
  modify fun s => { s with mono := s.mono.filter fun p => !group.contains p.1 }
  results.forM fun (_, it, t) => do
    let sc ← generalize t
    match it.core with
    | none => modify fun s => { s with env := dput s.env it.name sc }
    | some c => modify fun s =>
      { s with coreEnv := dput s.coreEnv c (dput ((s.coreEnv.lookup c).getD []) it.name sc) }

/-- `run_decl`: a run's interpreter, applied to its arguments, then the
    fuel and the datum, gives the result type. -/
def runDecl (tys : Types) (ctorOf : CtorOf) (fuelT objT : Nat) (resultN : Nm)
    (ms : List (Nm × Macro)) (n : Nm) (interp : Option Expr) : TM Unit := do
  let head := interp.getD (.name (nm! "whnfF"))
  match spine head with
  | (.name h, args) =>
    match (← get).env.lookup h with
    | none => pure ()
    | some sc =>
      let t0 ← instantiate sc
      let t ← args.foldlM (fun t x => do
        match expandE 400 ms 0 0 200000 x with
        | none => fail
        | some (x', _) =>
          let tx ← infer tys ctorOf fuelT none walkDepth x' []
          let r ← tfresh
          let ar ← alloc (.arr tx r true none false none)
          unify0 tys fuelT ar t
          pure r) t0
      let r ← tfresh
      let fa ← arrows [fuelT, objT] r
      unify0 tys fuelT fa t
      let rc ← alloc (.con resultN [])
      unify0 tys fuelT rc r
      let rc2 ← alloc (.con resultN [])
      modify fun s => { s with env := dput s.env n ⟨[], [], rc2⟩ }
  | _ => pure ()

/-- **Stage B** (`_Types.run`), over the generated program. -/
def stageBRun (ds : List Decl) : TM Unit := do
  let tyDecls := ds.filterMap fun d => match d with | .ty t => some t | _ => none
  let tys : Types := tyDecls.map fun t => (t.name, t)
  let ctorOf : CtorOf := (tyDecls.flatMap fun t => t.ftys.map fun c => (c.1, t)).reverse
  let ms := macrosOf ds
  let fuelT ← alloc (.con (nm! "fuel") [])
  let names := tyDecls.foldl (fun acc t => if acc.contains t.name then acc else acc ++ [t.name]) []
  names.forM fun tn => do
    match lastLookup tys tn with
    | none => pure ()
    | some d =>
      d.ftys.forM fun c => do
        let fs ← c.2.mapM (field tys)
        let tc ← alloc (.con d.name [])
        let t ← arrows fs tc
        modify fun s => { s with env := dput s.env c.1 ⟨[], [], t⟩ }
  let (obj, lt, answer) :=
    match findObject tyDecls with
    | some (some o) =>
      match findLoop tyDecls o with
      | some l =>
        match findAnswer tyDecls o l with
        | some a => (some o, some l, a)
        | none => (some o, some l, none)
      | none => (some o, none, none)
    | _ => (none, none, none)
  let objT ← match obj with
    | some o => some <$> alloc (.con o.decl.name [])
    | none => pure none
  let runs ← ds.filterMapM fun d => do
    match d with
    | .qdef n (.quote _ .none) =>
      match objT with
      | some ot => modify fun s => { s with env := dput s.env n ⟨[], [], ot⟩ }
      | none => pure ()
      pure none
    | .qdef n (.quote _ _) => pure (some (n, (none : Option Expr)))
    | .qdef n (.run i _ _) => pure (some (n, some i))
    | .qdef n (.nslit _) =>
      match objT, answer with
      | some ot, some (hit, _) =>
        let ansName := ((tyDecls.find? fun t => t.ftys.any (·.1 == hit)).map (·.name)).getD []
        let a ← alloc (.con ansName [])
        let t ← alloc (.arr ot a false none false none)
        modify fun s => { s with env := dput s.env n ⟨[], [], t⟩ }
      | _, _ => pure ()
      pure none
    | _ => pure none
  let items : List Item := ds.flatMap fun d =>
    match d with
    | .eqn e => [⟨e.name, none, e.params, e.body⟩]
    | .core c ps eqs => eqs.map fun q => ⟨q.1, some c, ps ++ q.2.1, q.2.2⟩
    | _ => []
  let expanded ← items.mapM fun it =>
    match expandE 400 ms 0 0 200000 it.body with
    | some (b, _) => pure { it with body := b }
    | none => fail
  let keys := expanded.foldl (fun acc it => if acc.contains it.key then acc else acc ++ [it.key]) []
  let itemOf : List (Nm × Item) := (expanded.map fun it => (it.key, it)).reverse
  let deps : List (Nm × List Nm) := keys.map fun k =>
    match itemOf.lookup k with
    | none => (k, [])
    | some it =>
      (k, (namesE it.body).foldl (fun acc nm =>
        if it.binders.contains nm then acc
        else
          let dep := match it.core with
            | some c => if keys.contains (c ++ [46] ++ nm) then some (c ++ [46] ++ nm)
                        else if keys.contains nm then some nm else none
            | none => if keys.contains nm then some nm else none
          match dep with
          | some x => if acc.contains x then acc else acc ++ [x]
          | none => acc) [])
  (sccs keys deps).forM (inferGroup tys ctorOf fuelT itemOf)
  match obj with
  | some o =>
    ds.forM fun d => do
      match d with
      | .core c _ eqs =>
        if isInterp o eqs then
          match ((← get).coreEnv.lookup c).bind (·.lookup (nm! "loop")) with
          | some l => modify fun s => { s with env := dput s.env c l }
          | none => pure ()
      | _ => pure ()
  | none => pure ()
  ds.forM fun d => do
    match d with
    | .sig n ts =>
      match (← get).env.lookup n with
      | some sc =>
        match ts.reverse with
        | last :: initR =>
          let fs ← initR.reverse.mapM (field tys)
          let l ← field tys last
          let sig ← arrows fs l
          let inst ← instantiate sc
          unify0 tys fuelT sig inst
        | [] => fail
      | none => pure ()
    | _ => pure ()
  runs.forM fun (n, interp) => do
    match objT, lt with
    | some ot, some l => runDecl tys ctorOf fuelT ot l.result ms n interp
    | _, _ => pure ()

/-- `true` when Stage B finds a problem, and the program is refused. -/
def stageB (ds : List Decl) : Bool :=
  ((stageBRun ds).run ⟨.leaf, 0, [], [], []⟩).isNone

/-- `skijack`'s checker passes: the program parses, Stage A finds nothing,
    generation succeeds and Stage B finds nothing. -/
def checkPass (u : Bool) (src : List Nat) : Bool :=
  match parseWith u src with
  | none => false
  | some ds =>
    !stageA ds &&
      match generate ds with
      | none => false
      | some gs => !stageB gs

/-- **The checked compilation**: `skijack` with its checker on.  A program
    passes Stage A before generation and Stage B after, and compiles; the
    terms are those of `compileWith`, since the checker only refuses. -/
def checkedWith (u : Bool) (src : List Nat) : Option (List (Nm × Term)) :=
  match parseWith u src with
  | none => none
  | some ds =>
    if stageA ds then none
    else
      match generate ds with
      | none => none
      | some gs => if stageB gs then none else (compileDecls gs).map (·.1)

/-- The checker only refuses: where it passes, the checked compilation is
    the unchecked one. -/
theorem checkedWith_of_pass {u : Bool} {src : List Nat} (h : checkPass u src = true) :
    checkedWith u src = compileWith u src := by
  unfold checkPass at h
  unfold checkedWith compileWith readWith
  cases hp : parseWith u src with
  | none => rw [hp] at h; cases h
  | some ds =>
    rw [hp] at h
    dsimp only at h
    dsimp only [Option.bind]
    cases hA : stageA ds with
    | true => rw [hA] at h; cases h
    | false =>
      rw [hA] at h
      rw [if_neg Bool.false_ne_true]
      cases hg : generate ds with
      | none => rw [hg] at h
      | some gs =>
        rw [hg] at h
        dsimp only at h ⊢
        cases hB : stageB gs with
        | true => rw [hB] at h; cases h
        | false => rw [if_neg Bool.false_ne_true]

/-- Where the checker refuses, the checked compilation refuses. -/
theorem checkedWith_of_fail {u : Bool} {src : List Nat} (h : checkPass u src = false) :
    checkedWith u src = none := by
  unfold checkPass at h
  unfold checkedWith
  cases hp : parseWith u src with
  | none => rfl
  | some ds =>
    rw [hp] at h
    dsimp only at h ⊢
    cases hA : stageA ds with
    | true => rw [if_pos rfl]
    | false =>
      rw [hA] at h
      rw [if_neg Bool.false_ne_true]
      cases hg : generate ds with
      | none => rfl
      | some gs =>
        rw [hg] at h
        dsimp only at h ⊢
        cases hB : stageB gs with
        | true => rw [if_pos rfl]
        | false => rw [hB] at h; cases h

end Front
