import Ski.Front
open Term

/-!
# SKIjack's checker: Stage A

`skijack` runs a checker before it compiles (`skijack/check.py`, Stage A)
and a type discipline after generation (`skijack/typecheck.py`, Stage
B).  Both only refuse: a program either compiles to the same terms with
checking on as off, or is refused.  This file is Stage A, over the parsed
program, before generation.

Every problem Stage A can find refuses the program, so the port is a
Boolean: `stageA ds` is `true` when the program has a problem.

- **(f) scope.**  A name declared twice among types, constructors,
  macros, equations, cores and definitions; an equation defined twice in
  a core; a name that is neither bound nor known.
- **(b) case.**  A branch of another type, a repeated branch, a missing
  one.
- **(c) data.**  An argument of `EQ` that is provably a function; a scry
  or a namespace literal at level 0; a fact whose value is not a
  quotation; a nested quotation with fuel or an interpreter.
- **(e) the two tables.**  Inside a quotation, a name that is neither a
  constructor of the object type nor a level-0 name, and a constructor of
  another type applied to other than all its fields.
- **(d) the interface.**  An interpreter core's `step`, `loop` and
  `loop1` of the wrong shape, a step equation for the application
  constructor, leaf equations installed out of declaration order.
- A path literal whose segment is not a nullary constructor of the
  segment type.
-/

namespace Front

/-- Tier 1: `B C W Y`. -/
def tier1Names : List Nm := [[66], [67], [87], [89]]

/-- The prelude's names. -/
def preludeNames : List Nm := prelude.map (·.1)

/-- An application's head and arguments, as `_spine`. -/
def spineA (e : Expr) : Expr × List Expr := spine e

/-- The last entry for a name: Python's dictionary, assigned in order. -/
def lastLookup {β : Type} (l : List (Nm × β)) (n : Nm) : Option β := l.reverse.lookup n

/-- What Stage A knows of the program (`_Env`). -/
structure AEnv where
  /-- each type's first declaration -/
  tys : List TypeDecl
  /-- each constructor's type and arity, the first declaration winning -/
  ctors : List (Nm × Nm × Nat)
  macros : List Nm
  /-- each top-level equation or definition with its binder count; the last wins -/
  eqns : List (Nm × Nat)
  /-- each core's parameters and its equations with their binder counts; the last wins -/
  cores : List (Nm × List Nm × List (Nm × Nat))
  generated : List Nm
  coreGen : List (Nm × List Nm)
  obj : Option ObjT
  path : Option (Nm × Nm × Nm)

/-- `known`: the ISA, Tier 1, the prelude; in a core its equations, what
    generation adds to it and its parameters; any declared name. -/
def AEnv.known (env : AEnv) (n : Nm) (core : Option Nm) : Bool :=
  isISA n || tier1Names.contains n || preludeNames.contains n ||
  (match core with
   | some c =>
     (match lastLookup env.cores c with
      | some (ps, eqs) => eqs.any (·.1 == n) || ps.contains n
      | none => false) ||
     ((lastLookup env.coreGen c).getD []).contains n
   | none => false) ||
  env.ctors.any (·.1 == n) || env.eqns.any (·.1 == n) || env.cores.any (·.1 == n) ||
  env.generated.contains n || env.macros.contains n

/-- What generation adds (`names_generation_adds`): the program-level
    names it would define, and each interpreter core's. -/
def genAdds (ds : List Decl) (o : ObjT) : List Nm × List (Nm × List Nm) :=
  let taken := ds.flatMap fun d =>
    match d with
    | .ty t => t.ctors.map (·.1)
    | .eqn e => [e.name]
    | .macro n _ _ _ => [n]
    | .core c _ _ => [c]
    | .qdef n _ => [n]
    | .sig _ _ => []
  let leaves := o.leaves.map (·.1)
  let steps := fun (l : Nm) (k : Nat) =>
    if leaves.contains l then
      ((List.range k).reverse.map fun i => nm! "step" ++ l ++ decimal (i + 1)) ++ [nm! "step" ++ l]
    else []
  let names := [nm! "spApp", nm! "sp", nm! "rb1", nm! "rb"] ++ leaves.map (nm! "res" ++ ·) ++
    steps [73] 1 ++ steps [75] 2 ++ steps [83] 3
  let top := names.filter fun n => !taken.contains n
  let perCore := ds.filterMap fun d =>
    match d with
    | .core c _ eqs =>
      if isInterp o eqs then
        let have_ := eqs.map (·.1)
        some (c, (if have_.contains (nm! "step") then [] else [nm! "step"]) ++
          (if have_.contains (nm! "loop") then [] else [nm! "loop", nm! "loop1"]))
      else none
    | _ => none
  (top, perCore)

/-- Pass one (`_collect`): the environment, and whether a name is declared
    twice, a core defines an equation twice, or the object or path type is
    malformed. -/
def collectA (ds : List Decl) : AEnv × Bool :=
  let step := fun (st : List Nm × List TypeDecl × Bool) (d : Decl) =>
    let (seen, tys, bad) := st
    let declare := fun (seen : List Nm) (bad : Bool) (n : Nm) => (seen ++ [n], bad || seen.contains n)
    match d with
    | .ty t =>
      let (seen, bad) := declare seen bad t.name
      if tys.any (·.name == t.name) then (seen, tys, bad)
      else
        let (seen, bad) := t.ctors.foldl (fun (sb : List Nm × Bool) c => declare sb.1 sb.2 c.1) (seen, bad)
        (seen, tys ++ [t], bad)
    | .macro n _ _ _ => let (seen, bad) := declare seen bad n; (seen, tys, bad)
    | .eqn e => let (seen, bad) := declare seen bad e.name; (seen, tys, bad)
    | .core c _ eqs =>
      let (seen, bad) := declare seen bad c
      (seen, tys, bad || !nodup (eqs.map (·.1)))
    | .qdef n _ => let (seen, bad) := declare seen bad n; (seen, tys, bad)
    | .sig _ _ => (seen, tys, bad)
  let (_, tys, bad) := ds.foldl step ([], [], false)
  let ctors := tys.flatMap fun t => t.ctors.map fun c => (c.1, t.name, c.2)
  let allTys := ds.filterMap fun d => match d with | .ty t => some t | _ => none
  let macros := ds.filterMap fun d => match d with | .macro n _ _ _ => some n | _ => none
  let eqs := ds.filterMap fun d =>
    match d with
    | .eqn e => some (e.name, e.params.length)
    | .qdef n _ => some (n, 0)
    | _ => none
  let cores := ds.filterMap fun d =>
    match d with
    | .core c ps eqs => some (c, ps, eqs.map fun q => (q.1, q.2.1.length))
    | _ => none
  let (obj, path, gen, coreGen, gbad) :=
    match findObject allTys, findPath allTys with
    | some o, some p =>
      match o with
      | some ob => let g := genAdds ds ob; (o, p, g.1, g.2, false)
      | none => (o, p, [], [], false)
    | some o, none => (o, none, [], [], true)
    | none, _ => (none, none, [], [], true)
  (⟨tys, ctors, macros, eqs, cores, gen, coreGen, obj, path⟩, bad || gbad)

/-- A constructor's type and arity. -/
def AEnv.ctor (env : AEnv) (n : Nm) : Option (Nm × Nat) := env.ctors.lookup n

/-- `provably_function`: an expression Stage A can prove is a function. -/
def AEnv.provablyFn (env : AEnv) (core : Option Nm) (bound : List Nm) (e : Expr) : Bool :=
  match e with
  | .quote .. | .run .. | .scry _ | .cell _ => false
  | .lam _ _ => true
  | .nslit _ => true
  | _ =>
    match spineA e with
    | (.name n, args) =>
      if bound.contains n then false
      else if isISA n || tier1Names.contains n then true
      else
        match env.ctor n with
        | some (_, k) => args.length < k
        | none =>
          if env.macros.contains n then true
          else if (lastLookup env.eqns n).any (· > 0) then true
          else if (match core with
            | some c => ((lastLookup env.cores c).bind fun p => lastLookup p.2 n).any (· > 0)
            | none => false) then true
          else env.cores.any (·.1 == n)
    | _ => false

/-- `path_literal`: the path type exists, and each segment is a nullary
    constructor of its segment type, without a payload. -/
def AEnv.pathBad (env : AEnv) (p : List (Nm × Bool)) : Bool :=
  match env.path with
  | none => true
  | some (_, _, seg) =>
    p.any fun s =>
      s.2 ||
        match env.ctor (capital s.1) with
        | some (t, k) => t != seg || k != 0
        | none => true

/-- A name at the head of an application of `k` arguments inside `< >`: a
    constructor of the object type, or a level-0 name, a constructor of
    another type applied to exactly its fields. -/
def AEnv.quotedHead (env : AEnv) (n : Nm) (k : Nat) : Bool :=
  if (match env.obj with | some o => o.decl.ftys.any (·.1 == n) | none => false) then false
  else if env.known n none then
    match env.ctor n with
    | some (_, a) => k != a
    | none => false
  else true

mutual
  /-- `quoted`: inside `< >`, §6b's level-1 table. -/
  def AEnv.quotedBad (env : AEnv) : Expr → Bool
    | .scry p =>
      env.pathBad p ||
        (match env.obj with
         | some o => !o.leaves.any (·.1 == nm! "Scry")
         | none => false)
    | .quote e fu => (match fu with | .none => false | _ => true) || env.quotedBad e
    | .run _ _ _ => true
    | .nslit _ => true
    | .lam _ b => env.quotedBad b
    | .cell items => env.quotedBadI items
    | .pick _ e => env.quotedBad e
    | .case e bs => env.quotedBad e || env.quotedBadB bs
    | .name n => env.quotedHead n 0
    | .app f a =>
      env.quotedBad a ||
        match f with
        | .app .. | .name _ => env.quotedFn f 1
        | _ => env.quotedBad f
  /-- The function part of an application inside `< >`, an application or a
      name, with `k` arguments already checked: each further argument, then
      the head. -/
  def AEnv.quotedFn (env : AEnv) : Expr → Nat → Bool
    | .app f a, k =>
      env.quotedBad a ||
        match f with
        | .app .. | .name _ => env.quotedFn f (k + 1)
        | _ => env.quotedBad f
    | .name n, k => env.quotedHead n k
    | _, _ => false
  def AEnv.quotedBadB (env : AEnv) : Branches → Bool
    | .nil => false
    | .cons _ _ body rest => env.quotedBad body || env.quotedBadB rest
  def AEnv.quotedBadI (env : AEnv) : Items → Bool
    | .nil => false
    | .cons e rest => env.quotedBad e || env.quotedBadI rest
end

/-- A case's branches, as a list. -/
def Branches.toList : Branches → List (Nm × List Nm × Expr)
  | .nil => []
  | .cons c xs b r => (c, xs, b) :: r.toList

/-- (b): every branch a constructor of the first branch's type, none
    repeated, none missing. -/
def AEnv.caseBad (env : AEnv) (bs : Branches) : Bool :=
  let cs := bs.toList.map (·.1)
  match cs with
  | [] => true
  | c0 :: _ =>
    match env.ctor c0 with
    | none => true
    | some (t, _) =>
      cs.any (fun c => (env.ctor c).all (·.1 != t)) || !nodup cs ||
        match env.tys.find? (·.name == t) with
        | some d => d.ctors.any fun p => !cs.contains p.1
        | none => true

/-- (c): an argument of `EQ`, among its first two, that is provably a
    function. -/
def AEnv.eqBad (env : AEnv) (core : Option Nm) (bound : List Nm) (e : Expr) : Bool :=
  match spineA e with
  | (.name n, args) => n == nm! "EQ" && (args.take 2).any (env.provablyFn core bound)
  | _ => false

mutual
  /-- The level-0 walk (`expr`): names resolve unless in a macro body, and
      the case, `EQ` and quotation checks. -/
  def AEnv.exprBad (env : AEnv) (core : Option Nm) (bound : List Nm) (inMacro : Bool) : Expr → Bool
    | .name n => !(bound.contains n || inMacro || env.known n core)
    | .app f a =>
      env.eqBad core bound (.app f a) || env.exprBad core bound inMacro f ||
        env.exprBad core bound inMacro a
    | .cell items => env.exprBadI core bound inMacro items
    | .pick _ e => env.exprBad core bound inMacro e
    | .lam x b => env.exprBad core (x :: bound) inMacro b
    | .case e bs => env.exprBad core bound inMacro e || env.caseBad bs || env.exprBadB core bound inMacro bs
    | .quote e _ => env.quotedBad e
    | .run i e _ => env.exprBad core bound inMacro i || env.quotedBad e
    | .scry _ => true
    | .nslit _ => true
  def AEnv.exprBadB (env : AEnv) (core : Option Nm) (bound : List Nm) (inMacro : Bool) : Branches → Bool
    | .nil => false
    | .cons _ xs body rest =>
      env.exprBad core (xs ++ bound) inMacro body || env.exprBadB core bound inMacro rest
  def AEnv.exprBadI (env : AEnv) (core : Option Nm) (bound : List Nm) (inMacro : Bool) : Items → Bool
    | .nil => false
    | .cons e rest => env.exprBad core bound inMacro e || env.exprBadI core bound inMacro rest
end

/-- `interp_application`: the interpreter left of `|-` is a core applied to
    all its parameters. -/
def AEnv.interpBad (env : AEnv) (i : Expr) : Bool :=
  match spineA i with
  | (.name c, args) =>
    match lastLookup env.cores c with
    | some (ps, _) => args.length != ps.length
    | none => true
  | _ => true

/-- A definition whose right side is level 1 (`definition`). -/
def AEnv.qdefBad (env : AEnv) : Expr → Bool
  | .nslit facts =>
    facts.toList.any fun (p, v) =>
      env.pathBad p ||
        match v with
        | .quote e .none => env.quotedBad e
        | _ => true
  | .quote e _ => env.quotedBad e
  | .run i e _ => env.interpBad i || env.quotedBad e
  | _ => false

/-- (d) an interpreter core's interface (`interface`, `step_arm`). -/
def AEnv.interfaceBad (env : AEnv) (eqs : List (Nm × List Nm × Expr)) : Bool :=
  match env.obj with
  | none => false
  | some o =>
    if !isInterp o eqs then false
    else
      let leaves := o.leaves.map (·.1)
      let written := fun (n : Nm) => lastLookup eqs n
      eqs.any (fun q => q.1 == nm! "step" ++ o.app) ||
      (match written (nm! "step") with
       | some (bs, body) =>
         if bs.length != 1 then true
         else
           match spineA body with
           | (.name sp, args) =>
             if sp != nm! "sp" then false
             else if args.length != 2 + leaves.length then true
             else
               let got := (args.drop 2).map fun x =>
                 match spineA x with
                 | (.name h, _) => some h
                 | _ => none
               let want := leaves.map (nm! "step" ++ ·)
               let named := got.filterMap id
               named.length == got.length && named.all (fun g => g.take 4 == nm! "step") &&
                 named.isPerm want && named != want
           | _ => false
       | none => false) ||
      (match written (nm! "loop") with
       | some (bs, _) => bs.length != 2
       | none => false) ||
      ((written (nm! "loop1")).isSome && (written (nm! "loop")).isNone) ||
      (match written (nm! "loop1") with
       | some (bs, _) => bs.length != 3
       | none => false)

/-- **Stage A** (`check.py`), over the parsed program: `true` when it finds
    a problem, and the program is refused. -/
def stageA (ds : List Decl) : Bool :=
  let (env, bad) := collectA ds
  bad || ds.any fun d =>
    match d with
    | .eqn e => env.exprBad none e.params false e.body
    | .macro _ ps b _ => env.exprBad none ps true b
    | .core c ps eqs =>
      eqs.any (fun q => env.exprBad (some c) (ps ++ q.2.1) false q.2.2) || env.interfaceBad eqs
    | .qdef _ e => env.qdefBad e
    | _ => false

end Front
