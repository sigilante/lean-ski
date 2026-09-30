import Ski.Composed
import Ski.Predicate
open Term

/-!
# A composed statement's text

`public.txt` as `lake exe composed statement` checks it and the verifier's
Lean comparison of its circuit reads it: a statement, a region size, and
the composed machine with the private cells blank (`publicText`), parsed
back only when it is exactly that text (`statementOfText`).  A statement is
a formula of atoms (`formula …`) or a predicate over literal bits
(`predicate V x n`, `Ski/Predicate.lean`).
-/

namespace ComposedText

open Mach Compose CompM

/-- A term's prefix form appended to `s`: linear in the term, where
    concatenating the halves' strings is quadratic on a deep spine. -/
def termTextTo : Term → String → String
  | .S, s => s.push 'S'
  | .K, s => s.push 'K'
  | .I, s => s.push 'I'
  | .app f a, s => termTextTo a (termTextTo f (s.push '`'))

def termText (t : Term) : String := termTextTo t ""

def parseTermF : Nat → List Char → Option (Term × List Char)
  | 0, _ => none
  | _ + 1, 'S' :: r => some (.S, r)
  | _ + 1, 'K' :: r => some (.K, r)
  | _ + 1, 'I' :: r => some (.I, r)
  | n + 1, '`' :: r => do
    let (f, r1) ← parseTermF n r
    let (a, r2) ← parseTermF n r1
    some (.app f a, r2)
  | _ + 1, _ => none

def parseTerm (s : String) : Option Term :=
  match parseTermF (s.length + 1) s.toList with
  | some (t, []) => some t
  | _ => none

def formulaText : MF → String
  | .atom V x => s!"A {termText V} {termText x}"
  | .and A B => s!"& {formulaText A} {formulaText B}"
  | .or A B => s!"| {formulaText A} {formulaText B}"

def parseFormulaF : Nat → List String → Option (MF × List String)
  | 0, _ => none
  | _ + 1, "A" :: v :: x :: r => do some (.atom (← parseTerm v) (← parseTerm x), r)
  | n + 1, "&" :: r => do
    let (a, r1) ← parseFormulaF n r
    let (b, r2) ← parseFormulaF n r1
    some (.and a b, r2)
  | n + 1, "|" :: r => do
    let (a, r1) ← parseFormulaF n r
    let (b, r2) ← parseFormulaF n r1
    some (.or a b, r2)
  | _ + 1, _ => none

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

def parseFormula (ws : List String) : Option MF :=
  match parseFormulaF (ws.length + 1) ws with
  | some (m, []) => some m
  | _ => none

def cellText : Cell → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .nil => "N"
  | .app f x => s!"A {f} {x}"
  | .cons x r => s!"C {x} {r}"
  | .atom n => s!"X {n}"

def parseCell (ws : List String) : Option Cell :=
  match ws with
  | ["S"] => some .S
  | ["K"] => some .K
  | ["I"] => some .I
  | ["N"] => some .nil
  | ["A", f, x] => do some (.app (← f.toNat?) (← x.toNat?))
  | ["C", x, r] => do some (.cons (← x.toNat?) (← r.toNat?))
  | ["X", n] => do some (.atom (← n.toNat?))
  | _ => none

def parseRow (ws : List String) : Option Air.Row :=
  match ws with
  | [h, s, c] => do some ⟨← h.toNat?, ← s.toNat?, ← c.toNat?⟩
  | _ => none

/-- The region holding `w` at its last cell, after `N` bit cells: filler `S`
    cells, then `w`'s cells, children first, at their absolute addresses. -/
def regionOf' (N W : Nat) (w : Term) : Option (List Cell) :=
  let pre := List.replicate (N + 3) Cell.S
  let n := (build pre w).1.length - (N + 3)
  if n ≤ W then some ((build (pre ++ List.replicate (W - n) .S) w).1.drop (N + 3)) else none

/-- **A composed statement**: a formula of atoms, or a predicate `V x` over
    `n` literal bits. -/
inductive CStmt
  | formula (M : MF)
  | pred (V x : Term) (n : Nat)

/-- Its bits' shape. -/
def CStmt.shp : CStmt → BT
  | .formula M => clear M
  | .pred _ _ n => combBT n

/-- Its terms, each to evaluate to `K` on the bits and the witness. -/
def CStmt.Ps : CStmt → List Term
  | .formula M => stmtOf M
  | .pred V x _ => [predStmt V x]

/-- Its first line. -/
def CStmt.header : CStmt → String
  | .formula M => s!"formula {formulaText M}"
  | .pred V x n => s!"predicate {termText V} {termText x} {n}"

def parseHeader (ws : List String) : Option CStmt :=
  match ws with
  | "formula" :: r => (parseFormula r).map .formula
  | ["predicate", v, x, n] => do
    let n ← n.toNat?
    if n = 0 then none else some (.pred (← parseTerm v) (← parseTerm x) n)
  | _ => none

/-- The CPU's and the memory's log heights when a statement names none. -/
def defaultLog : Nat × Nat := (11, 11)

/-- The log heights a statement may name: each in `[8, 20]`. -/
def logOK (lg : Nat × Nat) : Bool := 8 ≤ lg.1 && lg.1 ≤ 20 && 8 ≤ lg.2 && lg.2 ≤ 20

/-- **The statement** of a formula, a region size and the log heights of
    the CPU and the memory: `public.txt`.  The heap is the composed
    machine's with the bit cells and the region blank; by
    `CompM.cMachine_public` it states the machine for every witness of that
    size.  The heights take a line, `log R M`, only when they are not the
    default, so the statements written before it are unchanged. -/
def publicTextC (c : CStmt) (W : Nat) (lg : Nat × Nat := defaultLog) : String := Id.run do
  let shp := c.shp
  let N := BT.nleaves shp
  let region := List.replicate W Cell.S
  let m := cMachine (fun _ => false) shp region c.Ps
  let roots := (cHeap (fun _ => false) shp region c.Ps).2
  let logLine := if lg == defaultLog then "" else s!"log {lg.1} {lg.2}\n"
  let mut s := s!"{c.header}\nW {W}\n{logLine}bits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- A formula's statement. -/
def publicText (M : MF) (W : Nat) (lg : Nat × Nat := defaultLog) : String := publicTextC (.formula M) W lg

/-- The private cells the witness table holds: the bits and the region. -/
def privateOK (c : CStmt) (W : Nat) : Bool := 0 < W && BT.nleaves c.shp + W ≤ 2 ^ 8

def statementOfText (text : String) : Option (CStmt × Nat × (Nat × Nat)) := do
  let ls := text.splitOn "\n"
  let c ← parseHeader (words (ls.getD 0 ""))
  let W ← match words (ls.getD 1 "") with
    | ["W", n] => n.toNat?
    | _ => none
  let lg ← match words (ls.getD 2 "") with
    | ["log", r, m] => do some (← r.toNat?, ← m.toNat?)
    | _ => some defaultLog
  if privateOK c W && logOK lg && text == publicTextC c W lg then some (c, W, lg) else none

end ComposedText
