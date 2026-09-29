import Ski.Composed
open Term

/-!
# A composed statement's text

`public.txt` as `lake exe composed statement` checks it and the verifier's
Lean comparison of its circuit reads it: a formula and a region size, and
the composed machine with the private cells blank (`publicText`), parsed
back only when it is exactly that text (`statementOfText`).
-/

namespace ComposedText

open Mach Compose CompM

def termText : Term → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .app f a => "`" ++ termText f ++ termText a

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

/-- **The statement** of a formula and a region size: `public.txt`.  The
    heap is the composed machine's with the bit cells and the region blank;
    by `CompM.cMachine_public` it states the machine for every witness of
    that size. -/
def publicText (M : MF) (W : Nat) : String := Id.run do
  let shp := clear M
  let N := BT.nleaves shp
  let region := List.replicate W Cell.S
  let m := cMachine (fun _ => false) shp region (stmtOf M)
  let roots := (cHeap (fun _ => false) shp region (stmtOf M)).2
  let mut s := s!"formula {formulaText M}\nW {W}\nbits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

def statementOfText (text : String) : Option (MF × Nat) := do
  let ls := text.splitOn "\n"
  let M ← match words (ls.getD 0 "") with
    | "formula" :: ws => parseFormula ws
    | _ => none
  let W ← match words (ls.getD 1 "") with
    | ["W", n] => n.toNat?
    | _ => none
  if 0 < W && text == publicText M W then some (M, W) else none

end ComposedText
