import Ski.Witness
open Term

/-!
# A hidden-term statement's text

`public.txt` of the witness circuit, as `lake exe witness statement` checks
it and the verifier's Lean comparison of its circuit reads it: an atom
`V x`, a region size, and the witness machine with the region blank
(`publicText`), parsed back only when it is exactly that text
(`statementOfText`).
-/

namespace WitnessText

open Mach Wit

def termText : Term → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .app f a => "`" ++ termText f ++ termText a

/-- A term in prefix form, with fuel for the recursion. -/
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

def cellText : Cell → String
  | .S => "S"
  | .K => "K"
  | .I => "I"
  | .nil => "N"
  | .app f x => s!"A {f} {x}"
  | .cons x r => s!"C {x} {r}"
  | .atom n => s!"X {n}"

def words (l : String) : List String := (l.splitOn " ").filter (· ≠ "")

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

/-- The region holding `w` at its last cell: filler `S` cells, then `w`'s
    cells, children first.  `none` when `w` does not fit in `W` cells. -/
def regionOf (W : Nat) (w : Term) : Option (List Cell) :=
  let n := (build [] w).1.length
  if n ≤ W then some (build (List.replicate (W - n) .S) w).1 else none

/-- **The statement** of an atom and a region size: `public.txt`.  The heap
    is the witness machine's with the region blank; by
    `Wit.wMachine_public` it states the machine for every region of that
    size. -/
def publicText (V x : Term) (W : Nat) : String := Id.run do
  let m := wMachine (List.replicate W .S) (V ⬝ x)
  let mut s := s!"V {termText V}\nx {termText x}\nW {W}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if i < W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- The atom and region size a statement names, if the text is exactly
    their statement. -/
def statementOfText (text : String) : Option (Term × Term × Nat) := do
  let ls := text.splitOn "\n"
  let V ← match words (ls.getD 0 "") with
    | ["V", t] => parseTerm t
    | _ => none
  let x ← match words (ls.getD 1 "") with
    | ["x", t] => parseTerm t
    | _ => none
  let W ← match words (ls.getD 2 "") with
    | ["W", n] => n.toNat?
    | _ => none
  if 0 < W && text == publicText V x W then some (V, x, W) else none

end WitnessText
