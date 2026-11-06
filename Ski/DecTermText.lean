import Ski.ComposedDText
import Ski.Layout

/-!
# The text of a `decterm` statement

`publicTextDG Vs W lg` and `statementOfTextDG`: a composed statement with
the `dec` jet for any list of public verifiers open in the jet's atom,
read off the statement's heap.  What an accepted proof of one means is
`Ski/DecTerm.lean`.

Each is an instance of a form over a layout and a header word
(`publicTextDGL`, `statementOfTextDGL`): `decterm` for the statement as a
tree (`treeL`, the audited texts), `dectermS` for the statement shared
(`sharedL`, `publicTextDGS`, `statementOfTextDGS`).  The heap is read the
same way either way, every cell over earlier ones (`decodeDG`).
-/

namespace DecTerm

open Compose CompM ComposedText ComposedDText DecJet

/-- The verifier of a check term that ignores the bit and the witness. -/
def verT (C : OTerm) : OTerm := absN [0, 1] C

/-- Every variable of the verifier is the jet's. -/
def occOK (V : OTerm) : Bool := V.vars.all (· == JD)

theorem occOK_sound {V : OTerm} (h : occOK V = true) : ∀ x, Occ x V → x = JD := fun x hx => by
  have hm := (OTerm.mem_vars x V).1 (OTerm.mem_of_occ hx)
  have := List.all_eq_true.1 h x hm
  exact beq_iff_eq.1 this

/-- **The statement's text** in layout `L`: `publicTextD`'s layout, header
    `kw J`. -/
def publicTextDGL (L : Layout) (kw : String) (Vs : List OTerm) (W : Nat) (lg : DLogs) : String := Id.run do
  let N := BT.nleaves shpD
  let region := List.replicate W Cell.S
  let m := L.mach (fun _ => false) shpD region Vs
  let roots := (L.heap (fun _ => false) shpD region Vs).2
  let mut s := s!"{kw} {JD}\nW {W}\nlog {lg.rows} {lg.mem} {lg.dec}\nbits {N}\nroots {" ".intercalate (roots.map toString)}\nnil {m.stk}\n{m.hd} {m.stk} {m.heap.length}\n"
  let mut i := 0
  for c in m.heap do
    s := s ++ (if 3 ≤ i && i < N + 3 + W then "W" else cellText c) ++ "\n"
    i := i + 1
  return s

/-- The statement's text as a tree, header `decterm J`. -/
def publicTextDG (Vs : List OTerm) (W : Nat) (lg : DLogs) : String := publicTextDGL treeL "decterm" Vs W lg

/-- The statement's text shared, header `dectermS J`. -/
def publicTextDGS (Vs : List OTerm) (W : Nat) (lg : DLogs) : String := publicTextDGL sharedL "dectermS" Vs W lg

/-- The heap's cells read as open terms, each over earlier cells; a blank
    or a cell that does not read is `K` (the re-emitted text decides). -/
def decodeDG (cells : Array (Option Cell)) : Array OTerm := Id.run do
  let mut D : Array OTerm := #[]
  for i in [0:cells.size] do
    let t : OTerm := match cells[i]! with
      | some .S => .S
      | some .K => .K
      | some .I => .I
      | some (.atom x) => .var x
      | some (.app f a) => if f < i && a < i then .app D[f]! D[a]! else .K
      | _ => .K
    D := D.push t
  return D

/-- The text's parts: the verifiers read off the heap, the region size and
    the heights. -/
def parseDGK (kw text : String) : Option (List OTerm × Nat × DLogs) := do
  let ls := text.splitOn "\n"
  match words (ls.getD 0 "") with
    | [k, j] => if k == kw && j == toString JD then some () else none
    | _ => none
  let W ← match words (ls.getD 1 "") with
    | ["W", n] => n.toNat?
    | _ => none
  let lg ← match words (ls.getD 2 "") with
    | ["log", r, m, d] => do some ⟨← r.toNat?, ← m.toNat?, ← d.toNat?⟩
    | _ => none
  let roots ← match words (ls.getD 4 "") with
    | "roots" :: rs => rs.mapM String.toNat?
    | _ => none
  let n ← match words (ls.getD 6 "") with
    | [_, _, n] => n.toNat?
    | _ => none
  let cells : Array (Option Cell) := ((ls.drop 7).take n).toArray.map fun l =>
    if l == "W" then none else parseCell (words l)
  let D := decodeDG cells
  let Vs := roots.map fun r =>
    match cells[r]? with
    | some (some (.app a _)) =>
      match cells[a]? with
      | some (some (.app pp _)) => D.getD pp .K
      | _ => .K
    | _ => .K
  some (Vs, W, lg)

def parseDG (text : String) : Option (List OTerm × Nat × DLogs) := parseDGK "decterm" text

/-- What the verifiers must satisfy: at least one, each open only in the
    jet's atom. -/
def vsOK (Vs : List OTerm) : Bool := decide (0 < Vs.length) && Vs.all occOK

theorem vsOK_sound {Vs : List OTerm} (h : vsOK Vs = true) :
    0 < Vs.length ∧ ∀ V ∈ Vs, ∀ x, Occ x V → x = JD := by
  simp only [vsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun V hV => occOK_sound (List.all_eq_true.1 h.2 V hV)⟩

/-- What an accepted text must satisfy, in layout `L` under header `kw`. -/
def checkDGL (L : Layout) (kw text : String) (Vs : List OTerm) (W : Nat) (lg : DLogs) : Bool :=
  vsOK Vs && regionOKD W && dlogsOK lg && text == publicTextDGL L kw Vs W lg

/-- **The statement**, parsed back only when it is exactly `publicTextDGL`'s
    text of the verifiers its heap holds. -/
def statementOfTextDGL (L : Layout) (kw text : String) : Option (List OTerm × Nat × DLogs) :=
  match parseDGK kw text with
  | some (Vs, W, lg) => if checkDGL L kw text Vs W lg then some (Vs, W, lg) else none
  | none => none

theorem statementOfTextDGL_check {L : Layout} {kw text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDGL L kw text = some (Vs, W, lg)) : checkDGL L kw text Vs W lg = true := by
  unfold statementOfTextDGL at h
  cases hp : parseDGK kw text with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨Vs', W', lg'⟩ := r
    rw [hp] at h
    dsimp only at h
    cases hc : checkDGL L kw text Vs' W' lg' with
    | false => rw [hc, if_neg Bool.false_ne_true] at h; cases h
    | true =>
      rw [hc, if_pos rfl] at h
      cases h
      exact hc

/-- An accepted text's verifiers are `vsOK`. -/
theorem statementOfTextDGL_vsOK {L : Layout} {kw text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDGL L kw text = some (Vs, W, lg)) : vsOK Vs = true := by
  have hc := statementOfTextDGL_check h
  simp only [checkDGL, Bool.and_eq_true] at hc
  exact hc.1.1.1

/-- The text names its verifiers exactly. -/
theorem statementOfTextDGL_text {L : Layout} {kw text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDGL L kw text = some (Vs, W, lg)) : text = publicTextDGL L kw Vs W lg := by
  have hc := statementOfTextDGL_check h
  simp only [checkDGL, Bool.and_eq_true, beq_iff_eq] at hc
  exact hc.2

/-- What an accepted text must satisfy. -/
def checkDG (text : String) (Vs : List OTerm) (W : Nat) (lg : DLogs) : Bool :=
  checkDGL treeL "decterm" text Vs W lg

/-- **The statement**, parsed back only when it is exactly `publicTextDG`'s
    text of the verifiers its heap holds. -/
def statementOfTextDG (text : String) : Option (List OTerm × Nat × DLogs) :=
  statementOfTextDGL treeL "decterm" text

theorem statementOfTextDG_check {text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDG text = some (Vs, W, lg)) : checkDG text Vs W lg = true :=
  statementOfTextDGL_check h

/-- An accepted text's verifiers are `vsOK`. -/
theorem statementOfTextDG_vsOK {text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDG text = some (Vs, W, lg)) : vsOK Vs = true :=
  statementOfTextDGL_vsOK h

/-- The text names its verifiers exactly. -/
theorem statementOfTextDG_text {text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDG text = some (Vs, W, lg)) : text = publicTextDG Vs W lg :=
  statementOfTextDGL_text h

/-- **The shared statement**, header `dectermS`: parsed back only when it is
    exactly `publicTextDGS`'s text of the verifiers its heap holds. -/
def statementOfTextDGS (text : String) : Option (List OTerm × Nat × DLogs) :=
  statementOfTextDGL sharedL "dectermS" text

theorem statementOfTextDGS_vsOK {text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDGS text = some (Vs, W, lg)) : vsOK Vs = true :=
  statementOfTextDGL_vsOK h

theorem statementOfTextDGS_text {text : String} {Vs : List OTerm} {W : Nat} {lg : DLogs}
    (h : statementOfTextDGS text = some (Vs, W, lg)) : text = publicTextDGS Vs W lg :=
  statementOfTextDGL_text h

end DecTerm
