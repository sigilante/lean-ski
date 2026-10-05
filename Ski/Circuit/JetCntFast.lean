import Ski.Circuit.JetHonest

/-!
# A jet run's lookup counts, from its instantiations listed once

`JRun.cntRoots K v`, `cntHdr` and `cntTmpl` sum over the run's first `K`
rows, each row asking `instAt` whether it instantiates a jet.  A provider
table asks for one count per row, so evaluating them directly costs
`K` rows per provider row.  Here the instantiations are listed once
(`insts`), and each count is a fold over that list (`cntRoots_eq`,
`cntHdr_eq`, `cntTmpl_eq`).  And `firstOcc`, which compares a row with
every earlier one, reads the rows from an array (`firstOcc_arr`).

`lake exe composed check-cj-tables` uses them to compare the provider
tables with Lean's.
-/

namespace Circuit

open B Air JetTable Mach

/-- A fold that adds each term: its start added at the end. -/
theorem foldr_add_start {α : Type} (h : Nat → α → Nat) : ∀ (L : List (Nat × α)) (c : Nat),
    L.foldr (fun p acc => h p.1 p.2 + acc) c = L.foldr (fun p acc => h p.1 p.2 + acc) 0 + c
  | [], c => (Nat.zero_add c).symm
  | p :: L, c => by rw [List.foldr_cons, List.foldr_cons, foldr_add_start h L c, Nat.add_assoc]

/-- A sum over `K` rows of a term that vanishes off `o`'s `some`, as a fold
    over the rows where `o` is `some`. -/
theorem sumTo_filterMap {α : Type} (o : Nat → Option α) (h : Nat → α → Nat) : ∀ K,
    sumTo K (fun i => match o i with | some a => h i a | none => 0) =
      ((List.range K).filterMap fun i => (o i).map (i, ·)).foldr (fun p acc => h p.1 p.2 + acc) 0
  | 0 => rfl
  | K + 1 => by
    show sumTo K _ + _ = _
    rw [sumTo_filterMap o h K, List.range_succ, List.filterMap_append, List.foldr_append,
      foldr_add_start h _ (List.foldr _ 0 _)]
    congr 1
    cases ho : o K with
    | none => simp only [List.filterMap_cons, List.filterMap_nil, ho, Option.map_none, List.foldr_nil]
    | some a =>
      simp only [List.filterMap_cons, List.filterMap_nil, ho, Option.map_some, List.foldr_cons, List.foldr_nil,
        Nat.add_zero]

/-- The same, for any term that is that match pointwise. -/
theorem sumTo_filterMap' {α : Type} (o : Nat → Option α) (h : Nat → α → Nat) (f : Nat → Nat)
    (hf : ∀ i, f i = match o i with | some a => h i a | none => 0) (K : Nat) :
    sumTo K f = ((List.range K).filterMap fun i => (o i).map (i, ·)).foldr (fun p acc => h p.1 p.2 + acc) 0 := by
  rw [show f = _ from funext hf]; exact sumTo_filterMap o h K

namespace JRun

variable (R : JRun)

/-- The instantiations among the first `K` rows: row, jet index, jet. -/
def insts (K : Nat) : List (Nat × (Nat × Air.Jet)) :=
  (List.range K).filterMap fun i => (R.instAt i).map (i, ·)

theorem cntRoots_eq (K : Nat) (v : List F) :
    R.cntRoots K v = (R.insts K).foldr (fun p acc =>
      (if [ofN (R.row p.1).hd, ofN p.2.1] = v then 1 else 0) + acc) 0 :=
  sumTo_filterMap' R.instAt (fun i gJ => if [ofN (R.row i).hd, ofN gJ.1] = v then 1 else 0) _
    (fun i => by cases R.instAt i with | none => rfl | some a => obtain ⟨g, J⟩ := a; rfl) K

theorem cntHdr_eq (K : Nat) (v : List F) :
    R.cntHdr K v = (R.insts K).foldr (fun p acc => (if hdrRow p.2.2 p.2.1 = v then 1 else 0) + acc) 0 :=
  sumTo_filterMap' R.instAt (fun _ gJ => if hdrRow gJ.2 gJ.1 = v then 1 else 0) _
    (fun i => by cases R.instAt i with | none => rfl | some a => obtain ⟨g, J⟩ := a; rfl) K

theorem cntTmpl_eq (K : Nat) (v : List F) :
    R.cntTmpl K v = (R.insts K).foldr (fun p acc =>
      ((symCells p.2.2 p.2.2.body 0).1.zipIdx.map fun x => if tmplRow p.2.1 x.2 x.1 = v then 1 else 0).sum + acc) 0 := by
  unfold cntTmpl insts
  apply sumTo_filterMap' R.instAt
    (fun _ gJ => ((symCells gJ.2 gJ.2.body 0).1.zipIdx.map fun x => if tmplRow gJ.1 x.2 x.1 = v then 1 else 0).sum)
  intro i
  cases R.instAt i with
  | none => rfl
  | some a => obtain ⟨g, J⟩ := a; rfl

end JRun

/-- `firstOcc`, its rows read from an array. -/
theorem firstOcc_arr (rows : List (List F)) (q : Nat) :
    firstOcc rows q = (List.range q).all fun q' => !(decide (rows.toArray.getD q' [] = rows.toArray.getD q [])) := by
  unfold firstOcc
  have e : ∀ i, rows.toArray.getD i [] = rows.getD i [] := fun i => by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  simp only [e]

end Circuit
