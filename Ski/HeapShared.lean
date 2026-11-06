import Ski.ComposedO

/-!
# A shared statement heap

`obuild` writes an open term as a tree: every node a fresh cell, so a
subterm that occurs a thousand times takes a thousand copies.  The compiled
Nock programs are such terms: skinock's jetted loop statement is 2,329,975
cells as a tree and 2,449 as a DAG.

`obuildS` writes the same term hash-consed.  It builds the children first,
then looks the cell up in a memo of the cells it has itself allocated, and
allocates only on a miss.  Every memo entry `c ↦ q` has `heap[q] = c` and,
for an application, its children below `q` (`MemoOK`), so a cell found in
the memo reads back as the term it was built for (`obuildS_spec`), as
`obuild_spec` gives for the tree.  The memo starts empty past whatever heap
it is given, and holds only cells `obuildS` wrote, so a public cell never
aliases a private one: the builder reads the heap's length and its own
memo, nothing else (`obuildS_shape`).

Sharing is safe for the machines that run on such a heap because none of
them writes a cell in place.  A composed run's heap at a row is the prefix
`M.take r.ctr` of one memory table (`Air.st`); the statement is the prefix
at the first row (`AcceptsCD.heap0`); the counter only grows
(`normRowD_spec`, `AcceptsCD.within`); a step appends (`mstep_append`) and
the `dec` row writes its outcome at the counter (`DecJet.decRow`).  So a
public cell, shared or not, holds the same cell at every row.
-/

namespace Mach

/-- A cell's bucket key. -/
def cellKey : Cell → Nat
  | .S => 1
  | .K => 2
  | .I => 3
  | .app f a => 4 + 7 * f + 131 * a
  | .nil => 5
  | .cons x r => 6 + 11 * x + 137 * r
  | .atom n => 7 + 13 * n

/-- The memo's bucket count. -/
def memoBuckets : Nat := 4096

/-- A cell's bucket. -/
def cellIdx (c : Cell) : Nat := cellKey c % memoBuckets

/-- **The memo**: each cell the shared builder wrote, at its address, in a
    table of `memoBuckets` association lists.  A table, not a `HashMap`, so
    that its one law (`Memo.find_add`) needs no axiom past `propext`. -/
structure Memo where
  tab : Array (List (Cell × Nat))
  size_eq : tab.size = memoBuckets

/-- The empty memo. -/
def Memo.empty : Memo := ⟨Array.replicate memoBuckets [], Array.size_replicate⟩

/-- The address the memo holds for a cell. -/
def Memo.find (m : Memo) (c : Cell) : Option Nat :=
  ((m.tab[cellIdx c]?).getD []).lookup c

/-- The memo with `c ↦ q` added. -/
def Memo.add (m : Memo) (c : Cell) (q : Nat) : Memo :=
  ⟨m.tab.setIfInBounds (cellIdx c) ((c, q) :: (m.tab[cellIdx c]?).getD []),
    by rw [Array.size_setIfInBounds, m.size_eq]⟩

theorem Memo.find_empty (c : Cell) : Memo.empty.find c = none := by
  unfold Memo.find Memo.empty
  rw [Array.getElem?_replicate]
  split <;> rfl

theorem cellIdx_lt (c : Cell) : cellIdx c < memoBuckets := Nat.mod_lt _ (by decide)

theorem Memo.find_add (m : Memo) (c c' : Cell) (q : Nat) :
    (m.add c q).find c' = if c' = c then some q else m.find c' := by
  unfold Memo.find Memo.add
  dsimp only
  have hb : cellIdx c < m.tab.size := by rw [m.size_eq]; exact cellIdx_lt c
  by_cases hi : cellIdx c = cellIdx c'
  · rw [← hi, Array.getElem?_setIfInBounds_self_of_lt hb]
    simp only [Option.getD_some, List.lookup_cons]
    by_cases he : c' = c
    · subst he; simp
    · have : (c' == c) = false := by simp [he]
      rw [this, if_neg he]
  · rw [Array.getElem?_setIfInBounds_ne hi]
    by_cases he : c' = c
    · exact absurd (by rw [he]) hi
    · rw [if_neg he]

/-- A cell's pointers are below `q`. -/
def cellBelow : Cell → Nat → Prop
  | .app f a, q => f < q ∧ a < q
  | .cons x r, q => x < q ∧ r < q
  | _, _ => True

/-- **The memo's invariant**: every entry is the cell at its address, its
    pointers below it. -/
def MemoOK (h : List Cell) (m : Memo) : Prop :=
  ∀ c q, m.find c = some q → h[q]? = some c ∧ cellBelow c q

theorem MemoOK.empty (h : List Cell) : MemoOK h Memo.empty := fun c q hq => by
  rw [Memo.find_empty] at hq; cases hq

theorem MemoOK.grow {h : List Cell} {m : Memo} (hm : MemoOK h m) (cs : List Cell) :
    MemoOK (h ++ cs) m := fun c q hq => by
  obtain ⟨e, b⟩ := hm c q hq
  have hl : q < h.length := by
    rcases (List.getElem?_eq_some_iff.mp e) with ⟨hq, _⟩
    exact hq
  exact ⟨by rw [List.getElem?_append_left hl]; exact e, b⟩

/-- Put a cell: the memo's address for it, or a fresh one. -/
def sput (h : List Cell) (m : Memo) (c : Cell) : List Cell × Memo × Nat :=
  match m.find c with
  | some q => (h, m, q)
  | none => (h ++ [c], m.add c h.length, h.length)

/-- Write an open term, children first, hash-consed: a variable `n` is the
    atom `n`, as in `obuild`. -/
def obuildS : List Cell → Memo → OTerm → List Cell × Memo × Nat
  | h, m, .S => sput h m .S
  | h, m, .K => sput h m .K
  | h, m, .I => sput h m .I
  | h, m, .var n => sput h m (.atom n)
  | h, m, .app f a =>
    let r1 := obuildS h m f
    let r2 := obuildS r1.1 r1.2.1 a
    sput r2.1 r2.2.1 (.app r1.2.2 r2.2.2)

theorem sput_spec {h : List Cell} {m : Memo} (c : Cell) (hm : MemoOK h m)
    (hb : cellBelow c h.length) :
    ∃ cs, (sput h m c).1 = h ++ cs ∧ (sput h m c).1[(sput h m c).2.2]? = some c ∧
      cellBelow c (sput h m c).2.2 ∧ MemoOK (sput h m c).1 (sput h m c).2.1 := by
  unfold sput
  split
  · next q hq =>
    obtain ⟨e, b⟩ := hm c q hq
    exact ⟨[], by simp, e, b, hm⟩
  · next hn =>
    refine ⟨[c], rfl, by simp, hb, fun c' q hq => ?_⟩
    rw [Memo.find_add] at hq
    split at hq
    · next he =>
      subst he
      cases hq
      exact ⟨by simp, hb⟩
    · exact (hm.grow [c]) c' q hq

theorem cellBelow_mono {c : Cell} {q q' : Nat} (h : cellBelow c q) (hq : q ≤ q') : cellBelow c q' := by
  cases c <;> simp only [cellBelow] at h ⊢ <;> first | trivial | omega

/-- A leaf put: the address holds it, and reads back as its term. -/
theorem sput_leaf {h : List Cell} {m : Memo} (c : Cell) (t : OTerm) (hm : MemoOK h m)
    (hb : ∀ q, cellBelow c q)
    (hr : ∀ (h' : List Cell) (q : Nat), h'[q]? = some c → otermAt h' (q + 1) q = some t) :
    ∃ cs, (sput h m c).1 = h ++ cs ∧ (sput h m c).2.2 < (sput h m c).1.length ∧
      otermAt (sput h m c).1 ((sput h m c).2.2 + 1) (sput h m c).2.2 = some t ∧
      MemoOK (sput h m c).1 (sput h m c).2.1 := by
  obtain ⟨cs, e, g, _, m'⟩ := sput_spec c hm (hb _)
  exact ⟨cs, e, (List.getElem?_eq_some_iff.mp g).1, hr _ _ g, m'⟩

/-- **The shared builder's contract**, as `obuild_spec`: the heap grows,
    the address holds the term, and the memo stays sound. -/
theorem obuildS_spec : ∀ (t : OTerm) (h : List Cell) (m : Memo), MemoOK h m →
    ∃ cs, (obuildS h m t).1 = h ++ cs ∧ (obuildS h m t).2.2 < (obuildS h m t).1.length ∧
      otermAt (obuildS h m t).1 ((obuildS h m t).2.2 + 1) (obuildS h m t).2.2 = some t ∧
      MemoOK (obuildS h m t).1 (obuildS h m t).2.1
  | .S, h, m, hm => sput_leaf .S .S hm (fun _ => trivial) fun h' q e => by simp [otermAt, e]
  | .K, h, m, hm => sput_leaf .K .K hm (fun _ => trivial) fun h' q e => by simp [otermAt, e]
  | .I, h, m, hm => sput_leaf .I .I hm (fun _ => trivial) fun h' q e => by simp [otermAt, e]
  | .var n, h, m, hm =>
    sput_leaf (.atom n) (.var n) hm (fun _ => trivial) fun h' q e => by simp [otermAt, e]
  | .app f a, h, m, hm => by
    obtain ⟨cs1, e1, l1, t1, m1⟩ := obuildS_spec f h m hm
    let r1 := obuildS h m f
    obtain ⟨cs2, e2, l2, t2, m2⟩ := obuildS_spec a r1.1 r1.2.1 m1
    let r2 := obuildS r1.1 r1.2.1 a
    have l1' : r1.2.2 < r1.1.length := l1
    have hb : cellBelow (.app r1.2.2 r2.2.2) r2.1.length := by
      show r1.2.2 < r2.1.length ∧ r2.2.2 < r2.1.length
      refine ⟨?_, l2⟩
      have : r2.1.length = r1.1.length + cs2.length := by
        show (obuildS r1.1 r1.2.1 a).1.length = _; rw [e2]; simp
      omega
    obtain ⟨cs3, e3, g3, b3, m3⟩ := sput_spec (.app r1.2.2 r2.2.2) m2 hb
    let p := (sput r2.1 r2.2.1 (.app r1.2.2 r2.2.2)).2.2
    let h3 := (sput r2.1 r2.2.1 (.app r1.2.2 r2.2.2)).1
    have hp : p < h3.length := (List.getElem?_eq_some_iff.mp g3).1
    -- the children read back at any fuel up to p, in the grown heap
    have ef : otermAt h3 p r1.2.2 = some f := by
      have : h3 = r1.1 ++ (cs2 ++ cs3) := by
        show (sput r2.1 r2.2.1 _).1 = _; rw [e3]; show r2.1 ++ cs3 = _
        rw [show r2.1 = r1.1 ++ cs2 from e2]; simp
      rw [this]
      exact otermAt_mono (otermAt_append t1) (Nat.succ_le_of_lt b3.1)
    have ea : otermAt h3 p r2.2.2 = some a := by
      have : h3 = r2.1 ++ cs3 := e3
      rw [this]
      exact otermAt_mono (otermAt_append t2) (Nat.succ_le_of_lt b3.2)
    refine ⟨cs1 ++ cs2 ++ cs3, ?_, hp, ?_, m3⟩
    · show h3 = _
      rw [show h3 = r2.1 ++ cs3 from e3, show r2.1 = r1.1 ++ cs2 from e2,
        show r1.1 = h ++ cs1 from e1]
      simp
    · show otermAt h3 (p + 1) p = some (f ⬝ₒ a)
      unfold otermAt
      rw [g3]
      dsimp only
      rw [ef, ea]

/-- `sput` reads the heap's length and the memo only. -/
theorem sput_shape (c : Cell) (m : Memo) {h h' : List Cell} (hl : h.length = h'.length) :
    ∃ cs, (sput h m c).1 = h ++ cs ∧ (sput h' m c).1 = h' ++ cs ∧ (sput h m c).2 = (sput h' m c).2 := by
  unfold sput
  split
  · exact ⟨[], by simp, by simp, rfl⟩
  · exact ⟨[c], rfl, rfl, by rw [hl]⟩

/-- **The shared builder reads no cell of the heap it is given**: heaps of
    one length get the same cells appended, the same memo and the same
    address. -/
theorem obuildS_shape : ∀ (t : OTerm) (m : Memo) {h h' : List Cell}, h.length = h'.length →
    ∃ cs, (obuildS h m t).1 = h ++ cs ∧ (obuildS h' m t).1 = h' ++ cs ∧
      (obuildS h m t).2 = (obuildS h' m t).2
  | .S, m, _, _, hl => sput_shape .S m hl
  | .K, m, _, _, hl => sput_shape .K m hl
  | .I, m, _, _, hl => sput_shape .I m hl
  | .var n, m, _, _, hl => sput_shape (.atom n) m hl
  | .app f a, m, h, h', hl => by
    obtain ⟨c1, e1, e1', r1⟩ := obuildS_shape f m hl
    have hm1 : (obuildS h' m f).2.1 = (obuildS h m f).2.1 := by rw [r1]
    have hp1 : (obuildS h' m f).2.2 = (obuildS h m f).2.2 := by rw [r1]
    have hl1 : (obuildS h m f).1.length = (obuildS h' m f).1.length := by rw [e1, e1']; simp [hl]
    obtain ⟨c2, e2, e2', r2⟩ := obuildS_shape a (obuildS h m f).2.1 hl1
    have hm2 : (obuildS (obuildS h' m f).1 (obuildS h m f).2.1 a).2.1 =
        (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.1 := by rw [r2]
    have hp2 : (obuildS (obuildS h' m f).1 (obuildS h m f).2.1 a).2.2 =
        (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.2 := by rw [r2]
    have hl2 : (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).1.length =
        (obuildS (obuildS h' m f).1 (obuildS h m f).2.1 a).1.length := by rw [e2, e2']; simp [hl1]
    obtain ⟨c3, e3, e3', r3⟩ := sput_shape
      (.app (obuildS h m f).2.2 (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.2)
      (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.1 hl2
    have u : obuildS h' m (.app f a) =
        sput (obuildS (obuildS h' m f).1 (obuildS h m f).2.1 a).1
          (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.1
          (.app (obuildS h m f).2.2 (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.2) := by
      show sput (obuildS (obuildS h' m f).1 (obuildS h' m f).2.1 a).1
        (obuildS (obuildS h' m f).1 (obuildS h' m f).2.1 a).2.1
        (.app (obuildS h' m f).2.2 (obuildS (obuildS h' m f).1 (obuildS h' m f).2.1 a).2.2) = _
      rw [hm1, hp1, hm2, hp2]
    have v : obuildS h m (.app f a) =
        sput (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).1
          (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.1
          (.app (obuildS h m f).2.2 (obuildS (obuildS h m f).1 (obuildS h m f).2.1 a).2.2) := rfl
    refine ⟨c1 ++ c2 ++ c3, ?_, ?_, ?_⟩
    · rw [v, e3, e2, e1]; simp
    · rw [u, e3', e2', e1']; simp
    · rw [u, v, r3]

end Mach
