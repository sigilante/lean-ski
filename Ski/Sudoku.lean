import Ski.Statement

open Term

/-!
# Sudoku: a statement with a hidden solution

The witness is a solved grid, as 729 Boolean inputs: input `idx r c d` says
that the cell in row `r`, column `c` holds the digit `d + 1`.  The public
formula (`sudokuExpr`) says:

- every cell holds exactly one digit;
- every row, column and box holds every digit;
- every clue is respected.

**The theorems.**
- `eval_sudoku`: the formula's value is `validB`, a plain checker of the
  three conditions.
- `solves_of_valid`: a grid that passes `validB` decodes (`gridOf`) to a
  solution of the puzzle in the ordinary sense (`Solves`): digits 1 to 9,
  each row, column and box containing each digit, and the clues in place.
- `sudoku_sound`: if the AIR accepts a table started from the statement
  machine for inputs `ρ`, ending with the accepting marker at the head,
  then `gridOf ρ` solves the puzzle.

`wikiPuzzle` and `wikiSolution` are the puzzle and solution from Wikipedia's
Sudoku article; `wiki_valid` checks the solution in the kernel, and
`wiki_swapped` checks that a grid with two cells swapped fails.
-/

namespace Sudoku

open BExpr Stmt

def idx (r c d : Nat) : Nat := 81 * r + 9 * c + d

def nine : List Nat := List.range 9

def cells : List (Nat × Nat) := nine.flatMap fun r => nine.map fun c => (r, c)

/-- Pairs of distinct digits. -/
def pairs : List (Nat × Nat) := nine.flatMap fun d => (nine.filter fun d' => d < d').map fun d' => (d, d')

def rowsG : List (List (Nat × Nat)) := nine.map fun r => nine.map fun c => (r, c)
def colsG : List (List (Nat × Nat)) := nine.map fun c => nine.map fun r => (r, c)
def boxCell (b i : Nat) : Nat × Nat := (3 * (b / 3) + i / 3, 3 * (b % 3) + i % 3)
def boxesG : List (List (Nat × Nat)) := nine.map fun b => nine.map (boxCell b)
def groups : List (List (Nat × Nat)) := rowsG ++ colsG ++ boxesG

def bit (rc : Nat × Nat) (d : Nat) : BExpr := .var (idx rc.1 rc.2 d)

def cellOne (rc : Nat × Nat) : BExpr :=
  .and (any (nine.map (bit rc))) (all (pairs.map fun p => .not (.and (bit rc p.1) (bit rc p.2))))

def groupHas (g : List (Nat × Nat)) (d : Nat) : BExpr := any (g.map fun rc => bit rc d)

/-- A clue: row, column, digit (1 to 9). -/
abbrev Clue := Nat × Nat × Nat

/-- **The public formula.** -/
def sudokuExpr (clues : List Clue) : BExpr :=
  all (cells.map cellOne ++ (groups.flatMap fun g => nine.map (groupHas g)) ++
    clues.map fun cl => bit (cl.1, cl.2.1) (cl.2.2 - 1))

/-- **The plain checker.** -/
def validB (clues : List Clue) (ρ : Nat → Bool) : Bool :=
  (cells.all fun rc => nine.any (fun d => ρ (idx rc.1 rc.2 d)) &&
      pairs.all fun p => !(ρ (idx rc.1 rc.2 p.1) && ρ (idx rc.1 rc.2 p.2))) &&
    (groups.all fun g => nine.all fun d => g.any fun rc => ρ (idx rc.1 rc.2 d)) &&
    clues.all fun cl => ρ (idx cl.1 cl.2.1 (cl.2.2 - 1))

theorem eval_sudoku (clues : List Clue) (ρ : Nat → Bool) :
    eval ρ (sudokuExpr clues) = validB clues ρ := by
  simp [sudokuExpr, validB, eval_all, eval_any, List.all_append, List.all_map, List.any_map,
    List.all_flatMap, cellOne, groupHas, bit, eval, Function.comp_def, Bool.and_assoc]

-- ---------------------------------------------------------------------------
-- The formula's inputs are the 729 cells
-- ---------------------------------------------------------------------------

/-- Every clue names a cell and a digit. -/
def CluesOK (clues : List Clue) : Prop := ∀ cl ∈ clues, cl.1 < 9 ∧ cl.2.1 < 9 ∧ 1 ≤ cl.2.2 ∧ cl.2.2 ≤ 9

theorem bounded_all {N : Nat} : ∀ l : List BExpr, (∀ a ∈ l, Bounded N a) → Bounded N (all l)
  | [], _ => trivial
  | [a], h => h a (.head _)
  | a :: b :: as, h => ⟨h a (.head _), bounded_all (b :: as) fun x hx => h x (.tail _ hx)⟩

theorem bounded_any {N : Nat} : ∀ l : List BExpr, (∀ a ∈ l, Bounded N a) → Bounded N (any l)
  | [], _ => trivial
  | [a], h => h a (.head _)
  | a :: b :: as, h => ⟨h a (.head _), bounded_any (b :: as) fun x hx => h x (.tail _ hx)⟩

theorem idx_lt {r c d : Nat} (hr : r < 9) (hc : c < 9) (hd : d < 9) : idx r c d < 729 := by
  unfold idx; omega

theorem mem_nine {d : Nat} : d ∈ nine ↔ d < 9 := by simp [nine]

theorem mem_cells {rc : Nat × Nat} (h : rc ∈ cells) : rc.1 < 9 ∧ rc.2 < 9 := by
  simp [cells, nine] at h
  obtain ⟨r, hr, c, hc, rfl⟩ := h
  exact ⟨hr, hc⟩

theorem mem_pairs {p : Nat × Nat} (h : p ∈ pairs) : p.1 < 9 ∧ p.2 < 9 ∧ p.1 < p.2 := by
  simp [pairs, nine] at h
  obtain ⟨d, hd, d', ⟨hd', hlt⟩, rfl⟩ := h
  exact ⟨hd, hd', hlt⟩

theorem boxCell_lt {b i : Nat} (hb : b < 9) (hi : i < 9) : (boxCell b i).1 < 9 ∧ (boxCell b i).2 < 9 := by
  unfold boxCell; constructor <;> omega

theorem mem_groups {g : List (Nat × Nat)} (hg : g ∈ groups) : ∀ rc ∈ g, rc.1 < 9 ∧ rc.2 < 9 := by
  simp [groups, rowsG, colsG, boxesG, nine] at hg
  rcases hg with ⟨r, hr, rfl⟩ | ⟨c, hc, rfl⟩ | ⟨b, hb, rfl⟩
  · intro rc h; simp at h; obtain ⟨c, hc, rfl⟩ := h; exact ⟨hr, hc⟩
  · intro rc h; simp at h; obtain ⟨r, hr', rfl⟩ := h; exact ⟨hr', hc⟩
  · intro rc h; simp at h; obtain ⟨i, hi, rfl⟩ := h; exact boxCell_lt hb hi

theorem bounded_sudoku {clues : List Clue} (hc : CluesOK clues) : Bounded 729 (sudokuExpr clues) := by
  apply bounded_all
  intro a ha
  simp only [List.mem_append, List.mem_map, List.mem_flatMap] at ha
  rcases ha with (⟨rc, hrc, rfl⟩ | ⟨g, hg, a', ha', rfl⟩) | ⟨cl, hcl, rfl⟩
  · obtain ⟨h1, h2⟩ := mem_cells hrc
    refine ⟨bounded_any _ ?_, bounded_all _ ?_⟩
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      exact idx_lt h1 h2 (mem_nine.1 hd)
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨p1, p2, _⟩ := mem_pairs hp
      exact ⟨idx_lt h1 h2 p1, idx_lt h1 h2 p2⟩
  · apply bounded_any
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨rc, hrc, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := mem_groups hg rc hrc
    exact idx_lt h1 h2 (mem_nine.1 ha')
  · obtain ⟨h1, h2, h3, h4⟩ := hc cl hcl
    exact idx_lt h1 h2 (by omega)

-- ---------------------------------------------------------------------------
-- A grid that passes the checker solves the puzzle
-- ---------------------------------------------------------------------------

/-- The digit a cell holds: one more than the first `d` the inputs set. -/
def gridOf (ρ : Nat → Bool) (r c : Nat) : Nat :=
  match nine.find? fun d => ρ (idx r c d) with
  | some d => d + 1
  | none => 0

/-- **A solution**, in the ordinary sense. -/
structure Solves (clues : List Clue) (g : Nat → Nat → Nat) : Prop where
  digits : ∀ r c, r < 9 → c < 9 → 1 ≤ g r c ∧ g r c ≤ 9
  rows : ∀ r v, r < 9 → 1 ≤ v → v ≤ 9 → ∃ c, c < 9 ∧ g r c = v
  cols : ∀ c v, c < 9 → 1 ≤ v → v ≤ 9 → ∃ r, r < 9 ∧ g r c = v
  boxes : ∀ b v, b < 9 → 1 ≤ v → v ≤ 9 → ∃ i, i < 9 ∧ g (boxCell b i).1 (boxCell b i).2 = v
  clues : ∀ cl ∈ clues, g cl.1 cl.2.1 = cl.2.2

/-- A cell whose inputs set exactly one digit `d` holds `d + 1`. -/
theorem gridOf_eq {ρ : Nat → Bool} {r c d : Nat} (hd : d < 9) (hp : ρ (idx r c d) = true)
    (hu : ∀ d', d' < 9 → ρ (idx r c d') = true → d' = d) : gridOf ρ r c = d + 1 := by
  unfold gridOf
  cases hf : nine.find? (fun d => ρ (idx r c d)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd hp (hf d (mem_nine.2 hd))
  | some d0 =>
    have h1 := List.find?_some hf
    have h2 := mem_nine.1 (List.mem_of_find?_eq_some hf)
    simp only at h1 ⊢
    rw [hu d0 h2 h1]

theorem mem_pairs_iff {d d' : Nat} (h : d < 9) (h' : d' < 9) (hlt : d < d') : (d, d') ∈ pairs := by
  simp [pairs, nine]; exact ⟨h, h', hlt⟩

theorem mem_cells_iff {r c : Nat} (hr : r < 9) (hc : c < 9) : (r, c) ∈ cells := by
  simp [cells, nine]; exact ⟨hr, hc⟩

/-- What `validB` says about one cell: some digit, and at most one. -/
theorem valid_cell {clues : List Clue} {ρ : Nat → Bool} (hv : validB clues ρ = true) {r c : Nat}
    (hr : r < 9) (hc : c < 9) :
    (∃ d, d < 9 ∧ ρ (idx r c d) = true) ∧ ∀ d d', d < 9 → d' < 9 →
      ρ (idx r c d) = true → ρ (idx r c d') = true → d' = d := by
  simp only [validB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff] at hv
  obtain ⟨⟨hcell, _⟩, _⟩ := hv
  obtain ⟨⟨d, hd, hpd⟩, hpairs⟩ := hcell (r, c) (mem_cells_iff hr hc)
  refine ⟨⟨d, mem_nine.1 hd, hpd⟩, fun d1 d2 h1 h2 p1 p2 => ?_⟩
  rcases Nat.lt_trichotomy d1 d2 with hlt | heq | hgt
  · rcases hpairs (d1, d2) (mem_pairs_iff h1 h2 hlt) with h | h
    · rw [p1] at h; cases h
    · rw [p2] at h; cases h
  · exact heq.symm
  · rcases hpairs (d2, d1) (mem_pairs_iff h2 h1 hgt) with h | h
    · rw [p2] at h; cases h
    · rw [p1] at h; cases h

/-- A cell whose input for `d` is set, in a grid that passes, holds `d + 1`. -/
theorem valid_grid {clues : List Clue} {ρ : Nat → Bool} (hv : validB clues ρ = true) {r c d : Nat}
    (hr : r < 9) (hc : c < 9) (hd : d < 9) (hp : ρ (idx r c d) = true) : gridOf ρ r c = d + 1 :=
  gridOf_eq hd hp fun d' hd' hp' => (valid_cell hv hr hc).2 d d' hd hd' hp hp'

/-- What `validB` says about one group: every digit appears. -/
theorem valid_group {clues : List Clue} {ρ : Nat → Bool} (hv : validB clues ρ = true)
    {g : List (Nat × Nat)} (hg : g ∈ groups) {d : Nat} (hd : d < 9) :
    ∃ rc ∈ g, ρ (idx rc.1 rc.2 d) = true := by
  simp only [validB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hv
  exact hv.1.2 g hg d (mem_nine.2 hd)

theorem valid_digits {clues : List Clue} {ρ : Nat → Bool} (hv : validB clues ρ = true)
    (r c : Nat) (hr : r < 9) (hc : c < 9) : 1 ≤ gridOf ρ r c ∧ gridOf ρ r c ≤ 9 := by
  obtain ⟨d, hd, hp⟩ := (valid_cell hv hr hc).1
  rw [valid_grid hv hr hc hd hp]
  exact ⟨Nat.le_add_left 1 d, hd⟩

/-- A group of cells in which every digit appears holds every value. -/
theorem valid_values {clues : List Clue} {ρ : Nat → Bool} (hv : validB clues ρ = true)
    {α : Type} (f : α → Nat × Nat) (dom : List α) (hg : dom.map f ∈ groups)
    (hf : ∀ a ∈ dom, (f a).1 < 9 ∧ (f a).2 < 9) (v : Nat) (h1 : 1 ≤ v) (h9 : v ≤ 9) :
    ∃ a ∈ dom, gridOf ρ (f a).1 (f a).2 = v := by
  obtain ⟨rc, hrc, hp⟩ := valid_group hv hg (d := v - 1) (by omega)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hrc
  obtain ⟨b1, b2⟩ := hf a ha
  refine ⟨a, ha, ?_⟩
  rw [valid_grid hv b1 b2 (by omega) hp]; omega

theorem row_mem {r : Nat} (hr : r < 9) : (nine.map fun c => (r, c)) ∈ groups :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (f := fun r => nine.map fun c => (r, c)) (mem_nine.2 hr)))

theorem col_mem {c : Nat} (hc : c < 9) : (nine.map fun r => (r, c)) ∈ groups :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := fun c => nine.map fun r => (r, c)) (mem_nine.2 hc)))

theorem box_mem {b : Nat} (hb : b < 9) : nine.map (boxCell b) ∈ groups :=
  List.mem_append_right _ (List.mem_map_of_mem (f := fun b => nine.map (boxCell b)) (mem_nine.2 hb))

theorem valid_clues {clues : List Clue} (hc : CluesOK clues) {ρ : Nat → Bool} (hv : validB clues ρ = true)
    (cl : Clue) (hcl : cl ∈ clues) : gridOf ρ cl.1 cl.2.1 = cl.2.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc cl hcl
  have hp : ρ (idx cl.1 cl.2.1 (cl.2.2 - 1)) = true := by
    simp only [validB, Bool.and_eq_true, List.all_eq_true] at hv
    exact hv.2 cl hcl
  rw [valid_grid hv h1 h2 (by omega) hp]; omega

/-- **A grid that passes the checker solves the puzzle.** -/
theorem solves_of_valid {clues : List Clue} (hc : CluesOK clues) {ρ : Nat → Bool}
    (hv : validB clues ρ = true) : Solves clues (gridOf ρ) where
  digits := valid_digits hv
  rows r v hr h1 h9 := by
    obtain ⟨c, hc', e⟩ := valid_values hv (fun c => (r, c)) nine (row_mem hr)
      (fun c h => ⟨hr, mem_nine.1 h⟩) v h1 h9
    exact ⟨c, mem_nine.1 hc', e⟩
  cols c v hc' h1 h9 := by
    obtain ⟨r, hr, e⟩ := valid_values hv (fun r => (r, c)) nine (col_mem hc')
      (fun r h => ⟨mem_nine.1 h, hc'⟩) v h1 h9
    exact ⟨r, mem_nine.1 hr, e⟩
  boxes b v hb h1 h9 := by
    obtain ⟨i, hi, e⟩ := valid_values hv (boxCell b) nine (box_mem hb)
      (fun i h => boxCell_lt hb (mem_nine.1 h)) v h1 h9
    exact ⟨i, mem_nine.1 hi, e⟩
  clues := valid_clues hc hv

-- ---------------------------------------------------------------------------
-- The statement
-- ---------------------------------------------------------------------------

/-- **Sudoku soundness.**  If the AIR accepts a table started from the
    statement machine for the inputs `ρ` and the puzzle's formula, and the
    last row reads the accepting marker at the head, then `gridOf ρ` solves
    the puzzle. -/
theorem sudoku_sound {clues : List Clue} (hc : CluesOK clues) {ρ : Nat → Bool} {acc rej : Nat}
    (hacc : 731 ≤ acc) (hrej : 731 ≤ rej) (hne : acc ≠ rej)
    {M : List Cell} {k : Nat} {row : Nat → Air.Row}
    (h : Air.AcceptsFrom M (stmtMachine ρ 729 (sudokuExpr clues) acc rej) k row)
    (hi : Air.rd M (row (k - 1)).ctr (row (k - 1)).hd = some (.atom acc)) :
    Solves clues (gridOf ρ) := by
  have he := stmt_sound (bounded_sudoku hc) hacc hrej hne h hi
  rw [eval_sudoku] at he
  exact solves_of_valid hc he

-- ---------------------------------------------------------------------------
-- The Wikipedia puzzle
-- ---------------------------------------------------------------------------

/-- The clues of a grid, row by row, `0` for blank. -/
def cluesOf (g : List Nat) : List Clue :=
  (g.zipIdx.filter fun p => p.1 != 0).map fun p => (p.2 / 9, p.2 % 9, p.1)

/-- The inputs a filled grid, row by row, sets. -/
def inputsOf (g : List Nat) (n : Nat) : Bool := g.getD (n / 9) 0 == n % 9 + 1

def wikiPuzzle : List Nat := [
    5, 3, 0, 0, 7, 0, 0, 0, 0,
    6, 0, 0, 1, 9, 5, 0, 0, 0,
    0, 9, 8, 0, 0, 0, 0, 6, 0,
    8, 0, 0, 0, 6, 0, 0, 0, 3,
    4, 0, 0, 8, 0, 3, 0, 0, 1,
    7, 0, 0, 0, 2, 0, 0, 0, 6,
    0, 6, 0, 0, 0, 0, 2, 8, 0,
    0, 0, 0, 4, 1, 9, 0, 0, 5,
    0, 0, 0, 0, 8, 0, 0, 7, 9]

def wikiSolution : List Nat := [
    5, 3, 4, 6, 7, 8, 9, 1, 2,
    6, 7, 2, 1, 9, 5, 3, 4, 8,
    1, 9, 8, 3, 4, 2, 5, 6, 7,
    8, 5, 9, 7, 6, 1, 4, 2, 3,
    4, 2, 6, 8, 5, 3, 7, 9, 1,
    7, 1, 3, 9, 2, 4, 8, 5, 6,
    9, 6, 1, 5, 3, 7, 2, 8, 4,
    2, 8, 7, 4, 1, 9, 6, 3, 5,
    3, 4, 5, 2, 8, 6, 1, 7, 9]

def wikiClues : List Clue := cluesOf wikiPuzzle

/-- `CluesOK`, as a check. -/
def cluesOKB (clues : List Clue) : Bool :=
  clues.all fun cl => cl.1 < 9 && cl.2.1 < 9 && 1 ≤ cl.2.2 && cl.2.2 ≤ 9

theorem cluesOK_of {clues : List Clue} (h : cluesOKB clues = true) : CluesOK clues := by
  intro cl hcl
  have := List.all_eq_true.1 h cl hcl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem wiki_clues_ok : CluesOK wikiClues := cluesOK_of (by decide)

theorem wiki_valid : validB wikiClues (inputsOf wikiSolution) = true := by decide

/-- The same solution with two cells in row 0 swapped (`534…` to `354…`)
    breaks a clue and a column. -/
theorem wiki_swapped :
    validB wikiClues (inputsOf ([3, 5, 4] ++ wikiSolution.drop 3))
      = false := by decide

/-- The Wikipedia solution solves the Wikipedia puzzle, by the checker. -/
theorem wiki_solves : Solves wikiClues (gridOf (inputsOf wikiSolution)) :=
  solves_of_valid wiki_clues_ok wiki_valid

end Sudoku
