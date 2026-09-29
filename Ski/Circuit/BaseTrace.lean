import Ski.Circuit.BaseSound

/-!
# The honest trace of a run

For a run the Lean AIR accepts, each row's kind (`kindOf`) and the cells
its reads find (`fieldsAt`), classified (`shape`): a row that steps or
halts is one of the circuit's eleven kinds, reads the cells its kind's
tags name, and writes what its kind writes.
-/

namespace Circuit

open B Air

/-- A row's kind, from the cells it reads. -/
def kindOf (M : List Cell) (r : Row) : Nat :=
  match rd M r.ctr r.hd with
  | some (.app _ _) => 0
  | some .I =>
    match rd M r.ctr r.stk with
    | some (.cons _ _) => 1
    | _ => 4
  | some .K =>
    match rd M r.ctr r.stk with
    | some (.cons _ s1) =>
      match rd M r.ctr s1 with
      | some (.cons _ _) => 2
      | _ => 6
    | _ => 5
  | some .S =>
    match rd M r.ctr r.stk with
    | some (.cons _ s1) =>
      match rd M r.ctr s1 with
      | some (.cons _ s2) =>
        match rd M r.ctr s2 with
        | some (.cons _ _) => 3
        | _ => 9
      | _ => 8
    | _ => 7
  | _ => 10

/-- Read `j`'s address: the head, the stack, and the next two stack cells. -/
def addrAt (M : List Cell) (r : Row) : Nat → Nat
  | 0 => r.hd
  | 1 => r.stk
  | 2 => (cellFields ((rd M r.ctr r.stk).getD .nil)).2
  | _ => (cellFields ((rd M r.ctr (cellFields ((rd M r.ctr r.stk).getD .nil)).2).getD .nil)).2

/-- The fields of the cell read `j` finds. -/
def fieldsAt (M : List Cell) (r : Row) (j : Nat) : Nat × Nat :=
  cellFields ((rd M r.ctr (addrAt M r j)).getD .nil)

/-- A row that steps or halts. -/
def Valid (M : List Cell) (r : Row) : Prop := (stepRow M r).isSome = true ∨ haltRow M r = true

/-- What a valid row's kind fixes. -/
structure Shape (M : List Cell) (r : Row) (k : Nat) : Prop where
  lt : k < 11
  reads : ∀ j, j < 4 → actOf k j = 1 →
    ∃ cell, rd M r.ctr (addrAt M r j) = some cell ∧ cellTag cell = tagOf k j
  step : k < 4 → haltRow M r = false
  halt : 4 ≤ k → haltRow M r = true
  none : 4 ≤ k → stepRow M r = none
  app : k = 0 → M[r.ctr]? = some (.cons (fieldsAt M r 0).2 r.stk) ∧
    stepRow M r = some ⟨(fieldsAt M r 0).1, r.ctr, r.ctr + 1⟩
  i : k = 1 → stepRow M r = some ⟨(fieldsAt M r 1).1, (fieldsAt M r 1).2, r.ctr⟩
  k2 : k = 2 → stepRow M r = some ⟨(fieldsAt M r 1).1, (fieldsAt M r 2).2, r.ctr⟩
  s : k = 3 → M[r.ctr]? = some (.app (fieldsAt M r 2).1 (fieldsAt M r 3).1) ∧
    M[r.ctr + 1]? = some (.cons r.ctr (fieldsAt M r 3).2) ∧
    M[r.ctr + 2]? = some (.cons (fieldsAt M r 3).1 (r.ctr + 1)) ∧
    stepRow M r = some ⟨(fieldsAt M r 1).1, r.ctr + 2, r.ctr + 3⟩

theorem wrs_one {M : List Cell} {c : Nat} {w : Cell} (h : wrs M c [w] = true) : M[c]? = some w := by
  simpa [wrs] using h

theorem wrs_three {M : List Cell} {c : Nat} {w1 w2 w3 : Cell} (h : wrs M c [w1, w2, w3] = true) :
    M[c]? = some w1 ∧ M[c + 1]? = some w2 ∧ M[c + 2]? = some w3 := by
  simp only [wrs, Bool.and_eq_true, beq_iff_eq, Bool.and_true] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **Every valid row has the shape of its kind.** -/
theorem shape {M : List Cell} {r : Row} (hv : Valid M r) : Shape M r (kindOf M r) := by
  unfold Valid at hv
  have j4 : ∀ j, j < 4 → j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := fun j hj => by omega
  cases h0 : rd M r.ctr r.hd with
  | none => exfalso; simp [stepRow, stepG, haltRow, h0] at hv
  | some c0 =>
    cases c0 with
    | app f x =>
      have hk : kindOf M r = 0 := by simp only [kindOf, h0]
      have hh : haltRow M r = false := by simp only [haltRow, h0]
      have hst : stepRow M r = if wrs M r.ctr [.cons x r.stk] then some ⟨f, r.ctr, r.ctr + 1⟩ else none := by
        simp only [stepRow, stepG, h0]; rfl
      have hw : wrs M r.ctr [.cons x r.stk] = true := by
        cases hw : wrs M r.ctr [.cons x r.stk] <;> simp_all
      have hf0 : fieldsAt M r 0 = (f, x) := by simp only [fieldsAt, addrAt, h0, Option.getD_some, cellFields]
      rw [hk]
      refine ⟨by decide, ?_, fun _ => hh, fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ⟨?_, ?_⟩,
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      · intro j hj ha
        rcases j4 j hj with rfl | rfl | rfl | rfl
        · exact ⟨_, h0, rfl⟩
        all_goals exact absurd ha (by decide)
      · rw [hf0]; exact wrs_one hw
      · rw [hst, if_pos hw, hf0]
    | I =>
      cases h1 : rd M r.ctr r.stk with
      | none => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1] at hv
      | some c1 =>
        cases c1 with
        | cons x s =>
          have hk : kindOf M r = 1 := by simp only [kindOf, h0, h1]
          rw [hk]
          refine ⟨by decide, ?_, fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
            fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
          · intro j hj ha
            rcases j4 j hj with rfl | rfl | rfl | rfl
            · exact ⟨_, h0, rfl⟩
            · exact ⟨_, h1, rfl⟩
            all_goals exact absurd ha (by decide)
          · simp only [haltRow, h0, short, h1]
          · simp [stepRow, stepG, h0, h1, wrs, fieldsAt, addrAt, cellFields]
        | nil =>
          have hk : kindOf M r = 4 := by simp only [kindOf, h0, h1]
          rw [hk]
          refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
            fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
          · intro j hj ha
            rcases j4 j hj with rfl | rfl | rfl | rfl
            · exact ⟨_, h0, rfl⟩
            · exact ⟨_, h1, rfl⟩
            all_goals exact absurd ha (by decide)
          · simp only [haltRow, h0, short, h1]
          · simp [stepRow, stepG, h0, h1]
        | _ => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1] at hv
    | K =>
      cases h1 : rd M r.ctr r.stk with
      | none => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1] at hv
      | some c1 =>
        cases c1 with
        | cons x s1 =>
          cases h2 : rd M r.ctr s1 with
          | none => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1, h2] at hv
          | some c2 =>
            cases c2 with
            | cons y s2 =>
              have hk : kindOf M r = 2 := by simp only [kindOf, h0, h1, h2]
              rw [hk]
              refine ⟨by decide, ?_, fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
                fun h => absurd h (by decide), fun _ => ?_, fun h => absurd h (by decide)⟩
              · intro j hj ha
                rcases j4 j hj with rfl | rfl | rfl | rfl
                · exact ⟨_, h0, rfl⟩
                · exact ⟨_, h1, rfl⟩
                · simp only [addrAt, h1, Option.getD_some, cellFields]; exact ⟨_, h2, rfl⟩
                · exact absurd ha (by decide)
              · simp only [haltRow, h0, short, h1, h2]
              · simp [stepRow, stepG, h0, h1, h2, wrs, fieldsAt, addrAt, cellFields]
            | nil =>
              have hk : kindOf M r = 6 := by simp only [kindOf, h0, h1, h2]
              rw [hk]
              refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
                fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
              · intro j hj ha
                rcases j4 j hj with rfl | rfl | rfl | rfl
                · exact ⟨_, h0, rfl⟩
                · exact ⟨_, h1, rfl⟩
                · simp only [addrAt, h1, Option.getD_some, cellFields]; exact ⟨_, h2, rfl⟩
                · exact absurd ha (by decide)
              · simp only [haltRow, h0, short, h1, h2]
              · simp [stepRow, stepG, h0, h1, h2]
            | _ => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1, h2] at hv
        | nil =>
          have hk : kindOf M r = 5 := by simp only [kindOf, h0, h1]
          rw [hk]
          refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
            fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
          · intro j hj ha
            rcases j4 j hj with rfl | rfl | rfl | rfl
            · exact ⟨_, h0, rfl⟩
            · exact ⟨_, h1, rfl⟩
            all_goals exact absurd ha (by decide)
          · simp only [haltRow, h0, short, h1]
          · simp [stepRow, stepG, h0, h1]
        | _ => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1] at hv
    | S =>
      cases h1 : rd M r.ctr r.stk with
      | none => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1] at hv
      | some c1 =>
        cases c1 with
        | cons x s1 =>
          cases h2 : rd M r.ctr s1 with
          | none => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1, h2] at hv
          | some c2 =>
            cases c2 with
            | cons y s2 =>
              cases h3 : rd M r.ctr s2 with
              | none => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1, h2, h3] at hv
              | some c3 =>
                cases c3 with
                | cons z s3 =>
                  have hk : kindOf M r = 3 := by simp only [kindOf, h0, h1, h2, h3]
                  have hh : haltRow M r = false := by simp only [haltRow, h0, short, h1, h2, h3]
                  have hst : stepRow M r = if wrs M r.ctr [.app y z, .cons r.ctr s3, .cons z (r.ctr + 1)]
                      then some ⟨x, r.ctr + 2, r.ctr + 3⟩ else none := by
                    simp only [stepRow, stepG, h0, h1, h2, h3]; rfl
                  have hw : wrs M r.ctr [.app y z, .cons r.ctr s3, .cons z (r.ctr + 1)] = true := by
                    cases hw : wrs M r.ctr [.app y z, .cons r.ctr s3, .cons z (r.ctr + 1)] <;> simp_all
                  have hf1 : fieldsAt M r 1 = (x, s1) := by
                    simp only [fieldsAt, addrAt, h1, Option.getD_some, cellFields]
                  have hf2 : fieldsAt M r 2 = (y, s2) := by
                    simp only [fieldsAt, addrAt, h1, h2, Option.getD_some, cellFields]
                  have hf3 : fieldsAt M r 3 = (z, s3) := by
                    simp only [fieldsAt, addrAt, h1, h2, h3, Option.getD_some, cellFields]
                  rw [hk]
                  refine ⟨by decide, ?_, fun _ => hh, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
                    fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => ?_⟩
                  · intro j hj ha
                    rcases j4 j hj with rfl | rfl | rfl | rfl
                    · exact ⟨_, h0, rfl⟩
                    · exact ⟨_, h1, rfl⟩
                    · simp only [addrAt, h1, Option.getD_some, cellFields]; exact ⟨_, h2, rfl⟩
                    · simp only [addrAt, h1, h2, Option.getD_some, cellFields]; exact ⟨_, h3, rfl⟩
                  · obtain ⟨w1, w2, w3⟩ := wrs_three hw
                    rw [hf1, hf2, hf3, hst, if_pos hw]
                    exact ⟨w1, w2, w3, rfl⟩
                | nil =>
                  have hk : kindOf M r = 9 := by simp only [kindOf, h0, h1, h2, h3]
                  rw [hk]
                  refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
                    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
                  · intro j hj ha
                    rcases j4 j hj with rfl | rfl | rfl | rfl
                    · exact ⟨_, h0, rfl⟩
                    · exact ⟨_, h1, rfl⟩
                    · simp only [addrAt, h1, Option.getD_some, cellFields]; exact ⟨_, h2, rfl⟩
                    · simp only [addrAt, h1, h2, Option.getD_some, cellFields]; exact ⟨_, h3, rfl⟩
                  · simp only [haltRow, h0, short, h1, h2, h3]
                  · simp [stepRow, stepG, h0, h1, h2, h3]
                | _ => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1, h2, h3] at hv
            | nil =>
              have hk : kindOf M r = 8 := by simp only [kindOf, h0, h1, h2]
              rw [hk]
              refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
                fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
              · intro j hj ha
                rcases j4 j hj with rfl | rfl | rfl | rfl
                · exact ⟨_, h0, rfl⟩
                · exact ⟨_, h1, rfl⟩
                · simp only [addrAt, h1, Option.getD_some, cellFields]; exact ⟨_, h2, rfl⟩
                · exact absurd ha (by decide)
              · simp only [haltRow, h0, short, h1, h2]
              · simp [stepRow, stepG, h0, h1, h2]
            | _ => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1, h2] at hv
        | nil =>
          have hk : kindOf M r = 7 := by simp only [kindOf, h0, h1]
          rw [hk]
          refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
            fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
          · intro j hj ha
            rcases j4 j hj with rfl | rfl | rfl | rfl
            · exact ⟨_, h0, rfl⟩
            · exact ⟨_, h1, rfl⟩
            all_goals exact absurd ha (by decide)
          · simp only [haltRow, h0, short, h1]
          · simp [stepRow, stepG, h0, h1]
        | _ => exfalso; simp [stepRow, stepG, haltRow, short, h0, h1] at hv
    | atom n =>
      have hk : kindOf M r = 10 := by simp only [kindOf, h0]
      rw [hk]
      refine ⟨by decide, ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun h => absurd h (by decide),
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      · intro j hj ha
        rcases j4 j hj with rfl | rfl | rfl | rfl
        · exact ⟨_, h0, rfl⟩
        all_goals exact absurd ha (by decide)
      · simp only [haltRow, h0]
      · simp [stepRow, stepG, h0]
    | _ => exfalso; simp [stepRow, stepG, haltRow, h0] at hv

end Circuit
