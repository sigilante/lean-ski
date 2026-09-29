import Ski.Circuit.JetSound

/-!
# A jetted run, taken apart

What the honest jet tables are built from: for each row of a run of
`Air.AcceptsJ`, the jet it instantiates, if any (`jetOf`), and for an
instantiation, its pops (`popsOf`), which `Air.popR` reads.  Nothing here
is about tables.
-/

namespace Circuit

open B Air JetTable Mach

section

variable (A : List Cell) (roots : List (Nat × Nat)) (jets : List Air.Jet)

/-- The jet a row instantiates to reach the next: none when it steps or
    has halted and repeats. -/
def jetOf (r r' : Air.Row) : Option (Nat × Air.Jet) :=
  if stepRow A r = some r' ∨ (haltRow A r = true ∧ r' = r) then none
  else (roots.find? fun p => p.1 == r.hd && match jets[p.2]? with
      | some J => decide (instRow A J r = some r')
      | none => false).bind fun p => (jets[p.2]?).map fun J => (p.2, J)

variable {A roots jets}

theorem jetOf_some {r r' : Air.Row} {g : Nat} {J : Air.Jet} (h : jetOf A roots jets r r' = some (g, J)) :
    (r.hd, g) ∈ roots ∧ jets[g]? = some J ∧ instRow A J r = some r' := by
  unfold jetOf at h
  split at h
  · cases h
  · cases hf : roots.find? (fun p => p.1 == r.hd && match jets[p.2]? with
        | some J => decide (instRow A J r = some r')
        | none => false) with
    | none => rw [hf] at h; cases h
    | some p =>
      rw [hf] at h
      obtain ⟨a, g'⟩ := p
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Option.bind_some] at h
      cases hJ : jets[g']? with
      | none => rw [hJ] at h; cases h
      | some J' =>
        rw [hJ] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [hJ, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
        obtain ⟨ha, hi⟩ := hp
        subst ha
        exact ⟨hm, hJ, hi⟩

theorem jetOf_none {r r' : Air.Row} (h : jetOf A roots jets r r' = none)
    (ht : stepRow A r = some r' ∨
      (∃ g J, (r.hd, g) ∈ roots ∧ jets[g]? = some J ∧ instRow A J r = some r') ∨
      (haltRow A r = true ∧ r' = r)) :
    stepRow A r = some r' ∨ (haltRow A r = true ∧ r' = r) := by
  unfold jetOf at h
  split at h
  · next hc => exact hc
  · next hc =>
    exfalso
    rcases ht with ht | ⟨g, J, hm, hJ, hi⟩ | ht
    · exact hc (.inl ht)
    · cases hf : roots.find? (fun p => p.1 == r.hd && match jets[p.2]? with
          | some J => decide (instRow A J r = some r')
          | none => false) with
      | none =>
        have := List.find?_eq_none.1 hf (r.hd, g) hm
        simp only [beq_self_eq_true', hJ, Bool.true_and, decide_eq_true_eq] at this
        exact this hi
      | some p =>
        rw [hf] at h
        obtain ⟨a, g'⟩ := p
        have hp := List.find?_some hf
        simp only [Option.bind_some] at h
        cases hJ' : jets[g']? with
        | none => simp only [hJ', Bool.and_false] at hp; cases hp
        | some J' => rw [hJ'] at h; cases h
    · exact hc (.inr ht)

/-- An instantiation's pops, as `popR` reads them: each the stack cell's
    address, its argument, and the next cell's address. -/
def popsOf (A : List Cell) (c : Nat) : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | k + 1, s =>
    match rd A c s with
    | some (.cons x r) => (s, x, r) :: popsOf A c k r
    | _ => []

/-- **The pops of a successful `popR`**: `k` of them, chained from `s` to
    the rest, each reading a stack cell below the counter. -/
theorem popsOf_spec {c : Nat} : ∀ (k s : Nat) {ps : List Nat} {rest : Nat},
    popR (fun a => A[a]?) c k s = some (ps, rest) →
    ∃ σ ξ : Nat → Nat, σ 0 = s ∧ σ k = rest ∧ ps = (List.range k).map ξ ∧
      ∀ j, j < k → (popsOf A c k s)[j]? = some (σ j, ξ j, σ (j + 1)) ∧
        rd A c (σ j) = some (.cons (ξ j) (σ (j + 1)))
  | 0, s, ps, rest, h => by
    cases h
    exact ⟨fun _ => s, fun _ => 0, rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | k + 1, s, ps, rest, h => by
    unfold popR at h
    rw [← rd_G] at h
    cases hr : rd A c s with
    | none => rw [hr] at h; cases h
    | some cell =>
      rw [hr] at h
      cases cell with
      | cons x r =>
        dsimp only at h
        cases hp : popR (fun a => A[a]?) c k r with
        | none => rw [hp] at h; cases h
        | some q =>
          rw [hp] at h
          obtain ⟨ps', rest'⟩ := q
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨σ, ξ, h0, hk, hps, hj⟩ := popsOf_spec k r hp
          refine ⟨fun j => if j = 0 then s else σ (j - 1), fun j => if j = 0 then x else ξ (j - 1),
            rfl, by simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; exact hk, ?_, ?_⟩
          · rw [List.range_succ_eq_map, List.map_cons, List.map_map, hps]
            simp only [↓reduceIte]
            congr 1
          · intro j hjk
            have ep : popsOf A c (k + 1) s = (s, x, r) :: popsOf A c k r := by
              show (match rd A c s with | some (.cons x r) => _ | _ => []) = _
              rw [hr]
            rw [ep]
            cases j with
            | zero =>
              simp only [↓reduceIte, List.getElem?_cons_zero, Nat.zero_add, Nat.add_one_ne_zero,
                Nat.add_sub_cancel]
              rw [h0]
              exact ⟨rfl, hr⟩
            | succ j =>
              obtain ⟨e1, e2⟩ := hj j (by omega)
              simp only [List.getElem?_cons_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
              exact ⟨e1, e2⟩
      | _ => cases h

theorem popsOf_length_le (c : Nat) : ∀ k s, (popsOf A c k s).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, s => by
    unfold popsOf
    split
    · rw [List.length_cons]; exact Nat.succ_le_succ (popsOf_length_le c k _)
    · exact Nat.zero_le _

theorem popsOf_length {c : Nat} {k s : Nat} {ps : List Nat} {rest : Nat}
    (h : popR (fun a => A[a]?) c k s = some (ps, rest)) : (popsOf A c k s).length = k := by
  obtain ⟨σ, ξ, _, _, _, hj⟩ := popsOf_spec k s h
  apply Nat.le_antisymm (popsOf_length_le c k s)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]; exact Nat.zero_le _
  · have := (hj (k - 1) (by omega)).1
    have := (List.getElem?_eq_some_iff.1 this).1
    omega

end

end Circuit
