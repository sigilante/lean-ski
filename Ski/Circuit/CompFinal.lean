import Ski.Circuit.CompSound

/-!
# The composed circuit checks the composed statement

**`compExport_sound`**: tables accepted — with Plonky3's selectors — for
AIRs with the normal forms of the composed circuit of a formula `M` and a
region size `W` (what `composed-verify` checks of its own AIRs, through
`lake exe circuit compare-composed`) carry, in their memory, bits and a
region whose witness the formula's statement accepts, and which read back
as a realizer of the formula: `CompM.checkC_realizes`'s conclusion, for
every accepted proof rather than for the tables shown to Lean.
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

/-- The composed circuit is guarded, for every statement. -/
theorem comp_guarded (M : MF) (W : Nat) : ∀ A ∈ compAirs M W, A.cons.all E.guarded = true := by
  intro A hA
  simp only [compAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- With Plonky3's selectors or `0`/`1` ones, AIRs with a guarded
    circuit's normal forms accept the same tables. -/
theorem acceptedP_iff_of {Rs Ls : List AirD} (hg : ∀ A ∈ Ls, A.cons.all E.guarded = true)
    (hs : sameAirsB Rs Ls = true) (ts : List Table) : AcceptedP Rs ts ↔ Accepted Rs ts := by
  have pair : ∀ p ∈ Rs.zip ts, ∀ σ : Sels p.2.h, SatP p.1 p.2 σ ↔ Sat p.1 p.2 := by
    intro p hp σ
    obtain ⟨l, hl, e⟩ := zip_same hs p hp
    rw [satP_transfer e, satP_iff (hg l hl), ← (sameAirB_sound e).1]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun p hp => ?_, h3, h4, h5⟩
    obtain ⟨⟨σ, hσ⟩, hpre⟩ := h2 p hp
    exact ⟨(pair p hp σ).1 hσ, hpre⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun p hp => ?_, h3, h4, h5⟩
    exact ⟨⟨sels01 _, (pair p hp _).2 (h2 p hp).1⟩, (h2 p hp).2⟩

/-- Acceptance of the composed circuit's data is `CompOK`. -/
theorem compOK_of {M : MF} {W : Nat} {ts : List Table} (h : Accepted (compAirs M W) ts) :
    ∃ C Mm Pg Wt Sg, ts = [C, Mm, Pg, Wt, Sg] ∧
      CompOK (blankM (clear M) W (stmtOf M)).hd (blankM (clear M) W (stmtOf M)).stk
        (blankM (clear M) W (stmtOf M)).heap.length (blankRoots (clear M) W (stmtOf M)).length
        (blankM (clear M) W (stmtOf M)).stk (blankM (clear M) W (stmtOf M)).heap (BT.nleaves (clear M)) W
        (blankRoots (clear M) W (stmtOf M)) C Mm Pg Wt Sg := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := h
  match ts, hl with
  | [C, Mm, Pg, Wt, Sg], _ =>
    have mem : ∀ A T, (A, T) ∈ (compAirs M W).zip [C, Mm, Pg, Wt, Sg] →
        Sat A T ∧ (A.pre = 0 ∨ PreIs A T) := fun A T hm => hsat (A, T) hm
    have z : (compAirs M W).zip [C, Mm, Pg, Wt, Sg] =
        compTables (blankM (clear M) W (stmtOf M)).hd (blankM (clear M) W (stmtOf M)).stk
          (blankM (clear M) W (stmtOf M)).heap.length (blankRoots (clear M) W (stmtOf M)).length
          (blankM (clear M) W (stmtOf M)).stk (blankM (clear M) W (stmtOf M)).heap (BT.nleaves (clear M)) W
          (blankRoots (clear M) W (stmtOf M)) C Mm Pg Wt Sg := rfl
    rw [z] at mem hbal hht htwo
    have pre : ∀ A T, (A, T) ∈ compTables (blankM (clear M) W (stmtOf M)).hd (blankM (clear M) W (stmtOf M)).stk
          (blankM (clear M) W (stmtOf M)).heap.length (blankRoots (clear M) W (stmtOf M)).length
          (blankM (clear M) W (stmtOf M)).stk (blankM (clear M) W (stmtOf M)).heap (BT.nleaves (clear M)) W
          (blankRoots (clear M) W (stmtOf M)) C Mm Pg Wt Sg → A.pre ≠ 0 → PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    refine ⟨C, Mm, Pg, Wt, Sg, rfl, ⟨(mem _ _ (by simp [compTables])).1, (mem _ _ (by simp [compTables])).1,
      (mem _ _ (by simp [compTables])).1, (mem _ _ (by simp [compTables])).1,
      pre _ _ (by simp [compTables]) (by show (5 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compTables]) (by show (3 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compTables]) (by show (2 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

theorem stmtOf_pos (M : MF) : 0 < (stmtOf M).length := by simp [stmtOf]

/-- **Soundness of the composed circuit**: an accepted proof's memory
    holds bits and a region whose witness the formula's statement accepts,
    and which read back as a realizer of the formula. -/
theorem compExport_sound {M : MF} {W : Nat} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compAirs M W) = true) (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg, ts = [C, Mm, Pg, Wt, Sg] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) (BT.nleaves (clear M)) (regionM (memOf Mm) (BT.nleaves (clear M)) W) = some w ∧
      Compose.Accepts M (fillB (clear M) (bitsM (memOf Mm)) 0) w ∧
      Real M.toForm (readBack M (fillB (clear M) (bitsM (memOf Mm)) 0) w []) := by
  have hacc := accepted_transfer hs ((acceptedP_iff_of (comp_guarded M W) hs ts).1 h)
  obtain ⟨C, Mm, Pg, Wt, Sg, rfl, hok⟩ := compOK_of hacc
  obtain ⟨w, hw, hs', hall⟩ := hok.sound (stmtOf_pos M)
  have ha : Compose.Accepts M (fillB (clear M) (bitsM (memOf Mm)) 0) w := ⟨shape_of_same M _ hs', hall⟩
  exact ⟨C, Mm, Pg, Wt, Sg, rfl, w, hw, ha, real_of_accepted ha⟩

end Circuit

#print axioms Circuit.compExport_sound
