import Ski.Circuit.CompDSound
import Ski.Circuit.CompFinal

/-!
# The circuit with the `dec` jet: an accepted proof's run

**`compDExportG_sound`**: tables accepted, with Plonky3's selectors, for
AIRs with the normal forms of `compDAirsG Vs W` (what `compd-verify` checks
of its own AIRs, through `lake exe circuit compare-compd`) carry, in their
memory, a bit and a region of `W` cells whose witness makes every verifier
in `Vs`, applied to the bit and the witness, head-reduce with the `dec`
jet to `K`, every subject the jet takes held in the memory
(`CompM.HSteps`, `CompM.InMem`).  It needs at least one verifier, and each
verifier's only free variable to be the jet's.  `compDExport_sound` is its
instance for `decpre p`; what that run means is `Circuit.decpreExport_sound`
(`Ski/DecPreSound.lean`).
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit ComposedDText

set_option maxRecDepth 100000 in
/-- The circuit is guarded. -/
theorem compDG_guardedL (L : Layout) (Vs : List OTerm) (W : Nat) : ∀ A ∈ compDAirsGL L Vs W, A.cons.all E.guarded = true := by
  intro A hA
  simp only [compDAirsGL, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Acceptance of the circuit's data is `CompDOK`. -/
theorem compDOK_ofGL (L : Layout) {Vs : List OTerm} {W : Nat} {ts : List Table} (hacc : Accepted (compDAirsGL L Vs W) ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧
      CompDOK (L.blankM shpD W Vs).hd (L.blankM shpD W Vs).stk
        (L.blankM shpD W Vs).heap.length (L.blankRoots shpD W Vs).length
        (L.blankM shpD W Vs).stk JD (L.blankM shpD W Vs).heap (BT.nleaves shpD) W
        (L.blankRoots shpD W Vs) C Mm Pg Wt Sg D := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := hacc
  match ts, hl with
  | [C, Mm, Pg, Wt, Sg, D], _ =>
    have z : (compDAirsGL L Vs W).zip [C, Mm, Pg, Wt, Sg, D] =
        compDTables (L.blankM shpD W Vs).hd (L.blankM shpD W Vs).stk
          (L.blankM shpD W Vs).heap.length (L.blankRoots shpD W Vs).length
          (L.blankM shpD W Vs).stk JD (L.blankM shpD W Vs).heap (BT.nleaves shpD) W
          (L.blankRoots shpD W Vs) C Mm Pg Wt Sg D := rfl
    have mem : ∀ A T, (A, T) ∈ compDTables (L.blankM shpD W Vs).hd (L.blankM shpD W Vs).stk
          (L.blankM shpD W Vs).heap.length (L.blankRoots shpD W Vs).length
          (L.blankM shpD W Vs).stk JD (L.blankM shpD W Vs).heap (BT.nleaves shpD) W
          (L.blankRoots shpD W Vs) C Mm Pg Wt Sg D → Sat A T ∧ (A.pre = 0 ∨ PreIs A T) :=
      fun A T hm => hsat (A, T) (z ▸ hm)
    rw [z] at hbal hht htwo
    have pre : ∀ A T, (A, T) ∈ compDTables (L.blankM shpD W Vs).hd (L.blankM shpD W Vs).stk
          (L.blankM shpD W Vs).heap.length (L.blankRoots shpD W Vs).length
          (L.blankM shpD W Vs).stk JD (L.blankM shpD W Vs).heap (BT.nleaves shpD) W
          (L.blankRoots shpD W Vs) C Mm Pg Wt Sg D → A.pre ≠ 0 → PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    refine ⟨C, Mm, Pg, Wt, Sg, D, rfl, ⟨(mem _ _ (by simp [compDTables])).1,
      (mem _ _ (by simp [compDTables])).1, (mem _ _ (by simp [compDTables])).1,
      (mem _ _ (by simp [compDTables])).1,
      sat_of_withBlocks (mem decAirB D (by simp [compDTables])).1,
      pre _ _ (by simp [compDTables]) (by show (5 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compDTables]) (by show (3 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compDTables]) (by show (2 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

/-- **Soundness of the circuit with the `dec` jet**, for any verifiers whose
    only free variable is the jet's: an accepted proof has in its memory a
    bit and a region whose witness makes every verifier head-reduce with
    the jet to `K`, its subjects in the memory. -/
theorem compDExportG_soundL (L : Layout) {Vs : List OTerm} {W : Nat} (hVs : 0 < Vs.length)
    (hocc : ∀ V ∈ Vs, ∀ x, Occ x V → x = JD)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsGL L Vs W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 1 (regionM (memOf Mm) 1 W) = some w ∧
      ∀ V ∈ Vs, HSteps (InMem (memOf Mm)) JD (V ⬝ₒ (fillB shpD (bitsM (memOf Mm)) 0).enc.toO ⬝ₒ w.toO) .K := by
  have hacc' := accepted_transfer hs ((acceptedP_iff_of (compDG_guardedL L Vs W) hs ts).1 hacc)
  obtain ⟨C, Mm, Pg, Wt, Sg, D, rfl, ok⟩ := compDOK_ofGL L hacc'
  refine ⟨C, Mm, Pg, Wt, Sg, D, rfl, ?_⟩
  have hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < JD + 1 := fun V hV x hx => by
    rw [hocc V hV x hx]; exact Nat.lt_succ_self _
  have h3 : 3 ≤ (L.blankM shpD W Vs).heap.length := by
    have := L.blank_prefix shpD W Vs
    omega
  have hcp := ok.acceptsCD hv hVs (by decide) (by decide) h3
  have hl : (regionM (memOf Mm) (BT.nleaves shpD) W).length = (List.replicate W Cell.S).length := by
    rw [List.length_replicate]; exact ok.region_len
  obtain ⟨_, hstk, hR, _, _, _⟩ := L.pub (bitsM (memOf Mm)) (fun _ => false) shpD
    (regionM (memOf Mm) (BT.nleaves shpD) W) (List.replicate W .S) Vs hl
  have hroots : L.blankRoots shpD W Vs = (L.heap (bitsM (memOf Mm)) shpD (regionM (memOf Mm) (BT.nleaves shpD) W) Vs).2 :=
    hR.symm
  have hnil : (L.blankM shpD W Vs).stk =
      (L.heap (bitsM (memOf Mm)) shpD (regionM (memOf Mm) (BT.nleaves shpD) W) Vs).1.length := hstk.symm
  rw [hroots, hnil] at hcp
  have hwf := ok.regionWF
  exact composedD_sound_ofL L hwf hcp

/-- The tree layout's circuit is guarded. -/
theorem compDG_guarded (Vs : List OTerm) (W : Nat) : ∀ A ∈ compDAirsG Vs W, A.cons.all E.guarded = true :=
  compDG_guardedL treeL Vs W

/-- Acceptance of the tree layout's circuit is `CompDOK`. -/
theorem compDOK_ofG {Vs : List OTerm} {W : Nat} {ts : List Table} (hacc : Accepted (compDAirsG Vs W) ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧
      CompDOK (blankMO shpD W Vs).hd (blankMO shpD W Vs).stk
        (blankMO shpD W Vs).heap.length (blankRootsO shpD W Vs).length
        (blankMO shpD W Vs).stk JD (blankMO shpD W Vs).heap (BT.nleaves shpD) W
        (blankRootsO shpD W Vs) C Mm Pg Wt Sg D :=
  compDOK_ofGL treeL hacc

theorem shpD_nleaves : BT.nleaves shpD = 1 := rfl

/-- **Soundness of the circuit with the `dec` jet**, the statement as a
    tree: `compDExportG_soundL` at `treeL`. -/
theorem compDExportG_sound {Vs : List OTerm} {W : Nat} (hVs : 0 < Vs.length)
    (hocc : ∀ V ∈ Vs, ∀ x, Occ x V → x = JD)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirsG Vs W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 1 (regionM (memOf Mm) 1 W) = some w ∧
      ∀ V ∈ Vs, HSteps (InMem (memOf Mm)) JD (V ⬝ₒ (fillB shpD (bitsM (memOf Mm)) 0).enc.toO ⬝ₒ w.toO) .K :=
  compDExportG_soundL treeL hVs hocc hs hacc

theorem occ_absN : ∀ (xs : List Nat) {t : OTerm} {x : Nat}, Occ x (absN xs t) → Occ x t ∧ x ∉ xs
  | [], _, _, h => ⟨h, List.not_mem_nil⟩
  | y :: ys, _, x, h => by
    obtain ⟨h1, h2⟩ := occ_abs h
    obtain ⟨h3, h4⟩ := occ_absN ys h1
    exact ⟨h3, by simp [h2, h4]⟩

theorem occ_app {f g : OTerm} {x : Nat} (h : Occ x (f ⬝ₒ g)) : Occ x f ∨ Occ x g := by
  cases h with
  | left _ h => exact .inl h
  | right _ h => exact .inr h

theorem occ_K {x : Nat} (h : Occ x .K) : False := nomatch h

theorem badD_closed (x : Nat) : ¬ Occ x ComposedDText.badO := fun h => by
  rcases occ_app h with h | h
  · exact absurd (fresh_toO _ 0 x h) (Nat.not_lt_zero _)
  · exact occ_K h

theorem chkL_closed : ∀ (es : List Bool) (x : Nat), ¬ Occ x (chkL es)
  | [], x, h => by
    obtain ⟨h1, h2⟩ := occ_absN [0] h
    rcases occ_app h1 with h1 | h1
    · rcases occ_app h1 with h1 | h1
      · cases h1; exact h2 (List.mem_singleton.2 rfl)
      · exact occ_K h1
    · rcases occ_app h1 with h1 | h1
      · exact occ_K h1
      · rcases occ_app h1 with h1 | h1
        · exact occ_K h1
        · exact badD_closed x h1
  | e :: es, x, h => by
    obtain ⟨h1, h2⟩ := occ_absN [0] h
    have side : ∀ (b : Bool), ¬ Occ x (if b then chkL es ⬝ₒ .var 2 else badO) ∨ x = 2 := by
      intro b; cases b
      · exact .inl (badD_closed x)
      · by_cases hx : x = 2
        · exact .inr hx
        · refine .inl fun h3 => ?_
          rcases occ_app h3 with h3 | h3
          · exact chkL_closed es x h3
          · cases h3; exact hx rfl
    have side' : ∀ (b : Bool), ¬ Occ x (if b then badO else chkL es ⬝ₒ .var 2) ∨ x = 2 := by
      intro b; cases b
      · by_cases hx : x = 2
        · exact .inr hx
        · refine .inl fun h3 => ?_
          rcases occ_app h3 with h3 | h3
          · exact chkL_closed es x h3
          · cases h3; exact hx rfl
      · exact .inl (badD_closed x)
    rcases occ_app h1 with h1 | h1
    · rcases occ_app h1 with h1 | h1
      · cases h1; exact h2 (List.mem_singleton.2 rfl)
      · exact badD_closed x h1
    · obtain ⟨h3, h4⟩ := occ_absN [1, 2] h1
      rcases occ_app h3 with h3 | h3
      · rcases occ_app h3 with h3 | h3
        · cases h3; exact h4 (by simp)
        · rcases side e with s | s
          · exact s h3
          · exact h4 (by simp [s])
      · rcases side' e with s | s
        · exact s h3
        · exact h4 (by simp [s])

theorem checkD_closed (p x : Nat) : ¬ Occ x (checkD p) := fun h => by
  obtain ⟨h1, h2⟩ := occ_absN [0] h
  rcases occ_app h1 with h1 | h1
  · rcases occ_app h1 with h1 | h1
    · rcases occ_app h1 with h1 | h1
      · rcases occ_app h1 with h1 | h1
        · cases h1; exact h2 (List.mem_singleton.2 rfl)
        · exact badD_closed x h1
      · obtain ⟨h3, h4⟩ := occ_absN [1, 2] h1
        rcases occ_app h3 with h3 | h3
        · rcases occ_app h3 with h3 | h3
          · rcases occ_app h3 with h3 | h3
            · rcases occ_app h3 with h3 | h3
              · cases h3; exact h4 (by simp)
              · exact chkL_closed _ x h3
            · exact badD_closed x h3
          · exact badD_closed x h3
        · exact badD_closed x h3
    · exact badD_closed x h1
  · exact badD_closed x h1

/-- **The verifier's only variable is the jet's.** -/
theorem verifierD_occ (p x : Nat) (hx : Occ x (verifierD p)) : x = JD := by
  obtain ⟨h1, h2⟩ := occ_absN [0, 1] hx
  rcases occ_app h1 with h1 | h1
  · exact absurd h1 (checkD_closed p x)
  · rcases occ_app h1 with h1 | h1
    · cases h1; rfl
    · cases h1; exact absurd (by simp) h2

/-- **Soundness of the circuit for `decpre p`**: the verifier, on the bit
    and the region's witness, head-reduces with the jet to `K`. -/
theorem compDExport_sound {p W : Nat} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compDAirs p W) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg D, ts = [C, Mm, Pg, Wt, Sg, D] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 1 (regionM (memOf Mm) 1 W) = some w ∧
      HSteps (InMem (memOf Mm)) JD (verifierD p ⬝ₒ (fillB shpD (bitsM (memOf Mm)) 0).enc.toO ⬝ₒ w.toO) .K := by
  obtain ⟨C, Mm, Pg, Wt, Sg, D, rfl, w, hw, hrun⟩ := compDExportG_sound (Vs := VsD p) (W := W) (Nat.zero_lt_succ _)
    (fun V hV x hx => by
      simp only [VsD, List.mem_cons, List.not_mem_nil, or_false] at hV
      subst hV
      exact verifierD_occ p x hx) hs hacc
  exact ⟨C, Mm, Pg, Wt, Sg, D, rfl, w, hw, hrun _ (List.mem_singleton.2 rfl)⟩

end Circuit
