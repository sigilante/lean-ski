import Ski.Circuit.CompPSound
import Ski.Circuit.CompFinal

/-!
# The circuit with the Poseidon2 jet checks its verifier

**`compPExportG_sound`**: tables accepted, with Plonky3's selectors, for
AIRs with the normal forms of `compPAirsG Vs` (what `compp-verify` checks
of its own AIRs, through `lake exe circuit compare-compp`) carry, in their
memory, 496 bits and a region whose witness makes every verifier in `Vs`,
with `J` closed to `Poseidon2SKI.Pcomb`, evaluate to `K` on the bits'
comb: `CompM.composedP_sound`'s conclusion, for every accepted proof.  It
needs at least one verifier, and each verifier's only free variable to
be the jet's.
`compPExport_sound` is its instance for `p2pre h`, whose evaluation means
a Poseidon2 preimage (`Ski/P2PreSound.lean`); `p2commit c pat`'s is in
`Ski/P2Commit.lean`.
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit ComposedPText

set_option maxRecDepth 100000 in
/-- The circuit is guarded. -/
theorem compPG_guarded (Vs : List OTerm) : ∀ A ∈ compPAirsG Vs, A.cons.all E.guarded = true := by
  intro A hA
  simp only [compPAirsG, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Acceptance of the circuit's data is `CompPOK`. -/
theorem compPOK_ofG {Vs : List OTerm} {ts : List Table} (hacc : Accepted (compPAirsG Vs) ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧
      CompPOK (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
        (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length
        (blankMO shpP 1 Vs).stk JP2 rootP (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1
        (blankRootsO shpP 1 Vs) C Mm Pg Wt Sg Pi Po Pp Px := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := hacc
  match ts, hl with
  | [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px], _ =>
    have z : (compPAirsG Vs).zip [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] =
        compPTables (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
          (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length
          (blankMO shpP 1 Vs).stk JP2 rootP (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1
          (blankRootsO shpP 1 Vs) C Mm Pg Wt Sg Pi Po Pp Px := rfl
    have mem : ∀ A T, (A, T) ∈ compPTables (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
          (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length
          (blankMO shpP 1 Vs).stk JP2 rootP (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1
          (blankRootsO shpP 1 Vs) C Mm Pg Wt Sg Pi Po Pp Px → Sat A T ∧ (A.pre = 0 ∨ PreIs A T) :=
      fun A T hm => hsat (A, T) (z ▸ hm)
    rw [z] at hbal hht htwo
    have pre : ∀ A T, (A, T) ∈ compPTables (blankMO shpP 1 Vs).hd (blankMO shpP 1 Vs).stk
          (blankMO shpP 1 Vs).heap.length (blankRootsO shpP 1 Vs).length
          (blankMO shpP 1 Vs).stk JP2 rootP (blankMO shpP 1 Vs).heap (BT.nleaves shpP) 1
          (blankRootsO shpP 1 Vs) C Mm Pg Wt Sg Pi Po Pp Px → A.pre ≠ 0 → PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    refine ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ⟨(mem _ _ (by simp [compPTables])).1,
      (mem _ _ (by simp [compPTables])).1, (mem _ _ (by simp [compPTables])).1,
      (mem _ _ (by simp [compPTables])).1,
      sat_of_withBlocks (mem p2inAirB Pi (by simp [compPTables])).1,
      sat_of_withBlocks (mem p2outAirB Po (by simp [compPTables])).1,
      sat_of_withBlocks (mem p2AirB Pp (by simp [compPTables])).1,
      pre _ _ (by simp [compPTables]) (by show (5 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compPTables]) (by show (3 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compPTables]) (by show (2 : Nat) ≠ 0; decide),
      pre _ _ (by simp [compPTables]) (by show (6 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

theorem absorbO_closed : ∀ (m x : Nat), ¬ Occ x (absorbO m)
  | 0, _, h => nomatch h
  | m + 1, x, h => by
    cases h with
    | left _ h => nomatch h
    | right _ h => exact absorbO_closed m x h

theorem badO_closed (x : Nat) : ¬ Occ x badO := fun h => by
  cases h with
  | left _ h => exact absurd (fresh_toO _ 0 x h) (Nat.not_lt_zero _)
  | right _ h => nomatch h

theorem chkO_closed : ∀ (es : List Bool) (m x : Nat), ¬ Occ x (chkO es m)
  | [], m, x, h => absorbO_closed m x h
  | e :: es, m, x, h => by
    obtain ⟨h', hx⟩ := occ_abs h
    have side : ∀ (b : Bool), ¬ Occ x (if b then chkO es m else badO) ∧ ¬ Occ x (if b then badO else chkO es m) := by
      intro b; cases b
      · exact ⟨badO_closed x, chkO_closed es m x⟩
      · exact ⟨chkO_closed es m x, badO_closed x⟩
    cases h' with
    | left _ h'' =>
      cases h'' with
      | left _ h3 => cases h3; exact hx rfl
      | right _ h3 => exact (side e).1 h3
    | right _ h'' => exact (side e).2 h''

/-- **The verifier's only variable is the jet's.** -/
theorem verifierO_occ (h x : Nat) (hx : Occ x (verifierO h)) : x = JP2 := by
  obtain ⟨h1, hx0⟩ := occ_abs hx
  obtain ⟨h2, _⟩ := occ_abs h1
  cases h2 with
  | left _ h3 =>
    cases h3 with
    | left _ h4 => cases h4; rfl
    | right _ h4 => exact absurd h4 (chkO_closed _ _ x)
  | right _ h3 => cases h3; exact absurd rfl hx0

theorem shpP_nleaves : BT.nleaves shpP = 496 := combBT_nleaves 496 (by decide)

/-- **Soundness of the circuit with the Poseidon2 jet**, for any verifiers
    whose only free variable is the jet's: an accepted proof has in its
    memory 496 bits and a region whose witness makes every verifier, with
    `J` closed to `Pcomb`, evaluate to `K` on the bits. -/
theorem compPExportG_sound {Vs : List OTerm} (hVs : 0 < Vs.length) (hocc : ∀ V ∈ Vs, ∀ x, Occ x V → x = JP2)
    {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirsG Vs) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 496 (regionM (memOf Mm) 496 1) = some w ∧
      EvalRel (Vs.map (·.close (jetEnv JP2)), SameShape (combBT 496))
        (fillB (combBT 496) (bitsM (memOf Mm)) 0) w := by
  have hacc' := accepted_transfer hs ((acceptedP_iff_of (compPG_guarded Vs) hs ts).1 hacc)
  obtain ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ok⟩ := compPOK_ofG hacc'
  refine ⟨C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px, rfl, ?_⟩
  have hv : ∀ V ∈ Vs, ∀ x, Occ x V → x < JP2 + 1 := fun V hV x hx => by
    rw [hocc V hV x hx]; exact Nat.lt_succ_self _
  have hP : JP2 + 1 < P := by decide
  have hroot : rootP < P := by
    have := ok.heap_lt
    have hfit := cMachineO_fitsB (JP2 + 1) (fun _ => false) shpP (List.replicate 1 .S) Vs
      (fun i c h' => blank_region 1 i c h' _) hv
    have : rootP < (blankMO shpP 1 Vs).heap.length := hfit.2.2
    omega
  have h499 : 499 ≤ (blankMO shpP 1 Vs).heap.length := by
    have := blankO_prefix shpP 1 Vs
    rw [shpP_nleaves] at this
    omega
  have hcp := ok.acceptsCP hv hVs hP (by decide) hroot h499
  have hl : (regionM (memOf Mm) (BT.nleaves shpP) 1).length = (List.replicate 1 Cell.S).length := by
    rw [List.length_replicate]; exact ok.region_len
  obtain ⟨_, hstk, hR, _, _, _⟩ := cMachineO_public (bitsM (memOf Mm)) (fun _ => false) shpP
    (regionM (memOf Mm) (BT.nleaves shpP) 1) (List.replicate 1 .S) Vs hl
  have hroot' : rootP = combRoot (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) :=
    combRoot_public _ _ shpP (by rw [hl]; rfl)
  have hroots : blankRootsO shpP 1 Vs = (cHeapO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) Vs).2 :=
    hR.symm
  have hnil : (blankMO shpP 1 Vs).stk =
      (cHeapO (bitsM (memOf Mm)) shpP (regionM (memOf Mm) (BT.nleaves shpP) 1) Vs).1.length := hstk.symm
  rw [hroot', hroots, hnil] at hcp
  have hwf := ok.regionWF
  rw [shpP_nleaves] at hwf hcp
  exact composedP_sound hwf (fun _ _ h' => absurd h' List.not_mem_nil) hcp


/-- **Soundness of the circuit for `p2pre h`.** -/
theorem compPExport_sound {h : Nat} {Rs : List AirD} {ts : List Table}
    (hs : sameAirsB Rs (compPAirs h) = true) (hacc : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Pi Po Pp Px, ts = [C, Mm, Pg, Wt, Sg, Pi, Po, Pp, Px] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) 496 (regionM (memOf Mm) 496 1) = some w ∧
      EvalRel ((VsP h).map (·.close (jetEnv JP2)), SameShape (combBT 496))
        (fillB (combBT 496) (bitsM (memOf Mm)) 0) w :=
  compPExportG_sound (Vs := VsP h) (Nat.zero_lt_succ _)
    (fun V hV x hx => by
      simp only [VsP, List.mem_cons, List.not_mem_nil, or_false] at hV
      subst hV
      exact verifierO_occ h x hx) hs hacc

end Circuit
