import Ski.Circuit.CompJSound
import Ski.Circuit.CompPred
open Term

/-!
# The composed circuit with jets checks the composed statement

**`compJExport_sound`**: tables accepted — with Plonky3's selectors — for
AIRs with the normal forms of the composed circuit with jets of a
statement and its jet table (what `compj-verify` checks of its own AIRs,
through `lake exe circuit compare-compJ`), for a jet table the verifier's
statement check accepts (`Air.jetStmtC`) and whose numbers fit, carry, in
their memory, bits and a region whose witness makes every term evaluate to
`K` on those bits: `compExportG_sound`'s conclusion, with jets.  The jet
table's roots are licensed over the heap of the bits and region the memory
holds (`Air.jetStmtC_sound`), which is what an instantiation row needs.

`predJExport_sound` is the predicate statement's case, and `checkCJ_pred`
the checker's.
-/

namespace Circuit

open B Air Compose CompM Stmt Mach Wit

/-- The composed circuit with jets is guarded, for every statement and jet
    table. -/
theorem compJ_guarded (shp : BT) (Ps : List Term) (W : Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) :
    ∀ A ∈ compJAirs shp Ps W roots jets, A.cons.all E.guarded = true := by
  intro A hA
  simp only [compJAirs, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Acceptance of the composed circuit with jets is `CJOK`. -/
theorem compJOK_of {shp : BT} {Ps : List Term} {W : Nat} {roots : List (Nat × Nat)} {jets : List Air.Jet}
    {ts : List Table} (h : Accepted (compJAirs shp Ps W roots jets) ts) :
    ∃ C Mm Pg Wt Sg Rt Hd Tm Po Iw, ts = [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] ∧
      CJOK (blankM shp W Ps).hd (blankM shp W Ps).stk
        (blankM shp W Ps).heap.length (blankRoots shp W Ps).length
        (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
        (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw := by
  obtain ⟨hl, hsat, hbal, hht, htwo⟩ := h
  match ts, hl with
  | [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw], _ =>
    have mem : ∀ A T, (A, T) ∈ (compJAirs shp Ps W roots jets).zip [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] →
        Sat A T ∧ (A.pre = 0 ∨ PreIs A T) := fun A T hm => hsat (A, T) hm
    have z : (compJAirs shp Ps W roots jets).zip [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] =
        compJTables (blankM shp W Ps).hd (blankM shp W Ps).stk
          (blankM shp W Ps).heap.length (blankRoots shp W Ps).length
          (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
          (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw := rfl
    rw [z] at mem hbal hht htwo
    have pre : ∀ A T, (A, T) ∈ compJTables (blankM shp W Ps).hd (blankM shp W Ps).stk
          (blankM shp W Ps).heap.length (blankRoots shp W Ps).length
          (blankM shp W Ps).stk (blankM shp W Ps).heap (BT.nleaves shp) W
          (blankRoots shp W Ps) roots jets C Mm Pg Wt Sg Rt Hd Tm Po Iw → A.pre ≠ 0 → PreIs A T := by
      intro A T hm hp
      rcases (mem A T hm).2 with h0 | h0
      · exact absurd h0 hp
      · exact h0
    refine ⟨C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw, rfl,
      ⟨(mem _ _ (by simp [compJTables])).1, (mem _ _ (by simp [compJTables])).1,
       (mem _ _ (by simp [compJTables])).1, (mem _ _ (by simp [compJTables])).1,
       (mem _ _ (by simp [compJTables])).1, (mem _ _ (by simp [compJTables])).1,
       pre _ _ (by simp [compJTables]) (by show (5 : Nat) ≠ 0; decide),
       pre _ _ (by simp [compJTables]) (by show (3 : Nat) ≠ 0; decide),
       pre _ _ (by simp [compJTables]) (by show (2 : Nat) ≠ 0; decide),
       pre _ _ (by simp [compJTables]) (by show (2 : Nat) ≠ 0; decide),
       pre _ _ (by simp [compJTables]) (by show (7 : Nat) ≠ 0; decide),
       pre _ _ (by simp [compJTables]) (by show (11 : Nat) ≠ 0; decide), hbal, hht, htwo⟩⟩

/-- **Soundness of the composed circuit with jets, for any evaluation
    statement**: for a jet table the verifier's check accepts and whose
    numbers fit, an accepted proof's memory holds bits of the shape and a
    region whose witness makes every term evaluate to `K` on those bits. -/
theorem compJExport_sound {shp : BT} {Ps : List Term} {W : Nat} {text : String}
    {tmpls : List (List Nat × OTerm)} {Rs : List AirD} {ts : List Table}
    (hPs : 0 < Ps.length) (hj : jetStmtC text shp W Ps tmpls = true)
    (hfit : (jetTableC shp W Ps tmpls).2.all jetFitB = true)
    (hs : sameAirsB Rs (compJAirs shp Ps W (jetTableC shp W Ps tmpls).1 (jetTableC shp W Ps tmpls).2) = true)
    (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Rt Hd Tm Po Iw, ts = [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] ∧ ∃ w,
      cWitness (bitsM (memOf Mm)) (BT.nleaves shp) (regionM (memOf Mm) (BT.nleaves shp) W) = some w ∧
      EvalRel (Ps, SameShape shp) (fillB shp (bitsM (memOf Mm)) 0) w := by
  have hacc := accepted_transfer hs ((acceptedP_iff_of (compJ_guarded shp Ps W _ _) hs ts).1 h)
  obtain ⟨C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw, rfl, hok⟩ := compJOK_of hacc
  have hroots := jetStmtC_sound hj (bitsM (memOf Mm)) (regionM (memOf Mm) (BT.nleaves shp) W) hok.region_len
  exact ⟨C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw, rfl, hok.sound hPs hroots hfit⟩

/-- **The composed circuit with jets of a predicate over `n` bits.** -/
def predJAirs (V x : Term) (n W : Nat) (roots : List (Nat × Nat)) (jets : List Air.Jet) : List AirD :=
  compJAirs (combBT n) [predStmt V x] W roots jets

/-- **Soundness of the predicate circuit with jets**: an accepted proof's
    memory holds `n` literal bits on which the verifier accepts `x`. -/
theorem predJExport_sound {V x : Term} {n W : Nat} (hn : 0 < n) {text : String}
    {tmpls : List (List Nat × OTerm)} {Rs : List AirD} {ts : List Table}
    (hj : jetStmtC text (combBT n) W [predStmt V x] tmpls = true)
    (hfit : (jetTableC (combBT n) W [predStmt V x] tmpls).2.all jetFitB = true)
    (hs : sameAirsB Rs (predJAirs V x n W (jetTableC (combBT n) W [predStmt V x] tmpls).1
      (jetTableC (combBT n) W [predStmt V x] tmpls).2) = true)
    (h : AcceptedP Rs ts) :
    ∃ C Mm Pg Wt Sg Rt Hd Tm Po Iw, ts = [C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw] ∧
      (slotBits (bitsM (memOf Mm)) 0 n).length = n ∧
      Eval (V ⬝ x ⬝ boolsT (slotBits (bitsM (memOf Mm)) 0 n)) K := by
  obtain ⟨C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw, rfl, w, _, _, hall⟩ := compJExport_sound (by simp) hj hfit hs h
  have hP := hall (predStmt V x) List.mem_cons_self
  rw [pred_iff, fillB_combBT _ n 0 hn] at hP
  exact ⟨C, Mm, Pg, Wt, Sg, Rt, Hd, Tm, Po, Iw, rfl, slotBits_length _ 0 n, hP⟩

/-- **A table `checkCJ` accepts proves the predicate**: the verifier accepts
    `x` on the bits its memory sets. -/
theorem checkCJ_pred {V x : Term} {n W : Nat} (hn : 0 < n) {roots : List (Nat × Nat)} {jets : List Air.Jet}
    {A : Array Cell} {ends : Array Nat} {R : Array Air.Row}
    (h : checkCJ (combBT n) W [predStmt V x] roots jets A ends R = true) :
    Eval (V ⬝ x ⬝ boolsT (slotBits (bitsOf A) 0 n)) K := by
  obtain ⟨w, _, _, hall⟩ := checkCJ_sound h
  have hP := hall (predStmt V x) List.mem_cons_self
  rwa [pred_iff, fillB_combBT _ n 0 hn] at hP

end Circuit
