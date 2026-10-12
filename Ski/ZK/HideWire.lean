import Ski.ZK.HideP3
import Ski.ZK.Reject

/-!
# The hiding circuits' per-trace facts

`pcsCloseN_fri_corpus` asks of each private table, at each trace, a
table that meets `Sat` and whose `terminal` the transcript publishes at a
known index.  For the Sudoku, hidden-term and composed circuits the
transcript publishes `[memory, CPU, witness]` terminals of the blinded
tables (`enc3`), so:
- each blinded table meets `Sat` when the unblinded one does, through
  every blinding block (`sat_setBlind`, `blind_ok`);
- index 0, 1, 2 of the view is the blinded memory, CPU and witness
  table's terminal (`sud_view_get`, `wit_view_get`, `comp_view_get`).

Accepted tables give the unblinded `Sat` (`SudOK`, `WitOK`, `CompOK`).
The preprocessed columns, interpolated on the trace domain, give `hb`'s
preprocessed part for any table (`preInterp_spec`).  A circuit's private
tables each meet `tabsHonest_corpus_ite`, and `pcsCloseN_fri_tabs`
combines them into the `PCSCloseN` its transcript theorem takes as
`hpcs`.
-/

namespace Circuit

open ZKF

/-- **Sudoku**: the blinded private tables meet `Sat`, and the view
    publishes their terminals at 0, 1, 2. -/
theorem sud_wire {hd0 stk0 ctr0 : Nat} {heap : List Cell} {C Mm Pg Wt : Table}
    (h : SudOK hd0 stk0 ctr0 heap C Mm Pg Wt) (pre : String → EF) (β : EF) (t : Nat → Tup) :
    Sat memAirC (Mm.setBlind 5 (t 0)) ∧
    Sat (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    Sat witAirS (Wt.setBlind 1 (t 1)) ∧
    (sudViewN pre β hd0 stk0 ctr0 C Mm Wt t).getD 0 EF.zero = terminal pre β memAirC (Mm.setBlind 5 (t 0)) ∧
    (sudViewN pre β hd0 stk0 ctr0 C Mm Wt t).getD 1 EF.zero =
      terminal pre β (cpuAirS hd0 stk0 ctr0 SudokuText.ACC) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    (sudViewN pre β hd0 stk0 ctr0 C Mm Wt t).getD 2 EF.zero = terminal pre β witAirS (Wt.setBlind 1 (t 1)) := by
  obtain ⟨b1, b2, _, _, _, _, b7, b8, _, _⟩ := blind_ok hd0 stk0 ctr0 0 0 0 0
  exact ⟨sat_setBlind h.mem b7 _, sat_setBlind (sat_setBlind h.cpu b1 _) b2 _, sat_setBlind h.wit b8 _, rfl, rfl, rfl⟩

/-- **The hidden-term circuit**: as `sud_wire`. -/
theorem wit_wire {hd0 stk0 ctr0 : Nat} {heap : List Cell} {W : Nat} {C Mm Pg Wt : Table}
    (h : WitOK hd0 stk0 ctr0 heap W C Mm Pg Wt) (pre : String → EF) (β : EF) (t : Nat → Tup) :
    Sat memAirC (Mm.setBlind 5 (t 0)) ∧
    Sat (cpuAirW hd0 stk0 ctr0) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    Sat (witAirW W) (Wt.setBlind WT_BLIND (t 1)) ∧
    (witViewN pre β hd0 stk0 ctr0 W C Mm Wt t).getD 0 EF.zero = terminal pre β memAirC (Mm.setBlind 5 (t 0)) ∧
    (witViewN pre β hd0 stk0 ctr0 W C Mm Wt t).getD 1 EF.zero =
      terminal pre β (cpuAirW hd0 stk0 ctr0) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    (witViewN pre β hd0 stk0 ctr0 W C Mm Wt t).getD 2 EF.zero = terminal pre β (witAirW W) (Wt.setBlind WT_BLIND (t 1)) := by
  obtain ⟨_, _, b3, b4, _, _, b7, _, b9, _⟩ := blind_ok hd0 stk0 ctr0 0 0 0 W
  exact ⟨sat_setBlind h.mem b7 _, sat_setBlind (sat_setBlind h.cpu b3 _) b4 _, sat_setBlind h.wit b9 _, rfl, rfl, rfl⟩

/-- **The composed circuit**: as `sud_wire`. -/
theorem comp_wire {hd0 stk0 ctr0 n nilA : Nat} {heap : List Cell} {N W : Nat} {roots : List Nat}
    {C Mm Pg Wt Sg : Table} (h : CompOK hd0 stk0 ctr0 n nilA heap N W roots C Mm Pg Wt Sg)
    (pre : String → EF) (β : EF) (t : Nat → Tup) :
    Sat memAirC (Mm.setBlind 5 (t 0)) ∧
    Sat (cpuAirC hd0 stk0 ctr0 n nilA) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    Sat (witAir N W) (Wt.setBlind WT_BLIND (t 1)) ∧
    (compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t).getD 0 EF.zero = terminal pre β memAirC (Mm.setBlind 5 (t 0)) ∧
    (compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t).getD 1 EF.zero =
      terminal pre β (cpuAirC hd0 stk0 ctr0 n nilA) ((C.setBlind BLA (t 1)).setBlind BLB (t 0)) ∧
    (compViewN pre β hd0 stk0 ctr0 n nilA N W C Mm Wt t).getD 2 EF.zero =
      terminal pre β (witAir N W) (Wt.setBlind WT_BLIND (t 1)) := by
  obtain ⟨_, _, _, _, b5, b6, b7, _, _, b10⟩ := blind_ok hd0 stk0 ctr0 n nilA N W
  exact ⟨sat_setBlind h.mem b7 _, sat_setBlind (sat_setBlind h.cpu b5 _) b6 _, sat_setBlind h.wit b10 _, rfl, rfl, rfl⟩

-- ---------------------------------------------------------------------------
-- The preprocessed columns, interpolated
-- ---------------------------------------------------------------------------

/-- **A table's preprocessed column `i`, interpolated on `⟨g⟩`.** -/
def preInterp (Tb : Table) (g : F) (m i : Nat) : List F :=
  finterp ((cosetL 1 g (m + 1)).zip ((List.range (m + 1)).map fun r => Tb.pre r i))

/-- **The interpolated preprocessed columns** take the table's values at
    `gʳ`, with at most `m + 1` coefficients. -/
theorem preInterp_spec (Tb : Table) {g : F} {m : Nat}
    (hinj : ∀ a b, a < m + 1 → b < m + 1 → fpow g a = fpow g b → a = b) (i : Nat) :
    (preInterp Tb g m i).length ≤ m + 1 ∧
    ∀ r, r < m + 1 → fval (fpow g r) (preInterp Tb g m i) = Tb.pre r i := by
  have hT : (cosetL 1 g (m + 1)).length = m + 1 := cosetL_length 1 g (m + 1)
  have hV : ((List.range (m + 1)).map fun r => Tb.pre r i).length = m + 1 := by
    rw [List.length_map, List.length_range]
  have hl : (cosetL 1 g (m + 1)).length = ((List.range (m + 1)).map fun r => Tb.pre r i).length := by rw [hT, hV]
  refine ⟨?_, fun r hr => ?_⟩
  · unfold preInterp
    refine Nat.le_trans (finterp_length _) ?_
    rw [List.length_zip, hT, hV, Nat.min_self]; exact Nat.le_refl _
  · have hr' : r < (cosetL 1 g (m + 1)).length := by rw [hT]; exact hr
    have hmem := zip_mem hr' hl
    have := finterp_eval _ (by rw [map_fst_zip' hl]; exact cosetL_one_nodup hinj) _ hmem
    rw [cosetL_getElem g (m + 1) 1 r hr', one_mul'] at this
    unfold preInterp
    rw [this, List.getElem_map, List.getElem_range]

end Circuit
