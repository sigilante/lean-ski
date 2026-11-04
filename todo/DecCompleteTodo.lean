import Ski.Circuit.CompDCompleteFinal

/-!
# The open gap of the `dec` jet's completeness (not on the lib path)

`Circuit.compDG_complete_dec` (`Ski/Circuit/CompDCompleteFinal.lean`,
sorry-free) proves completeness of the circuit with the `dec` jet for every
honest run (`DRun.Honest`: each row a plain step, a halted row repeated, or
`DecJet.decRow`'s step, as `composed check-dec-run` replays it), the CPU
table the honest one (`DRun.cpuTableD`), given a DEC table that provides
the run's jet calls (`DecProvides`).  The gap is that table,
`decProvides_exists`: `decair.rs`'s `trace` in Lean, one row per cell
pattern of each call's subject (a `Cell` wrapper per cell noun, an `Atom`
wrapper and a `Cons` per bit and a nil per atom), padded with zero rows,

- satisfying `Dec.decAir`'s 717 constraints, per kind CELL/ATOM/CONS/NIL
  and on the zero row (the converse of `dec_sound_row`, `slotOK_all`);
- `Wide`, and its 25 reads and its writes `HonestMem` (the writes are
  `DecJet.outCells`, which `decRow`'s `wrs` puts in the memory);
- on `decn`, `decb`, `decd`, `decx`: each call's rows telescope (the shape
  `CompDTree`, `CompDHead`, `CompDVerd` read back), leaving the call's
  `decnT` received and `decxT` sent, the negation of `DRun.jetSendsD`.

The padding is done: the zero row satisfies DEC and is quiet (`decZero_sat`,
`decZero_sends`), so a run without jet calls is complete unconditionally
(`compDG_complete_nojet`); what remains is the calls' rows.

The DEC height must hold the run's DEC rows; the hypothesis `hHD` is to
be stated once the rows are defined (`decRows.length ≤ 2 ^ LD`).
-/

namespace Circuit

open B Air Compose CompM Mach Stmt Wit ComposedDText

/-- **The gap**: an honest run has a DEC table providing its jet calls. -/
theorem decProvides_exists {R LD : Nat} (hLD : LD ≤ 20) {Rn : DRun} {m0 : Mach} {nilA : Nat}
    (hA : Rn.Honest m0 nilA) (hK : Rn.e (Rn.n - 1) < 2 ^ R) :
    ∃ D : Table, D.h = 2 ^ LD ∧ DecProvides Rn (2 ^ R) D := by
  sorry

/-- **Completeness of the circuit for `decpre p`**, from the gap: an honest
    run of the decrement statement at the verifier's heights gives tables
    that AIRs with the normal forms of `compDAirs p W` accept, with
    Plonky3's selectors. -/
theorem decpre_complete_log {p R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compDAirs p W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    (hNW : BT.nleaves shpD + W ≤ 2 ^ 8)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : DRun.Honest ⟨A, JD, (cHeapO ρ shpD region (VsD p)).2, e, (VsD p).length, row⟩
      (cMachineO ρ shpD region (VsD p)) (cHeapO ρ shpD region (VsD p)).1.length)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e 0 < 2 ^ R) :
    ∃ C Mm Pg Wt Sg D, AcceptedP Rs [C, Mm, Pg, Wt, Sg, D] ∧
      Pg = progTableC (blankMO shpD W (VsD p)).heap (BT.nleaves shpD) W ∧
      Wt = witTable A (BT.nleaves shpD) W ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ D.h = 2 ^ LD ∧ memOf Mm = A ∧ ∀ i, i ≤ e 0 → rowOf C i = row i := by
  obtain ⟨D, hD, hdec⟩ := decProvides_exists (R := R) hLD hA hK
  obtain ⟨C, Mm, Pg, Wt, Sg, hacc, hC, hPg, hWt, hCh, hMh, hmem, hrow⟩ :=
    compDG_complete_dec hR hLm hLD hs hrl hr hNW hA hfit hlen hK hD hdec
  exact ⟨C, Mm, Pg, Wt, Sg, D, hacc, hPg, hWt, hCh, hMh, hD, hmem, hrow⟩

end Circuit
