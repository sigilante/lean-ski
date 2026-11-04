import Ski.Circuit.CompDComplete

/-!
# The open gap of the `dec` jet's completeness (not imported)

`Circuit.compDG_complete_of` (`Ski/Circuit/CompDComplete.lean`, sorry-free)
reduces completeness of the circuit with the `dec` jet to one statement:
every run `AcceptsCD` accepts has an honest CPU table and an honest DEC
table meeting `DecHonest`.  That statement is the gap, `decHonest_exists`
below; from it, `decpre_complete_log` follows with no other assumption.

What `decHonest_exists` needs, the analogue of the Poseidon2 chain
`CompPHonest` → `CompPBal` → `CompPComplete` → `CompPSat`/`CompPCpuSat`:

- **the CPU** (`P2Run.cpuTableP`'s analogue): the composed CPU's honest row
  (`cpuColC`), and on a `DecJet.decRow` row the selector `DECSEL`, the kinds
  cleared, the reads of the atom `J` at the head and of the stack cell
  `cons p rest` range-checked, `DROOT`/`DCTR` the row's result; its `Sat`
  (with `CompDKind.kind_factsD`, as `CompPCpuSat.cpuP_sat`), its `mem` and
  `segs` honesty (as `cpuP_honest`, `cpuP_segs`), clear blinding flags;
- **DEC** (`decair.rs`'s `trace`): per jet call one row per cell pattern of
  the subject (a `Cell` wrapper per cell noun, an `Atom` wrapper, a `Cons`
  per bit and a nil per atom), the borrow chain's and the need tree's
  columns, the 25 slots' addresses, tags, fields and range bits, padded with
  zero rows; its 717 constraints (`Sat Dec.decAir`), `Wide`, its 25 reads
  and its writes `HonestMem` (the writes are `DecJet.outCells`, which
  `decRow`'s `wrs` puts in the memory);
- **the jet buses**: on `decn`, `decb`, `decd` the call's rows telescope
  (each sent tuple received once), and the CPU's `decn` send and `decx`
  receive meet the call's subject and result rows (`hjet`).
-/

namespace Circuit

open B Air Compose CompM Mach Stmt Wit ComposedDText

/-- **The gap**: a run of the circuit with the `dec` jet has honest CPU and
    DEC tables at the statement's heights, the CPU decoding back to the
    run.  The DEC height must hold the run's DEC rows (`hHD`, to be stated
    once DEC's honest rows are defined: `decRows.length ≤ 2 ^ LD`). -/
theorem decHonest_exists {R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {Vs : List OTerm} {W : Nat} {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCD A (cMachineO ρ shpD region Vs) JD (cHeapO ρ shpD region Vs).2
      (cHeapO ρ shpD region Vs).1.length Vs.length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e (Vs.length - 1) < 2 ^ R) :
    ∃ C D : Table, C.h = 2 ^ R ∧ D.h = 2 ^ LD ∧ DecHonest A (cpuDG Vs W) (blankRootsO shpD W Vs) C D ∧
      ∀ i, i ≤ e (Vs.length - 1) → rowOf C i = row i := by
  sorry

/-- **Completeness of the circuit for `decpre p`**, from the gap: an honest
    run of the decrement statement (the run `composed check-dec-run`
    replays, each row `Air.stepRow` or `DecJet.decRow`) at the verifier's
    heights gives tables that AIRs with the normal forms of `compDAirs p W`
    accept, with Plonky3's selectors. -/
theorem decpre_complete_log {p R Lm LD : Nat} (hR : R ≤ 20) (hLm : Lm ≤ 20) (hLD : LD ≤ 20)
    {W : Nat} {Rs : List AirD} (hs : sameAirsB Rs (compDAirs p W) = true)
    {ρ : Nat → Bool} {region : List Cell} (hrl : region.length = W)
    (hr : ∀ i c, region[i]? = some c → cellOK (BT.nleaves shpD + 3 + i) c = true)
    (hNW : BT.nleaves shpD + W ≤ 2 ^ 8)
    {A : List Cell} {e : Nat → Nat} {row : Nat → Air.Row}
    (hA : AcceptsCD A (cMachineO ρ shpD region (VsD p)) JD (cHeapO ρ shpD region (VsD p)).2
      (cHeapO ρ shpD region (VsD p)).1.length (VsD p).length e row)
    (hfit : Fits A) (hlen : A.length = 2 ^ Lm) (hK : e 0 < 2 ^ R) :
    ∃ C Mm Pg Wt Sg D, AcceptedP Rs [C, Mm, Pg, Wt, Sg, D] ∧
      Pg = progTableC (blankMO shpD W (VsD p)).heap (BT.nleaves shpD) W ∧
      Wt = witTable A (BT.nleaves shpD) W ∧
      C.h = 2 ^ R ∧ Mm.h = 2 ^ Lm ∧ D.h = 2 ^ LD ∧ memOf Mm = A ∧ ∀ i, i ≤ e 0 → rowOf C i = row i := by
  obtain ⟨C, D, hC, hD, hH, hrow⟩ := decHonest_exists hR hLm hLD hrl hr hA hfit hlen hK
  obtain ⟨hacc, hmem, _⟩ := compDG_complete_of hR hLm hLD hs hrl hr hNW hA hfit hlen hK hC hD hH
  exact ⟨_, _, _, _, _, _, hacc, rfl, rfl, hC, hlen, hD, hmem, hrow⟩

end Circuit
