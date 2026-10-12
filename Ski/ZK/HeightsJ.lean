import Ski.ZK.Heights
import Ski.ZK.CompPHonest

/-!
# The jet circuits' honest heights are public

The honest tables `CRun.honest_zk` and `P2Run.honest_zkP` take have
heights that are the statement's budgets or public lengths: the CPU's `K`
rows, the memory's cells, the public program, segment and level tables',
the witness table's fixed height, the provider tables' (rows of the public
jet table), and POP's, INSTW's, P2IN's, P2OUT's and the Poseidon2 table's
budgets.  With the memory at `2^Lm` cells and the witness table at `2^8`
rows, as the statement fixes them, no height depends on the witness, so
`transcript_zkGH` applies with those heights.  Lean's provider tables are
the jet table's rows; the Rust pads them to at least `2^8`
(`bench/plonky3/src/compj.rs`), and both are public.
-/

namespace Circuit

open ZKF B Air JetTable Compose CompM Mach

/-- **The honest heights of the circuit with jets**: `K` CPU rows, `2^Lm`
    memory cells, the public tables', `2^8` witness rows, the provider
    tables' rows, and the POP and INSTW budgets. -/
theorem compJ_honest_heights (R : CRun) (hd0 stk0 ctr0 nilA : Nat) (heap : List Cell) (N W K HP HW Lm : Nat)
    (hlen : R.A.length = 2 ^ Lm) (hNW : N + W ≤ 2 ^ 8) :
    heightsOf (compJTables hd0 stk0 ctr0 R.n nilA heap N W R.segRoots R.jroots R.jets (R.cpuTableCJ K)
      (memTable5 R.A (cpuAirCJ hd0 stk0 ctr0 R.n nilA) (progAirC heap N W) popAirCJ instwAirCJ (witAir N W)
        (R.cpuTableCJ K) (progTableC heap N W) (R.J.popTable K HP) (R.J.instwTable K HW) (witTable R.A N W))
      (progTableC heap N W) (witTable R.A N W) (segsPub R.segRoots)
      (provTableCJ (rootsRowsCJ R.jroots) (R.J.cntRoots K)) (provTableCJ (hdrRowsCJ R.jets) (R.J.cntHdr K))
      (provTableCJ (tmplRowsCJ R.jets) (R.J.cntTmpl K)) (R.J.popTable K HP) (R.J.instwTable K HW)) =
    [K, 2 ^ Lm, (progTableC heap N W).h, 2 ^ 8, (segsPub R.segRoots).h, (rootsRowsCJ R.jroots).length,
      (hdrRowsCJ R.jets).length, (tmplRowsCJ R.jets).length, HP, HW] := by
  have hW : (witTable R.A N W).h = 2 ^ 8 := witRows_len hNW
  show [K, R.A.length, (progTableC heap N W).h, (witTable R.A N W).h, (segsPub R.segRoots).h,
    (rootsRowsCJ R.jroots).length, (hdrRowsCJ R.jets).length, (tmplRowsCJ R.jets).length, HP, HW] = _
  rw [hlen, hW]

/-- **The honest heights of the circuit with the Poseidon2 jet**: `K` CPU
    rows, `2^Lm` memory cells, the public tables' (the level table's 512),
    the witness table's fixed rows (a function of `N` and `W`),
    and the P2IN, P2OUT and Poseidon2 budgets. -/
theorem compP_honest_heights (R : P2Run) (hd0 stk0 ctr0 nilA J root : Nat) (heap : List Cell)
    (N W K HI HO HP Lm : Nat) (hlen : R.A.length = 2 ^ Lm) :
    heightsOf (compPTables hd0 stk0 ctr0 R.n nilA J root heap N W R.segRoots (R.cpuTableP K)
      (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n nilA J root) (progAirC heap N W) p2inAirB p2outAirB (witAirP N W)
        (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO) (witTableP R.A N W))
      (progTableC heap N W) (witTableP R.A N W) (segsPub R.segRoots) (R.pinTable K HI) (R.poutTable K HO)
      (R.p2Table K HP) (idxPub (R.calls K))) =
    [K, 2 ^ Lm, (progTableC heap N W).h, (witRowsP N W).length, (segsPub R.segRoots).h, HI, HO, HP, 512] := by
  simp only [heightsOf, compPTables, List.map_cons, List.map_nil]
  rw [show (memTable5 R.A (cpuAirP2 hd0 stk0 ctr0 R.n nilA J root) (progAirC heap N W) p2inAirB p2outAirB
      (witAirP N W) (R.cpuTableP K) (progTableC heap N W) (R.pinTable K HI) (R.poutTable K HO)
      (witTableP R.A N W)).h = R.A.length from rfl, hlen, idxPub_h,
    show (witTableP R.A N W).h = (witRowsP N W).length from rfl]
  rfl

end Circuit
