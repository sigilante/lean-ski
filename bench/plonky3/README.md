# The AIR in Plonky3, checked against Lean

`src/main.rs` is the AIR of `Ski/Air.lean` in Plonky3 0.8: a batch STARK
over BabyBear with three tables joined by one LogUp bus, `mem`, whose
entries are `(address, tag, a, b)`.

- **CPU**: one row per machine transition, padded to a power-of-two budget
  with halted rows. A row holds the registers `hd`, `stk`, `ctr`, a one-hot
  selector for its kind, the fields of the cells it reads, and 24 bits per
  read that range-check the address below `ctr`. The kinds are the cases of
  `Air.stepG` and `Air.haltRow`: an unwind, `I`, `K`, `S`, and the six ways a
  combinator can lack arguments. A kind fixes the tags of its reads, so the
  lookups check exactly the cells the Lean rule reads, and the writes are
  lookups at `ctr`, `ctr + 1`, `ctr + 2`.
- **Memory**: the committed memory table, one entry per address in order
  (`addr` starts at 0 and increases by 1), with each entry's lookup count.
- **Program**: the loaded heap of the public term, a preprocessed table the
  verifier rebuilds from the term. Every loaded cell is looked up in memory,
  which pins the memory table's prefix.

The verifier builds its AIRs and the program table's preprocessed
commitment from the public term alone, reads the CPU and memory heights
from the proof, and rejects heights above `2^21` or a program height other
than the term's. It never sees the traces.

## Checked against Lean

For every table it proves, the prover writes the same table (the memory
table and the rows) in the format of `Ski/AirCheck.lean`. `lake exe aircheck`
decides the AIR's constraints on it with `Air.checkA`: it accepts exactly
the tables that satisfy `Air.Accepts` (`Air.checkA_iff`), and by
`Air.air_sound_eval` an accepted table proves the evaluation it ends on.
Four tampered tables, changed identically in the trace and in the Lean
table, must fail both: the prover must produce a proof and the verifier
must reject it, and `aircheck` must reject the table. They are a forged
memory cell, a wrong transition, an early halt, and a forged program (the
honest run of `I S` offered for the public term `I K`).

```
lake env lean --run bench/Dump.lean > corpus.txt        # from the repository root
cd bench/plonky3 && cargo build --release
./target/release/ski-air ../../corpus.txt tables         # prove, verify, tamper
cd ../.. && lake build aircheck
lake exe aircheck bench/plonky3/tables/{ik,skks,compiled_*,interpreted_*,sumto_us}.txt
lake exe aircheck bench/plonky3/tables/tampered_*.txt    # each must be REJECT
```

## Measured, 2026-09-27, Apple M4 Max, release build

```
row               contr   rows budget  memory  prove s verify s  verdict
ik                    1      3     16      16     0.01    0.005  verified
skks                  2      6     16      16     0.06    0.001  verified
compiled_up         493   1207   2048    8192     0.05    0.009  verified
compiled_uq         440   1078   2048    4096     0.04    0.007  verified
compiled_ur         530   1297   2048    8192     0.05    0.009  verified
interpreted_up     2014   4909   8192   16384     0.13    0.012  verified
interpreted_uq     2029   4949   8192   16384     0.13    0.012  verified
interpreted_ur     2589   6308   8192   16384     0.13    0.012  verified
sumto_us          10297  25074  32768   65536     0.48    0.014  verified

tampered tables (each proof must be rejected by the verifier):
forged_cell      rejected by the verifier (verify: Lookup(TerminalSumNonZero))
wrong_step       rejected by the verifier (verify: Verification(OodEvaluationMismatch ...))
early_halt       rejected by the verifier (verify: Lookup(TerminalSumNonZero))
forged_loaded    rejected by the verifier (verify: Verification(InvalidOpeningArgument(...)))
```

`lake exe aircheck` accepts all nine honest tables (in about 1.4 s) and
rejects the four tampered ones. The forged program fails at the opening
check: the verifier computes the program table's commitment from the
public term, so the proof's transcript no longer matches. Timings vary by
a few percent between runs. The `rows` column equals `lake exe aircost`'s on
every corpus row; `prove s` includes the setup.

## What this is not

- **Not zero knowledge.** The PCS is not hiding, and the first row loads the
  whole term in the clear. Hiding the witness needs a hiding PCS and the
  loaded heap committed rather than public.
- **Not bound to an output.** As in `Ski/Air.lean`, the constraints fix the
  run, not the value it ends on.
- **Security is Plonky3's benchmark setting**: blowup 2, 100 queries and 16
  bits of query grinding. Plonky3's `conjectured_soundness_bits` gives 116,
  but that counts the query phase only and Plonky3 marks it as not a
  soundness bound; the composite conjectured bound (opening batching, the
  LogUp argument, DEEP, folding) is lower and was not computed here. Batch
  grinding would raise it.
- **The range checks** are sound because the verifier accepts CPU and
  memory heights only up to `2^21`: addresses stay below `2^21` and
  counters below `2^23`, so a read at or above the counter wraps to at
  least `p − 2^21`, which no 24-bit decomposition represents.
- **The link to Lean is per table.** The Lean checker decides `Accepts` on
  each table the prover proves; that every table the verifier accepts
  satisfies `Accepts` is argued in the header of `src/main.rs`, not proved
  in Lean.
