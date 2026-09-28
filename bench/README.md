# Cost of proving SKI reduction on RISC Zero

`risc0/` runs the conformance corpus in RISC Zero's zkVM (3.0.6). It measures
the two reducers of the Lean development: tree rewriting (`step?`/`runF`,
`Ski/Fuel.lean`) and the write-once heap machine (`mstep`/`mrunC`,
`Ski/Heap.lean`).

The reducers are hand ports to Rust (`risc0/ski`), not extracted code. The
host checks them before it measures anything: both ports must reach the
reference reducer's contraction count on every row, and their values must be
equal as graphs. The guest commits the statement to its journal: the input's
SHA-256, the contraction count, and the SHA-256 of the result's shared form.

Results are never printed. An `S` contraction duplicates its argument by
reference, and printing a reduced term takes space exponential in the
reduction. An earlier version printed its results; that is the likely cause
of a kernel panic. The shared form writes each distinct node once, which
takes at most 49 KB on this corpus.

```
lake env lean --run bench/Dump.lean > corpus.txt      # from the repository root
cd bench/risc0 && cargo build --release
./target/release/host corpus.txt --native             # conformance only
./target/release/host corpus.txt                      # cycles, in the executor
./target/release/host corpus.txt --prove              # also prove and verify
```

## Measured, 2026-09-26, Apple M4 Max, CPU prover

`cycles` is the whole guest. `reduce` counts only the reduction, parsing
excluded; the heap mode's `load` is included. The guest reports it through
`cycle_count` over stdout, outside the journal.

```
row              leaves  steps  mode      cycles      reduce red/step segs
compiled_up        1397    493  tree     3358265      332360      674    4
compiled_up        1397    493  heap     3392878      409298      830    4
compiled_uq         915    440  tree     4307407      235252      534    5
compiled_uq         915    440  heap     4301006      280595      637    5
compiled_ur        1267    530  tree     5493098      382665      722    6
compiled_ur        1267    530  heap     5418340      394608      744    6
interpreted_up     2769   2014  tree    12822729     1676516      832   14
interpreted_up     2769   2014  heap    11994326     1013406      503   13
interpreted_uq     2772   2029  tree    12878377     1695506      835   14
interpreted_uq     2772   2029  heap    12031801     1016638      501   13
interpreted_ur     2856   2589  tree    13737537     2241903      865   15
interpreted_ur     2856   2589  heap    12473474     1140049      440   14
sumto_us           3531  10297  tree    34199089    15133229     1469   40
sumto_us           3531  10297  heap    22015797     3179113      308   25
```

We proved and verified one row, `compiled_up`, in both modes:

- tree: 207 s;
- heap: 228 s;
- each: four segments, a 1,124,512-byte composite receipt, and a peak prover
  RSS of 9.6 GB.

A segment of 2^20 cycles takes about 55 s here, so proving `sumto_us` in heap
mode would take about 25 minutes.

Reading it:

- **Per step, the heap machine is flat and the tree rewriter grows.** (The
  table's `red/step` truncates; the figures here round.)
  - Reduction in heap mode costs 309 cycles per contraction on the
    longest run. The
    figure falls as `load` is amortized, because each transition does
    constant work.
  - Tree mode rises to 1,470 cycles per contraction. `step?` rebuilds the
    spine above each redex, so a step costs time in proportion to the spine.
- **Reduction is the smaller part of the bill.**
  - On `sumto_us` in heap mode, reduction is 3.2M of 22M cycles.
  - Most of the rest is parsing the input and hashing the result's shared
    form, which uses a `HashMap` for sharing.
  - A prover for L2 itself would commit the heap as the zk layer's memory
    table does, and would pay neither cost.
- **This is a general-purpose zkVM, not the custom AIR's prover.**
  - It gives a baseline in cycles per contraction and seconds per segment.
  - The target is the AIR of `Ski/Air.lean`, at about 2.44 rows per
    contraction (below).

## The AIR's size

`AirCost.lean` runs the proved rule table `Air.stepG` (`Ski/Air.lean`) over
the corpus, with the heap in an `Array`. Before printing a row it checks the
contraction count against the reference reducer, and the final state's
spine (head combinator and argument count) against `runF`'s value.

```
lake build aircost && lake exe aircost
```

```
row              leaves  contr  unwind    rows  loaded  written  memory  rows/contr
compiled_up      1397  493  713  1207  2794  1472  4266  2.448276
compiled_uq      915  440  637  1078  1830  1315  3145  2.450000
compiled_ur      1267  530  766  1297  2534  1588  4122  2.447170
interpreted_up   2769  2014  2894  4909  5538  6170  11708  2.437438
interpreted_uq   2772  2029  2919  4949  5544  6195  11739  2.439133
interpreted_ur   2856  2589  3718  6308  5712  7909  13621  2.436462
sumto_us         3531  10297  14776  25074  7062  30244  37306  2.435078
```

- `rows` is the least budget: one row per transition (a contraction or an
  unwind) plus the final halt. The AIR accepts a table of `k` rows exactly
  when `k` is at least this (`air_budgets`).
- `memory` is the committed memory table: the loaded heap (two cells per
  leaf, the term's nodes and the empty stack) and the cells the run
  writes (one per unwind, three per `S`).
- About 2.44 rows per contraction, since an unwind is a row.
- Rows and the memory table pad separately to public sizes (`air_budgets`,
  `Accepts.pad`). For `3 sumto` the next powers of two are 2^15 = 32,768
  rows, a tail of 7,694, and 2^16 = 65,536 memory cells, a tail of 28,230.
- The units differ from the RISC Zero figures above: `3 sumto` takes 25,074
  rows of three registers plus a 37,306-entry memory table here, against
  22.0M RISC-V cycles for the whole guest there, 3.18M of them reduction.
