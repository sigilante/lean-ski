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

- **Per step, the heap machine is flat and the tree rewriter grows.**
  - Heap mode costs 308 cycles per contraction on the longest run. The
    figure falls as `load` is amortized, because each transition does
    constant work.
  - Tree mode rises to 1,469 cycles per contraction. `step?` rebuilds the
    spine above each redex, so a step costs time in proportion to the spine.
- **Reduction is the smaller part of the bill.**
  - On `sumto_us` in heap mode, reduction is 3.2M of 22M cycles.
  - Most of the rest is parsing the input and hashing the result's shared
    form, which uses a `HashMap` for sharing.
  - A prover for L2 itself would commit the heap as the zk layer's memory
    table does, and would pay neither cost.
- **This is a general-purpose zkVM, not the traversal prover.**
  - It gives a baseline in cycles per contraction and seconds per segment.
  - The target is the RAP over the compute and memory tables of
    `zk/SkiZk`. There, one contraction is one row, not about 300 RISC-V
    cycles.
