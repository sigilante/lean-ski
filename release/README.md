# Release: `3 sumto`, proved

This directory holds a proof that the SKIlark program `3 sumto`, compiled
to SKI, evaluates to weak head normal form. The proof covers the run
Avon produced, with supercombinator jets. Anyone with a lean-ski checkout
can check it:

```
release/verify.sh
```

It needs elan (Lean) and cargo (Rust), and nothing from Avon. The first
run builds Lean's checkers and the verifier, which takes minutes; after
that it runs in seconds. It prints one `ok` line per check, then
`VERIFIED: release/sumto`, and exits nonzero if any check fails.

## What is verified

1. **The term.** `sumto/corpus.txt` holds lean-ski's corpus row `sumto_us`:
   `3 sumto`, compiled with its own quotation table (`Ski/Corpus.lean`;
   `Ski/Table.lean` pins the term to the kernel's compilation of the
   program, `sumto_us_eq`). `verify.sh` checks the file against what
   `bench/Dump.lean` prints.
2. **The jet table.** `sumto/jets/sumto_us.jets` lists 2,768 licensed
   roots and 78 jets. Before the verifier reads it, Lean's `lake exe jets
   statement` confirms that it is exactly the jet table of that term, and
   that every root passes `Air.rootsOKB` over the term's loaded heap. That
   gives `Air.RootsOK` (`Air.rootsOKB_sound`).
3. **The proof.** `sumto/sumto_us.proof` is a Plonky3 batch STARK over
   BabyBear, 375,160 bytes, over the eight tables of
   `bench/plonky3/src/jets.rs`. `ski-air jet-verify` checks it against the
   term and the jet table alone.
4. **Two forgeries are refused.** One is the proof with one byte
   changed. The other is the proof offered for another term
   (`compiled_up`).
5. **Lean's own check of the witness.** `lake exe jets check` accepts
   Avon's table, `sumto/sumto_us.table` (`Air.checkJA_sound`).

## What the proof means, and what it does not

An accepted table satisfies `Air.AcceptsJ` from the loaded term with
licensed roots. By `Air.air_sound_jet`, the term then evaluates in
normal order to a value that weakly reduces to the table's final value,
with the same head combinator and arity. So the proof shows that
`3 sumto` **halts**, and fixes the head and arity of its value.

The limits:

- **The output is not bound.** The proof does not show that the value
  decodes to `[6]`. Lean proves that separately about the term
  (`Ski/Examples.lean`, `us_six`), not about this run. Binding an output
  in the circuit takes an atom probe (`Air.air_probe`), and jets do not
  yet combine with probes.
- **The link from Plonky3 to Lean is argued, not proved.** That every
  table the verifier accepts satisfies `Air.AcceptsJ` is argued in the
  headers of `bench/plonky3/src/main.rs` and `src/jets.rs`. Lean checks
  the one table this proof covers (item 5 above).
- **The proof is not zero knowledge**, and has nothing to hide: the term
  is public.
- **Security is Plonky3's benchmark setting** (`bench/plonky3/README.md`).

## Cost

The plain run is the machine alone (`bench/plonky3`); the jetted run is
Avon's, the one proved here.

| | plain | jetted |
|---|---|---|
| contractions | 10,297 | 110, plus 939 instantiations |
| CPU rows (states) | 25,074 | 3,678 |
| CPU rows per plain contraction | 2.44 | 0.36 |
| all table rows (CPU, POP, INSTW) | 25,074 | 8,477 |
| rows per plain contraction | 2.44 | 0.82 |
| cells written | 30,244 | 5,242 |
| padded heights (CPU / memory) | 32,768 / 65,536 | 4,096 / 16,384 |
| prove, setup included (Apple M4 Max) | about 0.5 s | about 0.16 s |
| verify | about 0.015 s | about 0.02 s |
| proof | — | 375,160 bytes |

**The jet table** has 78 jets with 235 body cells in all, averaging 3.3
formals, and 2,768 roots in a 7,062-cell loaded heap. A jet is one
supercombinator the compiler lifted: an equation, a λ chain or a
constructor. Its body names its closed subterms as globals, so an
instantiation writes only the cells that depend on its arguments
(`bench/plonky3/DESIGN.md` §2).

## How it was produced

`release/produce.sh` regenerates everything here:

1. Lean emits the term and its jet table.
2. Avon (`avon witness --jet-table`, in the separate Avon repository)
   runs the term, instantiating at the table's roots, and writes the
   witness table.
3. Lean checks that table.
4. `ski-air jet-prove` proves it, and `ski-air jet-verify` checks the
   proof.

Avon's witness is byte-identical to the table lean-ski's own prover
writes for the same term and jet table (Avon's `make jet-witness-check`,
over the whole corpus). The verifier does not depend on Avon: it checks
the proof, not the producer.
