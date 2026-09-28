# Release: `3 sumto`, proved, and its output `[6]`

This directory holds two proofs about the SKIlark program `3 sumto`,
compiled to SKI:

- **It halts.** A proof of the jetted run Avon produced: the term
  evaluates to weak head normal form.
- **It decodes to `[6]`.** A proof of the probe segments Avon ran:
  applied to marker atoms, the term reads, constructor by constructor, as
  the result `RVal [6]` (`Decodes sumto_us (.val [.num 6])`).

Anyone with a lean-ski checkout can check both:

```
release/verify.sh
```

It needs elan (Lean) and cargo (Rust), and nothing from Avon. The first
run builds Lean's checkers and the verifier, which takes minutes; after
that it runs in about 15 seconds. It prints one `ok` line per check, then
`VERIFIED: release/sumto`, and exits nonzero if any check fails.

## What is verified

1. **The term.** `sumto/corpus.txt` holds lean-ski's corpus row `sumto_us`:
   `3 sumto`, compiled with its own quotation table (`Ski/Corpus.lean`;
   `Ski/Table.lean` pins the term to the kernel's compilation of the
   program, `SumTable.sumto_us_eq`). The line's middle field, the
   contraction count skijack's reducer reports, is informational: the
   proof claims nothing about it, and only step 1's comparison checks it. `verify.sh` checks the file against what
   `bench/Dump.lean` prints.
2. **The jet table.** `sumto/jets/sumto_us.jets` lists 2,768 licensed
   roots and 78 jets. The verifier reads the corpus line and the jet file
   once and pipes those bytes to Lean's `lake exe jets statement-stdin`,
   which reads no file. It confirms that the jet file is exactly the jet
   table of the term, and that every root passes `Air.rootsOKB` over the
   term's loaded heap. That gives `Air.RootsOK` (`Air.rootsOKB_sound`).
   The verifier then uses those same bytes, so what Lean checked is what
   it proves over. Corpus lines are split as Lean splits them, on spaces.
3. **The halting proof.** `sumto/sumto_us.proof` is a Plonky3 batch STARK
   over BabyBear, 378,776 bytes, over the eight tables of
   `bench/plonky3/src/jets.rs`. `ski-air jet-verify` checks it against the
   term and the jet table alone.
4. **Forgeries are refused:**
   - the proof with one byte changed;
   - the proof offered for another term (`compiled_up`);
   - the proof with a byte appended (a proof is one byte string);
   - a name that is a path (names are identifiers, on both sides);
   - a proof that Ω, which diverges, halts, made over a forged jet table
     (`forgeries/omega`). It is offered once with the forged table, and
     once through a FIFO that answers the first read with the honest table
     and the second with the forged one.

   An independent check from a clean clone found these holes. First, an
   absolute name let Lean check one file while the verifier read another.
   After names became identifiers, the FIFO let them read different
   bytes. Each let the Ω forgery verify. So did one more: a copy of the
   bytes in a temporary directory, which a process able to rename entries
   in a shared `$TMPDIR` replaced before Lean read it. Reading once and
   piping the bytes to Lean closes all three. The standing forgeries fail
   on the vulnerable builds (`a8ec55f`, `0b2fbcf`) and pass on this one,
   checked with the Ω proof made for their CPU layout. The CPU has since
   gained the probe kinds, and the Ω proof was remade for it: the old
   builds now reject it for its layout, so they no longer show the holes.
5. **Lean's own check of the witness.** `lake exe jets check` accepts
   Avon's table, `sumto/sumto_us.table` (`Air.checkJA_sound`). A table
   certifies its own term, on its first line. `verify.sh` binds it to the
   corpus row twice: it compares that line with the row's term, and runs
   Lean's checks with `--row sumto_us`, which refuse any other term.
6. **The output proof.** `sumto/sumto_us.probe.proof`, 434,238 bytes, is
   over the same eight tables and two more, PLAN and PW
   (`bench/plonky3/src/probe.rs`). `ski-air probe-verify … val 6` checks
   the jet file as in item 2, takes the plan of `[6]` from Lean (`lake exe
   jets plan val 6`, `Air.planOf`), and checks the proof against the term,
   the jet table and the plan. Offered for `[5]`, for the error outcome or
   for `[6, 0]`, spelled `06`, with one byte changed, or in place of the
   halting proof, it is refused (an outcome has one spelling: plain
   decimal). A number `n` takes `n + 1` probes, so Lean gives no plan
   past 65,536 segments. `lake exe jets check-probe` accepts its table,
   `sumto/sumto_us.probe.table`, for `[6]` (`Air.checkPA_decodes`),
   rejects it for `[5]`, and refuses it as row `compiled_up`, which also
   decodes to `[6]`.

## What the proofs mean, and what they do not

**The halting proof.** An accepted table satisfies `Air.AcceptsJ` from
the loaded term with licensed roots. By `Air.air_sound_jet`, the term
then evaluates in normal order to a value that weakly reduces to the
table's final value, with the same head combinator and arity. So
`3 sumto` **halts**, and the proof fixes the head and arity of its value.

**The output proof.** A result is read by probing: the term, applied to
three fresh marker atoms, must head-reduce to the marker of `RVal`
applied to one field; that field, applied to two fresh markers, to the
marker of a stack cell applied to its two fields; and so on down the
value, one probe per constructor. That is `Decodes` (`Ski/Decode.lean`),
the reading the compiler's contracts use. `[6]` takes 11 probes, the
plan's segments. An accepted table runs them in one table: each segment
starts with a probe row that writes its markers and applies its term to
them, runs by machine transitions and jet instantiations, and ends where
the head is the expected marker with exactly the expected fields on the
stack. By `Air.air_probe_decodes`, an accepted table proves that the
term decodes to the outcome. Lean proves the same outcome about the term
by its derivation (`SumTable.us_six`); this proof reaches it from the
run.

The limits:

- **The link from Plonky3 to Lean is argued, not proved.** That every
  table the verifier accepts satisfies `Air.AcceptsJ`, or with probe
  segments `Air.AcceptsP`, is argued in the headers of
  `bench/plonky3/src/main.rs`, `src/jets.rs` and `src/probe.rs`. Lean
  checks the tables these proofs cover (items 5 and 6), but nothing links
  a table to a proof's bytes. The tables and proofs do regenerate, byte
  for byte.
- **The verifier trusts its build.** The statement check runs the Lean
  project of the checkout the verifier binary was built in, with `lake`
  from `PATH`; `$LEAN_SKI` is consulted only when that is absent.
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
| proof | — | 378,776 bytes |

The output proof runs 11 probe segments in 4,144 CPU rows: 1,045
instantiations, 11 probe rows, and the machine's transitions. It writes
5,876 cells past the loaded heap, and one PW row per marker, 23 in all.
The first segment, the term applied to its three markers, takes 3,674
rows; the other ten, which read the value, take 470. It proves in about
0.24 s and verifies in about 0.02 s; the proof is 434,238 bytes.

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
5. Lean writes the plan of `[6]` (`lake exe jets plan val 6`). Avon
   (`avon witness --jet-table --plan`) runs the term's probe segments for
   it and writes their table, which `lake exe jets check-probe --row
   sumto_us` checks. `ski-air probe-prove-table` proves it, and `ski-air
   probe-verify` checks the proof.
6. The Ω forgery's hand-written table (`forgeries/omega/omega.table`,
   which `lake exe jets check` rejects) is proved over the forged jet
   table.

Avon's witnesses are byte-identical to the tables lean-ski's own prover
writes for the same term, jet table and plan (Avon's `make
jet-witness-check` and `make probe-witness-check`, over the corpus), and
`produce.sh` compares the probe table and its proof with ski-air's own. The verifier does not depend on Avon: it checks
the proof, not the producer.
