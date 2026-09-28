# lean-ski

SKI in Lean 4, in the shape of [`lean-nock`](https://github.com/sigilante/lean-nock):
an inductive relational semantics for normal-order reduction of the three
combinators, a fuel interpreter proved to agree with it, execution-trace
certificates, and the Scott constructors exactly as the
[SKIjack](https://github.com/sigilante/SKIjack) compiler emits them, each
with a kernel-checked elimination lemma. `PLAN.md` says where it goes: the
co-derivation theorem of the jet paper for [SKIlark](https://github.com/sigilante/SKIlark),
and a zero-knowledge proof of SKI execution.

All proofs are kernel-checked with no `sorry`. `Ski/Audit.lean` is
elaborated as part of `lake build` and **fails the build** if any listed
theorem's axiom footprint grows past `{propext, Quot.sound}`, if any `sorry`
appears, or if a cited name is renamed. There is no `native_decide` and no
`partial def`: every function is total, and the runtime is the proof-facing
`runF`, not a separate evaluator.

## Reproducing

Requires [`elan`](https://github.com/leanprover/elan); the toolchain is pinned
by `lean-toolchain` (Lean 4.31.0, as Pure Nock's). The core has no Mathlib and no
dependencies; the coverage project depends on the core only.

```sh
rm -rf .lake/build && lake build     # elaborates the audit manifest
./scripts/gates.sh                   # no sorry, no axioms, no native_decide, no panic!
lake exe main                        # the Lean interpreter's contraction counts
                                     # against the reference reducer's, per program
./scripts/build-coverage.sh          # the coverage project: every file checked against skijack
(cd zk && lake exe cache get && lake build)   # the zero-knowledge layer, over Mathlib
```

`lake exe main` prints one line per corpus program, e.g.

```
ok   compiled_up: 493 contractions (reference 493)  -- 1 2 + dup +
ok   interpreted_up: 2014 contractions (reference 2014)  -- 1 2 + dup +
```

and exits nonzero on any disagreement: `runF` and `skijack`'s host reducer
agree contraction for contraction on every SKIlark program in the corpus: the
three corpus programs in both forms, and `3 sumto` compiled.

## Modules

| module | contents |
|---|---|
| `Ski/Basic.lean` | `Term`, `Whnf`, `Step` (one congruence rule, `left`), `Step.det`, `progress`, `Steps`, `Eval`, `Eval.deterministic`, `Diverges` |
| `Ski/Fuel.lean` | `step?`, `iter`, `evalF`, `runF`; `step?_iff`, `evalF_sound`, `evalF_complete`, `evalF_mono`, `diverges_iff_fuel` |
| `Ski/Trace.lean` | `certified` (a verifier's check of a trace), `certified_sound`, `certified_complete`, `traceF` and `traceF_certified`; the budget-exact certificate a prover commits to, `certifiedPad`, with `certified_pad_iff`, `certifiedPad_unique` and `certified_pad_budgets` |
| `Ski/Heap.lean` | L2: a write-once heap machine (unwind, and `S` allocating three cells); `mstep_some`, `mstep_none`, `mstep_append`, `machine_eval` (it computes exactly `Eval`) and `machine_count` (with `runF`'s contraction count) |
| `Ski/Air.lean` | the circuit: an AIR over the heap machine. A row is the three registers; the heap is one committed memory table reached by lookups (a read only below the row's counter, a write checked at the counter). One rule table (`stepG`) is both the machine (`mstep_eq`) and the row constraint; halting is decided from reads alone. An accepted table ends on the value `runF` reaches (`air_sound`); a table of `k` rows is accepted exactly when `k` exceeds the run's transitions (`air_complete`, `air_budgets`); the memory table pads (`Accepts.pad`). Not fixed by the constraints: the output value, the witness's secrecy, and the lookups themselves, which a lookup argument must enforce |
| `Ski/AirCheck.lean` | the AIR's constraints decided on a concrete table: `checkB` over a list and `checkA` over an array, equal (`checkA_eq`) and deciding the AIR's constraints (`checkB_sound`, `checkB_complete`, `checkA_iff`); what tables produced outside Lean are checked against |
| `Ski/HeapOpen.lean` | atoms as probe markers: the heap machine's inert `atom` cell read back as an open term's variable; every transition is an unwind or one open head step (`omstep_some`); runs are open head reduction (`omachine_run`); an atom at the head is a stuck spine (`atom_head`) |
| `Ski/AirOpen.lean` | the AIR started from any state (`AcceptsFrom`, `accepts_iff`); on an open term it proves open head reduction (`air_sound_open`), and a last row with the atom `i` at the head binds the output: the term reduces to `i` applied to arguments (`air_probe`) |
| `Ski/Inst.lean` | supercombinator jets: an instantiation that pops the arguments and writes the body with their pointers is weak reduction when the head is `absN xs body` (`inst_sound`); a run mixing transitions and instantiations that halts proves normal-order evaluation, up to weak reduction of the value (`jet_run_eval`) |
| `Ski/Lambda.lean` | the untyped λ-calculus with de Bruijn indices: substitution fusion, Church–Rosser by complete development (`lsteps_confluent`), a sound normalizer |
| `Ski/Quote.lean` | Proposition 3.1 of the metacircular paper: no combinator quotes every live term (`no_quote`), through the λ-translation in which `S K X` is the identity |
| `Ski/Transfer.lean` | Part II's transfer lemmas: standardization (`eval_of_wsteps`); its counted form refuted in the kernel (`counted_standardization_false`: one weak step saves two head steps); counted β for `skijack`'s bracket abstraction, at most `3^k · vsize M` weak steps for `k` formals (`absN_beta_count`) |
| `Ski/Realize.lean` | Part II's logic: formulas (NP atoms, ∧, ∨, →, ∃), realizability closed under backward weak reduction (`Real.back`), atoms as verifier evaluation (`real_atom_iff`); `soundness` of the combinator system with Scott constants; `completeness`: natural deduction compiled by bracket abstraction (`abs_types`, Curry's theorem); existential elimination with `∀` over witnesses (`NDX.exElim`, `ndx_realizes`) |
| `Ski/Tait.lean` | Part II's realizer language: simply typed λ with products (eliminated by projections or by split) and sums over opaque base types and constants, full reduction; `strong_normalization` by Tait's reducibility (`cr`, `fundamental`); `omega_untyped` checks that `SN` is not vacuous |
| `Ski/Bridge.lean` | typed realizers written as SKIjack source (`Src`: λ, the compiled Scott constructors, case and split lowered to continuations) and compiled by `comp`; `compiled_converges`: the compiled term of a typed closed realizer converges in normal order, by Tait's reducibility on the `SKI` side; `glue_converges`, with no constants |
| `Ski/BridgeA.lean` | the same for the threaded compilation the prover runs: `compiledA_converges`, `glueA_converges`, so convergence and the cost bound speak of one compiled term |
| `Ski/Stratum.lean` | stratum 1 at the source: under the additive count (a case's branches count as the larger), every call-by-name step of an additively affine realizer shrinks its additive size (`WH.asz_lt`); reductions are shorter than it (`wh_steps_lt`) |
| `Ski/Stratum2.lean` | stratum 2: typed realizers with contraction normalize but have no elementary bound. The tower `two two ⋯ two` applied to a Boolean toggle is typed, has additive size `8k + 17`, terminates, and every call-by-name evaluation takes at least `2↑↑(k+1)` steps (`evalT_lower`, `evalT_terminates`); so no fixed height of exponentials of the size bounds it (`no_elementary_bound`) |
| `Ski/Stratum2C.lean` | stratum 2 on the compiled trace: under either compilation, every normal-order reduction of the compiled tower, applied to the toggle and `true`, to a weak head normal form takes at least `2↑↑(k+1)` steps (`compiled_evalT_lower`, `compiledA_evalT_lower`); the compiled term converges when the Boolean witness does and has `6k + 39` combinators plus the Boolean witness's, so no fixed height of exponentials of its size bounds it (`compiled_no_elementary_bound`, `compiledA_no_elementary_bound`) |
| `Ski/Stratum3.lean` | stratum 3: a typed fixed point `fix : (A ⇒ A) ⇒ A`, compiled to SKIjack's `Y`, breaks strong normalization. `fix (λx. x)` is typed and has no call-by-name normal form (`omegaF_diverges`), and its compiled term `Y ⬝ I` diverges, timing out at every fuel (`compiled_omegaF_timeout`). `fix (λx. inl c)` evaluates, source and compiled, so halting depends on the realizer. Without `fix`, typed closed realizers evaluate (`fixfree_evaluates`) |
| `Ski/Sigma.lean` | the Σ-protocol algebra: formulas with AND and OR primitive and threshold a fold (`thrF`), proof plans, and threshold's semantics (a plan for `k`-of-`φs` exists exactly when `k` components have plans: `thrPlan_isSome`, `thrPlan_extract`). Its glue (introduction, projection, split, case, AND and OR commutation, OR distributed over a context, threshold weakening, and the prover's composition of every plan) lies in stratum 1 (`glue_stratum1`), with the source and compiled bounds (`glue_bounds`); distributing OR over a context needs the additive count (`orDist_needs_additive`); AND commutation by split is in stratum 1 (`andComm_s1`), and by projections it is not (`swapT_not_affA`) |
| `Ski/Census.lean` | the census: a computable classification into strata (3 if a fixed point occurs, 1 if additively affine, 2 otherwise), exact (`census_one_iff`, `census_two_iff`, `census_three_iff`); each stratum's theorem in the language with `fix` (`census_one_bound`, `census_le_two_normalizes`, `census_le_two_evaluates`, `census_three_diverges`); the additive rule needed (`additive_rule_needed`, `additive_rule_needed_glue`); the census computed on the glue and the families (`census_table`) |
| `Ski/Cost.lean` | the compiled term's own normal-order steps: graded types (`⊸` uses its argument once, `⊸⁰` discards it), `S`, `K`, `I` each firing once, bracket abstraction yielding a graded arrow (`abs_OG`); a compiled affine glue realizer applied to witnesses head-normalizes within its combinator count plus the witnesses' costs (`glue_head_bound`) |
| `Ski/CostAdd.lean` | the same bound for additively affine realizers, the variables a case's branches share threaded through its continuations (`trA`, `glue_head_bound_add`) |
| `Ski/Weak.lean` | weak reduction (a contraction anywhere); `standardization`, `eval_back`, `church_rosser`; `par_step_le` (a head step costs a parallel reduct at most one) |
| `Ski/Abs.lean` | bracket abstraction as `skijack` does it (`abs`, `absN`), `abs_beta`, `absN_beta`, `abs_subst`; β for all formals under any substitution, `absN_beta_subst` and `absN_beta_close` |
| `Ski/Compile.lean` | the compilation scheme: `Src`, λ-lifting (`comp`), `compDef`, `compRec` with `Y`, Scott constructors (`ctorO`) |
| `Ski/Front.lean` | SKIjack's front end in Lean, both lexicons: lexer, parser, macros, generated forms, case lowering, λ, cells, picks, cores, the prelude, level 1 (data, runs, scry, namespace literals), `compileWith`; refuses what `skijack` refuses |
| `Ski/Check.lean` | `skijack`'s checker, Stage A (`check.py`): scope, case, data positions, the two symbol tables, the interpreter interface |
| `Ski/TypeCheck.lean` | Stage B (`typecheck.py`), ported object for object: oriented, equirecursive Hindley–Milner; `checkPass`, and `checkedWith_of_pass`: the checker only refuses |
| `Ski/Source.lean` | generated: the four source texts `skijack` compiled, character for character |
| `Ski/Kernel.lean` | the kernel's equations as the front end reads them from `kernelText` (`KernelSrc`), `kernel_agrees`, and `Table.kit : Table → Kit`; a program's term `Table.progT` |
| `Ski/Laws.lean` | the law classes for the kit compiled from every valid table: `Table.kit_elim`, `Table.kit_words`, `Table.kit_apply`, by β for compiled source |
| `Ski/Scott.lean` | generated: the constructors of `nat`, `item`, `stack`, `quot`, `result` as compiled, with `*_elim` lemmas by `iter_sound rfl`; the twelve compiled kernel words; `add`, `seq`, `idW`, `applyU` |
| `Ski/Words.lean` | `Item`, `Quotation` (with `stat k`, a table's static quotation), `Stack`; the quotation table `Kit`; `Word`, `phi`, the C model `cw` |
| `Ski/Open.lean` | `OTerm`, terms with inert variables: head reduction, substitution, closing, symbolic runs, and the split of weak reduction on open terms |
| `Ski/Decode.lean` | the decode relations, probing at fresh variables (a quotation at `n + 3`); `*.of_wsteps` (closed under backward weak reduction), the closed `probe_*`, `KitElim`, constructor lemmas, `enc*_dec`, `*.functional` |
| `Ski/Leaf.lean` | a leaf contract for every word over any input that decodes (`leafD_*`) and at the encoding (`leaf_*`); `KitWords`; `add_dec`, by fixpoint induction |
| `Ski/Composition.lean` | `N`, `Compiles`, `Csem`, `seq_contract`, `composition`, `composition_agree` |
| `Ski/Apply.lean` | `Run` (quotations, programs, words), `KitApply`, `run_sound`, `apply_sound`, `composition_apply` |
| `Ski/Converse.lean` | counted reduction, not lengthened by weak reduction (`StepsN.wtail`); `apply_complete`, `composition_complete`, and the biconditionals `apply_diverges`, `composition_diverges` |
| `Ski/Programs.lean` | every program over every valid table: `Table.program_apply`, `Table.program_diverges`, `Table.program_exact`, with `diverges_iff_of_wsteps` |
| `Ski/Simulation.lean` | the source semantics (λ-lifted β, δ with `Y`, Scott case) and `simulation`: every source step is matched by weak SKI steps; `kernel_fixed` and siblings for the four sources; `wPop_push` |
| `Ski/SourceEval.lean` | normal-order source steps (`sstep?`, `seval`) proved sound into the source semantics, and runs filled from placeholders (`SSteps.substC`) |
| `Ski/SourceJoy.lean` | `cw` from the source: every word's equation, run on a stack's encoding, reaches `cw`'s outcome (`plain_source`, `cwR_source`) |
| `Ski/SourceRun.lean` | every `Run` derivation is a run of the source program (`run_source`) |
| `Ski/Adequacy.lean` | the compiled program, the source program and `Run` agree: `exact_iff`, `diverges_iff_source` |
| `Ski/SourceTables.lean` | the four compiled sources meet adequacy's hypotheses; `3 sumto` reaches `[6]` at the source, `[dup i] dup i` nothing |
| `coverage/` | a separate Lake project, generated: SKIjack files (level 0, macros, generation, level 1, the corpus) in both lexicons compiled to `skijack`'s terms, the simulation applying to each, the checker passing exactly where `skijack`'s does, and programs `skijack` refuses refused; built one module at a time by `scripts/build-coverage.sh` |
| `zk/` | a separate Lake project over the core and Pure Nock: recursively verifiable trees and traversability as Pure Nock's paper defines them; SKI execution (`execution_traversable`, states `S K I halt`) and memory (`memory_traversable`, terms as nouns) are traversable; term fingerprints collide for at most `2Λ − 1` field elements, over BabyBear and its degree-4 extension (`babyBear4_collision_card_le`); its own audit, with Pure Nock's allow-list |
| `bench/plonky3/` | the AIR in Plonky3 0.8: CPU, memory and program tables over BabyBear joined by a LogUp bus; every corpus row proved and verified (`3 sumto` in about 0.5 s), each proved table accepted by `lake exe aircheck`, and four tampered tables rejected by both (`bench/plonky3/README.md`) |
| `bench/` | the cost of proving reduction on RISC Zero: Rust ports of `runF` and the heap machine, checked against the corpus counts, measured in cycles and proving time (`bench/README.md`) |
| `Ski/Total.lean` | over a table with no static quotations nothing diverges: `apply_total`, `program_converges` |
| `Ski/Table.lean` | generated: the tables `NoQuot`, `CorpusTable`, `LoopTable` and `SumTable` (`3 sumto`) as data, checked by `rfl` against `skijack`'s terms (`table_*`) and valid (`table_valid`), their laws from `Ski/Laws.lean`; each program's term pinned to the kernel's compilation of its words (`c*_eq`), the corpus rows as those programs run, and `3 sumto`'s derivation (`cs_run`) |
| `Ski/Examples.lean` | `1 2 + dup +`, `3 [dup +] i`, `1 2 over` end to end from `skijack`'s terms; `cloop_diverges`: the compiled `[dup i] dup i` diverges; `us_six`: `3 sumto`, through Joy's `y`, decodes to `[6]` |
| `Ski/Audit.lean` | the manifest and the `#audit_clean` command |
| `scripts/emit.py` | regenerates `Scott.lean`, `Corpus.lean`, `Table.lean` and `Source.lean` from `skijack` (needs the SKIlark venv); gate 3 checks the committed files match |

## Fuel

`evalF k t` makes at most `k` step-attempts, the last of which must be the
no-redex check, so a run of `s` contractions needs fuel `s + 1` and times out
at `s` — SKIjack's rule (SPEC §6) — and `diverges_iff_fuel` says divergence
is exactly "timeout at every fuel". There is no crash at this level: the
calculus has no ill-formed terms. Crashes are data one level up (`RErr`,
the object language's `Err`), which is where the jet paper's three-valued
contract lives for SKI.
