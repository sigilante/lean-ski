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
by `lean-toolchain` (Lean 4.28.0). No Mathlib, no dependencies.

```sh
rm -rf .lake/build && lake build     # elaborates the audit manifest
./scripts/gates.sh                   # no sorry, no axioms, no native_decide, no panic!
lake exe main                        # the Lean interpreter's contraction counts
                                     # against the reference reducer's, per program
```

`lake exe main` prints one line per corpus program, e.g.

```
ok   compiled_up: 493 contractions (reference 493)  -- 1 2 + dup +
ok   interpreted_up: 2014 contractions (reference 2014)  -- 1 2 + dup +
```

and exits nonzero on any disagreement: `runF` and `skijack`'s host reducer
agree contraction for contraction on every SKIlark program in the corpus, in
both its forms.

## Modules

| module | contents |
|---|---|
| `Ski/Basic.lean` | `Term`, `Whnf`, `Step` (one congruence rule, `left`), `Step.det`, `progress`, `Steps`, `Eval`, `Eval.deterministic`, `Diverges` |
| `Ski/Fuel.lean` | `step?`, `iter`, `evalF`, `runF`; `step?_iff`, `evalF_sound`, `evalF_complete`, `evalF_mono`, `diverges_iff_fuel` |
| `Ski/Trace.lean` | `certified` (a verifier's check of a trace), `certified_sound`, `certified_complete`, `traceF` and `traceF_certified` |
| `Ski/Weak.lean` | weak reduction (a contraction anywhere); `standardization`, `eval_back`, `church_rosser` |
| `Ski/Scott.lean` | generated: the constructors of `nat`, `item`, `stack`, `quot`, `result` as compiled, with `*_elim` lemmas by `iter_sound rfl`; the twelve compiled kernel words; `add`, `seq`, `idW`, `applyU` |
| `Ski/Words.lean` | `Item`, `Quotation` (with `stat k`, a table's static quotation), `Stack`; the quotation table `Kit`; `Word`, `phi`, the C model `cw` |
| `Ski/Decode.lean` | the decode relations (probing at every continuation; a quotation at `n + 3`), `KitElim`, constructor lemmas, `enc*_dec`, `*.functional` |
| `Ski/Leaf.lean` | a leaf contract for every word over any input that decodes (`leafD_*`) and at the encoding (`leaf_*`); `KitWords`; `add_dec`, by fixpoint induction |
| `Ski/Composition.lean` | `N`, `Compiles`, `Csem`, `seq_contract`, `composition`, `composition_agree` |
| `Ski/Apply.lean` | `Run` (quotations, programs, words), `KitApply`, `run_sound`, `apply_sound`, `composition_apply` |
| `Ski/Converse.lean` | counted reduction; `apply_complete`, `composition_complete`, and the biconditionals `apply_diverges`, `composition_diverges` |
| `Ski/Total.lean` | over a table with no static quotations nothing diverges: `apply_total`, `program_converges` |
| `Ski/Table.lean` | generated: the tables `NoQuot`, `CorpusTable` and `LoopTable` as `Kit` instances, every law by `iter_sound rfl`, each program's compiled form, and the corpus rows as those programs run |
| `Ski/Examples.lean` | `1 2 + dup +`, `3 [dup +] i`, `1 2 over` end to end from `skijack`'s terms; `cloop_diverges`: the compiled `[dup i] dup i` diverges |
| `Ski/Audit.lean` | the manifest and the `#audit_clean` command |
| `scripts/emit.py` | regenerates `Scott.lean`, `Corpus.lean` and `Table.lean` from `skijack` (needs the SKIlark venv); gate 3 checks the committed files match |

## Fuel

`evalF k t` makes at most `k` step-attempts, the last of which must be the
no-redex check, so a run of `s` contractions needs fuel `s + 1` and times out
at `s` — SKIjack's rule (SPEC §6) — and `diverges_iff_fuel` says divergence
is exactly "timeout at every fuel". There is no crash at this level: the
calculus has no ill-formed terms. Crashes are data one level up (`RErr`,
the object language's `Err`), which is where the jet paper's three-valued
contract lives for SKI.
