# lean-ski: the plan

> **Status (2026-09-25).** L0 and L1 built and audited: the calculus, the
> fuel interpreter, trace certificates, the compiled Scott constructors,
> and conformance against `skijack` on six SKIlark programs. §2 items 1–6
> are built for the kernel without static quotations, with the divergence
> biconditional; the rest is a plan. Where this document and the build differ, the build
> is authoritative.

*The end of this program is a zero-knowledge proof of correct SKI execution
with verified jets as its precompiles — a proof system whose entire
transition relation is three rules and a spine walk, so that the statement
being proved can be audited completely, and whose semantics extend without
touching the circuit, since interpreters, new symbols and languages are all
terms. No one has built a proof system over a basic combinator calculus.
The nearest work is Zorp's zkVM for Nock (twelve opcodes, ePrint 2025/1110,
with its Pure Nock formalized in Lean) and the author's own `lean-nock`,
which verifies the jet co-derivation theorem of the USTJ jet paper. This
repository is the Lean spine that joins the two for SKI.*

## 0. What this is, and what it is not

`lean-ski` is the **proof-facing semantics**. It is not a runtime (that is
Avon, planned in SKIjack's `avon/DESIGN.md`), not a compiler (that is
`skijack`), and not a prover (§4). It is what each of those is checked
against, in the order Zorp's Pure Nock package fixes: a language core (L0),
executable trace certificates (L1), and the representation a prover
consumes (L2) — with, between L1 and L2, the layer Nock never had, a
verified compiler from a concatenative source to the ISA and to its jets.

The discipline is `lean-nock`'s and is enforced, not described: the audit
manifest elaborates at build time, the gates run in CI, generated modules
must match their generator, and the runtime is the proof-facing `runF` with
no separate evaluator to bridge.

## 1. Built

**L0, the calculus** (`Ski/Basic.lean`, `Ski/Fuel.lean`). `Term` is `S`,
`K`, `I` and application. `Step` has the three contractions and one
congruence rule, `left`: normal order means the redex is at the head of the
spine and nowhere else, which is what makes `Step.det` a short induction
(the Nock analogue is a 15×15 case bash that `lean-nock` avoids by
transfer). `progress` says every term is a weak head normal form or steps.
`step?` is the computable contraction, recursing into the function position
first exactly as `progress` does; `step?_iff` ties it to the relation, and
`whnf_iff_step?_none` says the interpreter stops exactly at the normal
forms. `evalF` is the fuel interpreter under SKIjack's rule (a run of `s`
contractions needs fuel `s + 1`); `evalF_sound`, `evalF_complete`,
`evalF_mono` and `diverges_iff_fuel` are the four theorems `Nock/Fuel.lean`
proves, at a fraction of the length.

**L1, trace certificates** (`Ski/Trace.lean`). `certified t ts u` re-runs
`step?` on consecutive pairs; `certified_sound` is what a verifier relies on,
`certified_complete` says every reduction has a certificate, and
`traceF_certified` says the interpreter's own trace is one. A row per
contraction, each checked by the same three rules: this is the witness
shape of §4.

**The compiled constructors** (`Ski/Scott.lean`, generated). `Zero` is
`K`; `Suc` is eight atoms; `Push` twenty-two. Each elimination lemma is the
reference reducer's contraction sequence on symbolic arguments, re-run by
the kernel: `iter_sound (k := 7) rfl` for `Suc`. The lemmas expose the fact
every word-level proof must reason through: bracket abstraction passes
fields as thunks, so `Suc n z s` reduces to `s (K n s)`, not `s n`.

**Conformance** (`Ski/Corpus.lean`, `Main.lean`). Six SKIlark programs in
both forms; `runF` agrees with `skijack`'s host reducer contraction for
contraction (493 for `1 2 + dup +` compiled, 2,014 interpreted). The
generator (`scripts/emit.py`) is the only place `skijack` is needed, and
gate 3 checks the committed modules are its output.

**The language layer, §2 items 1–6** (`Ski/Words.lean`, `Ski/Decode.lean`,
`Ski/Leaf.lean`, `Ski/Composition.lean`, `Ski/Apply.lean`). `phi` is the
twelve compiled words. `wQcons`, `wCat`, `wUnit` and `applyU` build or
case on `quot` values, and `quot` gains a constructor per static
quotation, so `phi` is fixed to programs with none. `cw` takes the
quotation eliminator as a parameter. `Decodes` reads a value by probing
at every choice of continuations and is a function.

Every word has a leaf contract over any input that decodes to its stack,
which is what lets `seq_contract` hand one word's result, a thunk, to the
next. `add` is Class C: the compiled `add` is `Y` of its body, and
`add_dec` inducts on the numeral over a semantic loop invariant, since
each unrolling wraps the self-application in one more `I`.
`composition` proves every compiled word list meets `Csem`, and
`compiled_cp_N` pins the compiler's program term to `N` of its words, so
`up_six` runs the corpus program `1 2 + dup +` to `[6]` with no
hypotheses.

`apply_sound` proves the compiled `applyU` realizes `ApplyRel`, its
big-step semantics, by induction on the derivation over every
self-reference of the fixpoint; `composition_apply` extends `composition`
to programs that run quotations. `composition_complete` is the converse,
by strong induction on the contraction count, since `QThen` runs a
quotation that is no part of the one being run; `composition_diverges`
follows: a compiled program diverges exactly when the relational C model
derives no outcome. Without static quotations nothing diverges
(`program_converges`, `Ski/Total.lean`): a quotation built at run time
carries data and `i`, and runs on no more than it was given. Code, and
with it divergence, enters only at the compile-time line; extending the
fragment to static quotation bodies, which admit Joy's `y`, is what makes
the biconditional bite, and is the next item.

Every theorem above is in the audit manifest with footprint
`{propext, Quot.sound}` or narrower.

## 2. Next: the language layer, `lean-nock` ported to SKIlark

The jet paper's pipeline, module for module (see `lean-nock`'s
`Comp`, `Term`, `CEval`, `Composition`):

1. **Words and `phi`.** `inductive Word` is Joy's kernel (`dup swap pop
   cons cat unit dip i ifz lit quote add`); `phi : Word → Term` is the
   term `skijack` emits for each compiled word (`wDup`, 77 atoms), pasted
   by the generator with a test that it equals the emitted term — the
   paper's canonicity requirement, since dispatch matches on structure.
   Canonicity holds for the nine words that never touch `quot`; it fails,
   necessarily, for the four that do, since the ski-in-ski manuscript's
   Proposition `prop:quote` puts a quotation's code on the compile-time
   side and the `quot` sum is closed per program.
2. **The C model `cw`.** `cw : Word → Stack → Outcome` over Lean stacks
   (`List Item`) and the three-valued outcome set `val | err | diverge`,
   nearly verbatim from the Nock version.
3. **The decode relation.** The port's one new lemma family. Nock results
   are nouns and equal syntactically; SKI results are terms and equal only
   up to reduction. The leaf contract is therefore stated as "`phi w`
   applied to the encoding of `S` reduces to a term that *decodes* to
   `cw w S`", with `decode` the marker-probing relation the papers use to
   read values, proved a function on reachable values.
4. **Constructor lemmas, then leaves.** The Scott lemmas of §1 are the
   primitives; each Class A word (`dup swap pop cons cat unit dip`) is a
   few rewrites over them. Class B is empty (SKI has no opcodes to lean
   on). Class C (`add`, `eqNat`, every jet worth having) needs induction
   on the numeral, as `dec` did.
5. **`seq` is opcode 7.** One lemma: `seq f g S` follows `f`'s outcome
   strictly. `composition_term` and `composition_diverges` then go through
   over the Class D term algebra as stated in `lean-nock`.
6. **`apply` is one more fixpoint schema.** SKIlark defunctionalizes
   quotations into a closed sum, so Joy's `i` is a case over a finite
   constructor set plus `seq`; its schema is `while`'s shape. If it goes
   through, the fragment boundary of the jet paper moves: runtime
   quotations are co-derivable whenever the program's quotations are known
   at compile time, which they are.

Effort: the decode relation and the constructor lemmas are the bulk, weeks;
the word table is days after that; `apply` is the theorem that decides
whether item 6 is a result or a conjecture.

## 3. Prior art, placed

- **`lean-nock`** (Davis): Nock 4K relational semantics, fuel, the
  co-derivation composition theorem over Class D, the audit discipline.
  This repository is its port, and inherits its shape and its gates.
- **Zorp, *A Framework for Compiling Custom Languages as Efficiently
  Verifiable Virtual Machines*** (ePrint 2025/1110), with the Pure Nock
  Lean package: a language is *traversable* when its execution and memory
  traces are verifiable walks over recursively verifiable trees with
  state–data separation and state-defined fanout; a traversable language
  gets an efficient RAP generically. Their Lean is the language layer
  (nouns, verbs, local transitions, traces, determinism, modular
  evaluation, noun fingerprints); the AIR is out of their Lean's scope
  too. SKI is the smallest candidate for that framework: a spine walk with
  three local transitions, whose "state" is the head combinator and its
  argument count and whose fanout is fixed per rule.
- **Aleo's `nock-leo`**: the earlier Nock zkVM, which `lean-nock`
  recapitulates.
- **KNock** (Runtime Verification): Nock in K with a reachability prover;
  the executable-semantics-with-prover route this repository does not take,
  because K's claims cannot state divergence and Lean's can.

## 4. The endgame: zero knowledge

Three statements, in rising strength, all about the same three rules.

1. **A proof of execution.** "`t` reduces to `u` in `n` contractions." The
   witness is the L1 certificate; the circuit is `step?` as an AIR: a row
   per contraction with a state column (head combinator, argument count),
   pointer columns, and a memory argument for the heap of nodes. This is
   Zorp's framework instantiated for SKI, and the first task is to show
   SKI's reduction relation is `(F, F*)`-traversable in their sense —
   plausibly the shortest such proof there will ever be. Outputs must be
   canonical: a whnf term carries unreduced closures, so the statement is
   about the decode relation (§2.3) or about a term of atoms, exactly the
   read-back problem SKIlark hit at level 1.
2. **Jets as precompiles.** A jet fires once per supercombinator
   application and does its body's work natively; that is precisely a
   zkVM precompile, whose soundness is the recurring weak point of every
   zkVM and is argued in prose. Here it is `composition_term` for the
   jetted word, and the three-valued contract is what the prover needs,
   since a precompile that bails where the term diverges is the same
   observable divergence `+mock` exposes.
3. **Semantics without touching the circuit.** The object language, the
   self-interpreter, scry and the namespace, SKIlark: all terms. The
   circuit is fixed once and audited once. New symbols, new interpreters
   and new languages are data.

The concrete route: (a) L2 here, the term representation a prover
consumes — content-addressed nodes with a fingerprint, as Zorp's
`NockPure.Fingerprint` does for nouns; (b) the traversability theorem;
(c) a first proof of execution on an existing stack (RISC Zero / SP1
running `runF`'s C extraction), which measures cost per contraction;
(d) the custom AIR, with the K-free `lean-ski` definition as its
specification and the corpus counts as its tests.

## 5. Acceptance

L0/L1: `lake build` elaborates the manifest, `gates.sh` passes, `lake exe
main` matches the reference on every corpus row — done. Language layer:
`composition_term` over SKIlark's Class D with `apply`, every leaf in the
manifest. Endgame: a proof of execution for one corpus program verified by
a third party, with its jet table and per-contraction cost reported.
