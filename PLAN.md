# lean-ski: the plan

> **Status (2026-09-25).** L0 and L1 built and audited: the calculus, the
> fuel interpreter, trace certificates, the compiled Scott constructors,
> and conformance against `skijack` on six SKIlark programs. §2 items 1–6
> are built over any quotation table, with the divergence biconditional,
> and checked for two tables: the kernel with no static quotations and the
> corpus table. §3, every table at once, is the next project; the rest is a
> plan. Where this document and the build differ, the build is
> authoritative.

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
`skijack`), and not a prover (§5). It is what each of those is checked
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

**The language layer, §2 items 1–6** (`Ski/Words.lean` through
`Ski/Total.lean`, `Ski/Table.lean`, `Ski/Examples.lean`). No `{S, K, I}`
term quotes a live term (Proposition `prop:quote` of the ski-in-ski
manuscript), so a quotation's code enters only at compile time, as a
constructor of the per-program sum `quot`. The development is therefore
stated over a `Kit`: one table of static quotations, with the four terms
that build or eliminate `quot` (`wQcons`, `wCat`, `wUnit`, `applyU`) and
each static quotation's body. Everything is proved once over a kit; the
facts the kernel checks per table are the fields of `KitElim`, `KitWords`
and `KitApply`, and `Ski/Table.lean` (generated) supplies them for two
tables by `iter_sound rfl`: the kernel with no static quotations
(`NoQuot`) and the corpus table (`[dup +]`, `[dup]`).

`Decodes` reads a value by probing at every choice of continuations, a
quotation at `n + 3` of them, and is a function. Every word has a leaf
contract over any input that decodes to its stack; `add` is Class C, by
fixpoint induction over a semantic loop invariant. `Run` is the big-step
semantics of programs, words and quotations together, so a static
quotation runs its body; `Compiles` relates a word list to the compiler's
term, which reaches `N` one `seq` at a time. `composition_apply` is the
forward theorem, `composition_complete` its converse by strong induction
on the contraction count, and `composition_diverges` the biconditional: a
compiled program diverges exactly when `Run` derives no outcome.

Both directions bite. `uq_six` and `ur_over` run `3 [dup +] i` and
`1 2 over` from skijack's terms to `[6]` and `[1, 2, 1]`; the corpus rows
are those terms (`compiled_uq_eq`, `compiled_ur_eq`). `cloop_diverges`
is the other side: `[dup i] dup i`, as skijack compiles it over its own
table (`LoopTable`), provably never reaches a weak head normal form,
because the static body `[dup i]` runs a quotation. Without static
quotations nothing diverges (`program_converges`): a quotation built at
run time carries data and `i`, and runs on no more than it was given.
`omega_diverges` is a weaker witness over the corpus table: its
quotation is written in by hand, not emitted by the compiler.

`composition`, the theorem over a total model of quotations, is
discharged here only by the eliminator that fails every quotation; with
a table's real `applyU` the forward theorem is `composition_apply`.

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
whether item 6 is a result or a conjecture. (Built; see §1.)

## 3. Next: every table at once

The three law classes hold for every quotation table, and the next project
is to prove it. Today a table's laws are about thirty facts the kernel
checks by `iter_sound rfl`, so a program with a new static quotation needs
a newly generated instance before any theorem applies to it. The generic
form proves `KitElim`, `KitWords` and `KitApply` once, for the kit
compiled from any table, and shrinks the generator's per-table work to
one equality test.

**What `skijack` does.** Read from `aviary_kernel/abstraction.py` and
`skijack/expand.py`: bracket abstraction is Curry's four rules with eta,

    [x] x = I      [x] E = K E  (x not in E)
    [x] (E x) = E  (x not in E) [x] (E F) = S ([x] E) ([x] F);

recursion enters only through `Y`, whose `{S, K, I}` form is the one
explicit override; and a case lowers to the scrutinee applied to one
continuation per constructor, in declaration order, each a λ over that
constructor's fields.

**The work, in dependency order.**

- **G1. Weak reduction and standardization — built** (`Ski/Weak.lean`).
  `WStep` is a contraction anywhere. `standardization`: if `t →w* u` and
  `u →h* w`, then `t →h* w'` with `w' →w* w`, by Takahashi's method over
  parallel reduction (`par_split` separates head steps from an internal
  step, `parI_step` commutes the two). `eval_back`: if `u` reaches a weak
  head normal form, so does every `t` that weakly reduces to it, so
  divergence transfers forward (`diverges_of_wsteps`). `church_rosser`:
  weak reduction is confluent, through complete development `dev`.
  `standardization` and `eval_back` use no axioms.
- **G1b. Decoding up to weak reduction — open.** This section first
  listed, as a corollary of G1, that every relation of `Ski/Decode.lean`
  is closed under backward weak reduction. It does not follow. A probe
  demands that head reduction reach the continuation exactly,
  `Steps (t ⬝ k0 ⬝ k1) k0`; standardization yields a head reduct `w'` with
  `w' →w* k0`, not one equal to `k0`. The closure is still true, by
  parametricity: `t` cannot inspect `k0`, so head reduction carries it
  untouched. Stating that needs terms with variables, which `Term` does
  not have. Two routes:
  (a) *Parametricity.* Add variables and a substitution lemma, and read
  the closed probe facts from generic ones. The hard part is the reverse
  direction, recovering a generic fact from closed probes, since a
  closed continuation can reduce its arguments.
  (b) *Probes up to weak reduction.* Replace `Steps` by `WSteps` in each
  probe clause. Closure under backward weak reduction becomes
  transitivity, and `eval_back` recovers the `Eval` a `Contract` ends in.
  Two steps this route needs beyond G1, found in review:
  *Functionality over joinable terms.* Two probes of one term now reach
  `S ⬝ f` and `S ⬝ f'` with `f` and `f'` only joinable, so the
  functionality proofs must induct over pairs of terms with a common weak
  reduct, not over one term. It works because every probe end (`K`, `S`,
  `K ⬝ f`, `S ⬝ f`, `S ⬝ f ⬝ g`) is a non-redex whose weak reducts keep its
  head and arity, so `church_rosser` separates distinct ends and joins
  the fields of equal ones. Closure under *forward* weak reduction fails
  for arbitrary continuations and is not needed.
  *The converse over weak predecessors.* `wsteps_split` reaches only an
  internal-step predecessor of a call `apT ⬝ x ⬝ th`, whose eliminator
  weakly reduces to the self-reference rather than equalling it, so the
  counted claims must generalize from `applyF` to its weak predecessors
  and transport `applyF_stages` along them.
  The remaining cost is that the leaf, composition and `apply` proofs
  chain `Steps` today and would chain `WSteps`.
  Route (b) is recommended: it uses only what G1 built, and G4 states its
  laws up to weak reduction anyway.
- **G2. λ-terms and abstraction.** A Lean syntax of λ-terms over `S`,
  `K`, `I`, globals and named variables; `abs` implementing exactly the
  four rules; and `abs_beta : abs x M ⬝ N →w* M[N/x]`, which G1 turns into
  a head-reduction fact up to weak reduction of the result.
- **G3. The kernel's source as a function of the table.** The `n + 3`
  constructors of `quot`, `applyU`'s case with `n + 3` arms, `wQcons`,
  `wCat`, `wUnit` and each body `b_k`, written as λ-terms after
  `COMPILED_KERNEL`, and `kitOf : Table → Kit` compiling them with `abs`.
  First check the constructor encoding and case lowering against
  `skijack`'s source; any further optimizer rule found there enters `abs`
  before G4 starts.
- **G4. The laws, generically.** `KitElim` becomes β-reduction of a Scott
  constructor, one lemma for every arity and position. `KitWords` and
  `KitApply` fix today's runs to exact skeleton terms (`consC`, `catC`)
  and contraction counts; restate them up to weak reduction ("reduces to
  `RVal ⬝ X` with `X →w* Push …`"), which G1b makes as good for `Decodes`,
  and prove them from the source by β. `body_compiles` becomes the
  abstraction of `seq w (seq …)` over the eliminator. Target:
  `kitOf_laws : ∀ tbl, tbl.valid → KitElim ∧ KitWords ∧ KitApply` at
  `kitOf tbl`.
- **G5. Pinning.** The generator emits each table as data (`n`, the
  bodies as word lists) instead of as terms and laws, and a gated test
  checks `kitOf tbl` equal to `skijack`'s terms by `decide`: the
  canonicity test, extended to the four table words. `Ski/Table.lean`
  shrinks from 30 kB of laws to the tables and these tests.
- **G6. The payoff.** `composition_diverges` and `composition_exact` for
  every program SKIlark's compiled form accepts, with no per-program
  instance, including Joy's recursion combinators (`y`, `sumto`).

**Rejected: characterizing the output.** One could read off the families
`skijack` emits (constructor `k` of `m`, `applyU` with `n` arms) and prove
those families directly. That is cheaper for `KitElim`, but `applyU` is
3,078 atoms at eight programs and its shape depends on every body;
proofs keyed to that shape break on the optimizer's next rule, and G1–G2
do not.

**Acceptance.** `kitOf_laws` in the manifest; `Ski/Table.lean` generated
as data; the corpus extended with a program using `y` (`3 sumto`) that
runs end to end under the generic laws.

## 4. Prior art, placed

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

## 5. The endgame: zero knowledge

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

## 6. Acceptance

L0/L1: `lake build` elaborates the manifest, `gates.sh` passes, `lake exe
main` matches the reference on every corpus row — done. Language layer:
composition and the divergence biconditional over SKIlark's compiled form
with `apply`, every leaf in the manifest — done for any table whose laws
are supplied, and checked for two; for every table at once, §3. Endgame: a proof of execution for one corpus program verified by
a third party, with its jet table and per-contraction cost reported.
