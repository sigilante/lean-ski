# lean-ski: the plan

> **Status (2026-09-27).** L0, L1 and L2 built and audited: the calculus, the
> fuel interpreter, budget-exact trace certificates, the write-once heap
> machine and its AIR, the compiled Scott constructors, and conformance
> against `skijack` on seven corpus rows (three SKIlark programs in both
> forms, and `3 sumto`). §2 and §3 are built: the language layer over every
> valid quotation table, with the divergence biconditional, four tables as
> data, and `3 sumto` end to end. From §5, the AIR is built in Plonky3 and
> checked against Lean, with a Sudoku solution in zero knowledge and
> supercombinator jet rows; the endgame of §6 is not reached. Where this
> document and the build differ, the build is authoritative.

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
contraction, each checked by the same three rules. A proof system hides a
trace's contents and not its length, and the contraction count depends on
the witness, so the certificate a prover commits to is budget-exact:
`certifiedPad` has exactly `k` rows for a public budget `k`, one per
contraction and then one per repeated no-redex check. `certified_pad_iff`:
such a certificate exists exactly when `evalF k` returns the value;
`certifiedPad_unique`: it is unique; `certified_pad_budgets`: a run of `s`
contractions is certified at exactly the budgets `k ≥ s + 1`.

**L2, the prover's representation** (`Ski/Heap.lean`). A Krivine-style
machine over a write-once heap: cells are the combinators, applications and
argument-stack cells, each written at the allocation counter and never
rewritten (`mstep_append`). An application at the head unwinds, pushing one
stack cell; `I` and `K` pop their arguments; `S` allocates exactly three
cells. Every transition is an unwind, which keeps the decoded term and
shrinks the head, or a contraction, which is `step?` (`mstep_some`); the
machine stops only at a weak head normal form (`mstep_none`). Loaded with a
term it halts on `v` exactly when the term evaluates to `v`
(`machine_eval`), after as many contractions as `runF` counts
(`machine_count`). Nothing is overwritten, so no work is shared and the
contraction counts are L1's.

**Graph reduction with update in place** (`Ski/Graph.lean`). A heap with
indirection cells, a head and a spine: `I x` and `K x y` overwrite their
cell with an indirection to `x`, and `S x y z` overwrites its cell with
`(x z)(y z)` over two fresh cells, `z` shared. Overwriting a redex is a
parallel step of every decoding, so the root's decoding takes a head step
and then a parallel step. A halted run from `t` leaves a weak head normal
form `v` with `u ↠ v` for L1's value `u`, so with `u`'s head and arity
(`graph_sound`, `graph_spine`), it halts whenever
L1 does (`graph_complete`), and it takes at most L1's contractions. On the
corpus (`lake exe graphcost`) it saves 0–2% of them, 14% on `3 sumto`, but
re-unwinds after each update: 35,675 transitions there against L2's
25,073. Its memory is read-write, and `Ski/RWMem.lean` proves the
generic timestamped multiset check sound: every read returns the last
write to its address (`rw_sound`), and honest runs pass (`rw_complete`).
`Ski/GraphMem.lean` instantiates it on the machine: refined to one access
a step, the statement "`t` halts within `n` steps" over a balanced trace
is sound (`accepts_sound`: `t` evaluates under L1), complete at every
budget from the halting step (`accepts_complete`), and its rows are unique
(`accepts_unique`). Open: a circuit that runs it, with the spine in
memory.

**No combinator quotes live terms** (`Ski/Lambda.lean`, `Ski/Quote.lean`).
The untyped λ-calculus with de Bruijn indices, parallel substitution with
its fusion lemmas, Church–Rosser by complete development and a sound
normalizer; combinators translate into it with weak reduction becoming
β-reduction, and `S K X` reduces to the identity for every `X`. So `Q (S K
S)` and `Q (S K K)` share a reduct, and `no_quote` follows: no closed term
reduces `Q M` to the encoding of `M` over `S | K | I | App` for every `M`,
since the encodings of `S K S` and `S K K` have different normal forms,
computed by the kernel. This is Proposition 3.1 of the metacircular paper. Re-encoding is
definable, since it acts on data: one closed term `R` takes every
encoding `⟨t⟩` to `⟨⟨t⟩⟩` under weak reduction (`Ski/Requote.lean`,
`requote`); under L1 its recursive calls stay lazy.

**Part II: a logic of proofs** (`Ski/Realize.lean`, `Ski/Transfer.lean`).
Formulas are NP atoms, `∧`, `∨`, `→` and `∃` over witnesses. Realizers
are closed terms: a witness for an atom, Scott pairs and injections, and
witness maps. An atom's realizer is a witness on which the verifier
evaluates to `K` (`real_atom_iff`). The combinator system (Hilbert
axioms for `S K I`, modus ponens, Scott constants) is sound (`soundness`).
Natural deduction compiles to it by bracket abstraction (`completeness`),
which is Curry's theorem. Existential elimination needs `∀` over witnesses; with
it, natural deduction with witness abstraction is sound for the compiled
terms (`ndx_realizes`, `NDX.exElim`). Of the two transfer lemmas,
standardization holds in its qualitative form (`eval_of_wsteps`). Its
counted form is false: `S I I (I F)` takes 10 head steps, and its weak
reduct `S I I F` takes 8 (`counted_standardization_false`), because weak
reduction shares a redex that head reduction contracts once per copy. So a
step bound on the trace must be proved of head reduction directly. β for
the compiler's bracket abstraction is counted: at most `3^k · vsize M`
weak steps for `k` formals (`absN_beta_count`). The typed realizer
language (`Ski/Tait.lean`) is simply typed λ with products and sums over
opaque base types (witness types) and constants (verifiers); a product is
eliminated by projection or by split, which binds both halves at once. Every typed
term is strongly normalizing under full reduction
(`strong_normalization`), by Tait's reducibility. A typed closed realizer,
written as SKIjack source and compiled by `comp`, converges when its atom
verifiers realize their types (`compiled_converges`, `Ski/Bridge.lean`);
constant-free glue converges outright (`glue_converges`); the proof is Tait's argument
on the compiled `SKI` terms, and needs no simulation. The same holds for the
threaded compilation the prover runs (`compiledA_converges`,
`Ski/BridgeA.lean`), so convergence and the cost bound speak of one term. Existential
elimination is in: `∀` over witnesses types the eliminator's argument,
and natural deduction with witness abstraction is sound for the compiled
terms (`ndx_realizes`). Stratum 1 is proved at the source
(`Ski/Stratum.lean`): under the additive count, every call-by-name step of
an additively affine realizer shrinks its additive size. The compiled
term's own normal-order steps are bounded too (`Ski/Cost.lean`,
`Ski/CostAdd.lean`). A graded typing charges each combinator once, since
bracket abstraction never duplicates a variable and a copy made by `S` goes
where `K` discards it. So a compiled affine glue realizer applied to
witnesses head-normalizes within its combinator count plus the witnesses'
costs (`glue_head_bound`). For variables shared across a case's branches,
compilation threads them through the continuations (`trA`,
`glue_head_bound_add`). Stratum 2 is proved (`Ski/Stratum2.lean`): typed
realizers with contraction normalize (`strong_normalization`,
`compiled_converges`) but admit no elementary bound. The tower `two two ⋯
two` applied to a Boolean toggle has additive size `8k + 17` and takes at
least `2↑↑(k+1)` call-by-name steps (`no_elementary_bound`). The bound holds
on the compiled trace too (`Ski/Stratum2C.lean`): under either compilation,
every normal-order reduction of the compiled tower, applied to the toggle
and `true`, to a weak head normal form takes at least `2↑↑(k+1)` steps,
and the compiled term has `6k + 39` combinators plus the witness's
(`compiledA_no_elementary_bound`). Stratum 3 is proved
(`Ski/Stratum3.lean`): a typed fixed point, compiled to SKIjack's `Y`,
breaks strong normalization. `fix (λx. x)` is typed and has no
call-by-name normal form, and its compiled term `Y ⬝ I` diverges, timing out
at every fuel. `fix (λx. inl c)` still evaluates, so fuel is the only
uniform treatment. Without `fix`, typed closed realizers evaluate. The Σ-protocol algebra's glue lies in stratum 1
(`Ski/Sigma.lean`). AND and OR are primitive and threshold is a fold.
Introduction, projection, split, case, AND and OR commutation, threshold
weakening, and the prover's composition of every plan are closed, typed and
additively affine, so the stratum-1 bounds apply at the source and on the
compiled term. OR distributed over a context shares the context across a
case's branches, so only the additive count puts it in stratum 1
(`additive_rule_needed_glue`). Using both halves of one pair variable by
projections (`λp. (snd p, fst p)`) is contraction; the split binds both
halves once, so AND commutation by split is in stratum 1 (`andComm_s1`).
The theorem covers the glue listed in `glue_stratum1`.
The census is computable and exact
(`Ski/Census.lean`): stratum 3 if a fixed point occurs, 1 if additively
affine, 2 otherwise. Each stratum carries its theorem in the language with
`fix`. The additive rule is needed: `sharedT` is contraction under the raw
count but stratum 1 under the additive one. The census of the Σ-algebra's
glue, the tower of twos and `fix (λx. x)` is computed in the kernel.

**The compiled constructors** (`Ski/Scott.lean`, generated). `Zero` is
`K`; `Suc` is eight atoms; `Push` twenty-two. Each elimination lemma is the
reference reducer's contraction sequence on symbolic arguments, re-run by
the kernel: `iter_sound (k := 7) rfl` for `Suc`. The lemmas expose the fact
every word-level proof must reason through: bracket abstraction passes
fields as thunks, so `Suc n z s` reduces to `s (K n s)`, not `s n`.

**Conformance** (`Ski/Corpus.lean`, `Main.lean`). Three SKIlark programs
in both forms, and `3 sumto`; `runF` agrees with `skijack`'s host reducer contraction for
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
each static quotation's body. Everything is proved once over a kit. What
a table must satisfy is the three law classes `KitElim`, `KitWords` and
`KitApply`, and `Ski/Laws.lean` proves them for the kit compiled from
every valid table (G4, §3). `Ski/Table.lean` (generated) gives four
tables as data and checks by `rfl` that compiling each gives `skijack`'s
terms: the kernel with no static quotations (`NoQuot`), the corpus table
(`[dup +]`, `[dup]`), the table of `[dup i] dup i` (`LoopTable`) and the
table of `3 sumto` (`SumTable`).

`Decodes` reads a value by probing it at fresh variables (`OTerm`), a
quotation at `n + 3` of them; at any closed continuations the probe then
holds exactly (`probe_*`), decoding is a function, and it is closed under
backward weak reduction (G1b). Every word has a leaf
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

## 2. The language layer, `lean-nock` ported to SKIlark (built)

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
   strictly. `composition` and `composition_diverges` then go through
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

## 3. Every table at once (built)

The three law classes hold for the kit compiled from every valid
quotation table (G4, `Ski/Laws.lean`), so a program with a new static
quotation needs only its table as data and the `rfl` checks that
`skijack`'s terms are that kit's (G5). Before G4, a table's laws were
about thirty facts the kernel checked by `iter_sound rfl` in a generated
instance. G6 states the headline theorems for every program over every
valid table, and runs `3 sumto`, built on Joy's `y`, end to end.

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
- **G1b. Decoding up to weak reduction — built, by route (a)**
  (`Ski/Open.lean`, `Ski/Decode.lean`). A probe demands that head
  reduction reach the continuation exactly, and standardization yields
  only a head reduct that weakly reduces to it, so closure needs the
  continuation carried untouched: parametricity. The decode relations now
  probe at *fresh variables* of `OTerm`, `Term` with inert variables: a
  term decodes when its open image, applied to the variables `vars b` for
  every `b` above its own, head-reduces to the constructor's variable
  applied to decoding fields. Three things follow.
  *Closure*: `DecStack.of_wsteps` and its siblings, and
  `Contract.of_wsteps` — if `t` weakly reduces to `u` and `u` decodes (or
  meets a contract), so does `t`. A probe ends at a variable-headed term,
  and internal parallel steps cannot change a variable at the head
  (`OParIs.var0` and its siblings). Both use no axioms.
  *The closed probes*: `DecStack.probe_cons` and its siblings recover the
  old definitions exactly — at any closed continuations, head reduction
  reaches the continuation applied to decoding fields — because head
  reduction commutes with substitution. Every leaf, `apply` and converse
  proof now calls these lemmas in place of the old definitions, with no
  other change, and every headline statement is unchanged.
  *Functionality*, with no markers: probes at the same variables end at
  the same stuck term, and distinct constructors end at distinct
  variables.
  What is not proved: the reverse of the closed probes, that a term which
  probes exactly at every closed continuation also probes at variables.
  The new relation is therefore at least as strong as the old and not
  shown equal. Where decoding is a conclusion (a contract's result) that
  only strengthens the theorems; where it is a hypothesis (an input stack
  in `composition_diverges`), it asks more of the input, and every input
  the development builds meets it (`encStack_dec`, every word's result).
  Route (b), probes up to weak reduction, was set aside: its converse
  must reach each recursive call only up to internal reduction, and no
  argument was found that the contraction count then falls strictly at
  every call, which the converse's induction needs.
- **G2. λ-terms and abstraction — built** (`Ski/Abs.lean`). The source
  syntax is `OTerm` (G1b): `S`, `K`, `I` and variables for the formals,
  with globals entering as closed terms, as `skijack` expands them before
  abstracting. `abs` is `bracket_abstract` rule for rule, tested in the
  same order. `abs_beta : abs x M ⬝ N →w* M[N/x]`; `abs_beta_head` is the
  same as head steps followed by internal parallel steps (G1's split);
  `absN_beta` is β for all the formals at once, for closed arguments,
  through `abs_subst` (abstraction commutes with substituting a closed
  term for another variable). Fidelity: for every Scott constructor of
  every table, a generated `*_abs` theorem checks by `rfl` that `absN` of
  its source `λ fields conts. k_j fields` is the term `skijack` emitted
  (21 constructors across `Ski/Scott.lean` and `Ski/Table.lean`), and the
  generator first checks the same with aviary's own abstraction.
- **G3. The kernel's source as a function of the table — built**
  (`Ski/Kernel.lean`). `skijack` compiles in four steps, read from
  `skijack/expand.py`: a case lowers to its scrutinee applied to one
  continuation per constructor; each λ chain is λ-lifted to its own
  combinator, whose formals are the enclosing binders free in it (in scope
  order) then its parameters; every combinator is bracket-abstracted over
  its formals; and a recursive equation becomes `Y` applied to the
  abstraction over a fresh self-parameter. `Src` is the desugared source,
  `comp` does the lifting and abstraction, `compDef` and `compRec` the
  definitions. Every table-independent equation of the kernel (the twelve
  words, `seq`, `idW`, and the recursive `add`) compiles to `skijack`'s
  term (`wPop_compiles` through `add_compiles`). The equations were first
  transcribed by hand; the front end below now reads them from the source. `Table` is a table as data (its size and its bodies as
  word lists), and `Table.kit : Table → Kit` compiles its constructors,
  `wQcons`, `wCat`, `wUnit`, each body `b_k` and `applyU` (with its
  `n + 3` arms and `Y`) from source. For each generated table,
  `Ski/Table.lean` checks every one of those terms by `rfl` against
  `skijack`'s (27 `table_*` theorems across the three tables).
- **G4. The laws, generically — built** (`Ski/Laws.lean`). The laws are
  restated up to weak reduction, and every one is β for compiled source.
  `absN_beta_subst` and `absN_beta_close` (`Ski/Abs.lean`) reduce an
  abstraction applied to all its formals to its body, under any
  substitution and with no capture condition. `lam1_beta` and `lam2_beta`
  do the same for a λ-lifted combinator, and `Src.ev` reads the result
  back as source. `KitElim` is `ctor_beta`, one lemma for every arity and
  position, on open terms. `KitWords` runs `unit`, `cons` and `cat` to
  `RVal` of the table's constructors applied to the fields; the skeletons
  (`consC`, `catC` and the rest) are gone. `KitApply` keeps `Y`'s
  unrolling as head reduction and runs the arms by β; `body_compiles` is
  `bodyT k ⬝ R →w* N R (body k)`. The consumers accept weak runs:
  `Contract.of_wsteps` and the `*W` shared steps for the forward theorem,
  and for the converse `StepsN.wtail`, which says weak reduction never
  lengthens the run to a normal form, from `par_step_le` (`Ski/Weak.lean`):
  a head step costs a parallel reduct at most one. Target met:
  `Table.kit_elim`, `Table.kit_words` and `Table.kit_apply` for every
  `tb : Table` with `tb.Valid`.
- **G5. Pinning — built.** The generator emits each table as data
  (`table`) with its `table_*` `rfl` checks against `skijack`'s terms and
  `table_valid`. Its instances are `table.kit` and the three theorems of
  G4. The per-table laws are gone: `Ski/Table.lean` falls from 46 kB to
  41 kB, and what remains is `skijack`'s literal terms, the
  constructors' `*_abs` checks, and the programs' `c*_compiles`.
- **G6. The payoff — built** (`Ski/Programs.lean`). A program compiles
  as a static quotation's body does (`Table.progT`), and
  `progT_wsteps` reduces `progT p ⬝ ap ⬝ s` weakly to `N ap p ⬝ s`, so no
  program needs a `Compiles` proof. Divergence is invariant under weak
  reduction (`diverges_iff_of_wsteps`, from `StepsN.wtail`). For every
  valid table, every program valid over it and every stack term that
  decodes: `Table.program_apply` (a `Run` derivation is realized),
  `Table.program_diverges` (the compiled program diverges exactly when
  `Run` derives nothing) and `Table.program_exact` (whatever it
  normalizes to decodes to a derived outcome). The generator pins each
  program's term to `progT` of its words by `rfl` (`c*_eq`), in place of
  the per-program `c*_compiles` runs. `3 sumto` is a fourth table
  (`SumTable`, five static quotations) and a corpus row, `sumto_us`, whose
  10,297 contractions `lake exe main` checks against the reference
  reducer. Its `Run` derivation is built on the host and checked by the
  kernel (`cs_run`). `SumTable.us_six` proves the row reaches a weak head
  normal form that decodes to `[6]`, and `us_exact` proves nothing else.

**Rejected: characterizing the output.** One could read off the families
`skijack` emits (constructor `k` of `m`, `applyU` with `n` arms) and prove
those families directly. That is cheaper for `KitElim`, but `applyU` is
3,078 atoms at eight programs and its shape depends on every body;
proofs keyed to that shape break on the optimizer's next rule, and G1–G2
do not.

**Acceptance.** The three classes at `tbl.kit` in the manifest (met, G4);
`Ski/Table.lean` generated as data (met, G5); the corpus extended with a
program using `y` (`3 sumto`) that runs end to end under the generic laws
(met, G6: `SumTable.us_six`).

**The front end — built** (`Ski/Front.lean`, `Ski/Source.lean`). The
kernel's source enters as the text `skijack` compiled, character for
character (`Ski/Source.lean`, generated), not as a transcription. A total
lexer, parser and desugarer for SKIjack's core reads it, lowers each case
in declaration order, and refuses an incomplete, mixed or repeated case
as `skijack` does (`Front.refuses_*`, `lowers_in_declaration_order`).
`compileFile` compiles a whole file. `KernelSrc` is the front end's
reading of `kernelText`. `kernel_agrees` and the four `front_agrees`
check, in the kernel, that Lean compiles each of the four source texts
to every term `skijack` emitted for it: constructors, words, `applyU`,
bodies, programs and corpus rows. `skijack` is now an untrusted second
implementation, as its SPEC §0 describes.

**The compiler simulates the source semantics — built**
(`Ski/Simulation.lean`). The source gets its own operational semantics,
`SStep`, on closed terms with closures, as λ-lifted code runs: β for a
closure applied to all its parameters, δ for a global equation (a
recursive one binds its self-parameter to itself), and Scott case (a
constructor applied to its fields and one continuation per constructor
selects its own), all under weak congruence. `Tr` relates a source term
to its compiled forms; it is a relation because `Y` unrolls a recursive
global to a self-reference that is not its compiled term but behaves as
it does. `simulation`: if `c` steps to `c'` and `t` is a compiled form of
`c`, then `t` weakly reduces to a compiled form of `c'`, for every
program whose compiled globals are what the compiler gives
(`Fixed`). `kernel_fixed`, `corpus_fixed`, `loop_fixed` and `sum_fixed`
check that for the four compiled sources. `wPop_push` applies it: the
source run of `wPop (Push x y)` gives `Scott.wPop ⬝ (Scott.Push ⬝ x ⬝ y)
→w* Scott.RVal ⬝ y`.

**`cw` from the source — built** (`Ski/SourceJoy.lean`). Each kernel
word's equation, as the front end reads it (`kernelDefs`, checked against
all four source texts), run in the source semantics on a stack's encoding,
reaches the encoding of `cw`'s outcome: `plain_source` for the nine words
that run no quotation, `cwR_source` for all twelve given an eliminator
that meets a relation at the source. The source has no thunks, so the
results are exact encodings. `Ski/SourceEval.lean` supplies normal-order
proof search (`seval_sound`), run on closed terms with placeholders and
filled (`SSteps.substC`), because the elaborator caches only closed terms.

**The converse, for programs — built** (`Ski/SourceRun.lean`,
`Ski/Adequacy.lean`). `run_source`: every `Run` derivation is a run of
the source program, through `applyU`'s case over the table's
constructors. With the simulation and `Table.program_exact`, the three
semantics agree for every valid table whose source has its structure
(`JoyProg`) and whose compiled globals are its terms (`GenvTable`), and
every valid program and stack: the compiled program normalizes to a term
decoding to a valid outcome iff the source program reaches its encoding
iff `Run` derives it (`exact_iff`), and it diverges iff the source reaches
no outcome (`diverges_iff_source`). `Ski/SourceTables.lean` instantiates
this for the four compiled sources; the source of `3 sumto` reaches
`[6]` and nothing else, and that of `[dup i] dup i` reaches nothing. Not
proved: the converse for arbitrary source programs, outside Joy's
encodings. Bracket abstraction's η rule makes some source β-steps free in
SKI (`λx. f x` compiles to `f`), so head-step counting alone does not
bound source runs, and a general proof needs a measure on source terms
that η-steps decrease.

**The front end's coverage of SKIjack** (`Ski/Front.lean`,
`coverage/`). The front end reads all of SKIjack that `skijack`
compiles, in both lexicons:

- level 0: types, signatures, equations, definitions, cores (with
  parameters, sibling resolution, `core.eq` names and an interpreter
  core's `loop`), λ, cells, axis picks and case, with the ISA, Tier 1 and
  the prelude;
- macros (`:=*`), as `expand_macros` expands them: capture-avoiding
  substitution with `skijack`'s fresh names, λ and case binders
  shadowing, the last declaration and parameter winning, and its three
  limits (nesting 256, 100 nested unfoldings, 200 000 substitutions);
- the forms `generate.py` generates for a file with an object type: the
  walker `sp`, the rebuilder `rb`, the default `S`/`K`/`I` step
  equations, and each interpreter core's `step` and fuel loop;
- level 1 (pass 6): data `<e>`, quoted over the object type with nested
  quotation and scry `?^/a/b`; runs `[i a… |-] <e>@n`, packaged as the
  interpreter core's loop applied to its arguments, the fuel numeral and
  the datum; namespace literals `ns{…}`, compiled to resolvers through
  `EQ5`. Data join the program in declaration order, so level 0 may name
  them and later data may inline what names them.

The coverage project `coverage/` (generated; its own Lake project, built one
module at a time by `scripts/build-coverage.sh`, with a generated audit)
checks in the kernel that the front end
compiles, in both lexicons, a coverage file, a macro file, a generation
file, a level-1 file and all seventeen corpus files `skijack` accepts to
exactly the terms `skijack` emits (`agrees_termOf`,
`agrees_termOf_rev`), that the simulation applies to each (`*_fixed`),
and that forty-one programs `skijack` refuses are refused (`refuses_*`):
at level 0, for macros or nesting, for generation, and at level 1; and
the four corpus files `skijack` refuses are refused in both lexicons
(`refuses_corpus_*`). A
declaration named `S`, `K` or `I`, such as an object type's leaf, and a
level-1 declaration are not globals of the source semantics
(`progDefs`): level 0 resolves those names to the ISA, and a datum or
run is a closed term. The substitution limit is not exercised: reaching
it costs 200 000 substitutions in the kernel. The kernel checks abstract
by `absNF`, proved equal to `absN`: `absN` rechecks occurrence at every
node, cubic for `ascii-digits`' 128-way type (220 s for its
constructors), and `absNF` carries the term's variables (5 s).

Where `skijack` emits a term that is not closed, the front end refuses
instead: an equation or a run's argument that names a run, and a
namespace literal whose `EQ5` names a datum, keep an atom for which
`skijack` defines no term. **The checker** (`Ski/Check.lean`, `Ski/TypeCheck.lean`). `skijack`
checks before it compiles: Stage A (`check.py`) over the parsed program,
for scope, case, data positions, the two symbol tables and the
interpreter interface; Stage B (`typecheck.py`) over the generated
program, Hindley–Milner with an oriented, equirecursive unifier in which
a datum may be applied and a function is never a datum. Both only refuse,
so `checkPass` is a Boolean and `checkedWith_of_pass` proves that where it
passes the checked compilation is the unchecked one. Stage B is ported
object for object: a type is a node in an arena whose index is its
identity, flags are updated in place, and nodes are allocated where the
Python allocates, so sharing and every flag update are the Python's.
Each walk is bounded by the Python's recursion limit, 1000; the Python's
Stage B recurses without end on `scripts/coverage.ski` (even at a limit
of a million), and the bound refuses it as the Python's `RecursionError`
does, in the same group (`arith.plus`). The coverage project checks, for
every file and lexicon, that the front end's checker passes exactly where
`skijack`'s does (`*_checks`, `*_check_refuses`), and thirty programs,
twenty-two the checker refuses (`refuses_checked_*`, sixteen at Stage A
and six at Stage B) and eight it accepts (`checks_*`). A differential
test (`scripts/differential.py`, over `lake exe front`) runs every corpus
and script file, in both lexicons, as written and with each line deleted
in turn: 1,260 programs, against `skijack` `e978e58`. The front end and
`skijack` agree on every compilation, every term, every checked
compilation and every verdict of the checker. (An earlier, uncommitted
run counted 629 programs on the corpus of 2026-09-26.)

**What is still per table and per program.** Every theorem is stated for
every valid table and every program. Three facts about each generated
table or program are still checked one by one:
- `skijack`'s terms equal the Lean compilation of the source, by the
  kernel (`front_agrees`, `table_*`, `c*_eq`). The Lean compiler is
  checked against `skijack` on four compilations and the coverage files,
  and proved to simulate the source's semantics (above).
- the table is valid (`table_valid`).
- for an end-to-end example, the program's `Run` derivation (`cs_run`
  and the hand-written ones in `Ski/Examples.lean`).

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
   circuit is an AIR over the heap machine (`Ski/Air.lean`): a row per
   machine transition, about 2.44 per contraction, holding the three
   registers, and a committed memory table for the heap reached by
   lookups. Zorp's framework frames it: SKI execution and memory each
   satisfy their component of traversability (`zk/`), but the execution
   labels are whole terms and the components are unlinked, so Zorp's
   compilation to a RAP does not apply as is. Outputs must be
   canonical: a whnf term carries unreduced closures, so the statement is
   about the decode relation (§2.3) or about a term of atoms, exactly the
   read-back problem SKIlark hit at level 1.
2. **Jets as precompiles.** A jet fires once per supercombinator
   application and does its body's work natively; that is precisely a
   zkVM precompile, whose soundness is the recurring weak point of every
   zkVM and is argued in prose. Here a supercombinator jet is licensed
   once for every template (`inst_sound_g`: instantiation is weak
   reduction), and the circuit's instantiation rows are proved to be
   jetted steps (`instRow_jstep`, `air_sound_jet`). A data jet over native
   words would be `composition` for the jetted word, under the table's
   `ApSound`; its three-valued contract, proved for the kit's eliminator
   and owed per table, is what the prover needs, since a precompile that
   bails where the term diverges is the same observable divergence
   `+mock` exposes.
3. **Semantics without touching the circuit.** The object language, the
   self-interpreter, scry and the namespace, SKIlark: all terms. The
   circuit is fixed once and audited once. New symbols, new interpreters
   and new languages are data.

The concrete route: (a) L2 here, the term representation a prover
consumes — the write-once heap machine is built (§1); terms have Pure
Nock noun fingerprints in the `zk/` project, which depends on Pure Nock
and so on Mathlib, keeping the core free of both (the machine's cells are
not yet fingerprinted) — done: distinct terms collide for at most `2Λ − 1` elements of any field where `2 ≠ 0`,
BabyBear's degree-4 extension included; (b) the traversability theorem,
in `zk/` — done: `execution_traversable` (states `S K I halt`, fanout 1)
and `memory_traversable` (terms as nouns, fanout 2), with state–data
separation for both; each is one component, the two are not linked, and
the execution labels are whole terms, so no RAP follows as is;
(c) a first proof of execution on an existing stack — done on RISC Zero
(`bench/`), with hand ports of `runF` and the heap machine checked against
the corpus counts in place of a C extraction. Reduction in heap mode costs 309
cycles per contraction on `3 sumto`, tree rewriting 1,470, and the whole
heap-mode guest 2,138. A
2^20-cycle segment proves in about 55 s on a CPU;
(d) the custom AIR — specified and proved (`Ski/Air.lean`): rows are the
machine's registers, the heap is a committed memory table reached by
lookups, and the constraints accept a table of `k` rows exactly when `k`
exceeds the run's transitions, ending on `runF`'s value (`air_sound`,
`air_complete`, `air_budgets`). Its size on the corpus
(`bench/AirCost.lean`, `lake exe aircost`): about 2.44 rows per
contraction, 25,074 rows and a 37,306-cell memory table for `3 sumto`.
The constraints fix the run, not its output, which is the read-back
problem; they load the whole term in the clear, so hiding a witness
needs the loaded heap committed; and they assume a lookup argument with
one value per address and range-checked reads. The prover is built in
Plonky3 (`bench/plonky3/`): CPU, memory and program tables over BabyBear
joined by a LogUp bus, with one value per address and 24-bit range checks.
Every corpus row proves and verifies (`3 sumto`, 32,768 rows, in about 0.5 s),
and `lake exe aircheck` (`Ski/AirCheck.lean`) accepts every table it
proves with a checker that decides the AIR's constraints, while four tampered
tables fail both. Outputs bind by probing: the machine has an inert
`atom` cell, read back as an open term's variable, and a table of
`t X₁ … Xₙ` whose last row has the atom `i` at the head proves
`t X₁ … Xₙ ⟶* Xᵢ a₁ … aₖ` (`Ski/HeapOpen.lean`, `Ski/AirOpen.lean`,
`air_probe`). The first zero-knowledge proof is a Sudoku solution
(`Ski/BoolProbe.lean`, `Ski/Statement.lean`, `Ski/Sudoku.lean`,
`Ski/SudokuCheck.lean`, `bench/plonky3/src/sudoku.rs`). The witness is 729
Scott Booleans; the formula (every cell one digit, every row, column and
box every digit, the clues) compiles to a selector over shared slot
cells, applied to the atoms `ACC` and `REJ`; a table that reads `ACC` at
the head proves that the inputs solve the puzzle (`sudoku_sound`); that
the prover knows them rests on the STARK's knowledge soundness, not proved
here. In
Plonky3, with a hiding PCS, a private witness table constrains each input
cell to `K` or `K I`, the CPU and memory heights are fixed constants, the
last row must read `ACC`, and two blinding messages mask the lookup sums
Plonky3 publishes per table, which otherwise let a verifier check a
guessed grid. 45,667 rows, proved in about 3 s and verified in 0.08 s;
the statement file checked by `lake exe sudoku statement`, the table
accepted by `lake exe sudoku check` (`sudokuCheck_sound`), and a wrong
grid and a non-Boolean input rejected by both. The terminals' hiding is
proved in Lean (`Ski/ZK/`); the rest rests on Plonky3's unaudited hiding PCS. The non-Boolean input (`I` in an input cell) reaches `ACC`, so
the witness table's Boolean constraint carries weight. The corpus
proofs stay non-hiding and load the whole term in the clear.
Supercombinator jets are licensed once for every template: an
instantiation is weak reduction when the head is `absN xs body`
(`inst_sound`), a jetted run that halts proves normal-order evaluation up
to weak reduction of the value (`jet_run_eval`, `Ski/Inst.lean`), and
weak reduction keeps a value's head and arity, so a jetted run reads back
what an unjetted one does (`jet_run_shape`, the small lemma,
`Ski/SmallLemma.lean`). The instantiation rows are built
(`Ski/AirJet.lean`, `bench/plonky3/src/jets.rs`). A body names its closed
subterms as globals, public cells (`inst_sound_g`); instantiation without
them costs 2.2–6.0× the plain run on the compiled rows and `3 sumto`, and
with them those rows take 28–34%; the interpreted rows gain nothing. An instantiation row at a licensed root is
a jetted step (`instRow_jstep`), and an accepted table proves that the
term evaluates to a value that weakly reduces to the table's, with its
head and arity (`air_sound_jet`). Every corpus row proves jetted, and
`lake exe jets check` accepts each table. The verifier runs `lake exe jets
statement` on its own terms first, which checks each jet file against its
term and licenses its roots (`rootsOKB`): `3 sumto` takes 3,304 CPU rows
instead of 25,074. Jets combine with probes: a jetted run from a state
with atoms is open weak reduction (`ojsteps_owsteps`, `Ski/InstOpen.lean`),
which reaches a marker's spine by head reduction (`owsteps_spine`,
`Ski/ProbeTree.lean`). A table of probe segments, one per constructor of
an outcome's probe tree, proves that the term decodes to the outcome
(`air_probe_decodes`, `Ski/AirProbe.lean`; `bench/plonky3/src/probe.rs`):
`3 sumto` decodes to `[6]` in 11 segments and 4,144 CPU rows. Jets do not
yet combine with zero knowledge.

A hidden term, not only Booleans: the witness machine
(`Ski/Witness.lean`) puts a private region of cells, each `S`, `K`, `I` or
an application of two cells below it, under the public `V x`, and a table
ending at `K` over an empty stack has in its region a realizer of `atom V
x` (`wit_realizes`), the atom Part II's logic composes. In Plonky3
(`src/witness.rs`), a hidden witness table commits the region's cells and
range-checks their pointers; hiding, fixed heights and blinding are the
Sudoku proof's. Two examples prove in about 0.1 s
(`Ski/WitnessExamples.lean`). The guess test does not match, and matches
with the blinding off. An atom certifies exactly its verifier's
evaluation: a verifier applies its witness to finitely many arguments,
and a term can fake any finite behaviour (`neg_fake`, `sat_fake`), so data
witnesses belong in cells the circuit fixes, as the Sudoku inputs are.

Zero knowledge, composed (`Ski/Compose.lean`): a formula of atoms under
`∧` and `∨` compiles to one statement about evaluation, exact in both
directions, and over an assumed, idealized proof system for such
statements the composed system inherits completeness, knowledge
soundness and zero knowledge, hence witness indistinguishability
(`compose`). The statement is a list of evaluations over hidden literal
bits and a hidden term, not one evaluation: an atom is realized by
evaluation to the literal `K`, which no combinator conjoins exactly, since
`S (K K) I` behaves as `K` and is not `K`. The circuit for it is built
(`Ski/Composed.lean`, `src/composed.rs`): one segment per term, each
ending at `K` over the empty stack, restart rows to the next root, bits
constrained to Scott Booleans. A table the checker accepts for a
formula's statement has bits and a witness that read back as a realizer
of the formula (`checkC_realizes`); the `∨` and `∧` of two atoms prove in
about 0.1 s. Not formalized: implication and `∃`.

### The verifier checks exactly the spec: done for the corpus circuit

The corpus circuit, the three AIRs the verifier builds for a public term,
is proved to check exactly `Air.Accepts` (`Ski/Circuit/`):

- **The circuit as data.** `Circuit.baseAirs t`: 125 CPU constraints and
  8 bus messages, the memory and program AIRs, as Plonky3's symbolic
  builder records them.
- **The Rust bound to the Lean value.** `ski-air export-base` prints the
  verifier's AIRs through `InteractionSymbolicBuilder`; `lake exe circuit
  compare` checks they have the normal forms of `baseAirs t`
  (`sameAirsB`), and normal forms fix meaning (`sameAirB_sound`). The
  verifier runs the comparison on the AIRs it verifies with, for every
  term, and refuses on a difference; gate 5 also runs it on three terms
  and refuses a doctored export.
- **Soundness** (`export_sound`): tables accepted for AIRs with those
  normal forms decode to a memory and rows that `Air.Accepts` accepts, so
  the term evaluates. The informal arguments, now proofs: one value per
  address (`mem_addr`), sends that are bits and a height check that keeps
  their count below `P` (`lookup`), range checks as `a < c` below the
  modulus (`BaseOK.read`).
- **Completeness** (`export_complete`): every evaluation has honest
  tables the circuit accepts at every CPU and memory height the verifier
  accepts (powers of two up to `2^21`) that holds the run, the memory
  padded with nils as the prover pads it; they decode back to the run.
- **Assumed, not proved** (`Accepted`): Plonky3's STARK and LogUp
  soundness (every constraint vanishes on every row; every bus balances,
  with the heights' check; LogUp's interactive core is since proved,
  `logup_accept`, below), and heights within BabyBear's two-adic
  domains, `2^27`, which the verifier's own cap of `2^21` implies.
  Plonky3's selectors are not `0`/`1`; `Ski/Circuit/Selectors.lean`
  proves soundness and completeness with any selectors of their zero
  pattern (`export_sound_P`, `export_complete_P`). Trusted, not proved: the export's parser and the
  compiled comparison, and Plonky3's symbolic builder recording what its
  verifier checks.

The composed circuit (`release/composed`): its five AIRs as data
(`compAirs`), checked against the Rust by `composed-verify` itself; its
soundness, `compExport_sound`: an accepted proof's memory holds bits and a
region whose witness the formula's statement accepts, and which read back
as a realizer. Its blinding columns take part in no lookup the proof uses.
Its completeness, `comp_complete`: every run the AIR with segments
accepts, from literal bits and a well-formed region, at the verifier's
heights, has honest tables the circuit accepts (the blinding flags clear),
decoding back to the run.

The hidden-term circuit (`bench/plonky3/src/witness.rs`): its four AIRs as
data (`witAirs`), checked against the Rust by its verifier; soundness,
`witExport_sound` (an accepted proof's region realizes the atom), and
completeness, `wit_complete` (every run from the witness machine of a
well-formed region, ending at `K`, at the verifier's heights).

The Sudoku circuit (`bench/plonky3/src/sudoku.rs`): its four AIRs as
data (`sudAirs`); soundness, `sudExport_sound` (an accepted proof's input
bits solve the puzzle), and completeness, `sud_complete` (every accepting
run of the statement machine at the verifier's fixed heights).

The jet circuit (`release/`): its eight AIRs as data (`jetAirs`), checked
against the Rust by the verifier, which also recomputes the jet table;
soundness, `jetExport_sound` (an accepted proof is a run of `AcceptsJ`,
so the term evaluates up to weak reduction of the value), and
completeness, `jet_complete` (every run of `AcceptsJ` within `2^21` rows).
The probe circuit: its ten AIRs as data (`probeAirs`), checked against
the Rust by the verifier, which recomputes the plan from the outcome;
soundness, `probeExport_sound` (an accepted proof decodes the term to the
outcome), and completeness, `probe_complete` (every run of `AcceptsP`
from the loaded term within the verifier's heights).

Zero knowledge of the published terminals (`Ski/ZK/`): over BabyBear's
quartic extension, built in Lean and proved a field, the three private
terminals of the Sudoku, hidden-term and composed proofs have one
distribution over the blinding for any two balanced, unblinded table sets
of a statement (`sud_zk`, `wit_zk`, `comp_zk`; the composed ones sharing
their segment table), for a fixed challenge whose combiner matrix is
invertible. That fails exactly for the `P^2` challenges in `F(x^2)`, about
`2^-62` (`generic_iff`, `nongeneric_count`). A zero denominator aborts the
prover for at most one `α` per message (`abort_count`), below `2^-99` for every released proof, whose `M` is under `2^24` (`csplit8`'s is the largest, `ski-air fs-budget`).
A simulator for the whole transcript (`transcript_zk`; the model in
`Ski/ZK/Transcript.lean`, the proof in `Ski/ZK/TranscriptN.lean`): fixed by the statement, it matches the real transcript
on every event within `P^2/P^4 + M/P^4 + ε/NR` of the draws, for
public-coin challenges and a PCS within `ε` of simulatable (`PCSClose`,
the one assumption). The composed proof's segment table is public for the
honest prover (`segs_honest`). Assumed: Plonky3's hiding PCS for the committed traces and
openings, and the challenge's independence of the blinding.

SKIlark in zero knowledge (`bench/Skilark.lean`, `release/skilark`): a
SKIlark program is the verifier of a predicate statement over literal
bits (`Ski/Predicate.lean`, `Ski/Circuit/CompPred.lean`). The composed
circuit is general in its statement (`compAirsG`, `compExportG_sound`,
`comp_completeG_log`), and a predicate's one term reads the bits, which the
circuit constrains to `K` or `K I`, and never the witness term: an
accepted proof holds Booleans on which the verifier accepts
(`predExport_sound`). A witness term would not do, since it answers the
verifier's case analysis however it likes. The first predicate, `split`
(`skilark.zk`), adds two hidden bit strings and compares the sum with
`x`; at `k = 8`, 129,965 rows at `2^17`. The statement names its heights
(`log R M`). The committed split `csplit` adds a knapsack commitment to
`a` under public weights, checked in the same pass: 471,888 rows at
`2^19`, proved in 42 s. At these sizes the commitment neither binds nor
hides (`2^16` openings, sums of at most 437); it is the statement's shape.
Jets on SKIlark code, measured in the clear (`bench/plonky3/README.md`):
`split8`'s verifier runs in 11,483 rows jetted against 129,957 plain,
8.8%, with 130 jets from the source's templates; Lean accepts the jetted
table (`jets check-src`). The design for jets under hiding is Avon's
`docs/ZK-JETS.md`; its tree lemma is built (`Ski/ZK/Tree.lean`,
`tree_hides`): a spanning tree of blinding buses over any number of
private tables hides their terminals, and the composed circuits' chain is
its three-table case (`chain_hides_tree`). The whole-transcript simulator
over any such tree is `transcript_zkN` (`Ski/ZK/TranscriptN.lean`), and
the three-table `transcript_zk` is its instance: the chain's view is the
tree's (`chain_viewT`), the tree's reference base the chain's reference
triple (`viewT_xrefN`), and the sums over two tuples are the sums over two
edges (`tsum_tsumN`). So `comp_transcript`, `sud_transcript` and
`wit_transcript`, their statements unchanged, rest on the tree: the
design's milestone 2. The non-generic `β`, `P^2` of `P^4`, are public, so
every hiding verifier rejects them and every prover that writes a hiding
proof redraws its seed (`bench/plonky3/src/reject.rs`); `transcript_zkG`
(`Ski/ZK/Reject.lean`) and each circuit's `*_transcriptG` bound the real
and simulated counts at the generic `β` within `M/P^4 + ε/NR` of all the
draws, without the `P^2/P^4` term. The honest prover's tables meet the
transcript theorems' hypotheses for every hiding circuit: balanced with
the public tables, blinding flags clear (`comp_honest_zk`,
`sud_honest_zk`, `wit_honest_zk` in `Ski/ZK/Honest.lean`;
`CRun.honest_zk`; `honest_zkP`). The view includes the trace heights:
blinding keeps them, the honest tables' are the statement's, and the
simulator emits those (`transcript_zkGH`, `Ski/ZK/Heights.lean`) for the
composed, Sudoku and hidden-term circuits; the jet circuits' heights are
public, but no theorem yet ties their honest tables to them. The margin
check counts two points a query; simulating the quotient's openings would
need `S` closed under the shift, up to 408 points, more than the smallest
tables' 256 rows. The
masked column openings hide for tables of several heights, each over its
own domain (`masks_hide_multi`, `pcsCloseN_multi` in
`Ski/ZK/MaskMulti.lean`), and every hiding circuit's transcript theorem
holds over that PCS with no PCS term (`*_transcriptG_masked`). Every
byte of a released hiding proof lies in a field of that view: `ski-air
proof-shape` (`release/verify.sh` step 15) refuses a proof whose bytes
are not its fields' own encoding, and proofs of one statement differ in
size only in the Merkle digests their query paths share.
The closure rule, the design's milestone 3 (`Ski/JetPublic.lean`): the
composed heap's private cells, the bit slots and the region, are pointed
into by public cells, so a jet table checked over the blank heap need not
hold over the filled one, and on `split8` and `csplit8` it does not. Lean
now computes a composed statement's table under the rule (roots and
globals only at cells whose closure is public, `jetTableC`), and the
verifier's check (`jetStmtC`: the recomputed table, `rootsOKB`, `publicB`)
licenses its roots over every filled heap (`jetStmtC_sound`, by
`termAt_public`). Under the rule `split8` ran in 11,598 CPU rows against
129,964 plain (8.9%), `csplit8` in 157,680 against 471,887 (33.4%), both
checked by `checkJA` from the filled heap (`lake exe skilark cjets`,
`cjets-statement`, `cjets-measure`). Most of `csplit8`'s cost was jets at
bare combinators: `seq`'s handler `λg t. g t` compiles to `I`, and each
of its 39,459 instantiations took six rows (three CPU, two POP, one
INSTW) where the machine took two. Templates that compile to `S`, `K` or `I` now make no jet
(`JetTable.isComb`, 2026-10-11): `split8` runs in 11,166 CPU rows
(8.6%) and `csplit8` in 118,221 (25.1%), proved at `2^17` and `2^18` in
16 s.
The circuit as data, milestone 4: `Ski/Circuit/CompJAir.lean`
(`compJAirs`) and `bench/plonky3/src/compj.rs`, ten tables and a blinding
tree of seven tuples, the same constraint for constraint
(`compare-compJ`). Proved under hiding: `split8` in 11,599 CPU rows
(11 s), `csplit8` at `2^18` and `2^19` against the plain `2^19` and
`2^20` (26 s against 42), and the three-segment `and` and `or`, whose
restarts fall between instantiations. Its soundness, milestone 5
(`Ski/ComposedJ.lean`, `Ski/Circuit/CompJ*.lean`): an accepted proof, for
the jet table Lean checked, has bits and a witness on which every term
evaluates to `K` (`compJExport_sound`). The jet circuit's instantiation
argument carries over whole (`CJOK.core : JetCore`), and a jetted run's
value `K` is exactly `K` (`chead_K`). The checker `checkCJ` accepts the
honest tables. Its completeness, milestone 6
(`Ski/Circuit/CompJComplete.lean`): a jetted run within `2^R` rows,
`2^Lm` cells and `2^Lp`, `2^Li` POP and INSTW rows gives honest tables
that `compJAirs` accepts at those heights, with the public program and
segment tables (`compJ_complete_log`). Every blinded table's flags are
clear, so it sends as its base, and the balance reuses the jet circuit's
bus by bus. Its zero knowledge, milestone 7 (`Ski/ZK/CompJ.lean`):
over a hiding PCS a simulator from the statement alone matches the real
transcript (`compJ_transcript`, `transcript_zkN` for the tree of eight
tables and seven tuples), and the honest tables meet its hypotheses
(`CRun.honest_zk`). The statement fixes POP's and INSTW's budgets with
the other heights (`log R M Lp Li`), so no height depends on the
witness. Avon writes the witness tables (milestone 8: `avon witness
--statement`), byte for byte ski-air's, and `ski-air compj-prove-table`
proves them under hiding. The release holds `split8` and `csplit8` with
jets and a Sudoku, all in zero knowledge (milestone 9, `release/verify.sh`).

Two assumptions, reduced to their algebra. **LogUp** (`Ski/ZK/LogUpSound.lean`):
tables whose buses do not balance pass Plonky3's check for at most
`P^4 · M (W + 2)` of the `P^8` challenge pairs (`logup_accept`), Plonky3's
own `N (W + 2) / |EF|` with `M ≤ N`, and
`compJ_logup_sound` instantiates it for `compJAirs`. The commitment's
binding and the STARK's soundness stay assumed. **The hiding PCS**
(`Ski/ZK/MaskOOD.lean`): the random rows `HidingFriPcs` interleaves make a
column's openings at `|S|` points of `F` and `|Z|` of the extension
independent of the trace when `|S| + 4|Z| ≤ n` (`masks_hide`), in the
public-coin interactive model with the points independent of the masks.
Applied with `S ∪ gS`, since the quotient's openings couple to the next
row. The quotient chunks, the codeword columns, FRI, Merkle salts and
Fiat–Shamir stay assumed. For a PCS whose view is exactly these openings,
`PCSCloseN` holds with `ε = 0` (`Ski/ZK/MaskPCS.lean`); for Plonky3's, it
stays a hypothesis. The prover's secret randomness is one 128-bit seed per
proof, expanded by ChaCha20 with a stream for each of the blinding
tuples, the leaf salts and the codewords (`bench/plonky3/src/seed.rs`);
`transcript_prg` carries the transcript theorems to it, assuming ChaCha20
fools the transcript's own tests for an efficient event, its event at
each pair of challenges (`PRGClose (TTests real)`, `Ski/ZK/PRG.lean`), so
the seeded guarantee is computational. Over every test the assumption
would fail for any generator with fewer seeds than draws: the test "is
some `G s`" tells the seeds from uniform draws.

Composed statements with `∃` and knowledge implication (`Ski/ComposeX.lean`).
`∃ y. F` holds `y` once in the hidden witness and pairs it into the inputs
of `F`'s atoms, so two atoms under one binder read the same hidden value.
Knowledge implication is a public witness map Lean certifies, applied to a
hidden realizer of its hypothesis: the statement proves `A`, the formula
concluded is `T A`, and zero knowledge covers `A`'s witness (`inl A B`
reveals that `A` holds). A hidden realizer of `A → B` is not checkable by
finitely many evaluations, as Part II says. Both
compile to the same evaluation statement, so the circuit is unchanged;
completeness, knowledge soundness and `composeX` are proved, and three
examples are proved in zero knowledge end to end.

Incremental composition without recursion (`Ski/Chain.lean`). A chain of
proofs, each stage its own statement and prover, later statements
computed from earlier ones and the values they publish; `chain2` makes a
proof system of the chain from the stages', complete, knowledge-sound and
zero knowledge (componentwise, the proofs' randomness independent), and
iterates to any length. With a distance (`Ski/ComposeDist.lean`): `PSD`
states zero knowledge as `CloseD` over explicit draws, `composeD` gives
zero knowledge within `err` and witness indistinguishability within
`2 · err`, and `chain2D` proves the hybrid argument, the chain within
`err₁/|D₁| + err₂/|D₂|`; the transcript theorems supply the field
(`closeD_of_transcriptG`, `comp_closeD` in `Ski/ZK/ComposeZK.lean`). Two composed statements over a public hand-off
prove the conjunction; a two-stage example is proved in zero knowledge, a
proof per stage.

Data jets (`Ski/DataJet.lean`, `Ski/ZK/Poseidon2.lean`). A data jet's
contract is a Lean function over encoded data, `J ⬝ encI x ⟶ encO (spec
x)`; a code jet's is an SKI term. Closing the jet head to any SKI term
that implements the contract turns each reduction with the jet into a
weak reduction (`JSteps.close`), so a verifier accepting under the jet
realizes its atom (`real_of_jet`). An implementation needs the
specification to be a function of the encoding (`Contract.Respects`);
the Poseidon2 contract takes states of sixteen canonical field elements,
injectively encoded (`poseidon2_respects`), and has a proved SKI
implementation (`Poseidon2SKI.poseidon2_implements`): binary arithmetic in
SKI (`Ski/BitArith.lean`) and the rounds as layers of arithmetic
expressions, each round of the specification equal to its expressions'
value (`Ski/ZK/Poseidon2SKI.lean`). The term has 12,370,891 nodes as a
tree. Avon's graph reduction runs it on Plonky3's three test vectors to
the proved normal form, Plonky3's output, in 962 to 981 million
contractions (about 10.4 s each; `lake exe p2run`). Without sharing,
which is how the circuit's write-once heap runs, it passes `8 × 10^9`;
the circuit's largest tables hold about 400,000. The specification of
Poseidon2 (BabyBear, width 16) is arithmetic modulo `p` with Plonky3's
constants, checked by the kernel against Plonky3's outputs on three
inputs (`permute_matches`). A hidden hand-off commits to the value with
Plonky3's compression, as specified and tested, on eight value and eight
random elements. From a verified proof of each stage over one
commitment, the extractors give one value satisfying both, or two
distinct inputs on which the compression agrees (`hidden_chain`), so
knowledge soundness reduces to collision resistance. The precompile's
table exists: one row per permutation; every row of a table that
satisfies its AIR computes `Poseidon2.permute` (`P2Air.p2_sound_row`);
its Rust export matches Lean's constraint for constraint; 4,096
permutations prove in 0.15 s. The jet takes a continuation, then the
inputs' 496 bits as Scott Booleans, and passes the continuation the
outputs' bits (`DataJet.CContract`, `CSteps.close`; `Poseidon2SKI.Pbits`
implements it, `Pbits_implements`). In the machine it is an atom `J`, and
one row pushes the output bits as stack cells into the heap's `K` and
`K I` slots (`P2Jet.p2Row`, read back as one jet step by
`p2Row_cstep`); composed statements may leave `J` free, and an accepted
table with jet rows proves the statement with `J` closed to `Pbits`
(`CompM.composedP_sound`). The circuit's jet rows exist and are proved
sound (`Circuit.compPExportG_sound`), complete
(`Circuit.compPG_complete_log`) and zero knowledge
(`Circuit.compP_transcript`). The hidden hand-off runs in the circuit:
two accepted `p2commit` proofs over one commitment, the first pattern
fixing value bits only and both keeping the value canonical, give one
value that meets both stages' patterns, or a collision read from the two
proofs' tables
(`Circuit.p2commit_chainB`, `ski-air compp-chain`). Open: the binding and
hiding assumptions, which are computational and stated in prose.

Fiat–Shamir, round by round (`Ski/ZK/FSRound.lean`, `ski-air fs-budget`).
Lean proves the counting step: `q` adaptive hash calls hit a round of bad
fraction `ε` with probability at most `q ε`, grinding `b` bits divides `ε`
by `2^b`, and the LogUp round's `ε` is `M (W + 2) / P^4` (`logup_fs`).
Round-by-round soundness and the other rounds' fractions are
`p3-security`'s, assumed. At Plonky3's benchmark FRI parameters the
released proofs were 57.5 to 66 bits proven and 91 to 100 conjectured,
bound by the low-degree test and the opening batch. Every configuration
now grinds 10 bits before the opening batch, 5 before the lookup and 3
before the out-of-domain point, which brings every round to 100
conjectured bits. 100 bits proven, a future option, takes 203 queries at
rate `1/2`, and so tables of at least `2^9` rows for the hiding PCS's
masking budget; 128 bits is out of reach with BabyBear's quartic extension
and an eight-element digest. The transcript absorbs a Poseidon2 digest of
every AIR's constants as the CPU instance's public values
(`bench/plonky3/src/stmt.rs`), so a proof binds its whole statement.

Step 1 (a commitment in SKIlark) is closed at this toy scope. Real
parameters do not fit SKI reduction: a full adder written natively in
SKIjack costs 450 to 640 host contractions a bit (measured on 8- to
128-bit sums), and the circuit's largest heights (`2^20` rows, about
400,000 contractions) afford some 800 of them, where a knapsack or SIS
commitment with sound parameters needs tens of thousands and a
lightweight-cipher hash about `10^4`. A commitment that binds needs the
hash computed outside the reduction: a precompile table (Poseidon2 over
BabyBear, Plonky3's own hash) with a Lean specification, the first data
jet, which Step 2 builds toward.

## 6. Acceptance

L0/L1: `lake build` elaborates the manifest, `gates.sh` passes, `lake exe
main` matches the reference on every corpus row — done. Language layer:
composition and the divergence biconditional over SKIlark's compiled form
with `apply`, every leaf in the manifest — done for every valid table
(§3), with four tables checked as data. Endgame: a proof of execution for one corpus program verified by
a third party, with its jet table and per-contraction cost reported —
done for `3 sumto` (`release/`). Avon's jetted witness is proved by
`ski-air`, 3,678 CPU rows where the plain run takes 25,074 (0.36 per
contraction, against 2.44), with 78 jets and 2,768 roots; without jets
at bare combinators, 3,304 rows (0.32) with 76 jets and 759 roots,
Avon's witness again. A reviewer that
had not seen the work cloned the repository, ran `release/verify.sh`, and
reproduced the proof byte for byte. Its attacks found that the
verifier's Lean check and its own reads could disagree, first through a
jet-file name that was a path and then through a FIFO, so that a forged
jet table verified a proof that Ω halts. They also found that trailing
proof bytes were ignored, and that a checked copy in a shared temporary
directory could be swapped. The verifier now reads each public file once
and pipes those bytes to Lean's statement check, which reads no file. Names are identifiers,
and a proof is one byte string. Each attack is kept as a standing forgery
in `release/verify.sh` that failed on the vulnerable builds (with the Ω
proof made for their CPU layout; it was remade when the CPU gained the
probe kinds). That proof
shows halting, with the value's head and arity. A second proof binds the
output: probe segments over jets show that `3 sumto` decodes to `[6]`
(`Decodes`, 434,238 bytes), refused for `[5]`, for the error outcome and
with one byte changed; Lean's `jets check-probe` accepts its table. Avon
runs its probe segments too (`avon witness --plan`), and its table is
byte-identical to `ski-air`'s own. The verifier's
constraints are proved to be `AcceptsJ` and `AcceptsP`
(`jetExport_sound`, `probeExport_sound`; `release/README.md`).
