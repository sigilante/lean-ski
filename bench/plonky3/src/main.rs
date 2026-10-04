//! The AIR of `Ski/Air.lean` in Plonky3, checked against Lean.
//!
//! Three tables under one batch STARK over BabyBear, joined by one LogUp bus,
//! `mem`, whose entries are `(address, tag, field a, field b)`:
//!
//! - **CPU**: one row per machine transition, padded to a public budget with
//!   halted rows.  A row holds the registers `hd`, `stk`, `ctr`, a one-hot
//!   selector for the rule kind, the fields of the cells it reads, and the
//!   bits that range-check each read address below `ctr`.  The kinds are the
//!   cases of `Air.stepG` and `Air.haltRow`: an unwind, `I`, `K`, `S`, the
//!   six ways a combinator can lack arguments, and an atom at the head
//!   (`src/jets.rs` adds an instantiation, and `src/probe.rs` two probe
//!   rows, each zero when its columns are absent).  A read's tag is fixed
//!   by the kind, so the lookups check the cells the kind needs.
//! - **Memory**: the committed memory table, one entry per address in order
//!   (`addr` starts at 0 and increases by 1), with the number of times each
//!   entry is looked up.  One value per address, as `rd` needs.
//! - **Program**: the loaded heap of the public term, as a preprocessed
//!   table the verifier rebuilds from the term.  Every loaded cell is looked
//!   up in memory, which pins the memory table's prefix (`heap0`).
//!
//! The check against Lean: for every table proved here, the same table is
//! written in the format of `Ski/AirCheck.lean`, and `lake exe aircheck`
//! decides the AIR's constraints on it (`Air.checkA_iff`).  Tampered tables
//! must fail both: the verifier must reject a proof of each.
//!
//! `src/sudoku.rs` adds a fourth table, the private inputs, and proves a
//! Sudoku solution in zero knowledge; its header gives the argument.
//!
//! **Why the constraints are `Accepts`.**  Read a table off an accepted
//! proof: the rows are the CPU's registers, and `M[a]` is the memory entry at
//! address `a` (one per address), decoded by its tag: 0..6 to `S`, `K`, `I`,
//! `A a b`, `N`, `C a b`, `X a` (the atom `a`), ignoring the fields of `S`,
//! `K`, `I`, `N` and the second field of `X`, and any other tag to `N`.
//! Such entries and fields are never used: every read's tag lies in 0..6,
//! and a nullary cell's fields feed only expressions its kind gates to
//! zero.  A lookup that balances names an entry, so a read of
//! `(a, tag, x, y)` means `M[a]` has that tag and those fields.
//! - The verifier accepts only CPU and memory heights up to `2^MAX_LOG_HEIGHT`.
//!   Then addresses stay below `2^21` and counters below `2^23` (a counter
//!   grows by at most 3 a row), so `ctr - a - 1` has a 24-bit decomposition
//!   only when `a < ctr`: otherwise it wraps to at least `p - 2^21`.  So each
//!   read is `rd M ctr a`.  (Even at Plonky3's own cap of `2^27` rows the
//!   wrap would be at least `p - 2^27 > 2^24`.)
//! - An unwind reads an application `(f, x)` at `hd` and writes `C x stk` at
//!   `ctr`; the next registers are `f, ctr, ctr + 1`.  That is `stepG`'s
//!   application case with its write checked (`wrs`).
//! - `I`, `K`, `S` read the head combinator and one, two, three stack cells
//!   `C x s1`, `C y s2`, `C z s3`; `S` writes `A y z`, `C ctr s3`,
//!   `C z (ctr + 1)`.  The next registers are `stepG`'s.
//! - The six halting kinds read the head combinator and the stack down to an
//!   empty stack before the rule's arity: `haltRow`'s `short`.  The seventh
//!   reads an atom at the head, which `haltRow` accepts outright.  A halted
//!   row's next row repeats it.
//! - The first row is the loaded term.  Each program lookup names an existing
//!   address, so the memory table has at least `ctr0` entries, and its
//!   prefix is the loaded heap: `M.take ctr0 = (load t).heap`.  The last row
//!   has halted, and, when the AIR names an accepting marker, reads it at
//!   the head: an atom read's first field is the atom.
//! So an accepted table satisfies `Air.Accepts`, which `lake exe aircheck`
//! decides for every table this program proves.
//!
//! Usage: `ski-air CORPUS OUTDIR` where CORPUS is `bench/Dump.lean`'s output.

use std::fmt::Debug;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Instant;

use p3_air::{Air, AirBuilder, BaseAir, PermutationAirBuilder, WindowAccess};
use p3_baby_bear::{default_babybear_poseidon2_16, BabyBear, Poseidon2BabyBear};
use p3_batch_stark::{prove_batch, verify_batch, ProverData, StarkInstance};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;

mod jets;
mod composed;
mod compj;
mod export;
mod probe;
mod fsbudget;
mod seed;
mod stmt;
mod sudoku;
mod witness;
mod p2air;
mod compp;

// ---------------------------------------------------------------------------
// The STARK configuration
// ---------------------------------------------------------------------------

type Val = BabyBear;
type Challenge = BinomialExtensionField<Val, 4>;
type Perm = Poseidon2BabyBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type Dft = Radix2DitParallel<Val>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
type Config = StarkConfig<Pcs, Challenge, Challenger>;

/// Plonky3's benchmark FRI parameters (blowup 2, 100 queries, 16 bits of
/// query grinding), with the batch, lookup and out-of-domain grinding of
/// `GRIND_*`.
/// Grinding before the opening batch, the lookup challenges and the
/// out-of-domain point: with the benchmark FRI parameters, every released
/// proof reaches 100 conjectured bits in each round, with a bit to spare
/// (`ski-air fs-budget`).  Proven 100 bits needs more queries
/// (`bench/plonky3/README.md`, "Fiat–Shamir, round by round").
pub(crate) const GRIND_BATCH: usize = 10;
pub(crate) const GRIND_LOOKUP: usize = 5;
pub(crate) const GRIND_OOD: usize = 3;

/// The FRI parameters of every configuration, hiding or not; the
/// per-round budget (`fsbudget`) reads them from here.
pub(crate) fn fri_params<M>(mmcs: M) -> FriParameters<M> {
    FriParameters { batch_proof_of_work_bits: GRIND_BATCH, ..FriParameters::new_benchmark(mmcs) }
}

fn make_config() -> Config {
    let perm = default_babybear_poseidon2_16();
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = fri_params(challenge_mmcs);
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri);
    Config::new(pcs, Challenger::new(perm))
        .with_lookup_proof_of_work_bits(GRIND_LOOKUP)
        .with_ood_proof_of_work_bits(GRIND_OOD)
}

// ---------------------------------------------------------------------------
// Terms, the heap and the machine: `Ski/Heap.lean`, `Air.stepG`
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Cell {
    S,
    K,
    I,
    App(u32, u32),
    Nil,
    Cons(u32, u32),
    /// A marker: `Mach.Cell.atom`.
    Atom(u32),
}

impl Cell {
    /// The tag on the `mem` bus.
    fn tag(self) -> u32 {
        match self {
            Cell::S => 0,
            Cell::K => 1,
            Cell::I => 2,
            Cell::App(..) => 3,
            Cell::Nil => 4,
            Cell::Cons(..) => 5,
            Cell::Atom(_) => 6,
        }
    }
    fn fields(self) -> (u32, u32) {
        match self {
            Cell::App(f, x) => (f, x),
            Cell::Cons(x, r) => (x, r),
            Cell::Atom(n) => (n, 0),
            _ => (0, 0),
        }
    }
    /// The cell in `Ski/AirCheck.lean`'s format.
    fn lean(self) -> String {
        match self {
            Cell::S => "S".into(),
            Cell::K => "K".into(),
            Cell::I => "I".into(),
            Cell::App(f, x) => format!("A {f} {x}"),
            Cell::Nil => "N".into(),
            Cell::Cons(x, r) => format!("C {x} {r}"),
            Cell::Atom(n) => format!("X {n}"),
        }
    }
}

enum Term {
    S,
    K,
    I,
    App(Box<Term>, Box<Term>),
}

/// A term in prefix form, `` ` `` for application.
fn parse(s: &[u8], pos: &mut usize) -> Term {
    let c = s[*pos];
    *pos += 1;
    match c {
        b'S' => Term::S,
        b'K' => Term::K,
        b'I' => Term::I,
        b'`' => {
            let f = parse(s, pos);
            let a = parse(s, pos);
            Term::App(Box::new(f), Box::new(a))
        }
        _ => panic!("bad term byte {c}"),
    }
}

/// `Mach.build`: children first, the function before the argument.
fn build(heap: &mut Vec<Cell>, t: &Term) -> u32 {
    let cell = match t {
        Term::S => Cell::S,
        Term::K => Cell::K,
        Term::I => Cell::I,
        Term::App(f, a) => {
            let pf = build(heap, f);
            let pa = build(heap, a);
            Cell::App(pf, pa)
        }
    };
    heap.push(cell);
    (heap.len() - 1) as u32
}

/// `Mach.load`: the term's heap, then the empty stack.
fn load(t: &Term) -> (Vec<Cell>, u32, u32) {
    let mut heap = Vec::new();
    let hd = build(&mut heap, t);
    let stk = heap.len() as u32;
    heap.push(Cell::Nil);
    (heap, hd, stk)
}

/// `Air.stepG` over the machine's own heap, counter the heap's length.
fn step(heap: &[Cell], hd: u32, stk: u32) -> Option<(u32, u32, Vec<Cell>)> {
    let c = heap.len() as u32;
    let g = |a: u32| heap.get(a as usize).copied();
    match g(hd)? {
        Cell::App(f, x) => Some((f, c, vec![Cell::Cons(x, stk)])),
        Cell::I => match g(stk)? {
            Cell::Cons(x, s) => Some((x, s, vec![])),
            _ => None,
        },
        Cell::K => match g(stk)? {
            Cell::Cons(x, s1) => match g(s1)? {
                Cell::Cons(_, s2) => Some((x, s2, vec![])),
                _ => None,
            },
            _ => None,
        },
        Cell::S => match g(stk)? {
            Cell::Cons(x, s1) => match g(s1)? {
                Cell::Cons(y, s2) => match g(s2)? {
                    Cell::Cons(z, s3) => Some((
                        x,
                        c + 2,
                        vec![Cell::App(y, z), Cell::Cons(c, s3), Cell::Cons(z, c + 1)],
                    )),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// A run to a halt: the registers of every state, the final heap, the
/// loaded heap's size and the contractions.
struct Run {
    rows: Vec<[u32; 3]>,
    heap: Vec<Cell>,
    loaded: Vec<Cell>,
    contractions: u64,
}

fn run(t: &Term) -> Run {
    let (mut heap, mut hd, mut stk) = load(t);
    let loaded = heap.clone();
    let mut rows = Vec::new();
    let mut contractions = 0;
    loop {
        rows.push([hd, stk, heap.len() as u32]);
        match step(&heap, hd, stk) {
            None => break,
            Some((h, s, ws)) => {
                if !matches!(heap[hd as usize], Cell::App(..)) {
                    contractions += 1;
                }
                heap.extend(ws);
                hd = h;
                stk = s;
            }
        }
    }
    Run { rows, heap, loaded, contractions }
}

// ---------------------------------------------------------------------------
// Row kinds: the cases of `Air.stepG` and `Air.haltRow`
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    App,
    I,
    K,
    S,
    /// `I` with an empty stack.
    HI1,
    /// `K` with no argument, with one.
    HK1,
    HK2,
    /// `S` with no argument, one, two.
    HS1,
    HS2,
    HS3,
    /// An atom at the head: a marker, which no rule applies to.
    HA,
    /// An instantiation at a jet's root (`src/jets.rs`).
    Inst,
    /// A probe row (`src/probe.rs`): the first, which starts the first
    /// segment, and a later one, which also ends the segment before.
    PFirst,
    PLater,
}

const NKINDS: usize = 14;

const KINDS: [Kind; NKINDS] = [
    Kind::App,
    Kind::I,
    Kind::K,
    Kind::S,
    Kind::HI1,
    Kind::HK1,
    Kind::HK2,
    Kind::HS1,
    Kind::HS2,
    Kind::HS3,
    Kind::HA,
    Kind::Inst,
    Kind::PFirst,
    Kind::PLater,
];

/// A state's kind and the cells it reads (`R0` at `hd`, `R1` at `stk`, `R2`
/// at `R1`'s rest, `R3` at `R2`'s rest), as `(address, cell)`.
fn classify(m: &[Cell], hd: u32, stk: u32) -> (Kind, [Option<(u32, Cell)>; 4]) {
    let at = |a: u32| m[a as usize];
    let r0 = Some((hd, at(hd)));
    match at(hd) {
        Cell::App(..) => (Kind::App, [r0, None, None, None]),
        Cell::I => {
            let c1 = at(stk);
            let r1 = Some((stk, c1));
            match c1 {
                Cell::Cons(..) => (Kind::I, [r0, r1, None, None]),
                Cell::Nil => (Kind::HI1, [r0, r1, None, None]),
                _ => panic!("not a machine state"),
            }
        }
        Cell::K => {
            let c1 = at(stk);
            let r1 = Some((stk, c1));
            match c1 {
                Cell::Nil => (Kind::HK1, [r0, r1, None, None]),
                Cell::Cons(_, s1) => {
                    let c2 = at(s1);
                    let r2 = Some((s1, c2));
                    match c2 {
                        Cell::Cons(..) => (Kind::K, [r0, r1, r2, None]),
                        Cell::Nil => (Kind::HK2, [r0, r1, r2, None]),
                        _ => panic!("not a machine state"),
                    }
                }
                _ => panic!("not a machine state"),
            }
        }
        Cell::S => {
            let c1 = at(stk);
            let r1 = Some((stk, c1));
            match c1 {
                Cell::Nil => (Kind::HS1, [r0, r1, None, None]),
                Cell::Cons(_, s1) => {
                    let c2 = at(s1);
                    let r2 = Some((s1, c2));
                    match c2 {
                        Cell::Nil => (Kind::HS2, [r0, r1, r2, None]),
                        Cell::Cons(_, s2) => {
                            let c3 = at(s2);
                            let r3 = Some((s2, c3));
                            match c3 {
                                Cell::Cons(..) => (Kind::S, [r0, r1, r2, r3]),
                                Cell::Nil => (Kind::HS3, [r0, r1, r2, r3]),
                                _ => panic!("not a machine state"),
                            }
                        }
                        _ => panic!("not a machine state"),
                    }
                }
                _ => panic!("not a machine state"),
            }
        }
        Cell::Atom(_) => (Kind::HA, [r0, None, None, None]),
        _ => panic!("not a machine state"),
    }
}

// ---------------------------------------------------------------------------
// The AIRs
// ---------------------------------------------------------------------------

/// Bits of each range check: a read address `a` satisfies `a < ctr` when
/// `ctr - a - 1` has `RANGE_BITS` bits.  Sound while every address and
/// counter stays below `2^RANGE_BITS`, far below BabyBear's modulus
/// `15 · 2^27 + 1`; `MAX_LOG_HEIGHT` keeps them there.
const RANGE_BITS: usize = 24;
const MAX_LOG_HEIGHT: usize = 21;

const HD: usize = 0;
const STK: usize = 1;
const CTR: usize = 2;
const SEL: usize = 3;
const FLD: usize = SEL + NKINDS;
const BITS: usize = FLD + 8;
const CPU_WIDTH: usize = BITS + 4 * RANGE_BITS;

/// A blinding message: a random tuple of `BLIND_LEN` field elements and a
/// flag, on a bus of its own.  See `src/sudoku.rs`.
const BLIND_LEN: usize = 4;
const BLIND_WIDTH: usize = BLIND_LEN + 1;
/// The CPU's blinding columns, when it has them: it receives on `BLIND_A`
/// and sends on `BLIND_B`.
const CPU_BLA: usize = CPU_WIDTH;
const CPU_BLB: usize = CPU_WIDTH + BLIND_WIDTH;
const BLIND_A: &str = "blind_a";
const BLIND_B: &str = "blind_b";

/// The composed circuit with jets (`src/compj.rs`) sends a third blinding
/// message, to POP.
const BLIND_C: &str = "blind_c";

/// The CPU's jet columns, when it has them (right after the corpus CPU's;
/// the blinding columns follow them, `CpuAir::bl_base`): the row
/// counter, then an instantiation's jet, arity, cell count, root operand
/// (one-hot local, argument, global, and its value), the root's argument
/// pointer, and the rest of the stack.
const J_CLK: usize = CPU_WIDTH;
const J_G: usize = CPU_WIDTH + 1;
const J_K: usize = CPU_WIDTH + 2;
const J_N: usize = CPU_WIDTH + 3;
const J_RL: usize = CPU_WIDTH + 4;
const J_RA: usize = CPU_WIDTH + 5;
const J_RG: usize = CPU_WIDTH + 6;
const J_RV: usize = CPU_WIDTH + 7;
const J_XROOT: usize = CPU_WIDTH + 8;
const J_REST: usize = CPU_WIDTH + 9;
const JET_WIDTH: usize = 10;

const BUS: &str = "mem";

#[derive(Clone, Debug)]
struct CpuAir {
    hd0: u32,
    stk0: u32,
    ctr0: u32,
    /// The accepting marker, when the last row must read it at the head.
    accept: Option<u32>,
    /// Whether the last row must have `K` at the head and an empty stack:
    /// the run evaluates to `K` (`src/witness.rs`).
    accept_k: bool,
    /// Whether the table carries blinding columns.
    blind: bool,
    /// Whether the table carries jet columns and may instantiate.
    jets: bool,
    /// The public probe plan, when the table carries probe columns (after
    /// the jet columns; only with jets) and runs probe segments.
    probe: Option<probe::ProbePub>,
    /// The public segments, when the table runs several evaluations
    /// (`src/composed.rs`): its restart columns come last.
    restart: Option<composed::RestartPub>,
    /// The Poseidon2 jet's atom and the comb's root, when the table carries
    /// the jet's row (`src/compp.rs`): its columns follow the restart
    /// columns.
    p2: Option<compp::P2Pub>,
}

#[derive(Clone, Debug)]
struct MemAir {
    /// Whether the table carries blinding columns: it receives on `BLIND_B`.
    blind: bool,
}

/// The loaded heap: rows `(addr, tag, a, b, active)`.
#[derive(Clone, Debug)]
struct ProgAir {
    pre: Vec<[u32; 5]>,
}

/// The private inputs: a preprocessed `(addr, active)` per row, and one
/// committed column, the input's bit.
#[derive(Clone, Debug)]
struct WitAir {
    pre: Vec<[u32; 2]>,
}

#[derive(Clone, Debug)]
enum SkiAir {
    Cpu(CpuAir),
    Mem(MemAir),
    Prog(ProgAir),
    Wit(WitAir),
    Jet(jets::JetAir),
    Probe(probe::ProbeAir),
    WitT(witness::WitTAir),
    Segs(composed::SegsAir),
    /// The Poseidon2 table (`src/p2air.rs`).
    /// The Poseidon2 table, with its blinding block when blinded.
    P2(bool),
    /// The Poseidon2 jet's input bits, output bits and level index
    /// (`src/compp.rs`).
    P2In,
    P2Out,
    P2Idx(Vec<[u32; 6]>),
}

impl CpuAir {
    /// The number of blinding messages: `blind_a` and `blind_b`, and
    /// `blind_c` with jets (`src/compj.rs`).
    fn nblind(&self) -> usize {
        match (self.blind, self.jets) {
            (false, _) => 0,
            (true, false) => 2,
            (true, true) => 3,
        }
    }

    /// The first blinding column: after the jet and probe columns.
    fn bl_base(&self) -> usize {
        CPU_WIDTH
            + if self.jets { JET_WIDTH } else { 0 }
            + if self.probe.is_some() { probe::PROBE_WIDTH } else { 0 }
    }

    /// The first restart column: after the blinding columns.
    fn rbase(&self) -> usize {
        self.bl_base() + self.nblind() * BLIND_WIDTH
    }

    /// The jet's columns, `P2SEL` and its blinding block on `blind_c`: after
    /// the restart columns.
    fn p2base(&self) -> usize {
        self.rbase() + if self.restart.is_some() { composed::RESTART_WIDTH } else { 0 }
    }
}

impl<F: Field> BaseAir<F> for SkiAir {
    fn width(&self) -> usize {
        match self {
            SkiAir::Cpu(c) => c.p2base() + if c.p2.is_some() { compp::P2_CPU_WIDTH } else { 0 },
            SkiAir::Mem(m) => 5 + if m.blind { BLIND_WIDTH } else { 0 },
            SkiAir::Prog(_) => 1,
            SkiAir::Wit(_) => 1 + BLIND_WIDTH,
            SkiAir::Jet(j) => j.width(),
            SkiAir::Probe(p) => p.width(),
            SkiAir::WitT(_) => witness::WT_W,
            SkiAir::Segs(_) => 1,
            SkiAir::P2(blind) => p2air::P2_WIDTH + if *blind { BLIND_WIDTH } else { 0 },
            SkiAir::P2In => compp::PI_W + 2 * BLIND_WIDTH,
            SkiAir::P2Out => compp::PO_W + 2 * BLIND_WIDTH,
            SkiAir::P2Idx(_) => 1,
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            SkiAir::Prog(p) => Some(RowMajorMatrix::new(
                p.pre
                    .iter()
                    .flat_map(|r| r.iter().map(|&v| F::from_u32(v)))
                    .collect(),
                5,
            )),
            SkiAir::Wit(w) => Some(RowMajorMatrix::new(
                w.pre
                    .iter()
                    .flat_map(|r| r.iter().map(|&v| F::from_u32(v)))
                    .collect(),
                2,
            )),
            SkiAir::Jet(j) => j.preprocessed(),
            SkiAir::Probe(p) => p.preprocessed(),
            SkiAir::WitT(w) => Some(RowMajorMatrix::new(
                w.pre.iter().flat_map(|r| r.iter().map(|&v| F::from_u32(v))).collect(),
                3,
            )),
            SkiAir::Segs(sg) => Some(RowMajorMatrix::new(
                sg.pre.iter().flat_map(|r| r.iter().map(|&v| F::from_u32(v))).collect(),
                2,
            )),
            SkiAir::P2Idx(pre) => Some(RowMajorMatrix::new(
                pre.iter().flat_map(|r| r.iter().map(|&v| F::from_u32(v))).collect(),
                6,
            )),
            _ => None,
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            SkiAir::Cpu(_) => stmt::STMT_LEN,
            _ => 0,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            SkiAir::Prog(_) => 5,
            SkiAir::Wit(_) => 2,
            SkiAir::Jet(j) => j.preprocessed_width(),
            SkiAir::Probe(p) => p.preprocessed_width(),
            SkiAir::WitT(_) => 3,
            SkiAir::Segs(_) => 2,
            SkiAir::P2Idx(_) => 6,
            _ => 0,
        }
    }
}

impl<AB: PermutationAirBuilder + InteractionBuilder> Air<AB> for SkiAir
where
    AB::Var: Debug,
{
    fn eval(&self, b: &mut AB) {
        match self {
            SkiAir::Cpu(a) => a.eval(b),
            SkiAir::Mem(m) => eval_mem(b, m.blind),
            SkiAir::Prog(_) => eval_prog(b),
            SkiAir::Wit(_) => eval_wit(b),
            SkiAir::Jet(j) => j.eval(b),
            SkiAir::Probe(p) => p.eval(b),
            SkiAir::WitT(_) => witness::eval_witt(b),
            SkiAir::Segs(_) => composed::eval_segs(b),
            SkiAir::P2(blind) => {
                p2air::eval_p2(b);
                if *blind {
                    compp::eval_blocks(b, p2air::P2_WIDTH, &compp::P2_BLOCKS);
                }
            }
            SkiAir::P2In => {
                compp::eval_p2in(b);
                compp::eval_blocks(b, compp::PI_W, &compp::PI_BLOCKS);
            }
            SkiAir::P2Out => {
                compp::eval_p2out(b);
                compp::eval_blocks(b, compp::PO_W, &compp::PO_BLOCKS);
            }
            SkiAir::P2Idx(_) => compp::eval_p2idx(b),
        }
    }
}

fn sum<AB: AirBuilder>(xs: &[AB::Expr]) -> AB::Expr {
    xs.iter().cloned().fold(AB::Expr::ZERO, |acc, x| acc + x)
}

impl CpuAir {
    fn eval<AB: PermutationAirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        let main = b.main();
        let loc: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
        let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&v| v.into()).collect();
        let one = AB::Expr::ONE;
        let c = |n: u32| AB::Expr::from_u32(n);

        let hd = loc[HD].clone();
        let stk = loc[STK].clone();
        let ctr = loc[CTR].clone();
        let s = |i: usize| loc[SEL + i].clone();
        let (app, ki, kk, ks) = (s(0), s(1), s(2), s(3));
        let (hi1, hk1, hk2, hs1, hs2, hs3) = (s(4), s(5), s(6), s(7), s(8), s(9));
        let ha = s(10);
        let inst = s(11);
        let (p_first, p_later) = (s(12), s(13));
        // A restart row (`src/composed.rs`), when the table has segments: its
        // selector is the first restart column, outside the kinds, so tables
        // without segments keep their layout.
        let rbase = self.rbase();
        let rs = if self.restart.is_some() { loc[rbase].clone() } else { AB::Expr::ZERO };
        let probe = p_first.clone() + p_later.clone();
        let f = |i: usize| loc[FLD + i].clone();
        let (a0, b0, a1, b1, a2, b2, a3, b3) = (f(0), f(1), f(2), f(3), f(4), f(5), f(6), f(7));

        // Exactly one kind per row.
        for i in 0..NKINDS {
            b.assert_bool(s(i));
        }
        let mut sels: Vec<AB::Expr> = (0..NKINDS).map(s).collect();
        if self.restart.is_some() {
            b.assert_bool(rs.clone());
            sels.push(rs.clone());
        }
        // The Poseidon2 jet's row (`src/compp.rs`): a selector outside the
        // kinds, as the restart's.
        let p2sel = if self.p2.is_some() { loc[self.p2base()].clone() } else { AB::Expr::ZERO };
        if self.p2.is_some() {
            b.assert_bool(p2sel.clone());
            sels.push(p2sel.clone());
        }
        b.assert_eq(sum::<AB>(&sels), one.clone());

        let halt = sum::<AB>(&[
            hi1.clone(),
            hk1.clone(),
            hk2.clone(),
            hs1.clone(),
            hs2.clone(),
            hs3.clone(),
            ha.clone(),
        ]);

        // The reads each kind makes, and the tags the kind requires of them.
        // A first probe row reads nothing; a later one reads the atom at the
        // head (the end of the segment before), and no stack cell here.
        let acts = [
            one.clone() - inst.clone() - p_first.clone(),
            one.clone() - app.clone() - ha.clone() - inst.clone() - probe.clone(),
            sum::<AB>(&[kk.clone(), ks.clone(), hk2.clone(), hs2.clone(), hs3.clone(), p2sel.clone()]),
            ks.clone() + hs3.clone(),
        ];
        let tags = [
            (kk.clone() + hk1.clone() + hk2.clone()) * c(1)
                + (ki.clone() + hi1.clone()) * c(2)
                + app.clone() * c(3)
                + (ha.clone() + p_later.clone()) * c(6)
                + rs.clone() * c(1)
                + p2sel.clone() * c(6),
            sum::<AB>(&[ki.clone(), kk.clone(), ks.clone(), hk2.clone(), hs2.clone(), hs3.clone()]) * c(5)
                + sum::<AB>(&[hi1.clone(), hk1.clone(), hs1.clone(), rs.clone()]) * c(4)
                + p2sel.clone() * c(5),
            sum::<AB>(&[kk.clone(), ks.clone(), hs3.clone()]) * c(5)
                + (hk2.clone() + hs2.clone()) * c(4)
                + p2sel.clone() * c(5),
            ks.clone() * c(5) + hs3.clone() * c(4),
        ];
        let addrs = [hd.clone(), stk.clone(), b1.clone(), b2.clone()];
        let fields = [(a0.clone(), b0.clone()), (a1.clone(), b1.clone()), (a2.clone(), b2.clone()), (a3.clone(), b3.clone())];

        for j in 0..4 {
            // Each active read's address lies below the counter.
            let mut val = AB::Expr::ZERO;
            for i in 0..RANGE_BITS {
                let bit = loc[BITS + j * RANGE_BITS + i].clone();
                b.assert_bool(bit.clone());
                val = val + bit * c(1 << i);
            }
            b.assert_zero(acts[j].clone() * (ctr.clone() - addrs[j].clone() - one.clone() - val));
            // The read itself.
            b.push_interaction(
                BUS,
                [addrs[j].clone(), tags[j].clone(), fields[j].0.clone(), fields[j].1.clone()],
                Count::bounded(acts[j].clone(), 1),
            );
        }

        // The writes, at the counter: the unwind's stack cell, `S`'s three cells.
        b.push_interaction(
            BUS,
            [ctr.clone(), c(5), b0.clone(), stk.clone()],
            Count::bounded(app.clone(), 1),
        );
        b.push_interaction(
            BUS,
            [ctr.clone(), c(3), a2.clone(), a3.clone()],
            Count::bounded(ks.clone(), 1),
        );
        b.push_interaction(
            BUS,
            [ctr.clone() + one.clone(), c(5), ctr.clone(), b3.clone()],
            Count::bounded(ks.clone(), 1),
        );
        b.push_interaction(
            BUS,
            [ctr.clone() + c(2), c(5), a3.clone(), ctr.clone() + one.clone()],
            Count::bounded(ks.clone(), 1),
        );

        // The next registers.
        let mut next_hd = app.clone() * a0.clone()
            + (ki.clone() + kk.clone() + ks.clone()) * a1.clone()
            + halt.clone() * hd.clone();
        let mut next_stk = app.clone() * ctr.clone()
            + ki.clone() * b1.clone()
            + kk.clone() * b2.clone()
            + ks.clone() * (ctr.clone() + c(2))
            + halt.clone() * stk.clone();
        let mut next_ctr = ctr.clone() + app.clone() + ks.clone() * c(3);
        if self.jets {
            let (next_hd_i, next_stk_i, next_ctr_i) = jets::eval_cpu_inst(b, &loc, &nxt, inst.clone());
            next_hd = next_hd + next_hd_i;
            next_stk = next_stk + next_stk_i;
            next_ctr = next_ctr + next_ctr_i;
        } else {
            b.assert_zero(inst.clone());
        }
        match &self.probe {
            Some(pp) => {
                assert!(self.jets, "probe segments run with jets");
                let (h, s, c) = probe::eval_cpu_probe(b, &loc, &nxt, p_first.clone(), p_later.clone(), ha.clone(), pp);
                next_hd = next_hd + h;
                next_stk = next_stk + s;
                next_ctr = next_ctr + c;
            }
            None => {
                b.assert_zero(p_first.clone());
                b.assert_zero(p_later.clone());
            }
        }
        if let Some(rp) = &self.restart {
            assert!(self.probe.is_none(), "segments run without probes");
            let (h, st) = composed::eval_cpu_restart(b, &loc, &nxt, rs.clone(), rbase, rp);
            next_hd = next_hd + h;
            next_stk = next_stk + st;
        }
        if let Some(pp) = &self.p2 {
            let (h, st, cn) = compp::eval_cpu_p2(b, &loc, p2sel.clone(), self.p2base(), pp);
            next_hd = next_hd + h;
            next_stk = next_stk + st;
            next_ctr = next_ctr + cn;
        }
        {
            let mut t = b.when_transition();
            t.assert_eq(nxt[HD].clone(), next_hd);
            t.assert_eq(nxt[STK].clone(), next_stk);
            t.assert_eq(nxt[CTR].clone(), next_ctr);
        }

        // The first row is the loaded term; the last has halted.
        {
            let mut t = b.when_first_row();
            t.assert_eq(hd, c(self.hd0));
            t.assert_eq(stk, c(self.stk0));
            t.assert_eq(ctr, c(self.ctr0));
        }
        b.when_last_row().assert_eq(halt, one.clone());
        if self.blind {
            let bl = self.bl_base();
            blind_msg(b, &loc, bl, BLIND_A, false);
            blind_msg(b, &loc, bl + BLIND_WIDTH, BLIND_B, true);
            if self.jets {
                blind_msg(b, &loc, bl + 2 * BLIND_WIDTH, BLIND_C, true);
            }
        }
        // The output: the last row is `K` with no argument, the halting kind
        // `HK1`, which reads `K` at the head and a nil at the stack.
        if self.accept_k {
            b.when_last_row().assert_one(hk1.clone());
        }
        // The output: the last row reads the accepting marker at the head.
        if let Some(acc) = self.accept {
            let mut t = b.when_last_row();
            t.assert_eq(ha, one);
            t.assert_eq(a0, c(acc));
        }
    }
}

/// A blinding message at column `col`: the tuple, then a Boolean flag, sent
/// with count `sign · flag` on `bus`.
fn blind_msg<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB, loc: &[AB::Expr], col: usize, bus: &str, send: bool) {
    let flag = loc[col + BLIND_LEN].clone();
    b.assert_bool(flag.clone());
    let count = Count::bounded(flag, 1);
    b.push_interaction(bus, loc[col..col + BLIND_LEN].to_vec(), if send { count } else { -count });
}

fn eval_mem<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB, blind: bool) {
    let main = b.main();
    let loc: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let nxt: Vec<AB::Expr> = main.next_slice().iter().map(|&v| v.into()).collect();
    // One entry per address, in order.
    b.when_first_row().assert_zero(loc[0].clone());
    b.when_transition().assert_eq(nxt[0].clone(), loc[0].clone() + AB::Expr::ONE);
    b.push_interaction(
        BUS,
        [loc[0].clone(), loc[1].clone(), loc[2].clone(), loc[3].clone()],
        Count::provided(-loc[4].clone()),
    );
    if blind {
        blind_msg(b, &loc, 5, BLIND_B, false);
    }
}

fn eval_prog<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
    let main = b.main();
    let dummy: AB::Expr = main.current_slice()[0].into();
    b.assert_zero(dummy);
    b.push_interaction(
        BUS,
        [pre[0].clone(), pre[1].clone(), pre[2].clone(), pre[3].clone()],
        Count::bounded(pre[4].clone(), 1),
    );
}

/// Each active row is the input cell at `addr`: `K` when its bit is 1 and
/// `A 0 1` (`K I`, the slot cells at 0 and 1) when it is 0.  So an input
/// cell is a Scott Boolean, and nothing else.
fn eval_wit<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
    let main = b.main();
    let loc: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let bit = loc[0].clone();
    blind_msg(b, &loc, 1, BLIND_A, true);
    b.assert_bool(bit.clone());
    let one = AB::Expr::ONE;
    b.push_interaction(
        BUS,
        [
            pre[0].clone(),
            AB::Expr::from_u32(3) - bit.clone() * AB::Expr::from_u32(2),
            AB::Expr::ZERO,
            one - bit,
        ],
        Count::bounded(pre[1].clone(), 1),
    );
}

// ---------------------------------------------------------------------------
// The table: rows, memory, program; its traces; its Lean form
// ---------------------------------------------------------------------------

struct Table {
    /// The loaded heap (public).
    loaded: Vec<Cell>,
    hd0: u32,
    stk0: u32,
    /// Registers of every row, padded to the budget with the halted state.
    rows: Vec<[u32; 3]>,
    /// The memory table, padded with empty stacks.
    mem: Vec<Cell>,
}

fn pow2_at_least(n: usize, min_log: usize) -> usize {
    n.next_power_of_two().max(1 << min_log)
}

/// The table at the least power-of-two budgets for this run.
fn table_of(t: &Term, min_log: usize) -> (Table, Run) {
    let r = run(t);
    let k = pow2_at_least(r.rows.len(), min_log);
    let mut rows = r.rows.clone();
    let last = *rows.last().unwrap();
    rows.resize(k, last);
    let msize = pow2_at_least(r.heap.len().max(r.loaded.len()), min_log);
    let mut mem = r.heap.clone();
    mem.resize(msize, Cell::Nil);
    let (_, hd0, stk0) = load(t);
    (
        Table { loaded: r.loaded.clone(), hd0, stk0, rows, mem },
        r,
    )
}

fn f(n: u32) -> Val {
    Val::from_u32(n)
}

/// The CPU trace of the rows over the memory table, counting each read and
/// write into `mult`.
fn cpu_trace(rows: &[[u32; 3]], memory: &[Cell], mult: &mut [u32]) -> RowMajorMatrix<Val> {
    let mut cpu = Vec::with_capacity(rows.len() * CPU_WIDTH);
    for &[hd, stk, ctr] in rows {
        let (kind, reads) = classify(memory, hd, stk);
        let mut row = vec![Val::ZERO; CPU_WIDTH];
        row[HD] = f(hd);
        row[STK] = f(stk);
        row[CTR] = f(ctr);
        let ki = KINDS.iter().position(|&k| k == kind).unwrap();
        row[SEL + ki] = Val::ONE;
        for (j, rd) in reads.iter().enumerate() {
            if let Some((addr, cell)) = rd {
                assert!(*addr < ctr, "a read at or above the counter");
                let (a, b) = cell.fields();
                row[FLD + 2 * j] = f(a);
                row[FLD + 2 * j + 1] = f(b);
                let d = ctr - addr - 1;
                assert!(d < (1 << RANGE_BITS));
                for i in 0..RANGE_BITS {
                    row[BITS + j * RANGE_BITS + i] = f((d >> i) & 1);
                }
                mult[*addr as usize] += 1;
            }
        }
        // An inactive read's fields, as Lean's honest row has them
        // (`Circuit.cpuCol`, `fieldsAt`): the cell at its address
        // (`addrAt`) below the counter, else none.  No constraint or message
        // reads them; filling them makes the trace Lean's model, column for
        // column.
        let rd = |a: u32| if a < ctr { memory.get(a as usize).copied() } else { None };
        let fld = |a: u32| rd(a).map_or((0, 0), |c| c.fields());
        let a2 = fld(stk).1;
        let addr = [hd, stk, a2, fld(a2).1];
        for (j, read) in reads.iter().enumerate() {
            if read.is_none() {
                let (a, b) = fld(addr[j]);
                row[FLD + 2 * j] = f(a);
                row[FLD + 2 * j + 1] = f(b);
            }
        }
        match kind {
            Kind::App => mult[ctr as usize] += 1,
            Kind::S => {
                mult[ctr as usize] += 1;
                mult[ctr as usize + 1] += 1;
                mult[ctr as usize + 2] += 1;
            }
            _ => {}
        }
        cpu.extend(row);
    }
    RowMajorMatrix::new(cpu, CPU_WIDTH)
}

/// The three traces, with the memory multiplicities counted from the rows.
fn traces(tb: &Table, min_log: usize) -> (RowMajorMatrix<Val>, RowMajorMatrix<Val>, RowMajorMatrix<Val>, Vec<[u32; 5]>) {
    let mut mult = vec![0u32; tb.mem.len()];
    let cpu = cpu_trace(&tb.rows, &tb.mem, &mut mult);
    let psize = pow2_at_least(tb.loaded.len(), min_log);
    let mut pre = Vec::with_capacity(psize);
    for (i, cell) in tb.loaded.iter().enumerate() {
        let (a, b) = cell.fields();
        pre.push([i as u32, cell.tag(), a, b, 1]);
        mult[i] += 1;
    }
    pre.resize(psize, [0, 0, 0, 0, 0]);
    let mut mem = Vec::with_capacity(tb.mem.len() * 5);
    for (i, cell) in tb.mem.iter().enumerate() {
        let (a, b) = cell.fields();
        mem.extend([f(i as u32), f(cell.tag()), f(a), f(b), f(mult[i])]);
    }
    let prog = vec![Val::ZERO; psize];
    (
        cpu,
        RowMajorMatrix::new(mem, 5),
        RowMajorMatrix::new(prog, 1),
        pre,
    )
}

/// The table in `Ski/AirCheck.lean`'s format.
fn lean_table(term: &str, tb: &Table) -> String {
    let mut s = String::new();
    s.push_str(term);
    s.push('\n');
    s.push_str(&format!("{}\n", tb.mem.len()));
    for cell in &tb.mem {
        s.push_str(&cell.lean());
        s.push('\n');
    }
    s.push_str(&format!("{}\n", tb.rows.len()));
    for [h, st, c] in &tb.rows {
        s.push_str(&format!("{h} {st} {c}\n"));
    }
    s
}

// ---------------------------------------------------------------------------
// Proving and verifying
// ---------------------------------------------------------------------------

/// The AIRs, with the constants and the program table given.
fn airs_of(hd0: u32, stk0: u32, ctr0: u32, pre: Vec<[u32; 5]>) -> Vec<SkiAir> {
    vec![
        SkiAir::Cpu(CpuAir { hd0, stk0, ctr0, accept: None, accept_k: false, blind: false, jets: false, probe: None, restart: None, p2: None }),
        SkiAir::Mem(MemAir { blind: false }),
        SkiAir::Prog(ProgAir { pre }),
    ]
}

/// The program table of a term: its loaded heap, padded with inactive rows.
fn program(t: &Term, min_log: usize) -> Vec<[u32; 5]> {
    let (loaded, _, _) = load(t);
    let psize = pow2_at_least(loaded.len(), min_log);
    let mut pre: Vec<[u32; 5]> = loaded
        .iter()
        .enumerate()
        .map(|(i, cell)| {
            let (a, b) = cell.fields();
            [i as u32, cell.tag(), a, b, 1]
        })
        .collect();
    pre.resize(psize, [0, 0, 0, 0, 0]);
    pre
}

/// The verifier's AIRs, built from the public term alone.
fn verifier_airs(t: &Term) -> Vec<SkiAir> {
    let (loaded, hd0, stk0) = load(t);
    airs_of(hd0, stk0, loaded.len() as u32, program(t, MIN_LOG))
}

/// What happened to a table.
enum Outcome {
    /// Proved, and the proof verified: prove and verify seconds.
    Verified(f64, f64),
    /// The prover could not produce a proof (it failed or panicked).
    Refused(String),
    /// A proof was produced and the verifier rejected it.
    Rejected(String),
}

/// Prove a table with the prover's AIRs, then verify the proof against the
/// public term alone.  The verifier rebuilds its AIRs and the program
/// table's preprocessed commitment from the term, has Lean confirm those
/// AIRs are `Circuit.baseAirs` for the term, takes the CPU and memory
/// heights from the proof, and rejects heights above `MAX_LOG_HEIGHT` (the
/// range checks' bound) or a program height other than the term's.
fn prove_and_verify(
    public: &Term,
    tb: &Table,
    cpu: &RowMajorMatrix<Val>,
    mem: &RowMajorMatrix<Val>,
    prog: &RowMajorMatrix<Val>,
    pre: Vec<[u32; 5]>,
) -> Outcome {
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = make_config();
        let airs = airs_of(tb.hd0, tb.stk0, tb.loaded.len() as u32, pre);
        let log = |m: &RowMajorMatrix<Val>| p3_util::log2_strict_usize(m.values.len() / m.width);
        let degrees = [log(cpu), log(mem), log(prog)];
        let t0 = Instant::now();
        let prover_data = ProverData::<Config>::from_airs_and_degrees(&config, &airs, &degrees)
            .map_err(|e| format!("setup: {e:?}"))?;
        let traces = [cpu, mem, prog];
        let pvs = stmt::public_values(&airs);
        let instances = StarkInstance::new_multiple(&airs, &traces, &pvs);
        let proof =
            prove_batch(&config, &instances, &prover_data).map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    let (proof, prove_s) = match proved {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => return Outcome::Refused(e),
        Err(e) => return Outcome::Refused(format!("panic: {}", panic_text(&e))),
    };

    // The verifier: the public term, the proof, nothing else.
    let t1 = Instant::now();
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let v_config = make_config();
        let v_airs = verifier_airs(public);
        // The AIRs it verifies with are the Lean circuit: Lean compares
        // their symbolic export with `Circuit.baseAirs` for the term, the
        // hypothesis of `Circuit.export_sound`.
        lean_statement("circuit", &["compare", "-"], export::export_airs(public, &v_airs).as_bytes())?;
        let d = &proof.degree_bits;
        let prog_log = p3_util::log2_strict_usize(program(public, MIN_LOG).len());
        if d.len() != 3 || d[0] > MAX_LOG_HEIGHT || d[1] > MAX_LOG_HEIGHT || d[2] != prog_log {
            return Err(format!("heights {d:?} out of bounds"));
        }
        let v_data = ProverData::<Config>::from_airs_and_degrees(&v_config, &v_airs, d)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        let pvs = stmt::public_values(&v_airs);
        let r = verify_batch(&v_config, &v_airs, &proof, &pvs, &v_data.common)
            .map_err(|e| format!("verify: {e:?}"));
        if r.is_ok() {
            crate::fsbudget::budget!("corpus", &v_airs, &proof, &v_data.common, v_config, p3_uni_stark::OpeningShape::new());
        }
        r
    }));
    match verified {
        Ok(Ok(())) => Outcome::Verified(prove_s, t1.elapsed().as_secs_f64()),
        Ok(Err(e)) => Outcome::Rejected(e),
        Err(e) => Outcome::Rejected(format!("verifier panic: {}", panic_text(&e))),
    }
}

/// The verifier's statement check, run in Lean: `lake exe EXE ARGS…` in the
/// lean-ski checkout, with `input` on stdin.  The statement files are
/// public, but only Lean knows what they must be, so the verifier refuses
/// anything Lean does not confirm.  The bytes are piped, never written to a
/// file: what Lean checks is exactly what the verifier holds and then
/// parses, with no file between a read and a check that a writer, a FIFO or
/// a hostile temporary directory could change.
fn lean_statement(exe: &str, args: &[&str], input: &[u8]) -> Result<String, String> {
    use std::io::Write;
    // The Lean project: the lean-ski checkout this binary was built in (it
    // lives at bench/plonky3/target/…), so the statement check is the one
    // shipped with the verifier; else $LEAN_SKI; else one above the working
    // directory.
    let me = std::env::current_exe().map_err(|e| format!("{e}"))?;
    let cwd = std::env::current_dir().map_err(|e| format!("{e}"))?;
    let env = std::env::var_os("LEAN_SKI").map(std::path::PathBuf::from);
    let root = me
        .ancestors()
        .chain(env.iter().map(|p| p.as_path()))
        .chain(cwd.ancestors())
        .find(|d| d.join("lakefile.toml").exists() && d.join("bench/Jets.lean").exists())
        .ok_or_else(|| "no lean-ski checkout found (set LEAN_SKI)".to_string())?
        .to_path_buf();
    let mut child = std::process::Command::new("lake")
        .args(["exe", exe])
        .args(args)
        .current_dir(root)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("lake: {e}"))?;
    // Drain both pipes on their own threads, so neither fills while the
    // child runs, and bound the child's wall-clock time: a wedged check
    // fails rather than hanging the verifier.
    let read = |p: Option<Box<dyn std::io::Read + Send>>| {
        std::thread::spawn(move || {
            let mut buf = Vec::new();
            if let Some(mut p) = p {
                let _ = std::io::Read::read_to_end(&mut p, &mut buf);
            }
            buf
        })
    };
    let out_t = read(child.stdout.take().map(|p| Box::new(p) as Box<dyn std::io::Read + Send>));
    let err_t = read(child.stderr.take().map(|p| Box::new(p) as Box<dyn std::io::Read + Send>));
    let written = child
        .stdin
        .take()
        .ok_or_else(|| "lake: no stdin".to_string())
        .and_then(|mut w| w.write_all(input).map_err(|e| format!("lake stdin: {e}")));
    let limit = std::env::var("LEAN_TIMEOUT").ok().and_then(|t| t.parse::<u64>().ok()).unwrap_or(600);
    let start = Instant::now();
    let status = loop {
        match child.try_wait().map_err(|e| format!("lake: {e}"))? {
            Some(st) => break st,
            None if start.elapsed().as_secs() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("lake exe {exe}: no answer within {limit} s (LEAN_TIMEOUT)"));
            }
            None => std::thread::sleep(std::time::Duration::from_millis(20)),
        }
    };
    let stdout = out_t.join().map_err(|_| "lake: stdout reader panicked".to_string())?;
    let stderr = err_t.join().map_err(|_| "lake: stderr reader panicked".to_string())?;
    written?;
    if status.success() {
        Ok(String::from_utf8_lossy(&stdout).into_owned())
    } else {
        let msg = String::from_utf8_lossy(&stdout).lines().filter(|l| !l.starts_with("STATEMENT")).collect::<Vec<_>>().join("; ");
        if msg.is_empty() {
            // A Lean exception prints to stderr only.
            Err(format!("{}: {}", status, String::from_utf8_lossy(&stderr).trim_end()))
        } else {
            Err(msg)
        }
    }
}

/// A corpus line's fields, split as Lean's `words` splits them: on the
/// space character only, empty fields dropped.
fn lean_words(l: &str) -> Vec<&str> {
    l.split(' ').filter(|w| !w.is_empty()).collect()
}

fn panic_text(e: &Box<dyn std::any::Any + Send>) -> String {
    e.downcast_ref::<String>()
        .cloned()
        .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

const MIN_LOG: usize = 4;

/// Set by `ski-air fs-budget …`: verifiers print the proof's per-round
/// Fiat–Shamir budget (`fsbudget`).
static FS_BUDGET: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub(crate) fn fs_budget_on() -> bool {
    FS_BUDGET.load(std::sync::atomic::Ordering::Relaxed)
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    if args.len() >= 2 && args[1] == "fs-budget" {
        FS_BUDGET.store(true, std::sync::atomic::Ordering::Relaxed);
        args.remove(1);
    }
    // Under `fs-budget`, say so when the command printed no budget.
    struct BudgetGuard;
    impl Drop for BudgetGuard {
        fn drop(&mut self) {
            if fs_budget_on() && !fsbudget::EMITTED.load(std::sync::atomic::Ordering::Relaxed) {
                eprintln!("fs-budget: this command printed no budget (none verified, or it has no budget hook)");
            }
        }
    }
    let _budget_guard = BudgetGuard;
    if args.len() == 2 && args[1] == "poseidon2-lean" {
        print!("{}", poseidon2_lean());
        return;
    }
    if args.len() == 5 && args[1] == "compp-prove-table" {
        match compp::compp_prove_table(std::path::Path::new(&args[2]), std::path::Path::new(&args[3]), std::path::Path::new(&args[4])) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("compp-prove-table: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 4 && args[1] == "compp-guess" {
        match compp::compp_guess(std::path::Path::new(&args[2]), std::path::Path::new(&args[3])) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("compp-guess: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 5 && args[1] == "compp-dump" {
        match compp::compp_dump(std::path::Path::new(&args[2]), std::path::Path::new(&args[3]), std::path::Path::new(&args[4])) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("compp-dump: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 6 && args[1] == "compp-chain" {
        let p = |i: usize| std::path::Path::new(&args[i]);
        match compp::compp_chain(p(2), p(3), p(4), p(5)) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("compp-chain: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 4 && args[1] == "compp-verify" {
        match compp::compp_verify(std::path::Path::new(&args[2]), std::path::Path::new(&args[3])) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("compp-verify: {e}");
                std::process::exit(1);
            }
        }
    }
    if (args.len() == 5 || args.len() == 6) && args[1] == "compp-prove" {
        let (forge, table_out) = match args.get(5).map(|s| s.as_str()) {
            Some("forge-w") => (compp::Forge::W, None),
            Some("forge-v") => (compp::Forge::V, None),
            Some(t) if t.starts_with("--table=") && t.len() > 8 => (compp::Forge::None, Some(std::path::Path::new(&t[8..]))),
            Some(t) => {
                eprintln!("compp-prove: expected --table=PATH, forge-w or forge-v, not {t}");
                std::process::exit(2);
            }
            None => (compp::Forge::None, None),
        };
        match compp::compp_prove(std::path::Path::new(&args[2]), std::path::Path::new(&args[3]), std::path::Path::new(&args[4]), forge, table_out) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("compp-prove: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 2 && args[1] == "export-p2" {
        print!("{}", export::export_air("p2", &SkiAir::P2(false)));
        return;
    }
    if (args.len() == 3 || (args.len() == 4 && args[3] == "tamper")) && args[1] == "p2-bench" {
        match p2air::p2_bench(args[2].parse().expect("a count"), args.len() == 4) {
            Ok(()) => return,
            Err(e) => {
                eprintln!("p2-bench: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 3 && args[1] == "export-base" {
        print!("{}", export::export_base(&args[2]));
        return;
    }
    if args.len() >= 5 && args[1] == "export-probe" {
        let outcome: Vec<&str> = args[4..].iter().map(|s| s.as_str()).collect();
        match jets::export_probe(&args[2], std::path::Path::new(&args[3]), &outcome) {
            Ok(s) => print!("{s}"),
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 4 && args[1] == "export-jets" {
        match jets::export_jets(&args[2], std::path::Path::new(&args[3])) {
            Ok(s) => print!("{s}"),
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 3 && args[1] == "export-sudoku" {
        let text = std::fs::read_to_string(&args[2]).expect("statement");
        print!("{}", sudoku::export_sudoku(&text));
        return;
    }
    if args.len() == 3 && args[1] == "export-witness" {
        let text = std::fs::read_to_string(&args[2]).expect("statement");
        match witness::export_witness(&text) {
            Ok(s) => print!("{s}"),
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 3 && args[1] == "export-compp" {
        let text = std::fs::read_to_string(&args[2]).expect("a statement");
        match compp::export_compp(&text) {
            Ok(s) => {
                print!("{s}");
                return;
            }
            Err(e) => {
                eprintln!("export-compp: {e}");
                std::process::exit(1);
            }
        }
    }
    if args.len() == 4 && args[1] == "export-compj" {
        let text = std::fs::read_to_string(&args[2]).expect("statement");
        let jtext = std::fs::read_to_string(&args[3]).expect("jet table");
        match compj::export_compj(&text, &jtext) {
            Ok(s) => print!("{s}"),
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        return;
    }
    if args.len() == 7 && args[1] == "compj-prove-table" {
        std::panic::set_hook(Box::new(|_| {}));
        let pth = |i: usize| std::path::Path::new(&args[i]);
        if let Err(e) = compj::compj_prove_table(pth(2), pth(3), &args[4], pth(5), pth(6)) {
            println!("FAILED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if ((args.len() == 7 || args.len() == 8) && args[1] == "compj-prove") || (args.len() == 6 && (args[1] == "compj-verify" || args[1] == "compj-tamper")) {
        std::panic::set_hook(Box::new(|_| {}));
        let pth = |i: usize| std::path::Path::new(&args[i]);
        let r = match args[1].as_str() {
            "compj-prove" => compj::compj_prove(pth(2), pth(3), &args[4], pth(5), pth(6), args.get(7).map(std::path::Path::new)),
            "compj-verify" => compj::compj_verify(pth(2), pth(3), &args[4], pth(5)),
            _ => compj::compj_tamper(pth(2), pth(3), &args[4], pth(5)),
        };
        if let Err(e) = r {
            println!("FAILED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 3 && args[1] == "export-composed" {
        let text = std::fs::read_to_string(&args[2]).expect("statement");
        match composed::export_composed(&text) {
            Ok(s) => print!("{s}"),
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
        return;
    }
    if (args.len() == 5 || args.len() == 6) && args[1] == "composed-prove" {
        std::panic::set_hook(Box::new(|_| {}));
        let p = |i: usize| std::path::Path::new(&args[i]);
        if let Err(e) = composed::composed_prove(p(2), p(3), p(4), args.get(5).map(std::path::Path::new)) {
            println!("REFUSED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 4 && args[1] == "composed-verify" {
        std::panic::set_hook(Box::new(|_| {}));
        let p = |i: usize| std::path::Path::new(&args[i]);
        if let Err(e) = composed::composed_verify(p(2), p(3)) {
            println!("REJECTED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 4 && args[1] == "composed" {
        let out = std::path::Path::new(&args[3]);
        std::fs::create_dir_all(out).unwrap();
        if std::env::var_os("SKI_AIR_PANICS").is_none() {
            std::panic::set_hook(Box::new(|_| {}));
        }
        let failures = composed::main(std::path::Path::new(&args[2]), out);
        if failures > 0 {
            println!("\n{failures} FAILURES");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 4 && args[1] == "witness" {
        let out = std::path::Path::new(&args[3]);
        std::fs::create_dir_all(out).unwrap();
        if std::env::var_os("SKI_AIR_PANICS").is_none() {
            std::panic::set_hook(Box::new(|_| {}));
        }
        let failures = witness::main(std::path::Path::new(&args[2]), out);
        if failures > 0 {
            println!("\n{failures} FAILURES");
            std::process::exit(1);
        }
        return;
    }
    if ((args.len() == 5 || args.len() == 6) && args[1] == "sudoku-prove") || (args.len() == 4 && args[1] == "sudoku-verify") {
        std::panic::set_hook(Box::new(|_| {}));
        let pth = |i: usize| std::path::Path::new(&args[i]);
        let r = if args[1] == "sudoku-prove" {
            sudoku::sudoku_prove(pth(2), pth(3), pth(4), args.get(5).map(std::path::Path::new))
        } else {
            sudoku::sudoku_verify(pth(2), pth(3))
        };
        if let Err(e) = r {
            println!("FAILED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 4 && args[1] == "sudoku" {
        let out = std::path::Path::new(&args[3]);
        std::fs::create_dir_all(out).unwrap();
        std::panic::set_hook(Box::new(|_| {}));
        let failures = sudoku::main(std::path::Path::new(&args[2]), out);
        if failures > 0 {
            println!("\n{failures} FAILURES");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 6 && (args[1] == "jet-prove" || args[1] == "jet-verify") {
        std::panic::set_hook(Box::new(|_| {}));
        let p = |i: usize| std::path::Path::new(&args[i]);
        let r = if args[1] == "jet-prove" {
            jets::jet_prove(p(2), p(3), p(4), p(5))
        } else {
            jets::jet_verify(p(2), p(3), &args[4], p(5))
        };
        if let Err(e) = r {
            println!("REJECTED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() >= 7 && (args[1] == "probe-prove" || args[1] == "probe-prove-table" || args[1] == "probe-verify") {
        std::panic::set_hook(Box::new(|_| {}));
        let p = |i: usize| std::path::Path::new(&args[i]);
        let outcome: Vec<&str> = args[6..].iter().map(|x| x.as_str()).collect();
        let r = if args[1] == "probe-prove" {
            jets::probe_prove(p(2), p(3), p(4), p(5), &outcome)
        } else if args[1] == "probe-prove-table" {
            jets::probe_prove_table(p(2), p(3), p(4), p(5), &outcome)
        } else {
            jets::probe_verify(p(2), p(3), &args[4], p(5), &outcome)
        };
        if let Err(e) = r {
            println!("REJECTED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 5 && args[1] == "probes" {
        let corpus = std::fs::read_to_string(&args[2]).expect("corpus");
        let out = std::path::Path::new(&args[4]);
        std::fs::create_dir_all(out).unwrap();
        std::panic::set_hook(Box::new(|_| {}));
        let failures = jets::probe_main(&corpus, std::path::Path::new(&args[3]), out);
        if failures > 0 {
            println!("\n{failures} FAILURES");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 5 && args[1] == "jets-measure" {
        std::panic::set_hook(Box::new(|_| {}));
        let p = |i: usize| std::path::Path::new(&args[i]);
        if let Err(e) = jets::measure(p(2), p(3), p(4)) {
            println!("FAILED: {e}");
            std::process::exit(1);
        }
        return;
    }
    if args.len() == 5 && args[1] == "jets" {
        let corpus = std::fs::read_to_string(&args[2]).expect("corpus");
        let out = std::path::Path::new(&args[4]);
        std::fs::create_dir_all(out).unwrap();
        std::panic::set_hook(Box::new(|_| {}));
        let failures = jets::main(&corpus, std::path::Path::new(&args[2]), std::path::Path::new(&args[3]), out);
        if failures > 0 {
            println!("\n{failures} FAILURES");
            std::process::exit(1);
        }
        return;
    }
    if args.len() != 3 {
        eprintln!(
            "usage: ski-air CORPUS OUTDIR | ski-air sudoku DIR OUTDIR | ski-air witness DIR OUTDIR | ski-air composed DIR OUTDIR |\n       \
             ski-air composed-prove PUBLIC WITNESS PROOF [TABLE] | ski-air composed-verify PUBLIC PROOF | ski-air jets CORPUS JETSDIR OUTDIR\n       \
             ski-air jet-prove TERM JETS TABLE PROOF | ski-air jet-verify CORPUS JETSDIR NAME PROOF\n       \
             ski-air probes CORPUS JETSDIR OUTDIR | ski-air probe-prove TERM JETS TABLE PROOF OUTCOME...\n       \
             ski-air probe-prove-table TERM JETS TABLE PROOF OUTCOME...\n       \
             ski-air probe-verify CORPUS JETSDIR NAME PROOF OUTCOME...\n       \
             ski-air export-compj PUBLIC JETS | ski-air compj-prove PUBLIC JETS SRC WITNESS PROOF [TABLE]\n       \
             ski-air compj-verify PUBLIC JETS SRC PROOF | ski-air compj-tamper PUBLIC JETS SRC WITNESS\n       \
             ski-air compj-prove-table PUBLIC JETS SRC TABLE PROOF\n       \
             ski-air sudoku-prove PUBLIC WITNESS PROOF [TABLE] | ski-air sudoku-verify PUBLIC PROOF\n       \
             ski-air fs-budget VERIFY-COMMAND ARGS... | ski-air poseidon2-lean | ski-air export-p2 | ski-air p2-bench N [tamper] | ski-air compp-prove PUBLIC WITNESS PROOF [--table=PATH|forge-w|forge-v] | ski-air compp-prove-table PUBLIC TABLE PROOF | ski-air compp-verify PUBLIC PROOF | ski-air compp-chain PUBLIC1 PROOF1 PUBLIC2 PROOF2 | ski-air compp-dump PUBLIC WITNESS DIR | ski-air compp-guess PUBLIC WITNESS | ski-air export-compp PUBLIC"
        );
        std::process::exit(2);
    }
    let corpus = std::fs::read_to_string(&args[1]).expect("corpus");
    let out = std::path::Path::new(&args[2]);
    std::fs::create_dir_all(out).unwrap();
    std::panic::set_hook(Box::new(|_| {}));

    let mut rows: Vec<(String, u64, String)> = vec![
        // Small terms first: `I K` and `S K K S`.
        ("ik".into(), 1, "`IK".into()),
        ("skks".into(), 2, "```SKKS".into()),
    ];
    for line in corpus.lines().filter(|l| !l.trim().is_empty()) {
        let mut it = lean_words(line).into_iter();
        let name = it.next().unwrap().to_string();
        let steps: u64 = it.next().unwrap().parse().unwrap();
        let term = it.next().unwrap().to_string();
        rows.push((name, steps, term));
    }

    println!(
        "{:<16} {:>6} {:>6} {:>6} {:>7} {:>8} {:>8}  verdict",
        "row", "contr", "rows", "budget", "memory", "prove s", "verify s"
    );
    let mut failures = 0;
    for (name, steps, term) in &rows {
        let t = parse(term.as_bytes(), &mut 0);
        let (tb, r) = table_of(&t, MIN_LOG);
        if r.contractions != *steps {
            println!("{name}: {} contractions, reference {steps}", r.contractions);
            failures += 1;
            continue;
        }
        std::fs::write(out.join(format!("{name}.txt")), lean_table(term, &tb)).unwrap();
        let (cpu, mem, prog, pre) = traces(&tb, MIN_LOG);
        match prove_and_verify(&t, &tb, &cpu, &mem, &prog, pre) {
            Outcome::Verified(p, v) => println!(
                "{:<16} {:>6} {:>6} {:>6} {:>7} {:>8.2} {:>8.3}  verified",
                name,
                r.contractions,
                r.rows.len(),
                tb.rows.len(),
                tb.mem.len(),
                p,
                v
            ),
            Outcome::Refused(e) | Outcome::Rejected(e) => {
                println!("{name}: FAILED an honest table: {e}");
                failures += 1;
            }
        }
    }

    // Tampered tables.  The honest traces are built first; one change is
    // made in the trace and the same change in the Lean table.  A tamper
    // passes only when the prover produces a proof and the verifier rejects
    // it; a prover that refuses proves nothing about the verifier.
    println!("\ntampered tables (each proof must be rejected by the verifier):");
    let term = "```SKKS";
    let t = parse(term.as_bytes(), &mut 0);
    let (tb, r) = table_of(&t, MIN_LOG);
    let n = r.rows.len();
    let a = tb.loaded.len();
    for tname in ["forged_cell", "wrong_step", "early_halt", "forged_loaded"] {
        let (mut cpu, mut mem, prog, pre) = traces(&tb, MIN_LOG);
        let mut bad = Table {
            loaded: tb.loaded.clone(),
            hd0: tb.hd0,
            stk0: tb.stk0,
            rows: tb.rows.clone(),
            mem: tb.mem.clone(),
        };
        let mut public_term = term.to_string();
        let (mut cpu_b, mut mem_b, mut prog_b, mut pre_b) = (None, None, None, None);
        match tname {
            // A forged cell: the first cell the run writes, a stack cell,
            // names a different argument.
            "forged_cell" => {
                let (x, rest) = match bad.mem[a] {
                    Cell::Cons(x, rest) => (x, rest),
                    c => panic!("expected a stack cell, found {c:?}"),
                };
                bad.mem[a] = Cell::Cons(x + 1, rest);
                mem.values[a * 5 + 2] = f(x + 1);
            }
            // A wrong transition: the second row's head pointer moves.
            "wrong_step" => {
                bad.rows[1][0] += 1;
                cpu.values[CPU_WIDTH + HD] += Val::ONE;
            }
            // An early halt: from the second row on, the unhalted second
            // state repeats as if halted, claiming `S` with no arguments.
            "early_halt" => {
                assert!(n > 2, "the run must pass its second state");
                let row1 = bad.rows[1];
                for row in bad.rows.iter_mut().skip(1) {
                    *row = row1;
                }
                let base: Vec<Val> = cpu.values[CPU_WIDTH..2 * CPU_WIDTH].to_vec();
                let k = cpu.values.len() / CPU_WIDTH;
                for i in 1..k {
                    let row = &mut cpu.values[i * CPU_WIDTH..(i + 1) * CPU_WIDTH];
                    row.copy_from_slice(&base);
                    for sel in 0..NKINDS {
                        row[SEL + sel] = Val::ZERO;
                    }
                    row[SEL + 7] = Val::ONE; // HS1
                }
            }
            // A forged program: the honest run of `I S` offered for the
            // public term `I K`, which loads to a heap of the same shape.
            "forged_loaded" => {
                public_term = "`IK".to_string();
                let other = parse(b"`IS", &mut 0);
                let (tb2, _) = table_of(&other, MIN_LOG);
                let (c2, m2, p2, pr2) = traces(&tb2, MIN_LOG);
                bad = tb2;
                cpu_b = Some(c2);
                mem_b = Some(m2);
                prog_b = Some(p2);
                pre_b = Some(pr2);
            }
            _ => unreachable!(),
        }
        std::fs::write(
            out.join(format!("tampered_{tname}.txt")),
            lean_table(&public_term, &bad),
        )
        .unwrap();
        let public = parse(public_term.as_bytes(), &mut 0);
        let outcome = prove_and_verify(
            &public,
            &bad,
            cpu_b.as_ref().unwrap_or(&cpu),
            mem_b.as_ref().unwrap_or(&mem),
            prog_b.as_ref().unwrap_or(&prog),
            pre_b.unwrap_or(pre),
        );
        let verdict = match outcome {
            Outcome::Rejected(e) => format!("rejected by the verifier ({})", e.chars().take(60).collect::<String>()),
            Outcome::Verified(..) => {
                failures += 1;
                "ACCEPTED".to_string()
            }
            Outcome::Refused(e) => {
                failures += 1;
                format!("NOT TESTED: the prover refused ({})", e.chars().take(50).collect::<String>())
            }
        };
        println!("{:<16} {}", tname, verdict);
    }

    if failures > 0 {
        println!("\n{failures} FAILURES");
        std::process::exit(1);
    }
}

/// `ski-air poseidon2-lean`: the round constants of the Poseidon2
/// permutation every configuration hashes with
/// (`default_babybear_poseidon2_16`), and its outputs on three inputs, as a
/// Lean file: `Ski/ZK/Poseidon2Data.lean`, against which
/// `Ski/ZK/Poseidon2.lean`'s specification is checked.
fn poseidon2_lean() -> String {
    use p3_baby_bear::{
        BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
        BABYBEAR_POSEIDON2_RC_16_INTERNAL,
    };
    use p3_field::PrimeField32;
    use p3_symmetric::Permutation;
    let row = |r: &[BabyBear]| format!("[{}]", r.iter().map(|x| x.as_canonical_u32().to_string()).collect::<Vec<_>>().join(", "));
    let rows = |rs: &[[BabyBear; 16]]| format!("[{}]", rs.iter().map(|r| row(r)).collect::<Vec<_>>().join(",\n    "));
    let perm = default_babybear_poseidon2_16();
    let inputs: [[u32; 16]; 3] = [
        [0; 16],
        core::array::from_fn(|i| i as u32),
        core::array::from_fn(|i| (2013265920 - 7 * i as u32) % 2013265921),
    ];
    let mut s = String::from("/-! Generated by `ski-air poseidon2-lean` from Plonky3 0.8's\n    `default_babybear_poseidon2_16`: its round constants and its outputs on\n    three inputs.  Do not edit. -/\n\nnamespace Poseidon2\n\n");
    s += &format!("def rcInitial : List (List Nat) :=\n  {}\n\n", rows(&BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL));
    s += &format!("def rcTerminal : List (List Nat) :=\n  {}\n\n", rows(&BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL));
    s += &format!("def rcInternal : List Nat :=\n  {}\n\n", row(&BABYBEAR_POSEIDON2_RC_16_INTERNAL));
    s += "/-- Inputs and Plonky3's outputs. -/\ndef vectors : List (List Nat × List Nat) :=\n  [";
    let mut first = true;
    for inp in inputs {
        let mut st: [BabyBear; 16] = core::array::from_fn(|i| BabyBear::new(inp[i]));
        let x = st;
        perm.permute_mut(&mut st);
        if !first { s += ",\n   "; }
        first = false;
        s += &format!("({}, {})", row(&x), row(&st));
    }
    s += "]\n\nend Poseidon2\n";
    s
}
