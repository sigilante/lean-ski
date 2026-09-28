//! The AIR of `Ski/Air.lean` in Plonky3, checked against Lean.
//!
//! Three tables under one batch STARK over BabyBear, joined by one LogUp bus,
//! `mem`, whose entries are `(address, tag, field a, field b)`:
//!
//! - **CPU**: one row per machine transition, padded to a public budget with
//!   halted rows.  A row holds the registers `hd`, `stk`, `ctr`, a one-hot
//!   selector for the rule kind, the fields of the cells it reads, and the
//!   bits that range-check each read address below `ctr`.  The kinds are the
//!   cases of `Air.stepG` and `Air.haltRow`: an unwind, `I`, `K`, `S`, and the
//!   six ways a combinator can lack arguments.  A read's tag is fixed by the
//!   kind, so the lookups check the cells the kind needs.
//! - **Memory**: the committed memory table, one entry per address in order
//!   (`addr` starts at 0 and increases by 1), with the number of times each
//!   entry is looked up.  One value per address, as `rd` needs.
//! - **Program**: the loaded heap of the public term, as a preprocessed
//!   table the verifier rebuilds from the term.  Every loaded cell is looked
//!   up in memory, which pins the memory table's prefix (`heap0`).
//!
//! The check against Lean: for every table proved here, the same table is
//! written in the format of `Ski/AirCheck.lean`, and `lake exe aircheck`
//! decides the AIR's constraints on it with a checker proved sound for the
//! AIR (`Air.checkA_sound`).  Tampered tables must fail both.
//!
//! **Why the constraints are `Accepts`.**  Read a table off an accepted
//! proof: the rows are the CPU's registers, and `M[a]` is the memory entry at
//! address `a` (one per address).  A lookup that balances names an entry, so
//! a read of `(a, tag, x, y)` means `M[a]` has that tag and those fields.
//! - Every read address lies below the row's counter: its 24 bits represent
//!   `ctr - a - 1` only when `a < ctr`, since addresses and counters stay
//!   below `2^23`.  So each read is `rd M ctr a`.
//! - An unwind reads an application `(f, x)` at `hd` and writes `C x stk` at
//!   `ctr`; the next registers are `f, ctr, ctr + 1`.  That is `stepG`'s
//!   application case with its write checked (`wrs`).
//! - `I`, `K`, `S` read the head combinator and one, two, three stack cells
//!   `C x s1`, `C y s2`, `C z s3`; `S` writes `A y z`, `C ctr s3`,
//!   `C z (ctr + 1)`.  The next registers are `stepG`'s.
//! - The six halting kinds read the head combinator and the stack down to an
//!   empty stack before the rule's arity: `haltRow`'s `short`.  A halted row's
//!   next row repeats it.
//! - The first row is the loaded term, the program table pins `M`'s prefix to
//!   the loaded heap, and the last row has halted.
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

/// Plonky3's benchmark FRI parameters: blowup 2, 100 queries, 16 bits of
/// query grinding.
fn make_config() -> Config {
    let perm = default_babybear_poseidon2_16();
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = ValMmcs::new(hash, compress, 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters::new_benchmark(challenge_mmcs);
    let pcs = Pcs::new(Dft::default(), val_mmcs, fri);
    Config::new(pcs, Challenger::new(perm))
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
        }
    }
    fn fields(self) -> (u32, u32) {
        match self {
            Cell::App(f, x) => (f, x),
            Cell::Cons(x, r) => (x, r),
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
}

const KINDS: [Kind; 10] = [
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
const FLD: usize = SEL + 10;
const BITS: usize = FLD + 8;
const CPU_WIDTH: usize = BITS + 4 * RANGE_BITS;

const BUS: &str = "mem";

#[derive(Clone, Debug)]
struct CpuAir {
    hd0: u32,
    stk0: u32,
    ctr0: u32,
}

#[derive(Clone, Debug)]
struct MemAir;

/// The loaded heap: rows `(addr, tag, a, b, active)`.
#[derive(Clone, Debug)]
struct ProgAir {
    pre: Vec<[u32; 5]>,
}

#[derive(Clone, Debug)]
enum SkiAir {
    Cpu(CpuAir),
    Mem(MemAir),
    Prog(ProgAir),
}

impl<F: Field> BaseAir<F> for SkiAir {
    fn width(&self) -> usize {
        match self {
            SkiAir::Cpu(_) => CPU_WIDTH,
            SkiAir::Mem(_) => 5,
            SkiAir::Prog(_) => 1,
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
            _ => None,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            SkiAir::Prog(_) => 5,
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
            SkiAir::Mem(_) => eval_mem(b),
            SkiAir::Prog(_) => eval_prog(b),
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
        let f = |i: usize| loc[FLD + i].clone();
        let (a0, b0, a1, b1, a2, b2, a3, b3) = (f(0), f(1), f(2), f(3), f(4), f(5), f(6), f(7));

        // Exactly one kind per row.
        for i in 0..10 {
            b.assert_bool(s(i));
        }
        let sels: Vec<AB::Expr> = (0..10).map(s).collect();
        b.assert_eq(sum::<AB>(&sels), one.clone());

        let halt = sum::<AB>(&[hi1.clone(), hk1.clone(), hk2.clone(), hs1.clone(), hs2.clone(), hs3.clone()]);

        // The reads each kind makes, and the tags the kind requires of them.
        let acts = [
            one.clone(),
            one.clone() - app.clone(),
            sum::<AB>(&[kk.clone(), ks.clone(), hk2.clone(), hs2.clone(), hs3.clone()]),
            ks.clone() + hs3.clone(),
        ];
        let tags = [
            (kk.clone() + hk1.clone() + hk2.clone()) * c(1)
                + (ki.clone() + hi1.clone()) * c(2)
                + app.clone() * c(3),
            sum::<AB>(&[ki.clone(), kk.clone(), ks.clone(), hk2.clone(), hs2.clone(), hs3.clone()]) * c(5)
                + sum::<AB>(&[hi1.clone(), hk1.clone(), hs1.clone()]) * c(4),
            sum::<AB>(&[kk.clone(), ks.clone(), hs3.clone()]) * c(5)
                + (hk2.clone() + hs2.clone()) * c(4),
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
        let next_hd = app.clone() * a0.clone()
            + (ki.clone() + kk.clone() + ks.clone()) * a1.clone()
            + halt.clone() * hd.clone();
        let next_stk = app.clone() * ctr.clone()
            + ki.clone() * b1.clone()
            + kk.clone() * b2.clone()
            + ks.clone() * (ctr.clone() + c(2))
            + halt.clone() * stk.clone();
        let next_ctr = ctr.clone() + app.clone() + ks.clone() * c(3);
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
        b.when_last_row().assert_eq(halt, one);
    }
}

fn eval_mem<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
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

/// The three traces, with the memory multiplicities counted from the rows.
fn traces(tb: &Table, min_log: usize) -> (RowMajorMatrix<Val>, RowMajorMatrix<Val>, RowMajorMatrix<Val>, Vec<[u32; 5]>) {
    let mut mult = vec![0u32; tb.mem.len()];
    let mut cpu = Vec::with_capacity(tb.rows.len() * CPU_WIDTH);
    for &[hd, stk, ctr] in &tb.rows {
        let (kind, reads) = classify(&tb.mem, hd, stk);
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
        RowMajorMatrix::new(cpu, CPU_WIDTH),
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

/// The verifier's AIRs, rebuilt from the public term.
fn airs_for(tb: &Table, pre: Vec<[u32; 5]>) -> Vec<SkiAir> {
    vec![
        SkiAir::Cpu(CpuAir { hd0: tb.hd0, stk0: tb.stk0, ctr0: tb.loaded.len() as u32 }),
        SkiAir::Mem(MemAir),
        SkiAir::Prog(ProgAir { pre }),
    ]
}

/// Prove a table and verify the proof with verifier-side data rebuilt from
/// the public term and heights.  `Ok` only when the proof verifies.
fn prove_and_verify(
    tb: &Table,
    cpu: &RowMajorMatrix<Val>,
    mem: &RowMajorMatrix<Val>,
    prog: &RowMajorMatrix<Val>,
    pre: Vec<[u32; 5]>,
) -> Result<(f64, f64), String> {
    let config = make_config();
    let airs = airs_for(tb, pre.clone());
    let log = |m: &RowMajorMatrix<Val>| p3_util::log2_strict_usize(m.values.len() / m.width);
    let degrees = [log(cpu), log(mem), log(prog)];
    for &d in &degrees {
        assert!(d <= MAX_LOG_HEIGHT, "a table above the range-check bound");
    }
    let t0 = Instant::now();
    let prover_data = ProverData::<Config>::from_airs_and_degrees(&config, &airs, &degrees)
        .map_err(|e| format!("setup: {e:?}"))?;
    let traces = [cpu, mem, prog];
    let pvs = vec![vec![], vec![], vec![]];
    let instances = StarkInstance::new_multiple(&airs, &traces, &pvs);
    let proof = prove_batch(&config, &instances, &prover_data).map_err(|e| format!("prove: {e:?}"))?;
    let prove_s = t0.elapsed().as_secs_f64();

    // The verifier rebuilds its AIRs and common data from the public term.
    let t1 = Instant::now();
    let v_config = make_config();
    let v_airs = airs_for(tb, pre);
    let v_data = ProverData::<Config>::from_airs_and_degrees(&v_config, &v_airs, &degrees)
        .map_err(|e| format!("verifier setup: {e:?}"))?;
    verify_batch(&v_config, &v_airs, &proof, &pvs, &v_data.common)
        .map_err(|e| format!("verify: {e:?}"))?;
    Ok((prove_s, t1.elapsed().as_secs_f64()))
}

/// `prove_and_verify`, with a panic in the prover counted as a rejection.
fn attempt(
    tb: &Table,
    cpu: &RowMajorMatrix<Val>,
    mem: &RowMajorMatrix<Val>,
    prog: &RowMajorMatrix<Val>,
    pre: Vec<[u32; 5]>,
) -> Result<(f64, f64), String> {
    match catch_unwind(AssertUnwindSafe(|| prove_and_verify(tb, cpu, mem, prog, pre))) {
        Ok(r) => r,
        Err(e) => Err(format!(
            "panic: {}",
            e.downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default()
        )),
    }
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

const MIN_LOG: usize = 4;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: ski-air CORPUS OUTDIR");
        std::process::exit(2);
    }
    let corpus = std::fs::read_to_string(&args[1]).expect("corpus");
    let out = std::path::Path::new(&args[2]);
    std::fs::create_dir_all(out).unwrap();
    std::panic::set_hook(Box::new(|_| {}));

    let mut rows: Vec<(String, u64, String)> = vec![
        // Small terms first: `I K`, `S K K S`, `K I (S I I)`-free forms.
        ("ik".into(), 1, "`IK".into()),
        ("skks".into(), 2, "```SKKS".into()),
    ];
    for line in corpus.lines().filter(|l| !l.trim().is_empty()) {
        let mut it = line.split_whitespace();
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
        match attempt(&tb, &cpu, &mem, &prog, pre) {
            Ok((p, v)) => println!(
                "{:<16} {:>6} {:>6} {:>6} {:>7} {:>8.2} {:>8.3}  verified",
                name,
                r.contractions,
                r.rows.len(),
                tb.rows.len(),
                tb.mem.len(),
                p,
                v
            ),
            Err(e) => {
                println!("{name}: REJECTED an honest table: {e}");
                failures += 1;
            }
        }
    }

    // Tampered tables: each must be rejected by the STARK and by Lean.  The
    // honest traces are built first, then one value is changed in the trace
    // and the same change is made in the Lean table.
    println!("\ntampered tables (each must be rejected):");
    let term = "```SKKS";
    let t = parse(term.as_bytes(), &mut 0);
    let (tb, r) = table_of(&t, MIN_LOG);
    let n = r.rows.len();
    let a = tb.loaded.len();
    for tname in ["forged_cell", "wrong_step", "early_halt"] {
        let (mut cpu, mut mem, prog, pre) = traces(&tb, MIN_LOG);
        let mut bad = Table {
            loaded: tb.loaded.clone(),
            hd0: tb.hd0,
            stk0: tb.stk0,
            rows: tb.rows.clone(),
            mem: tb.mem.clone(),
        };
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
                    for sel in 0..10 {
                        row[SEL + sel] = Val::ZERO;
                    }
                    row[SEL + 7] = Val::ONE; // HS1
                }
            }
            _ => unreachable!(),
        }
        std::fs::write(out.join(format!("tampered_{tname}.txt")), lean_table(term, &bad)).unwrap();
        let verdict = match attempt(&bad, &cpu, &mem, &prog, pre) {
            Ok(_) => {
                failures += 1;
                "ACCEPTED".to_string()
            }
            Err(e) => format!("rejected ({})", e.chars().take(70).collect::<String>()),
        };
        println!("{:<16} {}", tname, verdict);
    }

    if failures > 0 {
        println!("\n{failures} FAILURES");
        std::process::exit(1);
    }
}
