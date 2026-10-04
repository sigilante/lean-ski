//! A composed statement with the Poseidon2 jet (`Ski/ComposedP.lean`,
//! `Ski/P2Jet.lean`), proved with Plonky3.
//!
//! The statement is `lake exe composed emit-p2`'s: the composed machine of
//! an open verifier whose jet is the atom `J` (`ComposedPText.publicTextP`).
//! The machine runs as the composed one does, and at `J` with `k` and the
//! comb's root `β` on the stack it takes the jet's step (`P2Jet.p2Row`): it
//! reads the 496 bits from their slots `3 … 498`, and pushes the outputs'
//! 496 bits for `k`, each a stack cell pointing at the `K` slot (0) or the
//! `K I` slot (2).  The root is public (`CompM.combRoot_public`), so the
//! jet's row checks `β` against the statement's constant.
//!
//! Nine tables: the composed circuit's five (CPU, memory, program, witness,
//! segments), the CPU carrying the jet's row, and the jet's four:
//!
//! - **P2IN**, one row per input bit: it reads the bit's slot, a `K` cell or
//!   the cell `app 0 1`, and accumulates the element's value; after the
//!   element's 31st bit it sends `(ctr, e, value)` on `p2v`.  The rows of a
//!   call form a chain on `p2i` from `(ctr, 0, 0)` to `(ctr, 496, 0)`, which
//!   the CPU's jet row starts and ends.
//! - **P2OUT**, one row per output bit: it writes the bit's stack cell,
//!   accumulates the element's value, checks the bits are its canonical
//!   binary (below `p`), and after the element's 31st bit receives `(ctr,
//!   e, value)` on `p2w`.  A chain on `p2o`, as P2IN's.
//! - **P2**, the permutation (`src/p2air.rs`), keyed by the call's counter:
//!   it receives the sixteen inputs on `p2v` and sends the sixteen outputs on
//!   `p2w`.
//! - **P2IDX**, public: for each level `0 … 495`, the element, the power of
//!   two, and whether the bit is an element's last, among its low 27, or the
//!   call's last.
//!
//! P2IN, P2OUT and P2 are private; each carries blinding blocks, the
//! blinding tree's edges `CPU —c— P2IN —d— P2OUT —e— P2` (`PI_BLOCKS`,
//! `PO_BLOCKS`, `P2_BLOCKS`), as the composed circuit's tables do
//! `WIT —a— CPU —b— MEM`.  P2IDX is public, its multiplicities fixed by
//! the number of calls.

use super::*;
use crate::seed::{BlindStream, PcsStreams, ProverSeed};
use composed::{nums, parse_cell, RestartPub, SegsAir, RESTART_WIDTH};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;
use p3_uni_stark::StarkGenericConfig;
use sudoku::{blind_tuple, public_zk_config, secret_zk_config, set_blind, widen, ZkConfig};
use witness::{witness_rows, WitTAir, WT_BLIND};

/// The CPU's jet columns: `P2SEL`, then the blinding block it sends to
/// P2IN on `blind_c`.
pub const P2_CPU_WIDTH: usize = 1 + BLIND_WIDTH;
/// The inputs' bits.
pub const P2_BITS: usize = 496;
/// The first bit's slot.
pub const P2_SLOT0: u32 = 3;
pub const P2I: &str = "p2i";
pub const P2O: &str = "p2o";
pub const P2V: &str = "p2v";
pub const P2W: &str = "p2w";
pub const P2IDX: &str = "p2idx";

/// What the CPU's jet row needs of the statement: the jet's atom and the
/// comb's root.
#[derive(Clone, Debug)]
pub struct P2Pub {
    pub j: u32,
    pub root: u32,
}

// ---------------------------------------------------------------------------
// The CPU's jet row
// ---------------------------------------------------------------------------

/// The jet row's constraints and messages; returns its parts of the next
/// head, stack and counter.  The row's reads are the CPU's reads 0, 1 and
/// 2: the atom `J` at the head (`a0 = J`), the stack cell `cons k s₁`, and
/// the cell `cons β rest` at `s₁`, with `β` the comb's root.
pub fn eval_cpu_p2<AB: PermutationAirBuilder + InteractionBuilder>(
    b: &mut AB,
    loc: &[AB::Expr],
    p2sel: AB::Expr,
    base: usize,
    pp: &P2Pub,
) -> (AB::Expr, AB::Expr, AB::Expr) {
    let c = |n: u32| AB::Expr::from_u32(n);
    let ctr = loc[CTR].clone();
    let (a0, a1, a2, rest) = (loc[FLD].clone(), loc[FLD + 2].clone(), loc[FLD + 4].clone(), loc[FLD + 5].clone());
    b.assert_zero(p2sel.clone() * (a0 - c(pp.j)));
    b.assert_zero(p2sel.clone() * (a2 - c(pp.root)));
    // The slots: `K`, `I`, `K I` at 0, 1, 2.
    b.push_interaction(BUS, [c(0), c(1), c(0), c(0)], Count::bounded(p2sel.clone(), 1));
    b.push_interaction(BUS, [c(1), c(2), c(0), c(0)], Count::bounded(p2sel.clone(), 1));
    b.push_interaction(BUS, [c(2), c(3), c(0), c(1)], Count::bounded(p2sel.clone(), 1));
    // The input chain.
    b.push_interaction(P2I, [ctr.clone(), c(0), c(0)], Count::bounded(p2sel.clone(), 1));
    b.push_interaction(P2I, [ctr.clone(), c(P2_BITS as u32), c(0)], -Count::bounded(p2sel.clone(), 1));
    // The output chain.
    b.push_interaction(P2O, [ctr.clone(), c(0), rest.clone(), c(0), c(0), c(1)], Count::bounded(p2sel.clone(), 1));
    b.push_interaction(
        P2O,
        [ctr.clone(), c(P2_BITS as u32), rest, c(0), c(0), c(1)],
        -Count::bounded(p2sel.clone(), 1),
    );
    // The blinding tree's edge to P2IN.
    blind_msg(b, loc, base + 1, BLIND_C, true);
    (
        p2sel.clone() * a1,
        p2sel.clone() * (ctr.clone() + c(P2_BITS as u32 - 1)),
        p2sel * c(P2_BITS as u32),
    )
}

// ---------------------------------------------------------------------------
// The jet's tables
// ---------------------------------------------------------------------------

/// P2IN's columns, before its blinding blocks.
pub const PI_W: usize = 13;
/// P2OUT's columns, before its blinding blocks.
pub const PO_W: usize = 23;

/// The jet tables' blinding blocks, their edges in the blinding tree
/// `CPU —c— P2IN —d— P2OUT —e— P2`: a received message (the edge to the
/// parent), then a sent one (the edge to the child).
pub const PI_BLOCKS: [(&str, bool); 2] = [("blind_c", false), ("blind_d", true)];
pub const PO_BLOCKS: [(&str, bool); 2] = [("blind_d", false), ("blind_e", true)];
pub const P2_BLOCKS: [(&str, bool); 1] = [("blind_e", false)];

/// A table's blinding blocks, after its first `base` columns.
pub fn eval_blocks<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB, base: usize, blocks: &[(&str, bool)]) {
    let main = b.main();
    let loc: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    for (i, &(bus, send)) in blocks.iter().enumerate() {
        blind_msg(b, &loc, base + BLIND_WIDTH * i, bus, send);
    }
}

/// P2IN: `ctr lvl b acc act e pow last islow ilast val nacc em`.  The bit
/// `lvl` is the slot `3 + lvl`: a `K` cell when true, the cell `app 0 1`
/// when false.
pub fn eval_p2in<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let one = AB::Expr::ONE;
    let c = |n: u32| AB::Expr::from_u32(n);
    let v = |i: usize| l[i].clone();
    let (ctr, lvl, bit, acc, act) = (v(0), v(1), v(2), v(3), v(4));
    let (e, pow, last, islow, ilast) = (v(5), v(6), v(7), v(8), v(9));
    let (val, nacc, em) = (v(10), v(11), v(12));
    b.assert_bool(act.clone());
    b.assert_bool(bit.clone());
    b.assert_eq(val.clone(), acc.clone() + pow.clone() * bit.clone());
    b.assert_eq(nacc.clone(), (one.clone() - last.clone()) * val.clone());
    b.assert_eq(em.clone(), act.clone() * last.clone());
    b.push_interaction(P2IDX, [lvl.clone(), e.clone(), pow, last, islow, ilast], Count::bounded(act.clone(), 1));
    b.push_interaction(P2I, [ctr.clone(), lvl.clone(), acc], -Count::bounded(act.clone(), 1));
    b.push_interaction(P2I, [ctr.clone(), lvl.clone() + one.clone(), nacc], Count::bounded(act.clone(), 1));
    b.push_interaction(
        BUS,
        [lvl + c(P2_SLOT0), c(3) - bit.clone() * c(2), c(0), one - bit],
        Count::bounded(act, 1),
    );
    b.push_interaction(P2V, [ctr, e, val], Count::bounded(em, 1));
}

/// P2OUT: `ctr lvl rest b acc low hi act e pow last islow ilast val nacc
/// nlow nhi nlowr nhir em addr prev ptr`.
pub fn eval_p2out<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let one = AB::Expr::ONE;
    let c = |n: u32| AB::Expr::from_u32(n);
    let v = |i: usize| l[i].clone();
    let (ctr, lvl, rest, bit, acc, low, hi, act) = (v(0), v(1), v(2), v(3), v(4), v(5), v(6), v(7));
    let (e, pow, last, islow, ilast) = (v(8), v(9), v(10), v(11), v(12));
    let (val, nacc, nlow, nhi, nlowr, nhir, em, addr, prev, ptr) =
        (v(13), v(14), v(15), v(16), v(17), v(18), v(19), v(20), v(21), v(22));
    b.assert_bool(act.clone());
    b.assert_bool(bit.clone());
    b.assert_eq(val.clone(), acc.clone() + pow.clone() * bit.clone());
    b.assert_eq(nacc.clone(), (one.clone() - last.clone()) * val.clone());
    // Canonical: the high four bits all set leave the low 27 all clear.
    b.assert_eq(nlow.clone(), low.clone() + islow.clone() * bit.clone() * (one.clone() - low.clone()));
    b.assert_eq(nhi.clone(), hi.clone() * (islow.clone() + (one.clone() - islow.clone()) * bit.clone()));
    b.assert_zero(last.clone() * nhi.clone() * nlow.clone());
    b.assert_eq(nlowr.clone(), (one.clone() - last.clone()) * nlow);
    b.assert_eq(nhir.clone(), (one.clone() - last.clone()) * nhi + last.clone());
    b.assert_eq(em.clone(), act.clone() * last.clone());
    // The bit's stack cell: the output bit `lvl` sits at `ctr + 495 - lvl`,
    // over the cell below it, or over the rest at the bottom.
    b.assert_zero(act.clone() * (addr.clone() - (ctr.clone() + c(P2_BITS as u32 - 1) - lvl.clone())));
    b.assert_zero(
        act.clone()
            * (prev.clone() - (ilast.clone() * rest.clone() + (one.clone() - ilast.clone()) * (addr.clone() - one.clone()))),
    );
    b.assert_zero(act.clone() * (ptr.clone() - (c(2) - c(2) * bit.clone())));
    b.push_interaction(P2IDX, [lvl.clone(), e.clone(), pow, last, islow, ilast], Count::bounded(act.clone(), 1));
    b.push_interaction(P2O, [ctr.clone(), lvl.clone(), rest.clone(), acc, low, hi], -Count::bounded(act.clone(), 1));
    b.push_interaction(P2O, [ctr.clone(), lvl + one, rest, nacc, nlowr, nhir], Count::bounded(act.clone(), 1));
    b.push_interaction(BUS, [addr, c(5), ptr, prev], Count::bounded(act, 1));
    b.push_interaction(P2W, [ctr, e, val], -Count::bounded(em, 1));
}

/// P2IDX's rows: `lvl e pow last islow ilast` for each level.
pub fn idx_pre() -> Vec<[u32; 6]> {
    let mut pre: Vec<[u32; 6]> = (0..P2_BITS as u32)
        .map(|l| {
            let j = l % 31;
            [l, l / 31, 1 << j, (j == 30) as u32, (j < 27) as u32, (l == P2_BITS as u32 - 1) as u32]
        })
        .collect();
    let first = pre[0];
    pre.resize(512, first);
    pre
}

pub fn eval_p2idx<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
    let main = b.main();
    let mult: AB::Expr = main.current_slice()[0].into();
    b.push_interaction(P2IDX, pre, Count::provided(-mult));
}

// ---------------------------------------------------------------------------
// The machine's jet step
// ---------------------------------------------------------------------------

/// A call of the jet: what its rows record.
#[derive(Clone, Debug)]
pub struct P2Call {
    ctr: u32,
    stk: u32,
    k: u32,
    s1: u32,
    rest: u32,
    bits: Vec<bool>,
    /// The inputs the P2 table permutes: the bits' elements, but for a
    /// forgery.
    p2_ins: [u32; 16],
    out_bits: Vec<bool>,
}

/// A forgery, for the tamper tests: the jet's outputs are the permutation
/// of the inputs with bit 0 flipped, and the P2 table permutes the true
/// inputs (`W`: its outputs disagree with P2OUT's) or the flipped ones
/// (`V`: its inputs disagree with P2IN's).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Forge {
    None,
    W,
    V,
}

/// The jet's step at `(hd, stk)`, when the head is the atom `pp.j` with `k`
/// and the root `pp.root` on the stack, the slots in place and each bit's
/// slot a `K` cell or the cell `app 0 1`: the next head and stack, the
/// cells written, and the call.
pub fn p2_step(heap: &[Cell], hd: u32, stk: u32, pp: &P2Pub, forge: Forge) -> Option<(u32, u32, Vec<Cell>, P2Call)> {
    if heap.get(hd as usize) != Some(&Cell::Atom(pp.j)) {
        return None;
    }
    if heap.len() < (P2_SLOT0 as usize) + P2_BITS
        || heap[0] != Cell::K
        || heap[1] != Cell::I
        || heap[2] != Cell::App(0, 1)
    {
        return None;
    }
    let Cell::Cons(k, s1) = *heap.get(stk as usize)? else { return None };
    let Cell::Cons(beta, rest) = *heap.get(s1 as usize)? else { return None };
    if beta != pp.root {
        return None;
    }
    let bits: Vec<bool> = (0..P2_BITS)
        .map(|l| match heap[P2_SLOT0 as usize + l] {
            Cell::K => Some(true),
            Cell::App(0, 1) => Some(false),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let mut ins = [0u32; 16];
    for e in 0..16 {
        ins[e] = (0..31).map(|jb| (bits[31 * e + jb] as u32) << jb).sum();
    }
    let mut fins = ins;
    if forge != Forge::None {
        fins[0] ^= 1;
    }
    let p2_ins = if forge == Forge::V { fins } else { ins };
    let mut state: [Val; 16] = std::array::from_fn(|e| Val::from_u32(fins[e]));
    default_babybear_poseidon2_16().permute_mut(&mut state);
    let outs: [u32; 16] = std::array::from_fn(|e| state[e].as_canonical_u32());
    let out_bits: Vec<bool> = outs.iter().flat_map(|&y| (0..31).map(move |jb| (y >> jb) & 1 == 1)).collect();
    let c = heap.len() as u32;
    let ptr = |b: bool| if b { 0 } else { 2 };
    let cells: Vec<Cell> = (0..P2_BITS)
        .map(|m| Cell::Cons(ptr(out_bits[P2_BITS - 1 - m]), if m == 0 { rest } else { c + m as u32 - 1 }))
        .collect();
    let call = P2Call { ctr: c, stk, k, s1, rest, bits, p2_ins, out_bits };
    Some((k, c + P2_BITS as u32 - 1, cells, call))
}

// ---------------------------------------------------------------------------
// The statement
// ---------------------------------------------------------------------------

pub struct PPublic {
    header: String,
    pp: P2Pub,
    w: u32,
    logs: [usize; 5],
    nbits: u32,
    roots: Vec<u32>,
    nil: u32,
    hd0: u32,
    stk0: u32,
    ctr0: u32,
    cells: Vec<Option<Cell>>,
    text: String,
}

/// The statement's text, parsed; `lake exe composed statement-p2` checks it
/// is exactly the statement it names.
pub fn parse_public_p(text: &str) -> Result<PPublic, String> {
    let mut ls = text.lines();
    let mut next = || ls.next().ok_or_else(|| "a truncated statement".to_string());
    let header = next()?.to_string();
    let hw: Vec<&str> = header.split(' ').collect();
    let num = |x: &str| x.parse::<u32>().map_err(|_| "a bad header".to_string());
    // `p2pre h J ROOT` or `p2commit c₀ … c₇ PATTERN J ROOT`: the statement's
    // kind and data, then the jet's atom and the comb's root.  Lean checks
    // the whole text (`statement-p2`).
    let pp = match (hw.first(), hw.len()) {
        (Some(&"p2pre"), 4) | (Some(&"p2commit"), 12) => {
            P2Pub { j: num(hw[hw.len() - 2])?, root: num(hw[hw.len() - 1])? }
        }
        _ => return Err("expected `p2pre h J ROOT` or `p2commit c₀ … c₇ PATTERN J ROOT`".into()),
    };
    let w = nums(next()?, "W")?;
    let lg = nums(next()?, "log")?;
    if lg.len() != 5 || lg.iter().any(|&x| !(8..=20).contains(&x)) {
        return Err("a bad `log` line".into());
    }
    let nbits = nums(next()?, "bits")?;
    let roots = nums(next()?, "roots")?;
    let nil = nums(next()?, "nil")?;
    let regs: Vec<u32> =
        next()?.split(' ').map(|x| x.parse().map_err(|_| "a bad register".to_string())).collect::<Result<_, _>>()?;
    if w.len() != 1 || nbits.len() != 1 || nil.len() != 1 || regs.len() != 3 || roots.is_empty() {
        return Err("a malformed header".into());
    }
    let (w, nbits, nil) = (w[0], nbits[0], nil[0]);
    if regs[2] > 1 << 24 {
        return Err("a heap past 2^24 cells".into());
    }
    let mut cells = Vec::with_capacity(regs[2] as usize);
    for _ in 0..regs[2] {
        let l = next()?;
        cells.push(if l == "W" { None } else { Some(parse_cell(l)?) });
    }
    for (i, c) in cells.iter().enumerate() {
        let blank = (i as u32) >= 3 && (i as u32) < 3 + nbits + w;
        if c.is_none() != blank {
            return Err("the bits and the region are not exactly the blank cells".into());
        }
    }
    let logs = [lg[0] as usize, lg[1] as usize, lg[2] as usize, lg[3] as usize, lg[4] as usize];
    Ok(PPublic { header, pp, w, logs, nbits, roots, nil, hd0: regs[0], stk0: regs[1], ctr0: regs[2], cells, text: text.to_string() })
}

fn program_of(p: &PPublic) -> Vec<[u32; 5]> {
    let mut pre: Vec<[u32; 5]> = p
        .cells
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            c.map(|c| {
                let (a, b) = c.fields();
                [i as u32, c.tag(), a, b, 1]
            })
        })
        .collect();
    pre.resize(pow2_at_least(pre.len(), 8), [0, 0, 0, 0, 0]);
    pre
}

/// The witness table's height: the private cells, at least `2^8`.
fn log_wit(p: &PPublic) -> usize {
    p3_util::log2_strict_usize(pow2_at_least((p.nbits + p.w) as usize, 8))
}

fn wit_pre(p: &PPublic) -> Vec<[u32; 3]> {
    let mut pre: Vec<[u32; 3]> = (0..p.nbits).map(|i| [3 + i, 1, 1]).collect();
    pre.extend((0..p.w).map(|i| [3 + p.nbits + i, 1, 0]));
    pre.resize(1 << log_wit(p), [0, 0, 0]);
    pre
}

fn segs_pre(p: &PPublic) -> Vec<[u32; 2]> {
    let mut pre: Vec<[u32; 2]> = p.roots.iter().enumerate().map(|(j, &r)| [j as u32, r]).collect();
    let first = pre[0];
    pre.resize(pow2_at_least(pre.len(), 8), first);
    pre
}

fn airs(p: &PPublic) -> Vec<SkiAir> {
    vec![
        SkiAir::Cpu(CpuAir {
            hd0: p.hd0,
            stk0: p.stk0,
            ctr0: p.ctr0,
            accept: None,
            accept_k: true,
            blind: true,
            jets: false,
            probe: None,
            restart: Some(RestartPub { n: p.roots.len() as u32, nil: p.nil }),
            p2: Some(p.pp.clone()),
        }),
        SkiAir::Mem(MemAir { blind: true }),
        SkiAir::Prog(ProgAir { pre: program_of(p) }),
        SkiAir::WitT(WitTAir { pre: wit_pre(p) }),
        SkiAir::Segs(SegsAir { pre: segs_pre(p) }),
        SkiAir::P2In,
        SkiAir::P2Out,
        SkiAir::P2(true),
        SkiAir::P2Idx(idx_pre()),
    ]
}

// ---------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------

struct PTable {
    rows: Vec<[u32; 3]>,
    restarts: Vec<usize>,
    /// The jet's rows and their calls.
    calls: Vec<(usize, P2Call)>,
    mem: Vec<Cell>,
    run_rows: usize,
    run_mem: usize,
}

fn table(p: &PPublic, mut heap: Vec<Cell>, forge: Forge) -> Result<PTable, String> {
    let (mut rows, mut restarts, mut calls) = (Vec::new(), Vec::new(), Vec::new());
    for (jx, &root) in p.roots.iter().enumerate() {
        let (mut hd, mut stk) = (root, p.nil);
        loop {
            if rows.len() >= 1 << 22 {
                return Err("the run exceeds 2^22 rows".into());
            }
            rows.push([hd, stk, heap.len() as u32]);
            if let Some((h, s, ws, call)) = p2_step(&heap, hd, stk, &p.pp, forge) {
                calls.push((rows.len() - 1, call));
                heap.extend(ws);
                hd = h;
                stk = s;
                continue;
            }
            match step(&heap, hd, stk) {
                None => break,
                Some((h, s, ws)) => {
                    heap.extend(ws);
                    hd = h;
                    stk = s;
                }
            }
        }
        if jx + 1 < p.roots.len() {
            restarts.push(rows.len() - 1);
        }
    }
    let (run_rows, run_mem) = (rows.len(), heap.len());
    if run_rows > 1 << p.logs[0]
        || run_mem > 1 << p.logs[1]
        || P2_BITS * calls.len() > 1 << p.logs[2].min(p.logs[3])
        || calls.len() > 1 << p.logs[4]
    {
        return Err(format!(
            "the run ({run_rows} rows, {run_mem} memory cells, {} jet calls) does not fit the statement's heights {:?}",
            calls.len(),
            p.logs
        ));
    }
    let last = *rows.last().unwrap();
    rows.resize(1 << p.logs[0], last);
    heap.resize(1 << p.logs[1], Cell::Nil);
    Ok(PTable { rows, restarts, calls, mem: heap, run_rows, run_mem })
}

fn traces(p: &PPublic, tb: &PTable, blind: bool, bs: BlindStream) -> Vec<RowMajorMatrix<Val>> {
    let mut mult = vec![0u32; tb.mem.len()];
    let cpu0 = cpu_trace(&tb.rows, &tb.mem, &mut mult);
    let mut cpu = widen(cpu0, 2 * BLIND_WIDTH + RESTART_WIDTH + P2_CPU_WIDTH);
    let w = cpu.width;
    let rbase = CPU_WIDTH + 2 * BLIND_WIDTH;
    let pbase = rbase + RESTART_WIDTH;
    let mut cnt = 0u32;
    let mut used: std::collections::HashMap<[u32; 2], u32> = std::collections::HashMap::new();
    for i in 0..tb.rows.len() {
        let r = &mut cpu.values[i * w..(i + 1) * w];
        r[rbase + 1] = f(cnt);
        if tb.restarts.contains(&i) {
            for k in 0..NKINDS {
                r[SEL + k] = Val::ZERO;
            }
            r[rbase] = Val::ONE;
            let next = p.roots[cnt as usize + 1];
            r[rbase + 2] = f(next);
            *used.entry([cnt + 1, next]).or_default() += 1;
            cnt += 1;
        }
    }
    // The jet's rows: the atom at the head classified as a halt; it is the
    // jet's instead, and reads the two stack cells too, and the slots.
    for (i, call) in &tb.calls {
        let r = &mut cpu.values[i * w..(i + 1) * w];
        for k in 0..NKINDS {
            r[SEL + k] = Val::ZERO;
        }
        r[pbase] = Val::ONE;
        for (j, (addr, a, b)) in [(1usize, (call.stk, call.k, call.s1)), (2, (call.s1, p.pp.root, call.rest))] {
            r[FLD + 2 * j] = f(a);
            r[FLD + 2 * j + 1] = f(b);
            let d = call.ctr - addr - 1;
            for k in 0..RANGE_BITS {
                r[BITS + j * RANGE_BITS + k] = f((d >> k) & 1);
            }
            mult[addr as usize] += 1;
        }
        for a in 0..3 {
            mult[a] += 1;
        }
    }
    // P2IN, P2OUT, P2.
    let hin = 1 << p.logs[2];
    let hout = 1 << p.logs[3];
    let mut pin = vec![Val::ZERO; hin * PI_W];
    let mut pout = vec![Val::ZERO; hout * PO_W];
    let mut p2rows: Vec<([Val; 16], u32, u32)> = Vec::new();
    let idx = idx_pre();
    let mut idx_mult = vec![0u32; idx.len()];
    for (ci, (_, call)) in tb.calls.iter().enumerate() {
        let mut acc = 0u32;
        let (mut oacc, mut low, mut hi) = (0u32, 0u32, 1u32);
        for l in 0..P2_BITS {
            let [_, e, pow, last, islow, ilast] = idx[l];
            idx_mult[l] += 2;
            // P2IN
            let b = call.bits[l] as u32;
            let val = acc + pow * b;
            let nacc = if last == 1 { 0 } else { val };
            let row = &mut pin[(ci * P2_BITS + l) * PI_W..(ci * P2_BITS + l + 1) * PI_W];
            let v = [call.ctr, l as u32, b, acc, 1, e, pow, last, islow, ilast, val, nacc, last];
            for (k, &x) in v.iter().enumerate() {
                row[k] = f(x);
            }
            mult[P2_SLOT0 as usize + l] += 1;
            acc = nacc;
            // P2OUT
            let ob = call.out_bits[l] as u32;
            let oval = oacc + pow * ob;
            let onacc = if last == 1 { 0 } else { oval };
            let nlow = low + islow * ob * (1 - low);
            let nhi = hi * (islow + (1 - islow) * ob);
            assert!(!(last == 1 && nhi == 1 && nlow == 1), "an output not below p");
            let nlowr = if last == 1 { 0 } else { nlow };
            let nhir = if last == 1 { 1 } else { nhi };
            let addr = call.ctr + P2_BITS as u32 - 1 - l as u32;
            let prev = if ilast == 1 { call.rest } else { addr - 1 };
            let ptr = 2 - 2 * ob;
            let row = &mut pout[(ci * P2_BITS + l) * PO_W..(ci * P2_BITS + l + 1) * PO_W];
            let v = [
                call.ctr, l as u32, call.rest, ob, oacc, low, hi, 1, e, pow, last, islow, ilast, oval, onacc, nlow, nhi,
                nlowr, nhir, last, addr, prev, ptr,
            ];
            for (k, &x) in v.iter().enumerate() {
                row[k] = f(x);
            }
            mult[addr as usize] += 1;
            oacc = onacc;
            low = nlowr;
            hi = nhir;
        }
        p2rows.push((std::array::from_fn(|e| Val::from_u32(call.p2_ins[e])), call.ctr, 1));
    }
    let mut p2 = widen(p2air::p2_trace_keyed(&p2rows, p.logs[4]), BLIND_WIDTH);
    let mut pin = widen(RowMajorMatrix::new(pin, PI_W), 2 * BLIND_WIDTH);
    let mut pout = widen(RowMajorMatrix::new(pout, PO_W), 2 * BLIND_WIDTH);
    // Program, witness, memory.
    let pre = program_of(p);
    for r in &pre {
        if r[4] == 1 {
            mult[r[0] as usize] += 1;
        }
    }
    let addrs: Vec<u32> = wit_pre(p).iter().filter(|r| r[1] == 1).map(|r| r[0]).collect();
    let mut wit = witness_rows(&addrs, 1 << log_wit(p), &tb.mem, &mut mult);
    let mut mem = Vec::with_capacity(tb.mem.len() * 5);
    for (i, cell) in tb.mem.iter().enumerate() {
        let (a, b) = cell.fields();
        mem.extend([f(i as u32), f(cell.tag()), f(a), f(b), f(mult[i])]);
    }
    let mut mem = widen(RowMajorMatrix::new(mem, 5), BLIND_WIDTH);
    if blind {
        let mut rng = bs;
        let (ba, bb) = (blind_tuple(&mut rng), blind_tuple(&mut rng));
        set_blind(&mut wit, WT_BLIND, ba);
        set_blind(&mut cpu, CPU_BLA, ba);
        set_blind(&mut cpu, CPU_BLB, bb);
        set_blind(&mut mem, 5, bb);
        // The jet tables' edges: CPU —c— P2IN —d— P2OUT —e— P2.
        let (tc, td, te) = (blind_tuple(&mut rng), blind_tuple(&mut rng), blind_tuple(&mut rng));
        set_blind(&mut cpu, pbase + 1, tc);
        set_blind(&mut pin, PI_W, tc);
        set_blind(&mut pin, PI_W + BLIND_WIDTH, td);
        set_blind(&mut pout, PO_W, td);
        set_blind(&mut pout, PO_W + BLIND_WIDTH, te);
        set_blind(&mut p2, p2air::P2_WIDTH, te);
    }
    let sp = segs_pre(p);
    let mut seen = std::collections::HashSet::new();
    let segs = sp.iter().map(|r| if seen.insert(*r) { f(*used.get(r).unwrap_or(&0)) } else { Val::ZERO }).collect();
    // P2IDX's multiplicities, on each tuple's first row.
    let mut seen_i = std::collections::HashSet::new();
    let idxm: Vec<Val> = idx
        .iter()
        .enumerate()
        .map(|(l, r)| if seen_i.insert(*r) { f(if l < P2_BITS { idx_mult[l] } else { 0 }) } else { Val::ZERO })
        .collect();
    vec![
        cpu,
        mem,
        RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1),
        wit,
        RowMajorMatrix::new(segs, 1),
        pin,
        pout,
        p2,
        RowMajorMatrix::new(idxm, 1),
    ]
}

fn heights(p: &PPublic, zk: usize) -> Vec<usize> {
    let lg = |n: usize| p3_util::log2_strict_usize(n);
    vec![
        p.logs[0] + zk,
        p.logs[1] + zk,
        lg(program_of(p).len()) + zk,
        log_wit(p) + zk,
        lg(segs_pre(p).len()) + zk,
        p.logs[2] + zk,
        p.logs[3] + zk,
        p.logs[4] + zk,
        9 + zk,
    ]
}

/// The verifier's nine AIRs for a statement, in the export format of
/// `src/export.rs`, after the statement's text.
fn export_airs(p: &PPublic, v_airs: &[SkiAir]) -> String {
    let mut s = format!("public {}\n{}", p.text.lines().count(), p.text);
    if !p.text.ends_with('\n') {
        s.push('\n');
    }
    for (n, a) in ["cpu", "mem", "prog", "wit", "segs", "p2in", "p2out", "p2", "p2idx"].iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

/// `ski-air export-compp PUBLIC`.
pub fn export_compp(text: &str) -> Result<String, String> {
    let p = parse_public_p(text)?;
    Ok(export_airs(&p, &airs(&p)))
}

type PProof = p3_batch_stark::BatchProof<ZkConfig>;

fn prove(p: &PPublic, tr: &[RowMajorMatrix<Val>], ps: PcsStreams) -> Result<(PProof, f64), String> {
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = secret_zk_config(ps);
        let a = airs(p);
        let t0 = Instant::now();
        let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&public_zk_config(), &a, &heights(p, config.is_zk()))
            .map_err(|e| format!("setup: {e:?}"))?;
        let trs: Vec<&RowMajorMatrix<Val>> = tr.iter().collect();
        let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &trs, &crate::stmt::public_values(&a)), &pd)
            .map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    match proved {
        Ok(r) => r,
        Err(e) => Err(format!("panic: {}", panic_text(&e))),
    }
}

/// The verifier: the public statement and the proof, nothing else.  It
/// rebuilds its AIRs from the statement, checks them against the Lean
/// circuit (`lake exe circuit compare-compp`), and accepts only the
/// statement's heights.
fn verify(p: &PPublic, proof: &PProof) -> Result<(), String> {
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let v_config = public_zk_config();
        let v_airs = airs(p);
        lean_statement("circuit", &["compare-compp", "-"], export_airs(p, &v_airs).as_bytes())?;
        let want = heights(p, v_config.is_zk());
        if proof.degree_bits != want {
            return Err(format!("heights {:?}, the statement's are {want:?}", proof.degree_bits));
        }
        let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &want)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        verify_batch(&v_config, &v_airs, proof, &crate::stmt::public_values(&v_airs), &v_data.common)
            .map_err(|e| format!("verify: {e:?}"))
    }));
    match verified {
        Ok(r) => r,
        Err(e) => Err(format!("verifier panic: {}", panic_text(&e))),
    }
}

/// `ski-air compp-prove PUBLIC WITNESS PROOF`: prove the statement for the
/// prover's bits and region, write the proof, and check it verifies.
pub fn compp_prove(public: &std::path::Path, wit: &std::path::Path, proof_out: &std::path::Path, forge: Forge,
    table_out: Option<&std::path::Path>) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-p2", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_p(&text)?;
    let wtext = std::fs::read_to_string(wit).map_err(|e| format!("{}: {e}", wit.display()))?;
    let ls: Vec<&str> = wtext.lines().filter(|l| !l.is_empty()).collect();
    if ls.len() != (p.nbits + p.w) as usize {
        return Err(format!("{}: {} lines, not {}", wit.display(), ls.len(), p.nbits + p.w));
    }
    let private: Vec<Cell> = ls
        .iter()
        .enumerate()
        .map(|(i, l)| {
            if (i as u32) < p.nbits {
                match *l {
                    "1" => Ok(Cell::K),
                    "0" => Ok(Cell::App(0, 1)),
                    other => parse_cell(other),
                }
            } else {
                parse_cell(l)
            }
        })
        .collect::<Result<_, _>>()?;
    let heap: Vec<Cell> = p.cells.iter().enumerate().map(|(i, c)| c.unwrap_or_else(|| private[i - 3])).collect();
    let tb = match table(&p, heap, forge) {
        Ok(t) => t,
        Err(e) => {
            if std::env::var("COMPP_DEBUG").is_ok() {
                let mut q = PPublic { logs: [22, 22, 20, 20, 20], ..parse_public_p(&text)? };
                q.logs = [22, 22, 20, 20, 20];
                let heap2: Vec<Cell> = q.cells.iter().enumerate().map(|(i, c)| c.unwrap_or_else(|| private[i - 3])).collect();
                if let Ok(t) = table(&q, heap2, forge) {
                    let [hd, stk, _] = t.rows[t.run_rows - 1];
                    let mut depth = 0;
                    let mut cur = stk;
                    let mut args = Vec::new();
                    while let Cell::Cons(x, r) = t.mem[cur as usize] {
                        depth += 1;
                        if args.len() < 5 {
                            let c = t.mem[x as usize];
                            let sub = match c { Cell::App(a, b) => Some((t.mem[a as usize], t.mem[b as usize])), _ => None };
                            args.push((x, c, sub));
                        }
                        cur = r;
                    }
                    eprintln!("final: head {hd} = {:?}, {depth} arguments, {} calls; slots {:?}; first {:?}", t.mem[hd as usize], t.calls.len(), &t.mem[0..3], args);
                }
            }
            return Err(e);
        }
    };
    if std::env::var("COMPP_DEBUG").is_ok() {
        let [hd, stk, _] = tb.rows[tb.run_rows - 1];
        let mut depth = 0;
        let mut cur = stk;
        let mut args = Vec::new();
        while let Cell::Cons(x, r) = tb.mem[cur as usize] {
            depth += 1;
            if args.len() < 4 { args.push((x, tb.mem[x as usize])); }
            cur = r;
        }
        eprintln!("final: head {hd} = {:?}, {depth} arguments, first {:?}", tb.mem[hd as usize], args);
    }
    let [hd, stk, _] = tb.rows[tb.run_rows - 1];
    if (tb.mem[hd as usize], tb.mem[stk as usize]) != (Cell::K, Cell::Nil) {
        return Err("the run does not end at K over a nil: the witness does not satisfy the statement".into());
    }
    one_call(&tb)?;
    if let Some(t) = table_out {
        std::fs::write(t, lean_table(&p, &tb)).map_err(|e| format!("{}: {e}", t.display()))?;
    }
    let (bs, ps) = ProverSeed::fresh().split();
    let (proof, prove_s) = prove(&p, &traces(&p, &tb, true, bs), ps)?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    let t1 = Instant::now();
    verify(&p, &proof)?;
    println!(
        "{}: proved {} rows ({} jet calls), {} memory cells, in {prove_s:.2} s; verified in {:.3} s; proof {} bytes -> {}",
        p.header,
        tb.run_rows,
        tb.calls.len(),
        tb.run_mem,
        t1.elapsed().as_secs_f64(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// `ski-air compp-verify PUBLIC PROOF`: check the statement, then the proof
/// against the AIRs built from it alone.
pub fn compp_verify(public: &std::path::Path, proof: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    let bytes = std::fs::read(proof).map_err(|e| format!("{}: {e}", proof.display()))?;
    verify_text(&text, &bytes)
}

/// Check a statement's text, then the proof's bytes against the AIRs built
/// from that same text.
fn verify_text(text: &str, bytes: &[u8]) -> Result<(), String> {
    let text = text.to_string();
    lean_statement("composed", &["statement-p2", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_p(&text)?;
    let proof: PProof = postcard::from_bytes(bytes).map_err(|e| format!("deserialize: {e}"))?;
    let t0 = Instant::now();
    verify(&p, &proof)?;
    println!("{}: VERIFIED in {:.3} s", p.header, t0.elapsed().as_secs_f64());
    Ok(())
}

/// `ski-air compp-chain PUBLIC1 PROOF1 PUBLIC2 PROOF2`: the hidden hand-off.
/// Lean checks that the two statements are `p2commit` statements with one
/// commitment whose patterns meet the chain's conditions (`composed
/// chain-p2`, `P2Commit.chainB`); then each proof verifies against its own
/// statement.  `Circuit.p2commit_chainB` states what the two together prove.
/// Each statement file is read once: Lean's chain check and the proof's
/// verification see the same bytes, whatever the path yields on a later read.
pub fn compp_chain(pub1: &std::path::Path, proof1: &std::path::Path, pub2: &std::path::Path, proof2: &std::path::Path)
    -> Result<(), String> {
    let read = |p: &std::path::Path| std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()));
    let (t1, t2) = (read(pub1)?, read(pub2)?);
    let readb = |p: &std::path::Path| std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()));
    let (b1, b2) = (readb(proof1)?, readb(proof2)?);
    // `chain-p2 -` reads the two texts from stdin, split at a NUL; no
    // statement's text contains one.
    if t1.contains('\0') || t2.contains('\0') {
        return Err("a statement containing a NUL byte".into());
    }
    let ok = lean_statement("composed", &["chain-p2", "-"], format!("{t1}\0{t2}").as_bytes())
        .map_err(|e| format!("chain: {e}"))?;
    verify_text(&t1, &b1)?;
    verify_text(&t2, &b2)?;
    println!("{}", ok.trim_end());
    Ok(())
}

/// The level table's multiplicities, public, count the jet's calls
/// (`Circuit.idxPub`): the verifiers of `p2pre` and `p2commit` call the jet
/// once on every witness that satisfies them (`Circuit.P2Run.calls_one`), so
/// a run with another count is refused rather than proved, lest its proof
/// publish the count.
fn one_call(tb: &PTable) -> Result<(), String> {
    if tb.calls.len() != 1 {
        return Err(format!("the run calls the jet {} times, not once", tb.calls.len()));
    }
    Ok(())
}

/// The table in `lake exe composed check`'s format: the header, `W w`, the
/// memory, `ends n` and the segments' ends (the restarts, then the last
/// row), and the rows.  Avon's `witness --statement` writes the same.
fn lean_table(p: &PPublic, tb: &PTable) -> String {
    let mut s = format!("{}\nW {}\n{}\n", p.header, p.w, tb.mem.len());
    for cell in &tb.mem {
        s.push_str(&cell.lean());
        s.push('\n');
    }
    let mut ends: Vec<usize> = tb.restarts.clone();
    ends.push(tb.rows.len() - 1);
    s.push_str(&format!("ends {}\n", ends.len()));
    for e in ends {
        s.push_str(&format!("{e}\n"));
    }
    s.push_str(&format!("{}\n", tb.rows.len()));
    for [h, st, c] in &tb.rows {
        s.push_str(&format!("{h} {st} {c}\n"));
    }
    s
}

/// A table in `lean_table`'s format, read back: its memory, rows and
/// restarts as the statement's heights fix them, and its jet calls, each a
/// row whose next row and written cells are the jet's step from it.
fn table_of_text(p: &PPublic, text: &str) -> Result<PTable, String> {
    let mut ls = text.lines();
    let mut next = || ls.next().ok_or_else(|| "a truncated table".to_string());
    if next()? != p.header {
        return Err("the table's header is not the statement's".into());
    }
    if next()? != format!("W {}", p.w) {
        return Err("the table's region size is not the statement's".into());
    }
    let msize: usize = next()?.parse().map_err(|_| "a bad memory size")?;
    if msize != 1 << p.logs[1] {
        return Err(format!("the table's memory has {msize} cells, the statement's 2^{}", p.logs[1]));
    }
    let mut mem = Vec::with_capacity(msize);
    for _ in 0..msize {
        mem.push(parse_cell(next()?)?);
    }
    let ne: Vec<u32> = nums(next()?, "ends")?;
    if ne.len() != 1 || ne[0] as usize != p.roots.len() {
        return Err("the table's segment count is not the statement's".into());
    }
    let mut ends = Vec::with_capacity(p.roots.len());
    for _ in 0..p.roots.len() {
        ends.push(next()?.parse::<usize>().map_err(|_| "a bad segment end")?);
    }
    let k: usize = next()?.parse().map_err(|_| "a bad row count")?;
    if k != 1 << p.logs[0] {
        return Err(format!("the table has {k} rows, the statement's 2^{}", p.logs[0]));
    }
    let mut rows = Vec::with_capacity(k);
    for _ in 0..k {
        let r: Vec<u32> =
            next()?.split(' ').map(|x| x.parse().map_err(|_| "a bad row".to_string())).collect::<Result<_, _>>()?;
        if r.len() != 3 {
            return Err("a bad row".into());
        }
        rows.push([r[0], r[1], r[2]]);
    }
    if *ends.last().unwrap() != k - 1 || ends.windows(2).any(|w| w[0] >= w[1]) {
        return Err("the segment ends are not increasing to the last row".into());
    }
    // Every row reads below its counter, within the memory, as the CPU's
    // trace requires.
    for [hd, stk, ctr] in &rows {
        if *ctr as usize > mem.len() || hd >= ctr || stk >= ctr {
            return Err("a row reads at or above its counter, or its counter is past the memory".into());
        }
    }
    let restarts = ends[..ends.len() - 1].to_vec();
    let mut calls = Vec::new();
    for i in 0..k - 1 {
        let [hd, stk, ctr] = rows[i];
        if (ctr as usize) > mem.len() || mem.get(hd as usize) != Some(&Cell::Atom(p.pp.j)) {
            continue;
        }
        if let Some((h, st, ws, call)) = p2_step(&mem[..ctr as usize], hd, stk, &p.pp, Forge::None) {
            let c = ctr as usize;
            if rows[i + 1] == [h, st, ctr + P2_BITS as u32] && mem.get(c..c + ws.len()) == Some(&ws[..]) {
                calls.push((i, call));
            }
        }
    }
    if P2_BITS * calls.len() > 1 << p.logs[2].min(p.logs[3]) || calls.len() > 1 << p.logs[4] {
        return Err(format!("the table's {} jet calls do not fit the statement's heights {:?}", calls.len(), p.logs));
    }
    let last = *rows.last().unwrap();
    let run_rows = rows.iter().rposition(|r| *r != last).map_or(1, |i| i + 2);
    let run_mem = mem.iter().rposition(|c| *c != Cell::Nil).map_or(0, |i| i + 1);
    Ok(PTable { rows, restarts, calls, mem, run_rows, run_mem })
}

/// `ski-air compp-prove-table PUBLIC TABLE PROOF`: prove a table another
/// prover wrote (Avon's `witness --statement`), write the proof, and check
/// it verifies.  The verifier holds only the statement and the proof.
pub fn compp_prove_table(public: &std::path::Path, table: &std::path::Path, proof_out: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-p2", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_p(&text)?;
    let ttext = std::fs::read_to_string(table).map_err(|e| format!("{}: {e}", table.display()))?;
    let tb = table_of_text(&p, &ttext)?;
    one_call(&tb)?;
    let (bs, ps) = ProverSeed::fresh().split();
    let (proof, prove_s) = prove(&p, &traces(&p, &tb, true, bs), ps)?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    let t1 = Instant::now();
    verify(&p, &proof)?;
    // Only a proof that verifies is written.
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    println!(
        "{}: proved the table's {} rows ({} jet calls), {} memory cells, in {prove_s:.2} s; verified in {:.3} s; proof {} bytes -> {}",
        p.header,
        tb.run_rows,
        tb.calls.len(),
        tb.run_mem,
        t1.elapsed().as_secs_f64(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// The guess test for the jet's private tables: P2IN's, P2OUT's and P2's
/// published terminals, against the terminals recomputed from the true
/// witness's tables, unblinded, under the proof's own challenges.  None
/// matches when the proof is blinded; each matches when it is not (the
/// dictionary attack the blinding stops).
fn guess_matches(p: &PPublic, tb: &PTable, blind: bool) -> [bool; 3] {
    use p3_batch_stark::{BatchShape, BatchVerifierTranscript};
    use p3_lookup::{LogUpGadget, LookupProtocol};
    let (bs, ps) = ProverSeed::fresh().split();
    let tr = traces(p, tb, blind, bs);
    let config = secret_zk_config(ps);
    let a = airs(p);
    let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&public_zk_config(), &a, &heights(p, config.is_zk()))
        .expect("setup");
    let trs: Vec<&RowMajorMatrix<Val>> = tr.iter().collect();
    let pvs: Vec<Vec<Val>> = crate::stmt::public_values(&a);
    let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &trs, &pvs), &pd).expect("prove");
    let v_config = public_zk_config();
    let v_airs = airs(p);
    let v_data =
        ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &proof.degree_bits).expect("verifier setup");
    let v_pvs = crate::stmt::public_values(&v_airs);
    verify_batch(&v_config, &v_airs, &proof, &v_pvs, &v_data.common).expect("the honest proof verifies");
    let common = &v_data.common;
    let shape = BatchShape {
        trace_widths: v_airs.iter().map(|x| <SkiAir as BaseAir<Val>>::width(x)).collect(),
        public_value_counts: crate::stmt::public_value_counts(&v_airs),
        preprocessed_widths: v_airs.iter().map(|x| <SkiAir as BaseAir<Val>>::preprocessed_width(x)).collect(),
        has_preprocessed_commitment: true,
        num_lookup_instances: common.lookups.iter().filter(|l| !l.is_empty()).count(),
        lookup_pow_bits: v_config.lookup_proof_of_work_bits(),
        has_randomization_commitment: true,
        ood_pow_bits: v_config.ood_proof_of_work_bits(),
    };
    let mut ch = v_config.initialise_challenger();
    let mut t = BatchVerifierTranscript::<Challenger, Val, Challenge, _>::new(&mut ch, shape);
    t.instance_bindings(&proof.degree_bits);
    t.main_phase(proof.commitments.main.clone(), &v_pvs);
    t.preprocessed_phase(common.preprocessed.as_ref().map(|g| g.commitment.clone()));
    let chs = t.lookup_phase(&common.lookups, &LogUpGadget::new(), proof.lookup_pow_witness).expect("lookup challenges");
    t.abort();
    // The guesser's tables: the true witness's, with the blinding flags clear.
    let (gs, _) = ProverSeed::fresh().split();
    let guess_tr = traces(p, tb, false, gs);
    std::array::from_fn(|i| {
        let k = 5 + i;
        let published = proof.lookup_terminals[k].as_ref().expect("a jet table's terminal").0;
        let guess = LogUpGadget::new()
            .generate_permutation::<Val, Challenge>(&guess_tr[k], &None, &[], &common.lookups[k], &chs[k])
            .1
            .expect("a terminal")
            .0;
        guess == published
    })
}

/// `ski-air compp-guess PUBLIC WITNESS`: the guess test, blinded and as a
/// control unblinded.
pub fn compp_guess(public: &std::path::Path, wit: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-p2", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_p(&text)?;
    let wtext = std::fs::read_to_string(wit).map_err(|e| format!("{}: {e}", wit.display()))?;
    let ls: Vec<&str> = wtext.lines().filter(|l| !l.is_empty()).collect();
    if ls.len() != (p.nbits + p.w) as usize {
        return Err(format!("{}: {} lines, not {}", wit.display(), ls.len(), p.nbits + p.w));
    }
    let private: Vec<Cell> = ls
        .iter()
        .enumerate()
        .map(|(i, l)| match (i < p.nbits as usize, *l) {
            (true, "1") => Ok(Cell::K),
            (true, "0") => Ok(Cell::App(0, 1)),
            _ => parse_cell(l),
        })
        .collect::<Result<_, _>>()?;
    let heap: Vec<Cell> = p.cells.iter().enumerate().map(|(i, c)| c.unwrap_or_else(|| private[i - 3])).collect();
    let tb = table(&p, heap, Forge::None)?;
    let blinded = guess_matches(&p, &tb, true);
    let control = guess_matches(&p, &tb, false);
    let names = ["P2IN", "P2OUT", "P2"];
    for i in 0..3 {
        println!("{}: guess matches the blinded terminal: {}; the unblinded control: {}", names[i], blinded[i], control[i]);
    }
    if blinded.iter().any(|&b| b) || !control.iter().all(|&b| b) {
        return Err("the guess test fails".into());
    }
    println!("the guess test passes: the jet tables' terminals hide the witness");
    Ok(())
}
