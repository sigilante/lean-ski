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
//! The four jet tables carry no blinding blocks yet: this circuit is not yet
//! zero knowledge in its jet tables.

use super::*;
use crate::seed::{BlindStream, PcsStreams, ProverSeed};
use composed::{nums, parse_cell, RestartPub, SegsAir, RESTART_WIDTH};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;
use p3_uni_stark::StarkGenericConfig;
use sudoku::{blind_tuple, public_zk_config, secret_zk_config, set_blind, widen, ZkConfig};
use witness::{witness_rows, WitTAir, WT_BLIND};

/// The CPU's jet column: `P2SEL`.
pub const P2_CPU_WIDTH: usize = 1;
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
    (
        p2sel.clone() * a1,
        p2sel.clone() * (ctr.clone() + c(P2_BITS as u32 - 1)),
        p2sel * c(P2_BITS as u32),
    )
}

// ---------------------------------------------------------------------------
// The jet's tables
// ---------------------------------------------------------------------------

/// P2IN's columns.
pub const PI_W: usize = 13;
/// P2OUT's columns.
pub const PO_W: usize = 23;

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
    h: u32,
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
    let (h, pp) = match hw[..] {
        ["p2pre", h, j, root] => (num(h)?, P2Pub { j: num(j)?, root: num(root)? }),
        _ => return Err("expected `p2pre h J ROOT`".into()),
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
    Ok(PPublic { header, h, pp, w, logs, nbits, roots, nil, hd0: regs[0], stk0: regs[1], ctr0: regs[2], cells, text: text.to_string() })
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
        SkiAir::P2,
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
    let mut p2 = p2air::p2_trace_keyed(&p2rows, p.logs[4]);
    let _ = &mut p2;
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
        RowMajorMatrix::new(pin, PI_W),
        RowMajorMatrix::new(pout, PO_W),
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
pub fn compp_prove(public: &std::path::Path, wit: &std::path::Path, proof_out: &std::path::Path, forge: Forge) -> Result<(), String> {
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
    let _ = p.h;
    Ok(())
}

/// `ski-air compp-verify PUBLIC PROOF`: check the statement, then the proof
/// against the AIRs built from it alone.
pub fn compp_verify(public: &std::path::Path, proof: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-p2", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_p(&text)?;
    let bytes = std::fs::read(proof).map_err(|e| format!("{}: {e}", proof.display()))?;
    let proof: PProof = postcard::from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    let t0 = Instant::now();
    verify(&p, &proof)?;
    println!("{}: VERIFIED in {:.3} s", p.header, t0.elapsed().as_secs_f64());
    Ok(())
}
