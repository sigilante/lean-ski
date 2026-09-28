//! Supercombinator jets: instantiation rows, checked against Lean.
//!
//! The public jet table of a corpus term comes from `lake exe jets emit`
//! (`JetTable.jetTable`): the licensed roots, addresses in the loaded heap
//! where a jet's compiled form sits, and each jet's arity, cell count,
//! root operand and body cells in `ibuild` order, whose operands are a cell
//! the instantiation wrote (`L j`), an argument (`A i`) or a public cell
//! (`G a`).  Every root in a file Lean emits is licensed by `Air.rootOKB`.
//!
//! Five tables join the corpus's three, and the CPU gains a kind, `INST`:
//!
//! - **ROOTS** `(addr, g)`, **HDR** `(g, k, n, root)` and **TMPL**
//!   `(g, j, tag, operand a, operand b)`, preprocessed from the jet table,
//!   each with a committed multiplicity.  An operand is three flags (local,
//!   argument, global) and a value.  Padding rows copy a real row, so a
//!   multiplicity on padding provides only a genuine tuple.
//! - **POP**, one row per popped argument: it reads `C x s'` at `s` from
//!   memory, range-checked below the instantiation's counter `c`, and
//!   provides `ARG(clk, i, x)` as often as the body and root use it.
//! - **INSTW**, one row per written cell: it looks up its template row,
//!   resolves each operand (`c + j'`, an `ARG` lookup, or the address), and
//!   writes the cell at `c + j` (a memory lookup).
//! - **CPU `INST`**: it looks up `ROOTS(hd, g)` and `HDR(g, …)`, starts and
//!   ends the POP chain `POPCH(clk, c, i, s)` from `(0, stk)` to `(k, rest)`
//!   and the INSTW chain `WCH(clk, c, g, j)` from `0` to `n`, and sets
//!   `hd' = root`, `stk' = rest`, `ctr' = ctr + n`.  `clk` is a row counter
//!   (0 on the first row, one more each row), so each instantiation's
//!   chains are its own, even when two share a counter.
//!
//! A chain runs from its CPU start to its CPU end one step at a time (each
//! row receives step `i` and sends step `i + 1`), so it has exactly `k` (or
//! `n`) rows.  An `ARG` lookup finds only a tuple an active POP row provides
//! (inactive rows provide nothing: their use count is forced to zero).  So
//! an `INST` row is `Air.instRow` for the jet at a licensed root, and a
//! table the verifier accepts satisfies `Air.AcceptsJ`.  `lake exe jets
//! check` checks that on every table proved here (`Air.checkJA_sound`).
//!
//! **The verifier runs `lake exe jets statement CORPUS DIR` first**
//! (`lean_statement`), with its own corpus: for each term it will prove,
//! the jet file it will read must be exactly Lean's for that term, and its
//! roots must pass `Air.rootsOKB` over the term's loaded heap, so
//! `Air.RootsOK` holds (`Air.rootsOKB_sound`).  Keyed by the terms, not by
//! file names: unchecked, a file for another term could list an unlicensed
//! root, and a proof over it would verify.  With Lean's files, the template
//! rows are `icells` (`JetTable.symCells_icells`).
//!
//! Why a chain has exactly `k` (or `n`) rows: every chain count is a
//! Boolean, so per level the active rows balance to one more than the
//! level before, up to the end; a surplus would need a cycle of about `p`
//! rows, and heights are at most `2^21`.  `clk` is unique per row for the
//! same reason.

use super::*;
use p3_field::PrimeField32;

const ROOTS: &str = "roots";
const HDR: &str = "hdr";
const TMPL: &str = "tmpl";
const POPCH: &str = "popch";
const WCH: &str = "wch";
const ARG: &str = "arg";

// ---------------------------------------------------------------------------
// The jet table
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Op {
    Local(u32),
    Arg(u32),
    Glob(u32),
}

impl Op {
    /// Flags (local, argument, global) and value.
    fn cols(self) -> [u32; 4] {
        match self {
            Op::Local(j) => [1, 0, 0, j],
            Op::Arg(i) => [0, 1, 0, i],
            Op::Glob(a) => [0, 0, 1, a],
        }
    }
}

#[derive(Clone, Debug)]
pub struct JetT {
    k: u32,
    root: Op,
    /// Each cell: its tag, and its operands for an application.
    cells: Vec<(u32, Option<(Op, Op)>)>,
}

pub struct JetTable {
    roots: Vec<(u32, u32)>,
    jets: Vec<JetT>,
}

fn parse_op(w: &[&str]) -> Op {
    let v: u32 = w[1].parse().expect("an operand value");
    match w[0] {
        "L" => Op::Local(v),
        "A" => Op::Arg(v),
        "G" => Op::Glob(v),
        _ => panic!("bad operand {w:?}"),
    }
}

pub fn read_jets(path: &std::path::Path) -> JetTable {
    parse_jets(&std::fs::read_to_string(path).expect("a jets file"))
}

/// A jet file's text, parsed.
pub fn parse_jets(text: &str) -> JetTable {
    let mut ls = text.lines();
    let mut next = || ls.next().expect("a line").split_whitespace().collect::<Vec<_>>();
    let h = next();
    assert_eq!(h[0], "roots");
    let r: usize = h[1].parse().unwrap();
    let roots = (0..r)
        .map(|_| {
            let w = next();
            (w[0].parse().unwrap(), w[1].parse().unwrap())
        })
        .collect();
    let h = next();
    assert_eq!(h[0], "jets");
    let g: usize = h[1].parse().unwrap();
    let mut jets = Vec::with_capacity(g);
    for _ in 0..g {
        let w = next();
        let k = w[0].parse().unwrap();
        let n: usize = w[1].parse().unwrap();
        let root = parse_op(&w[2..4]);
        let cells = (0..n)
            .map(|_| {
                let w = next();
                let tag: u32 = w[0].parse().unwrap();
                if tag == 3 {
                    (tag, Some((parse_op(&w[1..3]), parse_op(&w[3..5]))))
                } else {
                    (tag, None)
                }
            })
            .collect();
        jets.push(JetT { k, root, cells });
    }
    JetTable { roots, jets }
}

/// Pad to a power of two (at least `2^min_log`) with copies of row 0.
fn pad_copies<const W: usize>(mut rows: Vec<[u32; W]>, min_log: usize) -> Vec<[u32; W]> {
    assert!(!rows.is_empty(), "a jet table with no rows");
    let first = rows[0];
    rows.resize(pow2_at_least(rows.len(), min_log), first);
    rows
}

fn roots_pre(t: &JetTable) -> Vec<[u32; 2]> {
    pad_copies(t.roots.iter().map(|&(a, g)| [a, g]).collect(), MIN_LOG)
}

fn hdr_pre(t: &JetTable) -> Vec<[u32; 7]> {
    pad_copies(
        t.jets
            .iter()
            .enumerate()
            .map(|(g, j)| {
                let r = j.root.cols();
                [g as u32, j.k, j.cells.len() as u32, r[0], r[1], r[2], r[3]]
            })
            .collect(),
        MIN_LOG,
    )
}

fn tmpl_pre(t: &JetTable) -> Vec<[u32; 11]> {
    let mut rows = Vec::new();
    for (g, jt) in t.jets.iter().enumerate() {
        for (j, &(tag, ops)) in jt.cells.iter().enumerate() {
            let (a, b) = match ops {
                Some((a, b)) => (a.cols(), b.cols()),
                None => ([0; 4], [0; 4]),
            };
            rows.push([g as u32, j as u32, tag, a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]]);
        }
    }
    pad_copies(rows, MIN_LOG)
}

// ---------------------------------------------------------------------------
// The AIRs
// ---------------------------------------------------------------------------

const POP_W: usize = 8 + RANGE_BITS;
const INSTW_W: usize = 18;

#[derive(Clone, Debug)]
pub enum JetAir {
    Roots(Vec<[u32; 2]>),
    Hdr(Vec<[u32; 7]>),
    Tmpl(Vec<[u32; 11]>),
    Pop,
    Instw,
}

fn matrix<F: Field, const W: usize>(rows: &[[u32; W]]) -> RowMajorMatrix<F> {
    RowMajorMatrix::new(rows.iter().flat_map(|r| r.iter().map(|&v| F::from_u32(v))).collect(), W)
}

impl JetAir {
    pub fn width(&self) -> usize {
        match self {
            JetAir::Roots(_) | JetAir::Hdr(_) | JetAir::Tmpl(_) => 1,
            JetAir::Pop => POP_W,
            JetAir::Instw => INSTW_W,
        }
    }

    pub fn preprocessed<F: Field>(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            JetAir::Roots(p) => Some(matrix(p)),
            JetAir::Hdr(p) => Some(matrix(p)),
            JetAir::Tmpl(p) => Some(matrix(p)),
            _ => None,
        }
    }

    pub fn preprocessed_width(&self) -> usize {
        match self {
            JetAir::Roots(_) => 2,
            JetAir::Hdr(_) => 7,
            JetAir::Tmpl(_) => 11,
            _ => 0,
        }
    }

    pub fn eval<AB: PermutationAirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        match self {
            JetAir::Roots(_) => eval_provider(b, ROOTS),
            JetAir::Hdr(_) => eval_provider(b, HDR),
            JetAir::Tmpl(_) => eval_provider(b, TMPL),
            JetAir::Pop => eval_pop(b),
            JetAir::Instw => eval_instw(b),
        }
    }
}

/// A preprocessed table that provides its rows on `bus`, each as often as
/// its committed multiplicity says.
fn eval_provider<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB, bus: &str) {
    let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
    let main = b.main();
    let mult: AB::Expr = main.current_slice()[0].into();
    b.push_interaction(bus, pre, Count::provided(-mult));
}

/// POP: `clk c i s x s' uses act`, then the range bits of `c - s - 1`.
fn eval_pop<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let (clk, c, i, s, x, s2, uses, act) =
        (l[0].clone(), l[1].clone(), l[2].clone(), l[3].clone(), l[4].clone(), l[5].clone(), l[6].clone(), l[7].clone());
    let one = AB::Expr::ONE;
    b.assert_bool(act.clone());
    b.assert_zero(uses.clone() * (one.clone() - act.clone()));
    let mut val = AB::Expr::ZERO;
    for k in 0..RANGE_BITS {
        let bit = l[8 + k].clone();
        b.assert_bool(bit.clone());
        val = val + bit * AB::Expr::from_u32(1 << k);
    }
    b.assert_zero(act.clone() * (c.clone() - s.clone() - one.clone() - val));
    b.push_interaction(POPCH, [clk.clone(), c.clone(), i.clone(), s.clone()], -Count::bounded(act.clone(), 1));
    b.push_interaction(POPCH, [clk.clone(), c, i.clone() + one, s2.clone()], Count::bounded(act.clone(), 1));
    b.push_interaction(BUS, [s, AB::Expr::from_u32(5), x.clone(), s2], Count::bounded(act, 1));
    b.push_interaction(ARG, [clk, i, x], Count::provided(-uses));
}

/// INSTW: `clk c g j tag aL aA aG av bL bA bG bv a b xa xb act`.
fn eval_instw<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let one = AB::Expr::ONE;
    let (clk, c, g, j, tag) = (l[0].clone(), l[1].clone(), l[2].clone(), l[3].clone(), l[4].clone());
    let act = l[17].clone();
    b.assert_bool(act.clone());
    for k in [5, 6, 7, 9, 10, 11] {
        b.assert_bool(l[k].clone());
        b.assert_zero(l[k].clone() * (one.clone() - act.clone()));
    }
    // Each operand resolves: a cell this instantiation wrote, an argument, or
    // a public address.
    for (fl, fa, fg, v, out, x) in [(5, 6, 7, 8, 13, 15), (9, 10, 11, 12, 14, 16)] {
        b.assert_eq(
            l[out].clone(),
            l[fl].clone() * (c.clone() + l[v].clone()) + l[fa].clone() * l[x].clone() + l[fg].clone() * l[v].clone(),
        );
        b.push_interaction(ARG, [clk.clone(), l[v].clone(), l[x].clone()], Count::bounded(l[fa].clone(), 1));
    }
    b.push_interaction(WCH, [clk.clone(), c.clone(), g.clone(), j.clone()], -Count::bounded(act.clone(), 1));
    b.push_interaction(WCH, [clk, c.clone(), g.clone(), j.clone() + one], Count::bounded(act.clone(), 1));
    b.push_interaction(TMPL, l[2..13].to_vec(), Count::bounded(act.clone(), 1));
    b.push_interaction(BUS, [c + j, tag, l[13].clone(), l[14].clone()], Count::bounded(act, 1));
}

/// The CPU's `INST` constraints; returns the instantiation's parts of the
/// next head, stack and counter.
pub fn eval_cpu_inst<AB: PermutationAirBuilder + InteractionBuilder>(
    b: &mut AB,
    loc: &[AB::Expr],
    nxt: &[AB::Expr],
    inst: AB::Expr,
) -> (AB::Expr, AB::Expr, AB::Expr) {
    let one = AB::Expr::ONE;
    let (hd, stk, ctr) = (loc[HD].clone(), loc[STK].clone(), loc[CTR].clone());
    let clk = loc[J_CLK].clone();
    let (g, k, n) = (loc[J_G].clone(), loc[J_K].clone(), loc[J_N].clone());
    let (rl, ra, rg, rv) = (loc[J_RL].clone(), loc[J_RA].clone(), loc[J_RG].clone(), loc[J_RV].clone());
    let (xroot, rest) = (loc[J_XROOT].clone(), loc[J_REST].clone());
    b.when_first_row().assert_zero(clk.clone());
    b.when_transition().assert_eq(nxt[J_CLK].clone(), clk.clone() + one.clone());
    for x in [rl.clone(), ra.clone(), rg.clone()] {
        b.assert_bool(x);
    }
    b.assert_eq(rl.clone() + ra.clone() + rg.clone(), inst.clone());
    b.push_interaction(ROOTS, [hd, g.clone()], Count::bounded(inst.clone(), 1));
    b.push_interaction(
        HDR,
        [g.clone(), k.clone(), n.clone(), rl.clone(), ra.clone(), rg.clone(), rv.clone()],
        Count::bounded(inst.clone(), 1),
    );
    b.push_interaction(POPCH, [clk.clone(), ctr.clone(), AB::Expr::ZERO, stk], Count::bounded(inst.clone(), 1));
    b.push_interaction(POPCH, [clk.clone(), ctr.clone(), k, rest.clone()], -Count::bounded(inst.clone(), 1));
    b.push_interaction(WCH, [clk.clone(), ctr.clone(), g.clone(), AB::Expr::ZERO], Count::bounded(inst.clone(), 1));
    b.push_interaction(WCH, [clk.clone(), ctr.clone(), g, n.clone()], -Count::bounded(inst.clone(), 1));
    b.push_interaction(ARG, [clk, rv.clone(), xroot.clone()], Count::bounded(ra.clone(), 1));
    (
        rl * (ctr + rv.clone()) + rg * rv + ra * xroot,
        inst.clone() * rest,
        inst * n,
    )
}

// ---------------------------------------------------------------------------
// The jetted run: `JetCost.runJ`
// ---------------------------------------------------------------------------

/// An instantiation, as its rows need it.
#[derive(Clone, Debug)]
struct InstInfo {
    g: u32,
    /// The stack cells popped: `(s, x, s')`.
    pops: Vec<(u32, u32, u32)>,
    rest: u32,
    xroot: u32,
    /// The written cells and, per cell, the argument pointers its operands use.
    cells: Vec<(Cell, u32, u32)>,
}

struct JRun {
    /// Registers of every state, and the instantiation a state makes.
    rows: Vec<([u32; 3], Option<InstInfo>)>,
    heap: Vec<Cell>,
    loaded: Vec<Cell>,
    insts: usize,
}

fn resolve(op: Op, c: u32, ps: &[u32]) -> u32 {
    match op {
        Op::Local(j) => c + j,
        Op::Arg(i) => ps[i as usize],
        Op::Glob(a) => a,
    }
}

/// Pop `k` arguments: `(s, x, s')` per cell, and the rest.
fn pop(heap: &[Cell], k: u32, mut s: u32) -> Option<(Vec<(u32, u32, u32)>, u32)> {
    let mut out = Vec::new();
    for _ in 0..k {
        match heap.get(s as usize)? {
            Cell::Cons(x, r) => {
                out.push((s, *x, *r));
                s = *r;
            }
            _ => return None,
        }
    }
    Some((out, s))
}

/// Run to a halt, instantiating at every root with enough arguments, for
/// at most `MAX_STATES` states.  `extra_root` is an unlicensed root, used
/// once (the tamper test).
fn run_jets(t: &Term, jt: &JetTable, extra_root: Option<(u32, u32)>) -> JRun {
    const MAX_STATES: usize = 1 << 20;
    let (mut heap, mut hd, mut stk) = load(t);
    let loaded = heap.clone();
    let roots: std::collections::HashMap<u32, u32> = jt.roots.iter().copied().collect();
    let mut extra = extra_root;
    let mut rows = Vec::new();
    let mut insts = 0;
    while rows.len() < MAX_STATES {
        let c = heap.len() as u32;
        let chosen = match extra {
            Some((a, g)) if a == hd => {
                extra = None;
                Some(g)
            }
            _ => roots.get(&hd).copied(),
        };
        let inst = chosen.and_then(|g| {
            let j = &jt.jets[g as usize];
            pop(&heap, j.k, stk).map(|(pops, rest)| (g, j, pops, rest))
        });
        if let Some((g, j, pops, rest)) = inst {
            let ps: Vec<u32> = pops.iter().map(|p| p.1).collect();
            let cells: Vec<(Cell, u32, u32)> = j
                .cells
                .iter()
                .map(|&(tag, ops)| match ops {
                    Some((a, b)) => {
                        let xa = if let Op::Arg(i) = a { ps[i as usize] } else { 0 };
                        let xb = if let Op::Arg(i) = b { ps[i as usize] } else { 0 };
                        (Cell::App(resolve(a, c, &ps), resolve(b, c, &ps)), xa, xb)
                    }
                    None => (
                        match tag {
                            0 => Cell::S,
                            1 => Cell::K,
                            _ => Cell::I,
                        },
                        0,
                        0,
                    ),
                })
                .collect();
            let root = resolve(j.root, c, &ps);
            let xroot = if let Op::Arg(i) = j.root { ps[i as usize] } else { 0 };
            rows.push(([hd, stk, c], Some(InstInfo { g, pops, rest, xroot, cells: cells.clone() })));
            heap.extend(cells.iter().map(|x| x.0));
            hd = root;
            stk = rest;
            insts += 1;
            continue;
        }
        rows.push(([hd, stk, c], None));
        match step(&heap, hd, stk) {
            None => break,
            Some((h, s, ws)) => {
                heap.extend(ws);
                hd = h;
                stk = s;
            }
        }
    }
    JRun { rows, heap, loaded, insts }
}

// ---------------------------------------------------------------------------
// Traces
// ---------------------------------------------------------------------------

struct JTraces {
    cpu: RowMajorMatrix<Val>,
    mem: RowMajorMatrix<Val>,
    prog: RowMajorMatrix<Val>,
    roots: RowMajorMatrix<Val>,
    hdr: RowMajorMatrix<Val>,
    tmpl: RowMajorMatrix<Val>,
    pop: RowMajorMatrix<Val>,
    instw: RowMajorMatrix<Val>,
    /// The memory table and the rows, for the Lean table.
    mem_cells: Vec<Cell>,
    regs: Vec<[u32; 3]>,
}

fn counts<const W: usize>(pre: &[[u32; W]], used: &std::collections::HashMap<[u32; W], u32>) -> RowMajorMatrix<Val> {
    // Each tuple's count goes on its first row; copies stay at zero.
    let mut seen = std::collections::HashSet::new();
    let v = pre
        .iter()
        .map(|r| if seen.insert(*r) { f(*used.get(r).unwrap_or(&0)) } else { Val::ZERO })
        .collect();
    RowMajorMatrix::new(v, 1)
}

fn build_traces(t: &Term, jt: &JetTable, run: &JRun) -> JTraces {
    use std::collections::HashMap;
    let k = pow2_at_least(run.rows.len(), MIN_LOG);
    let msize = pow2_at_least(run.heap.len(), MIN_LOG);
    let mut mem_cells = run.heap.clone();
    mem_cells.resize(msize, Cell::Nil);
    let mut mult = vec![0u32; msize];

    // The CPU: the ordinary rows by `cpu_trace`, the INST rows by hand.
    let w = CPU_WIDTH + JET_WIDTH;
    let mut cpu = Vec::with_capacity(k * w);
    let mut roots_used: HashMap<[u32; 2], u32> = HashMap::new();
    let mut hdr_used: HashMap<[u32; 7], u32> = HashMap::new();
    let mut tmpl_used: HashMap<[u32; 11], u32> = HashMap::new();
    let mut pop = Vec::new();
    let mut instw = Vec::new();
    let hdrs = hdr_pre(jt);
    let tmpls = tmpl_pre(jt);
    let last = run.rows.last().unwrap().0;
    for clk in 0..k {
        let (regs, info) = if clk < run.rows.len() { run.rows[clk].clone() } else { (last, None) };
        let [hd, stk, ctr] = regs;
        let mut row = match &info {
            None => {
                let m = cpu_trace(&[regs], &mem_cells, &mut mult);
                m.values
            }
            Some(_) => {
                let mut r = vec![Val::ZERO; CPU_WIDTH];
                r[HD] = f(hd);
                r[STK] = f(stk);
                r[CTR] = f(ctr);
                r[SEL + 11] = Val::ONE;
                r
            }
        };
        let mut jc = vec![Val::ZERO; JET_WIDTH];
        jc[0] = f(clk as u32);
        if let Some(ii) = &info {
            let j = &jt.jets[ii.g as usize];
            let hr = hdrs[ii.g as usize];
            let n = j.cells.len() as u32;
            jc[J_G - CPU_WIDTH] = f(ii.g);
            jc[J_K - CPU_WIDTH] = f(j.k);
            jc[J_N - CPU_WIDTH] = f(n);
            for q in 0..4 {
                jc[J_RL - CPU_WIDTH + q] = f(hr[3 + q]);
            }
            jc[J_XROOT - CPU_WIDTH] = f(ii.xroot);
            jc[J_REST - CPU_WIDTH] = f(ii.rest);
            *roots_used.entry([hd, ii.g]).or_default() += 1;
            *hdr_used.entry(hr).or_default() += 1;
            // Argument uses: each operand and the root.
            let mut uses = vec![0u32; j.k as usize];
            for &(_, ops) in &j.cells {
                if let Some((a, b)) = ops {
                    for o in [a, b] {
                        if let Op::Arg(i) = o {
                            uses[i as usize] += 1;
                        }
                    }
                }
            }
            if let Op::Arg(i) = j.root {
                uses[i as usize] += 1;
            }
            for (i, &(s, x, s2)) in ii.pops.iter().enumerate() {
                let mut pr = vec![Val::ZERO; POP_W];
                let vals = [clk as u32, ctr, i as u32, s, x, s2, uses[i], 1];
                for q in 0..8 {
                    pr[q] = f(vals[q]);
                }
                assert!(s < ctr, "a pop at or above the counter");
                let d = ctr - s - 1;
                for q in 0..RANGE_BITS {
                    pr[8 + q] = f((d >> q) & 1);
                }
                mult[s as usize] += 1;
                pop.extend(pr);
            }
            let first = tmpls.iter().position(|r| r[0] == ii.g).unwrap_or(0);
            for (jx, (cell, xa, xb)) in ii.cells.iter().enumerate() {
                let tr = tmpls[first + jx];
                assert_eq!((tr[0], tr[1]), (ii.g, jx as u32));
                *tmpl_used.entry(tr).or_default() += 1;
                let (a, b) = cell.fields();
                let mut wr = vec![Val::ZERO; INSTW_W];
                let mut vals = [0u32; INSTW_W];
                vals[0] = clk as u32;
                vals[1] = ctr;
                vals[2..13].copy_from_slice(&tr[0..11]);
                vals[13] = a;
                vals[14] = b;
                vals[15] = *xa;
                vals[16] = *xb;
                vals[17] = 1;
                for q in 0..INSTW_W {
                    wr[q] = f(vals[q]);
                }
                assert_eq!(cell.tag(), tr[2]);
                mult[(ctr + jx as u32) as usize] += 1;
                instw.extend(wr);
            }
        }
        row.extend(jc);
        cpu.extend(row);
    }
    let pad = |mut v: Vec<Val>, w: usize| {
        let h = pow2_at_least((v.len() / w).max(1), MIN_LOG);
        v.resize(h * w, Val::ZERO);
        RowMajorMatrix::new(v, w)
    };
    let pop = pad(pop, POP_W);
    let instw = pad(instw, INSTW_W);

    // The program table, and memory with its multiplicities.
    let (loaded, _, _) = load(t);
    let pre = program(t, MIN_LOG);
    for i in 0..loaded.len() {
        mult[i] += 1;
    }
    let mut mem = Vec::with_capacity(msize * 5);
    for (i, cell) in mem_cells.iter().enumerate() {
        let (a, b) = cell.fields();
        mem.extend([f(i as u32), f(cell.tag()), f(a), f(b), f(mult[i])]);
    }
    let roots_p = roots_pre(jt);
    JTraces {
        cpu: RowMajorMatrix::new(cpu, w),
        mem: RowMajorMatrix::new(mem, 5),
        prog: RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1),
        roots: counts(&roots_p, &roots_used),
        hdr: counts(&hdrs, &hdr_used),
        tmpl: counts(&tmpls, &tmpl_used),
        pop,
        instw,
        mem_cells,
        regs: (0..k).map(|i| if i < run.rows.len() { run.rows[i].0 } else { last }).collect(),
    }
}

// ---------------------------------------------------------------------------
// Proving and verifying
// ---------------------------------------------------------------------------

fn airs(t: &Term, jt: &JetTable) -> Vec<SkiAir> {
    let (loaded, hd0, stk0) = load(t);
    vec![
        SkiAir::Cpu(CpuAir { hd0, stk0, ctr0: loaded.len() as u32, accept: None, blind: false, jets: true }),
        SkiAir::Mem(MemAir { blind: false }),
        SkiAir::Prog(ProgAir { pre: program(t, MIN_LOG) }),
        SkiAir::Jet(JetAir::Roots(roots_pre(jt))),
        SkiAir::Jet(JetAir::Hdr(hdr_pre(jt))),
        SkiAir::Jet(JetAir::Tmpl(tmpl_pre(jt))),
        SkiAir::Jet(JetAir::Pop),
        SkiAir::Jet(JetAir::Instw),
    ]
}

/// Prove the traces, then verify against the public term and jet table.
/// The verifier rebuilds its AIRs and preprocessed tables, pins the
/// preprocessed heights, and bounds the others by `MAX_LOG_HEIGHT`.
type JProof = p3_batch_stark::BatchProof<Config>;

/// Prove the traces: the proof and the seconds it took, setup included.
fn prove_j(t: &Term, jt: &JetTable, tr: &JTraces) -> Result<(JProof, f64), String> {
    let traces = [&tr.cpu, &tr.mem, &tr.prog, &tr.roots, &tr.hdr, &tr.tmpl, &tr.pop, &tr.instw];
    let log = |m: &RowMajorMatrix<Val>| p3_util::log2_strict_usize(m.values.len() / m.width);
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = make_config();
        let a = airs(t, jt);
        let degrees: Vec<usize> = traces.iter().map(|m| log(m)).collect();
        let t0 = Instant::now();
        let pd = ProverData::<Config>::from_airs_and_degrees(&config, &a, &degrees)
            .map_err(|e| format!("setup: {e:?}"))?;
        let pvs = vec![vec![]; 8];
        let instances = StarkInstance::new_multiple(&a, &traces, &pvs);
        let proof = prove_batch(&config, &instances, &pd).map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    match proved {
        Ok(r) => r,
        Err(e) => Err(format!("panic: {}", panic_text(&e))),
    }
}

/// **The verifier**: the public term, its jet table and the proof, nothing
/// else.  It rebuilds its AIRs and preprocessed tables, pins the
/// preprocessed heights, and bounds the others by `MAX_LOG_HEIGHT`.  (The
/// jet table must first pass `lake exe jets statement`: `jet_verify`.)
fn verify_j(t: &Term, jt: &JetTable, proof: &JProof) -> Result<(), String> {
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let config = make_config();
        let a = airs(t, jt);
        let d = &proof.degree_bits;
        let lg = |n: usize| p3_util::log2_strict_usize(n);
        let fixed = [
            (2, lg(program(t, MIN_LOG).len())),
            (3, lg(roots_pre(jt).len())),
            (4, lg(hdr_pre(jt).len())),
            (5, lg(tmpl_pre(jt).len())),
        ];
        if d.len() != 8
            || fixed.iter().any(|&(i, h)| d[i] != h)
            || [0, 1, 6, 7].iter().any(|&i| d[i] > MAX_LOG_HEIGHT)
        {
            return Err(format!("heights {d:?} out of bounds"));
        }
        let vd = ProverData::<Config>::from_airs_and_degrees(&config, &a, d)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        let pvs = vec![vec![]; 8];
        verify_batch(&config, &a, proof, &pvs, &vd.common).map_err(|e| format!("verify: {e:?}"))
    }));
    match verified {
        Ok(r) => r,
        Err(e) => Err(format!("verifier panic: {}", panic_text(&e))),
    }
}

fn prove_and_verify_j(t: &Term, jt: &JetTable, tr: &JTraces) -> Outcome {
    let (proof, prove_s) = match prove_j(t, jt, tr) {
        Ok(p) => p,
        Err(e) => return Outcome::Refused(e),
    };
    let t1 = Instant::now();
    match verify_j(t, jt, &proof) {
        Ok(()) => Outcome::Verified(prove_s, t1.elapsed().as_secs_f64()),
        Err(e) => Outcome::Rejected(e),
    }
}

// ---------------------------------------------------------------------------
// A table from elsewhere (Avon's witness), proved; a proof, verified alone
// ---------------------------------------------------------------------------

/// A table in `Ski/AirCheck.lean`'s format: the term's prefix form, the
/// memory table and the rows.
fn read_table(path: &std::path::Path) -> Result<(String, Vec<Cell>, Vec<[u32; 3]>), String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut ls = text.lines();
    let mut next = || ls.next().ok_or_else(|| "a truncated table".to_string());
    let term = next()?.trim().to_string();
    let n: usize = next()?.trim().parse().map_err(|_| "a memory count".to_string())?;
    let mut mem = Vec::with_capacity(n);
    for _ in 0..n {
        let l = next()?;
        let w: Vec<&str> = l.split_whitespace().collect();
        let num = |i: usize| w.get(i).and_then(|x| x.parse::<u32>().ok()).ok_or_else(|| format!("a bad cell: {l}"));
        mem.push(match w.first().copied() {
            Some("S") => Cell::S,
            Some("K") => Cell::K,
            Some("I") => Cell::I,
            Some("N") => Cell::Nil,
            Some("A") => Cell::App(num(1)?, num(2)?),
            Some("C") => Cell::Cons(num(1)?, num(2)?),
            _ => return Err(format!("a bad cell: {l}")),
        });
    }
    let k: usize = next()?.trim().parse().map_err(|_| "a row count".to_string())?;
    let mut rows = Vec::with_capacity(k);
    for _ in 0..k {
        let l = next()?;
        let v: Vec<u32> = l.split_whitespace().filter_map(|x| x.parse().ok()).collect();
        if v.len() != 3 {
            return Err(format!("a bad row: {l}"));
        }
        rows.push([v[0], v[1], v[2]]);
    }
    Ok((term, mem, rows))
}

/// The run a table records: each row an instantiation when its head is a
/// licensed root and the next row and the memory at the counter are that
/// instantiation's (as `Air.instRow` would find them), and otherwise a
/// machine transition or a halt, which the traces classify.
fn run_of_table(t: &Term, jt: &JetTable, mem: Vec<Cell>, rows: Vec<[u32; 3]>) -> Result<JRun, String> {
    let (loaded, _, _) = load(t);
    if mem.len() < loaded.len() || mem[..loaded.len()] != loaded[..] {
        return Err("the memory table does not begin with the loaded term".into());
    }
    let roots: std::collections::HashMap<u32, u32> = jt.roots.iter().copied().collect();
    let mut out = Vec::with_capacity(rows.len());
    let mut insts = 0;
    for (i, &[hd, stk, ctr]) in rows.iter().enumerate() {
        let info = roots.get(&hd).and_then(|&g| {
            let j = &jt.jets[g as usize];
            let below = &mem[..(ctr as usize).min(mem.len())];
            let (pops, rest) = pop(below, j.k, stk)?;
            let ps: Vec<u32> = pops.iter().map(|p| p.1).collect();
            let cells: Vec<(Cell, u32, u32)> = j
                .cells
                .iter()
                .map(|&(tag, ops)| match ops {
                    Some((a, b)) => {
                        let xa = if let Op::Arg(q) = a { ps[q as usize] } else { 0 };
                        let xb = if let Op::Arg(q) = b { ps[q as usize] } else { 0 };
                        (Cell::App(resolve(a, ctr, &ps), resolve(b, ctr, &ps)), xa, xb)
                    }
                    None => (match tag { 0 => Cell::S, 1 => Cell::K, _ => Cell::I }, 0, 0),
                })
                .collect();
            let n = cells.len() as u32;
            let written = mem.get(ctr as usize..(ctr + n) as usize)?;
            if written.iter().zip(&cells).any(|(m, c)| *m != c.0) {
                return None;
            }
            let root = resolve(j.root, ctr, &ps);
            let xroot = if let Op::Arg(q) = j.root { ps[q as usize] } else { 0 };
            (rows.get(i + 1) == Some(&[root, rest, ctr + n]))
                .then_some(InstInfo { g, pops, rest, xroot, cells })
        });
        if info.is_some() {
            insts += 1;
        }
        out.push(([hd, stk, ctr], info));
    }
    Ok(JRun { rows: out, heap: mem, loaded, insts })
}

/// `ski-air jet-prove TERM JETS TABLE PROOF`: prove the table another
/// producer wrote (Avon's jetted witness) for the term and its jet table;
/// write the proof, and check it verifies.
pub fn jet_prove(term: &std::path::Path, jets: &std::path::Path, table: &std::path::Path, proof_out: &std::path::Path) -> Result<(), String> {
    let term_text = std::fs::read_to_string(term).map_err(|e| format!("{}: {e}", term.display()))?;
    let term_text = term_text.trim();
    let t = parse(term_text.as_bytes(), &mut 0);
    let jt = read_jets(jets);
    let (tterm, mem, rows) = read_table(table)?;
    if tterm != term_text {
        return Err("the table is for another term".into());
    }
    let run = run_of_table(&t, &jt, mem, rows)?;
    let tr = catch_unwind(AssertUnwindSafe(|| build_traces(&t, &jt, &run)))
        .map_err(|e| format!("the table is no run: {}", panic_text(&e)))?;
    let (proof, prove_s) = prove_j(&t, &jt, &tr)?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    verify_j(&t, &jt, &proof)?;
    println!(
        "proved {} rows ({} instantiations), {} memory cells, in {prove_s:.2} s; proof {} bytes -> {}",
        run.rows.len(),
        run.insts,
        run.heap.len(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// `ski-air jet-verify CORPUS JETSDIR NAME PROOF`: the verifier.  Lean
/// checks the jet files for the corpus's terms (`lake exe jets statement`),
/// then the proof is checked against the term named NAME and its jet file,
/// and nothing else.
pub fn jet_verify(corpus: &std::path::Path, dir: &std::path::Path, name: &str, proof_in: &std::path::Path) -> Result<(), String> {
    // A name is an identifier, as Lean's statement check requires, so the
    // file named is `DIR/<name>.jets` and no other.
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return Err(format!("a name must be an identifier, not {name:?}"));
    }
    // Read each public file once.  Lean checks a private copy of exactly
    // these bytes, and they are what is parsed below.
    let text = std::fs::read_to_string(corpus).map_err(|e| format!("{}: {e}", corpus.display()))?;
    let line = text
        .lines()
        .find(|l| l.split_whitespace().next() == Some(name))
        .ok_or_else(|| format!("no term named {name} in {}", corpus.display()))?
        .to_string();
    let w: Vec<&str> = line.split_whitespace().collect();
    if w.len() != 3 {
        return Err(format!("a malformed corpus line for {name}"));
    }
    let jets_path = dir.join(format!("{name}.jets"));
    let jets_text = std::fs::read_to_string(&jets_path).map_err(|e| format!("{}: {e}", jets_path.display()))?;
    let corpus_bytes = format!("{line}\n");
    let jets_rel = format!("jets/{name}.jets");
    let snap = Snapshot::new(&[("corpus.txt", corpus_bytes.as_bytes()), (&jets_rel, jets_text.as_bytes())])?;
    lean_statement("jets", &[&snap.path("corpus.txt"), &snap.path("jets")]).map_err(|e| format!("statement: {e}"))?;
    drop(snap);
    let t = parse(w[2].as_bytes(), &mut 0);
    let jt = parse_jets(&jets_text);
    let bytes = std::fs::read(proof_in).map_err(|e| format!("{}: {e}", proof_in.display()))?;
    // The whole file is the proof: trailing bytes are refused, so a proof
    // is one byte string.
    let (proof, rest): (JProof, &[u8]) =
        postcard::take_from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    if !rest.is_empty() {
        return Err(format!("{} bytes after the proof", rest.len()));
    }
    let t0 = Instant::now();
    verify_j(&t, &jt, &proof)?;
    println!("VERIFIED {name}: the proof checks against its term and Lean's jet table ({:.3} s)", t0.elapsed().as_secs_f64());
    Ok(())
}

fn lean_of(term: &str, run: &JRun, tr: &JTraces) -> String {
    let tb = Table {
        loaded: run.loaded.clone(),
        hd0: 0,
        stk0: 0,
        rows: tr.regs.clone(),
        mem: tr.mem_cells.clone(),
    };
    lean_table(term, &tb)
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

/// `ski-air jets CORPUS JETSDIR OUTDIR`: prove every corpus row jetted.
pub fn main(corpus: &str, corpus_path: &std::path::Path, dir: &std::path::Path, out: &std::path::Path) -> usize {
    let mut failures = 0;
    // The verifier's precondition: for each term it will prove, the jet file
    // is Lean's for that term, with licensed roots.  Each file is read once;
    // Lean checks a private copy of those bytes, which are the ones used.
    let mut jet_texts = std::collections::HashMap::new();
    let mut files: Vec<(String, Vec<u8>)> = vec![("corpus.txt".into(), corpus.as_bytes().to_vec())];
    for line in corpus.lines().filter(|l| !l.trim().is_empty()) {
        let name = line.split_whitespace().next().unwrap_or("").to_string();
        match std::fs::read_to_string(dir.join(format!("{name}.jets"))) {
            Ok(t) => {
                files.push((format!("jets/{name}.jets"), t.as_bytes().to_vec()));
                jet_texts.insert(name, t);
            }
            Err(e) => {
                println!("the jet file for {name}: {e}");
                return 1;
            }
        }
    }
    let refs: Vec<(&str, &[u8])> = files.iter().map(|(p, b)| (p.as_str(), b.as_slice())).collect();
    let checked = Snapshot::new(&refs)
        .and_then(|snap| lean_statement("jets", &[&snap.path("corpus.txt"), &snap.path("jets")]));
    if let Err(e) = checked {
        println!("the jet files are not Lean's for these terms: {e}");
        return 1;
    }
    let _ = corpus_path;
    println!("jet files: checked by lake exe jets statement, term by term");
    println!(
        "{:<16} {:>6} {:>7} {:>6} {:>7} {:>6} {:>6} {:>8} {:>8}  verdict",
        "row", "plain", "jetted", "insts", "budget", "pop", "instw", "prove s", "verify s"
    );
    let mut sumto: Option<(Term, JetTable, String)> = None;
    for line in corpus.lines().filter(|l| !l.trim().is_empty()) {
        let mut it = line.split_whitespace();
        let name = it.next().unwrap().to_string();
        let _steps = it.next();
        let term = it.next().unwrap().to_string();
        let t = parse(term.as_bytes(), &mut 0);
        let jt = parse_jets(&jet_texts[&name]);
        let plain = run(&t).rows.len();
        let jr = run_jets(&t, &jt, None);
        let tr = build_traces(&t, &jt, &jr);
        std::fs::write(out.join(format!("jet_{name}.txt")), lean_of(&term, &jr, &tr)).unwrap();
        let (pop_h, instw_h) = (tr.pop.values.len() / POP_W, tr.instw.values.len() / INSTW_W);
        match prove_and_verify_j(&t, &jt, &tr) {
            Outcome::Verified(p, v) => println!(
                "{:<16} {:>6} {:>7} {:>6} {:>7} {:>6} {:>6} {:>8.2} {:>8.3}  verified",
                name,
                plain,
                jr.rows.len(),
                jr.insts,
                tr.regs.len(),
                pop_h,
                instw_h,
                p,
                v
            ),
            Outcome::Refused(e) | Outcome::Rejected(e) => {
                println!("{name}: FAILED an honest jetted table: {e}");
                failures += 1;
            }
        }
        if name == "sumto_us" {
            sumto = Some((t, jt, term));
        }
    }

    // Tampered tables, on `3 sumto`: each proof must be rejected, and each
    // Lean table.
    println!("\ntampered jetted tables (each proof must be rejected by the verifier):");
    let (t, jt, term) = sumto.expect("the corpus has sumto_us");
    // A forged instantiation write: one argument operand points elsewhere.
    {
        let jr = run_jets(&t, &jt, None);
        let mut tr = build_traces(&t, &jt, &jr);
        let row = (0..tr.instw.values.len() / INSTW_W)
            .find(|&r| tr.instw.values[r * INSTW_W + 3 + 3] == Val::ONE && tr.instw.values[r * INSTW_W + 17] == Val::ONE)
            .expect("a cell with an argument operand");
        let v = &mut tr.instw.values;
        let addr = (v[row * INSTW_W + 1] + v[row * INSTW_W + 3]).as_canonical_u32() as usize;
        v[row * INSTW_W + 13] += Val::ONE;
        v[row * INSTW_W + 15] += Val::ONE;
        tr.mem.values[addr * 5 + 2] += Val::ONE;
        if let Cell::App(a, b) = tr.mem_cells[addr] {
            tr.mem_cells[addr] = Cell::App(a + 1, b);
        }
        std::fs::write(out.join("tampered_jet_forged_write.txt"), lean_of(&term, &jr, &tr)).unwrap();
        failures += report("forged_write", prove_and_verify_j(&t, &jt, &tr));
    }
    // An unlicensed root: the run instantiates jet 0 at an address that is
    // not its root.
    {
        let honest = run_jets(&t, &jt, None);
        let roots: std::collections::HashSet<u32> = jt.roots.iter().map(|r| r.0).collect();
        let k0 = jt.jets[0].k;
        let (pos, hd) = honest
            .rows
            .iter()
            .enumerate()
            .find_map(|(i, (r, info))| {
                (info.is_none() && !roots.contains(&r[0]) && pop(&honest.heap, k0, r[1]).is_some()
                    && matches!(honest.heap[r[0] as usize], Cell::App(..)))
                .then_some((i, r[0]))
            })
            .expect("a state to forge at");
        let _ = pos;
        let jr = run_jets(&t, &jt, Some((hd, 0)));
        let tr = build_traces(&t, &jt, &jr);
        std::fs::write(out.join("tampered_jet_unlicensed_root.txt"), lean_of(&term, &jr, &tr)).unwrap();
        failures += report("unlicensed_root", prove_and_verify_j(&t, &jt, &tr));
    }
    // A doctored jet file: an extra root, at an address that is not a
    // root.  The statement check refuses it before any proof.
    {
        let bad = out.join("doctored_jets");
        std::fs::create_dir_all(&bad).unwrap();
        for e in std::fs::read_dir(dir).unwrap() {
            let e = e.unwrap();
            std::fs::copy(e.path(), bad.join(e.file_name())).unwrap();
        }
        let path = bad.join("sumto_us.jets");
        let text = std::fs::read_to_string(&path).unwrap();
        let mut ls: Vec<String> = text.lines().map(String::from).collect();
        let r: usize = ls[0].split_whitespace().nth(1).unwrap().parse().unwrap();
        let roots: std::collections::HashSet<u32> = jt.roots.iter().map(|x| x.0).collect();
        let a = (0u32..).find(|a| !roots.contains(a)).unwrap();
        ls[0] = format!("roots {}", r + 1);
        ls.insert(1, format!("{a} 0"));
        std::fs::write(&path, ls.join("\n") + "\n").unwrap();
        match lean_statement("jets", &[corpus_path, &bad]) {
            Err(e) => println!("{:<16} refused by the statement check ({})", "doctored_jets", e.chars().take(60).collect::<String>()),
            Ok(_) => {
                println!("{:<16} ACCEPTED by the statement check", "doctored_jets");
                failures += 1;
            }
        }
    }
    // A made-up jet for a term outside Lean's corpus (the audit's
    // counterexample): `K S K` with a jet "K x ↦ I" at address 0.  The check
    // is keyed by the verifier's own terms, so it refuses this file.
    {
        let bad = out.join("made_up_jets");
        std::fs::create_dir_all(&bad).unwrap();
        std::fs::write(bad.join("ksk.jets"), "roots 1\n0 0\njets 1\n1 1 L 0\n2\n").unwrap();
        let cp = out.join("made_up_corpus.txt");
        std::fs::write(&cp, "ksk 1 ``KSK\n").unwrap();
        match lean_statement("jets", &[&cp, &bad]) {
            Err(e) => println!("{:<16} refused by the statement check ({})", "made_up_jets", e.chars().take(60).collect::<String>()),
            Ok(_) => {
                println!("{:<16} ACCEPTED by the statement check", "made_up_jets");
                failures += 1;
            }
        }
    }
    failures
}

fn report(name: &str, o: Outcome) -> usize {
    match o {
        Outcome::Rejected(e) => {
            println!("{name:<16} rejected by the verifier ({})", e.chars().take(60).collect::<String>());
            0
        }
        Outcome::Verified(..) => {
            println!("{name:<16} ACCEPTED");
            1
        }
        Outcome::Refused(e) => {
            println!("{name:<16} NOT TESTED: the prover refused ({})", e.chars().take(50).collect::<String>());
            1
        }
    }
}
