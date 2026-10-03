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
    pub(crate) fn cols(self) -> [u32; 4] {
        match self {
            Op::Local(j) => [1, 0, 0, j],
            Op::Arg(i) => [0, 1, 0, i],
            Op::Glob(a) => [0, 0, 1, a],
        }
    }
}

#[derive(Clone, Debug)]
pub struct JetT {
    pub(crate) k: u32,
    pub(crate) root: Op,
    /// Each cell: its tag, and its operands for an application.
    pub(crate) cells: Vec<(u32, Option<(Op, Op)>)>,
}

pub struct JetTable {
    pub(crate) roots: Vec<(u32, u32)>,
    pub(crate) jets: Vec<JetT>,
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
    roots_pre_min(t, MIN_LOG)
}

pub(crate) fn roots_pre_min(t: &JetTable, min_log: usize) -> Vec<[u32; 2]> {
    pad_copies(t.roots.iter().map(|&(a, g)| [a, g]).collect(), min_log)
}

fn hdr_pre(t: &JetTable) -> Vec<[u32; 7]> {
    hdr_pre_min(t, MIN_LOG)
}

pub(crate) fn hdr_pre_min(t: &JetTable, min_log: usize) -> Vec<[u32; 7]> {
    pad_copies(
        t.jets
            .iter()
            .enumerate()
            .map(|(g, j)| {
                let r = j.root.cols();
                [g as u32, j.k, j.cells.len() as u32, r[0], r[1], r[2], r[3]]
            })
            .collect(),
        min_log,
    )
}

fn tmpl_pre(t: &JetTable) -> Vec<[u32; 11]> {
    tmpl_pre_min(t, MIN_LOG)
}

pub(crate) fn tmpl_pre_min(t: &JetTable, min_log: usize) -> Vec<[u32; 11]> {
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
    pad_copies(rows, min_log)
}

// ---------------------------------------------------------------------------
// The AIRs
// ---------------------------------------------------------------------------

pub(crate) const POP_W: usize = 8 + RANGE_BITS;
pub(crate) const INSTW_W: usize = 18;

/// The jet tables; each flag says whether the table carries its blinding
/// blocks, its edges in the composed circuit's blinding tree
/// (`src/compj.rs`).
#[derive(Clone, Debug)]
pub enum JetAir {
    Roots(Vec<[u32; 2]>, bool),
    Hdr(Vec<[u32; 7]>, bool),
    Tmpl(Vec<[u32; 11]>, bool),
    Pop(bool),
    Instw(bool),
}

fn matrix<F: Field, const W: usize>(rows: &[[u32; W]]) -> RowMajorMatrix<F> {
    RowMajorMatrix::new(rows.iter().flat_map(|r| r.iter().map(|&v| F::from_u32(v))).collect(), W)
}

impl JetAir {
    /// The columns before the blinding blocks.
    pub fn base_width(&self) -> usize {
        match self {
            JetAir::Roots(..) | JetAir::Hdr(..) | JetAir::Tmpl(..) => 1,
            JetAir::Pop(_) => POP_W,
            JetAir::Instw(_) => INSTW_W,
        }
    }

    /// The blinding blocks, when blinded: a received message (the edge to
    /// the parent), then a sent one.  The tree is `CPU —c— POP —d— INSTW
    /// —e— TMPL —f— HDR —g— ROOTS`.
    pub fn blocks(&self) -> &'static [(&'static str, bool)] {
        match self {
            JetAir::Roots(_, true) => &[("blind_g", false)],
            JetAir::Hdr(_, true) => &[("blind_f", false), ("blind_g", true)],
            JetAir::Tmpl(_, true) => &[("blind_e", false), ("blind_f", true)],
            JetAir::Pop(true) => &[("blind_c", false), ("blind_d", true)],
            JetAir::Instw(true) => &[("blind_d", false), ("blind_e", true)],
            _ => &[],
        }
    }

    pub fn width(&self) -> usize {
        self.base_width() + BLIND_WIDTH * self.blocks().len()
    }

    pub fn preprocessed<F: Field>(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            JetAir::Roots(p, _) => Some(matrix(p)),
            JetAir::Hdr(p, _) => Some(matrix(p)),
            JetAir::Tmpl(p, _) => Some(matrix(p)),
            _ => None,
        }
    }

    pub fn preprocessed_width(&self) -> usize {
        match self {
            JetAir::Roots(..) => 2,
            JetAir::Hdr(..) => 7,
            JetAir::Tmpl(..) => 11,
            _ => 0,
        }
    }

    pub fn eval<AB: PermutationAirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        match self {
            JetAir::Roots(..) => eval_provider(b, ROOTS),
            JetAir::Hdr(..) => eval_provider(b, HDR),
            JetAir::Tmpl(..) => eval_provider(b, TMPL),
            JetAir::Pop(_) => eval_pop(b),
            JetAir::Instw(_) => eval_instw(b),
        }
        let blocks = self.blocks();
        if !blocks.is_empty() {
            let main = b.main();
            let loc: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
            for (i, &(bus, send)) in blocks.iter().enumerate() {
                blind_msg(b, &loc, self.base_width() + BLIND_WIDTH * i, bus, send);
            }
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
pub(crate) struct InstInfo {
    pub(crate) g: u32,
    /// The stack cells popped: `(s, x, s')`.
    pub(crate) pops: Vec<(u32, u32, u32)>,
    pub(crate) rest: u32,
    pub(crate) xroot: u32,
    /// The written cells and, per cell, the argument pointers its operands use.
    pub(crate) cells: Vec<(Cell, u32, u32)>,
}

struct JRun {
    /// Registers of every state, and the instantiation a state makes.
    rows: Vec<([u32; 3], Option<InstInfo>)>,
    heap: Vec<Cell>,
    loaded: Vec<Cell>,
    insts: usize,
    /// The probe rows and segments, when the run reads an output.
    probe: Option<probe::ProbeRun>,
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

pub(crate) const MAX_STATES: usize = 1 << 20;

/// Run from a state to a halt, instantiating at every root with enough
/// arguments, pushing every row but the halted one; `false` if the run
/// passes `MAX_STATES` rows first.  `extra` is an unlicensed root, used
/// once (the tamper test).
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_seg(
    heap: &mut Vec<Cell>,
    hd: &mut u32,
    stk: &mut u32,
    roots: &std::collections::HashMap<u32, u32>,
    jt: &JetTable,
    extra: &mut Option<(u32, u32)>,
    rows: &mut Vec<([u32; 3], Option<InstInfo>)>,
    insts: &mut usize,
) -> bool {
    while rows.len() < MAX_STATES {
        let c = heap.len() as u32;
        let chosen = match *extra {
            Some((a, g)) if a == *hd => {
                *extra = None;
                Some(g)
            }
            _ => roots.get(hd).copied(),
        };
        let inst = chosen.and_then(|g| {
            let j = &jt.jets[g as usize];
            pop(heap, j.k, *stk).map(|(pops, rest)| (g, j, pops, rest))
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
            rows.push(([*hd, *stk, c], Some(InstInfo { g, pops, rest, xroot, cells: cells.clone() })));
            heap.extend(cells.iter().map(|x| x.0));
            *hd = root;
            *stk = rest;
            *insts += 1;
            continue;
        }
        match step(heap, *hd, *stk) {
            None => return true,
            Some((h, s, ws)) => {
                rows.push(([*hd, *stk, c], None));
                heap.extend(ws);
                *hd = h;
                *stk = s;
            }
        }
    }
    false
}

/// Run to a halt, instantiating at every root with enough arguments, for
/// at most `MAX_STATES` states.  `extra_root` is an unlicensed root, used
/// once (the tamper test).
fn run_jets(t: &Term, jt: &JetTable, extra_root: Option<(u32, u32)>) -> JRun {
    let (mut heap, mut hd, mut stk) = load(t);
    let loaded = heap.clone();
    let roots: std::collections::HashMap<u32, u32> = jt.roots.iter().copied().collect();
    let mut extra = extra_root;
    let mut rows = Vec::new();
    let mut insts = 0;
    if run_seg(&mut heap, &mut hd, &mut stk, &roots, jt, &mut extra, &mut rows, &mut insts) {
        rows.push(([hd, stk, heap.len() as u32], None));
    }
    JRun { rows, heap, loaded, insts, probe: None }
}

/// **The probe run** of a plan: from the loaded term, each segment's probe
/// row, then its jetted run to the marker it must end at.  An error names
/// the segment that ends elsewhere: the term does not decode to the
/// plan's outcome.
fn run_probe(t: &Term, jt: &JetTable, plan: &[probe::Seg]) -> Result<JRun, String> {
    let (mut heap, mut hd, mut stk) = load(t);
    let loaded = heap.clone();
    let roots: std::collections::HashMap<u32, u32> = jt.roots.iter().copied().collect();
    let mut rows = Vec::new();
    let mut insts = 0;
    let n = plan.len();
    let mut prow = std::collections::HashMap::new();
    let mut starts = Vec::with_capacity(n + 1);
    let mut flds: Vec<Vec<u32>> = vec![Vec::new(); n];
    let mut end_clk = vec![0u32; n];
    let mut end: Option<(Vec<(u32, u32, u32)>, u32)> = None;
    for (j, s) in plan.iter().enumerate() {
        let clk = rows.len();
        let c = heap.len() as u32;
        let (f, clkp) = if j == 0 {
            (hd, 0)
        } else {
            let p = s.parent as usize;
            if p >= j {
                return Err(format!("segment {j}'s parent is not before it"));
            }
            let x = *flds[p].get(s.field as usize).ok_or(format!("segment {j} reads a missing field"))?;
            (x, end_clk[p])
        };
        prow.insert(clk, probe::ProbeRow { seg: j as u32, f, end: end.take(), clkp });
        starts.push(clk as u32);
        rows.push(([hd, stk, c], None));
        heap.extend(probe::pcells(s.base, s.k, c));
        hd = f;
        stk = c + s.k;
        if !run_seg(&mut heap, &mut hd, &mut stk, &roots, jt, &mut None, &mut rows, &mut insts) {
            return Err(format!("segment {j} runs past {MAX_STATES} rows"));
        }
        // The end: the segment's marker at the head, exactly its fields on
        // the stack.
        if heap[hd as usize] != Cell::Atom(s.ctor + s.base) {
            return Err(format!("segment {j} ends at {:?}, not its marker {}", heap[hd as usize], s.ctor + s.base));
        }
        let (pops, rest) = pop(&heap, s.arity, stk).ok_or(format!("segment {j} has too few fields"))?;
        if heap[rest as usize] != Cell::Nil {
            return Err(format!("segment {j} has too many fields"));
        }
        flds[j] = pops.iter().map(|p| p.1).collect();
        end_clk[j] = rows.len() as u32;
        end = Some((pops, rest));
    }
    rows.push(([hd, stk, heap.len() as u32], None));
    Ok(JRun {
        rows,
        heap,
        loaded,
        insts,
        probe: Some(probe::ProbeRun { plan: plan.to_vec(), rows: prow, starts, flds }),
    })
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
    /// PLAN's multiplicities and the PW table, with probe segments.
    plan: Option<RowMajorMatrix<Val>>,
    pw: Option<RowMajorMatrix<Val>>,
    /// The memory table and the rows, for the Lean table.
    mem_cells: Vec<Cell>,
    regs: Vec<[u32; 3]>,
}

pub(crate) fn counts<const W: usize>(pre: &[[u32; W]], used: &std::collections::HashMap<[u32; W], u32>) -> RowMajorMatrix<Val> {
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

    // The CPU: the ordinary rows by `cpu_trace`, the INST and probe rows by
    // hand.
    let pr = run.probe.as_ref();
    let w = CPU_WIDTH + JET_WIDTH + if pr.is_some() { probe::PROBE_WIDTH } else { 0 };
    let mut plan_used: HashMap<[u32; 7], u32> = HashMap::new();
    let mut pw: Vec<Val> = Vec::new();
    let mut cnt = 0u32;
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
        let is_probe = pr.is_some_and(|p| p.rows.contains_key(&clk));
        let mut row = match &info {
            None if is_probe => {
                let mut r = vec![Val::ZERO; CPU_WIDTH];
                r[HD] = f(hd);
                r[STK] = f(stk);
                r[CTR] = f(ctr);
                r
            }
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
        if let Some(p) = pr {
            let mut pc = vec![Val::ZERO; probe::PROBE_WIDTH];
            probe::fill_row(p, clk, cnt, regs, clk + 1 == k, &mut row, &mut pc, &mut mult, &mut plan_used, &mut pop, &mut pw, POP_W);
            if is_probe {
                cnt += 1;
            }
            row.extend(pc);
        }
        cpu.extend(row);
    }
    let pad = |mut v: Vec<Val>, w: usize| {
        let h = pow2_at_least((v.len() / w).max(1), MIN_LOG);
        v.resize(h * w, Val::ZERO);
        RowMajorMatrix::new(v, w)
    };
    let pop = pad(pop, POP_W);
    let instw = pad(instw, INSTW_W);
    let plan = pr.map(|p| counts(&probe::plan_pre(&p.plan), &plan_used));
    let pw = pr.map(|_| pad(pw, probe::PW_W));

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
        plan,
        pw,
        mem_cells,
        regs: (0..k).map(|i| if i < run.rows.len() { run.rows[i].0 } else { last }).collect(),
    }
}

// ---------------------------------------------------------------------------
// Proving and verifying
// ---------------------------------------------------------------------------

fn airs(t: &Term, jt: &JetTable, plan: Option<&[probe::Seg]>) -> Result<Vec<SkiAir>, String> {
    let (loaded, hd0, stk0) = load(t);
    let pp = plan.map(probe::ProbePub::of).transpose()?;
    let mut a = vec![
        SkiAir::Cpu(CpuAir { hd0, stk0, ctr0: loaded.len() as u32, accept: None, accept_k: false, blind: false, jets: true, probe: pp, restart: None, p2: None }),
        SkiAir::Mem(MemAir { blind: false }),
        SkiAir::Prog(ProgAir { pre: program(t, MIN_LOG) }),
        SkiAir::Jet(JetAir::Roots(roots_pre(jt), false)),
        SkiAir::Jet(JetAir::Hdr(hdr_pre(jt), false)),
        SkiAir::Jet(JetAir::Tmpl(tmpl_pre(jt), false)),
        SkiAir::Jet(JetAir::Pop(false)),
        SkiAir::Jet(JetAir::Instw(false)),
    ];
    if let Some(p) = plan {
        a.push(SkiAir::Probe(probe::ProbeAir::Plan(probe::plan_pre(p))));
        a.push(SkiAir::Probe(probe::ProbeAir::Pw));
    }
    Ok(a)
}

/// Prove the traces, then verify against the public term and jet table.
/// The verifier rebuilds its AIRs and preprocessed tables, pins the
/// preprocessed heights, and bounds the others by `MAX_LOG_HEIGHT`.
type JProof = p3_batch_stark::BatchProof<Config>;

/// Prove the traces: the proof and the seconds it took, setup included.
fn prove_j(t: &Term, jt: &JetTable, tr: &JTraces, plan: Option<&[probe::Seg]>) -> Result<(JProof, f64), String> {
    let mut traces = vec![&tr.cpu, &tr.mem, &tr.prog, &tr.roots, &tr.hdr, &tr.tmpl, &tr.pop, &tr.instw];
    if plan.is_some() {
        traces.push(tr.plan.as_ref().ok_or("a probe plan without probe traces")?);
        traces.push(tr.pw.as_ref().ok_or("a probe plan without probe traces")?);
    }
    let log = |m: &RowMajorMatrix<Val>| p3_util::log2_strict_usize(m.values.len() / m.width);
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = make_config();
        let a = airs(t, jt, plan)?;
        let degrees: Vec<usize> = traces.iter().map(|m| log(m)).collect();
        let t0 = Instant::now();
        let pd = ProverData::<Config>::from_airs_and_degrees(&config, &a, &degrees)
            .map_err(|e| format!("setup: {e:?}"))?;
        let pvs = crate::stmt::public_values(&a);
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
fn verify_j(t: &Term, jt: &JetTable, proof: &JProof, plan: Option<&[probe::Seg]>) -> Result<(), String> {
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let config = make_config();
        let a = airs(t, jt, plan)?;
        // The AIRs it verifies with are the Lean circuit for the term and
        // Lean's jet table: Lean compares their symbolic export with
        // `Circuit.jetAirs`.
        if plan.is_none() {
            lean_statement("circuit", &["compare-jets", "-"], export_airs_j(t, &a).as_bytes())?;
        }
        let d = &proof.degree_bits;
        let lg = |n: usize| p3_util::log2_strict_usize(n);
        let mut fixed = vec![
            (2, lg(program(t, MIN_LOG).len())),
            (3, lg(roots_pre(jt).len())),
            (4, lg(hdr_pre(jt).len())),
            (5, lg(tmpl_pre(jt).len())),
        ];
        let mut free = vec![0, 1, 6, 7];
        if let Some(p) = plan {
            fixed.push((8, lg(probe::plan_pre(p).len())));
            free.push(9);
        }
        if d.len() != a.len()
            || fixed.iter().any(|&(i, h)| d[i] != h)
            || free.iter().any(|&i| d[i] > MAX_LOG_HEIGHT)
        {
            return Err(format!("heights {d:?} out of bounds"));
        }
        let vd = ProverData::<Config>::from_airs_and_degrees(&config, &a, d)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        let pvs = crate::stmt::public_values(&a);
        let r = verify_batch(&config, &a, proof, &pvs, &vd.common).map_err(|e| format!("verify: {e:?}"));
        if r.is_ok() {
            crate::fsbudget::budget!("jets", &a, proof, &vd.common, config, p3_uni_stark::OpeningShape::new());
        }
        r
    }));
    match verified {
        Ok(r) => r,
        Err(e) => Err(format!("verifier panic: {}", panic_text(&e))),
    }
}

/// The jet verifier's AIRs for a term, in the export format of
/// `src/export.rs`, after the term (`lake exe circuit compare-jets`).
pub fn export_airs_j(t: &Term, v_airs: &[SkiAir]) -> String {
    let mut term = String::new();
    super::export::unparse(t, &mut term);
    let names = ["cpu", "mem", "prog", "roots", "hdr", "tmpl", "pop", "instw", "plan", "pw"];
    let mut s = format!("term {term}\n");
    for (n, a) in names.iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

/// `ski-air export-jets TERM JETS`: the jet verifier's AIRs for a term and
/// its jet file.
pub fn export_jets(term: &str, jets: &std::path::Path) -> Result<String, String> {
    let t = parse(term.trim().as_bytes(), &mut 0);
    let jt = read_jets(jets);
    Ok(export_airs_j(&t, &airs(&t, &jt, None)?))
}

/// The probe verifier's AIRs, after the term and the outcome (`lake exe
/// circuit compare-probe`, which recomputes the plan from the outcome).
pub fn export_airs_p(t: &Term, outcome: &[&str], v_airs: &[SkiAir]) -> String {
    let mut term = String::new();
    super::export::unparse(t, &mut term);
    let names = ["cpu", "mem", "prog", "roots", "hdr", "tmpl", "pop", "instw", "plan", "pw"];
    let mut s = format!("term {term}\noutcome {}\n", outcome.join(" "));
    for (n, a) in names.iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

/// Lean checks that the probe verifier's AIRs, for a term, its jet table and
/// the plan of an outcome, are `Circuit.probeAirs`.
fn compare_probe(t: &Term, jt: &JetTable, plan: &[probe::Seg], outcome: &[&str]) -> Result<(), String> {
    let a = catch_unwind(AssertUnwindSafe(|| airs(t, jt, Some(plan))))
        .map_err(|e| format!("verifier panic: {}", panic_text(&e)))??;
    lean_statement("circuit", &["compare-probe", "-"], export_airs_p(t, outcome, &a).as_bytes())?;
    Ok(())
}

/// `ski-air export-probe TERM JETS OUTCOME…`: the probe verifier's AIRs.
pub fn export_probe(term: &str, jets: &std::path::Path, outcome: &[&str]) -> Result<String, String> {
    let t = parse(term.trim().as_bytes(), &mut 0);
    let jt = read_jets(jets);
    let (plan, _) = probe::lean_plan(outcome)?;
    Ok(export_airs_p(&t, outcome, &airs(&t, &jt, Some(&plan))?))
}

fn prove_and_verify_j(t: &Term, jt: &JetTable, tr: &JTraces, plan: Option<&[probe::Seg]>) -> Outcome {
    let (proof, prove_s) = match prove_j(t, jt, tr, plan) {
        Ok(p) => p,
        Err(e) => return Outcome::Refused(e),
    };
    let t1 = Instant::now();
    match verify_j(t, jt, &proof, plan) {
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
    parse_table(&text)
}

/// A table's text, the table proper: the term, the memory, the rows.
fn parse_table(text: &str) -> Result<(String, Vec<Cell>, Vec<[u32; 3]>), String> {
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
            Some("X") => Cell::Atom(num(1)?),
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
/// What row `i` of a table another producer wrote records, if it is an
/// instantiation: at a licensed root with enough arguments below its
/// counter, the jet's cells written at the counter, and the next row the
/// body's root over the rest.  Anything else is a machine row, which the
/// circuit checks.
pub(crate) fn inst_of_row(
    jt: &JetTable,
    roots: &std::collections::HashMap<u32, u32>,
    mem: &[Cell],
    rows: &[[u32; 3]],
    i: usize,
) -> Option<InstInfo> {
    let [hd, stk, ctr] = rows[i];
    roots.get(&hd).and_then(|&g| {
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
        let written = mem.get(ctr as usize..ctr as usize + n as usize)?;
        if written.iter().zip(&cells).any(|(m, c)| *m != c.0) {
            return None;
        }
        let root = resolve(j.root, ctr, &ps);
        let xroot = if let Op::Arg(q) = j.root { ps[q as usize] } else { 0 };
        let next = ctr.checked_add(n)?;
        (rows.get(i + 1) == Some(&[root, rest, next])).then_some(InstInfo { g, pops, rest, xroot, cells })
    })
}

fn run_of_table(t: &Term, jt: &JetTable, mem: Vec<Cell>, rows: Vec<[u32; 3]>) -> Result<JRun, String> {
    let (loaded, _, _) = load(t);
    if mem.len() < loaded.len() || mem[..loaded.len()] != loaded[..] {
        return Err("the memory table does not begin with the loaded term".into());
    }
    let roots: std::collections::HashMap<u32, u32> = jt.roots.iter().copied().collect();
    let mut out = Vec::with_capacity(rows.len());
    let mut insts = 0;
    for i in 0..rows.len() {
        let info = inst_of_row(jt, &roots, &mem, &rows, i);
        if info.is_some() {
            insts += 1;
        }
        out.push((rows[i], info));
    }
    Ok(JRun { rows: out, heap: mem, loaded, insts, probe: None })
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
    let (proof, prove_s) = prove_j(&t, &jt, &tr, None)?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    verify_j(&t, &jt, &proof, None)?;
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
    // Read each public file once.  Lean checks exactly
    // these bytes, and they are what is parsed below.
    let text = std::fs::read_to_string(corpus).map_err(|e| format!("{}: {e}", corpus.display()))?;
    let line = text
        .lines()
        .find(|l| lean_words(l).first() == Some(&name))
        .ok_or_else(|| format!("no term named {name} in {}", corpus.display()))?
        .to_string();
    let w: Vec<&str> = lean_words(&line);
    if w.len() != 3 {
        return Err(format!("a malformed corpus line for {name}"));
    }
    let jets_path = dir.join(format!("{name}.jets"));
    let jets_text = std::fs::read_to_string(&jets_path).map_err(|e| format!("{}: {e}", jets_path.display()))?;
    lean_statement("jets", &["statement-stdin"], format!("{line}\n{jets_text}").as_bytes())
        .map_err(|e| format!("statement: {e}"))?;
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
    verify_j(&t, &jt, &proof, None)?;
    println!("VERIFIED {name}: the proof checks against its term and Lean's jet table ({:.3} s)", t0.elapsed().as_secs_f64());
    Ok(())
}

// ---------------------------------------------------------------------------
// Probe segments: the output bound
// ---------------------------------------------------------------------------

/// `ski-air probe-prove TERM JETS TABLE PROOF OUTCOME…`: run the term's
/// probe segments for the outcome's plan (Lean's), write the Lean table and
/// the proof, and check the proof verifies.
pub fn probe_prove(term: &std::path::Path, jets: &std::path::Path, table_out: &std::path::Path, proof_out: &std::path::Path, outcome: &[&str]) -> Result<(), String> {
    let term_text = std::fs::read_to_string(term).map_err(|e| format!("{}: {e}", term.display()))?;
    let term_text = term_text.trim();
    let t = parse(term_text.as_bytes(), &mut 0);
    let jt = read_jets(jets);
    let (plan, _) = probe::lean_plan(outcome)?;
    let run = run_probe(&t, &jt, &plan)?;
    let tr = catch_unwind(AssertUnwindSafe(|| build_traces(&t, &jt, &run)))
        .map_err(|e| format!("the run is no table: {}", panic_text(&e)))?;
    std::fs::write(table_out, lean_of(term_text, &run, &tr)).map_err(|e| format!("{}: {e}", table_out.display()))?;
    let (proof, prove_s) = prove_j(&t, &jt, &tr, Some(&plan))?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    compare_probe(&t, &jt, &plan, outcome)?;
    verify_j(&t, &jt, &proof, Some(&plan))?;
    println!(
        "proved {} rows ({} instantiations, {} segments), {} memory cells, in {prove_s:.2} s; proof {} bytes -> {}",
        run.rows.len(),
        run.insts,
        plan.len(),
        run.heap.len(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// A probe table's text: the table proper, then `starts N` and `N` row
/// indices, then `fields n` and `n` lines `a p1 … pa`
/// (`lake exe jets check-probe`'s format).
#[allow(clippy::type_complexity)]
fn parse_probe_table(text: &str) -> Result<(String, Vec<Cell>, Vec<[u32; 3]>, Vec<u32>, Vec<Vec<u32>>), String> {
    let at = text.find("\nstarts ").ok_or("a table with no starts section")?;
    let (term, mem, rows) = parse_table(&text[..at + 1])?;
    let mut ls = text[at + 1..].lines();
    let mut count = |head: &str| -> Result<usize, String> {
        let l = ls.next().ok_or("a truncated probe section")?;
        let w: Vec<&str> = l.split(' ').collect();
        if w.len() != 2 || w[0] != head {
            return Err(format!("expected `{head} N`, found {l:?}"));
        }
        w[1].parse().map_err(|_| format!("a bad count: {l}"))
    };
    let ns = count("starts")?;
    let mut starts = Vec::with_capacity(ns);
    let mut lines = Vec::new();
    for _ in 0..ns {
        lines.push(ls.next().ok_or("a truncated starts section")?.to_string());
    }
    for l in &lines {
        starts.push(l.trim().parse().map_err(|_| format!("a bad start: {l}"))?);
    }
    let mut ls2 = ls;
    let l = ls2.next().ok_or("no fields section")?;
    let w: Vec<&str> = l.split(' ').collect();
    if w.len() != 2 || w[0] != "fields" {
        return Err(format!("expected `fields n`, found {l:?}"));
    }
    let nf: usize = w[1].parse().map_err(|_| format!("a bad count: {l}"))?;
    let mut flds = Vec::with_capacity(nf);
    for _ in 0..nf {
        let l = ls2.next().ok_or("a truncated fields section")?;
        let v: Vec<u32> = l.split(' ').map(|x| x.parse::<u32>()).collect::<Result<_, _>>().map_err(|_| format!("a bad fields line: {l}"))?;
        if v.is_empty() || v.len() != v[0] as usize + 1 {
            return Err(format!("a bad fields line: {l}"));
        }
        flds.push(v[1..].to_vec());
    }
    if ls2.any(|l| !l.trim().is_empty()) {
        return Err("lines after the fields".into());
    }
    Ok((term, mem, rows, starts, flds))
}

/// The run a probe table records, for the plan: the probe rows at the
/// given starts (each segment's pointer read off the next row, its end's
/// pops read off the memory below the counter), and every other row
/// classified as `run_of_table` does.  The traces check the rest.
fn run_of_probe_table(t: &Term, jt: &JetTable, plan: &[probe::Seg], mem: Vec<Cell>, rows: Vec<[u32; 3]>, starts: Vec<u32>, flds: Vec<Vec<u32>>) -> Result<JRun, String> {
    let n = plan.len();
    if starts.len() != n + 1 || flds.len() != n {
        return Err(format!("{} starts and {} field lines for a plan of {n} segments", starts.len(), flds.len()));
    }
    if starts.last().map(|&l| l as usize + 1) != Some(rows.len()) {
        return Err("the last start is not the last row".into());
    }
    let mut run = run_of_table(t, jt, mem, rows)?;
    let mut prow = std::collections::HashMap::new();
    for (j, s) in plan.iter().enumerate() {
        let clk = starts[j] as usize;
        let next = run.rows.get(clk + 1).ok_or(format!("segment {j} starts at the last row"))?.0;
        let end = if j == 0 {
            None
        } else {
            let [_, stk, ctr] = run.rows[clk].0;
            let below = &run.heap[..(ctr as usize).min(run.heap.len())];
            let e = plan[j - 1];
            let (pops, rest) = pop(below, e.arity, stk).ok_or(format!("segment {} ends with too few fields", j - 1))?;
            if pops.iter().map(|p| p.1).collect::<Vec<_>>() != flds[j - 1] {
                return Err(format!("segment {}'s fields are not the ones on its stack", j - 1));
            }
            Some((pops, rest))
        };
        let clkp = if j == 0 { 0 } else { starts[s.parent as usize + 1] };
        // A probe row is no instantiation.
        run.rows[clk].1 = None;
        prow.insert(clk, probe::ProbeRow { seg: j as u32, f: next[0], end, clkp });
    }
    let mut ps = starts.clone();
    ps.pop();
    run.insts = run.rows.iter().filter(|r| r.1.is_some()).count();
    run.probe = Some(probe::ProbeRun { plan: plan.to_vec(), rows: prow, starts: ps, flds });
    Ok(run)
}

/// `ski-air probe-prove-table TERM JETS TABLE PROOF OUTCOME…`: prove the
/// probe table another producer wrote (Avon's) for the term, its jet table
/// and the outcome's plan (Lean's); write the proof, and check it
/// verifies.
pub fn probe_prove_table(term: &std::path::Path, jets: &std::path::Path, table: &std::path::Path, proof_out: &std::path::Path, outcome: &[&str]) -> Result<(), String> {
    let term_text = std::fs::read_to_string(term).map_err(|e| format!("{}: {e}", term.display()))?;
    let term_text = term_text.trim();
    let t = parse(term_text.as_bytes(), &mut 0);
    let jt = read_jets(jets);
    let (plan, _) = probe::lean_plan(outcome)?;
    let text = std::fs::read_to_string(table).map_err(|e| format!("{}: {e}", table.display()))?;
    let (tterm, mem, rows, starts, flds) = parse_probe_table(&text)?;
    if tterm != term_text {
        return Err("the table is for another term".into());
    }
    let run = run_of_probe_table(&t, &jt, &plan, mem, rows, starts, flds)?;
    let tr = catch_unwind(AssertUnwindSafe(|| build_traces(&t, &jt, &run)))
        .map_err(|e| format!("the table is no run: {}", panic_text(&e)))?;
    let (proof, prove_s) = prove_j(&t, &jt, &tr, Some(&plan))?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    compare_probe(&t, &jt, &plan, outcome)?;
    verify_j(&t, &jt, &proof, Some(&plan))?;
    println!(
        "proved {} rows ({} instantiations, {} segments), {} memory cells, in {prove_s:.2} s; proof {} bytes -> {}",
        run.rows.len(),
        run.insts,
        plan.len(),
        run.heap.len(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// `ski-air probe-verify CORPUS JETSDIR NAME PROOF OUTCOME…`: the verifier
/// of an output.  Lean checks the jet file for the term (as `jet-verify`)
/// and gives the outcome's plan; the proof is checked against the term,
/// the jet table and the plan, and nothing else.
pub fn probe_verify(corpus: &std::path::Path, dir: &std::path::Path, name: &str, proof_in: &std::path::Path, outcome: &[&str]) -> Result<(), String> {
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
        return Err(format!("a name must be an identifier, not {name:?}"));
    }
    let text = std::fs::read_to_string(corpus).map_err(|e| format!("{}: {e}", corpus.display()))?;
    let line = text
        .lines()
        .find(|l| lean_words(l).first() == Some(&name))
        .ok_or_else(|| format!("no term named {name} in {}", corpus.display()))?
        .to_string();
    let w: Vec<&str> = lean_words(&line);
    if w.len() != 3 {
        return Err(format!("a malformed corpus line for {name}"));
    }
    let jets_path = dir.join(format!("{name}.jets"));
    let jets_text = std::fs::read_to_string(&jets_path).map_err(|e| format!("{}: {e}", jets_path.display()))?;
    lean_statement("jets", &["statement-stdin"], format!("{line}\n{jets_text}").as_bytes())
        .map_err(|e| format!("statement: {e}"))?;
    let (plan, _) = probe::lean_plan(outcome).map_err(|e| format!("plan: {e}"))?;
    let t = parse(w[2].as_bytes(), &mut 0);
    let jt = parse_jets(&jets_text);
    let bytes = std::fs::read(proof_in).map_err(|e| format!("{}: {e}", proof_in.display()))?;
    let (proof, rest): (JProof, &[u8]) =
        postcard::take_from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    if !rest.is_empty() {
        return Err(format!("{} bytes after the proof", rest.len()));
    }
    let t0 = Instant::now();
    compare_probe(&t, &jt, &plan, outcome)?;
    verify_j(&t, &jt, &proof, Some(&plan))?;
    println!(
        "VERIFIED {name}: the term decodes to {} ({} segments; {:.3} s)",
        outcome.join(" "),
        plan.len(),
        t0.elapsed().as_secs_f64()
    );
    Ok(())
}

/// `ski-air probes CORPUS JETSDIR OUTDIR`: `3 sumto`'s output proved, then
/// forgeries, each of which the verifier must reject.
pub fn probe_main(corpus: &str, dir: &std::path::Path, out: &std::path::Path) -> usize {
    let mut failures = 0;
    let line = match corpus.lines().find(|l| lean_words(l).first() == Some(&"sumto_us")) {
        Some(l) => l,
        None => {
            println!("the corpus has no sumto_us");
            return 1;
        }
    };
    let jets_text = std::fs::read_to_string(dir.join("sumto_us.jets")).unwrap_or_default();
    if let Err(e) = lean_statement("jets", &["statement-stdin"], format!("{line}\n{jets_text}").as_bytes()) {
        println!("the jet file is not Lean's: {e}");
        return 1;
    }
    let term = lean_words(line)[2].to_string();
    let t = parse(term.as_bytes(), &mut 0);
    let jt = parse_jets(&jets_text);
    let plan_of = |o: &[&str]| probe::lean_plan(o).map(|p| p.0);
    let (six, five, err) = match (plan_of(&["val", "6"]), plan_of(&["val", "5"]), plan_of(&["err"])) {
        (Ok(a), Ok(b), Ok(c)) => (a, b, c),
        _ => {
            println!("no plans from Lean");
            return 1;
        }
    };
    let run = match run_probe(&t, &jt, &six) {
        Ok(r) => r,
        Err(e) => {
            println!("sumto_us: FAILED its honest probe run: {e}");
            return 1;
        }
    };
    let tr = build_traces(&t, &jt, &run);
    std::fs::write(out.join("probe_sumto_us.txt"), lean_of(&term, &run, &tr)).unwrap();
    let (pw_h, pop_h) = (tr.pw.as_ref().unwrap().values.len() / probe::PW_W, tr.pop.values.len() / POP_W);
    println!("{:<18} {:>6} {:>6} {:>6} {:>6} {:>8} {:>8}  verdict", "row", "rows", "insts", "segs", "pw", "prove s", "verify s");
    let proof = match prove_j(&t, &jt, &tr, Some(&six)) {
        Ok((p, s)) => {
            let t1 = Instant::now();
            match verify_j(&t, &jt, &p, Some(&six)) {
                Ok(()) => println!(
                    "{:<18} {:>6} {:>6} {:>6} {:>6} {:>8.2} {:>8.3}  verified: decodes to [6] (pop {pop_h})",
                    "sumto_us",
                    run.rows.len(),
                    run.insts,
                    six.len(),
                    pw_h,
                    s,
                    t1.elapsed().as_secs_f64()
                ),
                Err(e) => {
                    println!("sumto_us: FAILED its honest proof: {e}");
                    failures += 1;
                }
            }
            Some(p)
        }
        Err(e) => {
            println!("sumto_us: FAILED to prove: {e}");
            failures += 1;
            None
        }
    };

    println!("\nforgeries (each must be refused or rejected):");
    // Another output: the prover's run refuses it, and the honest proof,
    // offered for it, is rejected.
    for (name, plan) in [("claims_5", &five), ("claims_err", &err)] {
        match run_probe(&t, &jt, plan) {
            Ok(_) => {
                println!("{name:<18} the probe run ACCEPTED a false output");
                failures += 1;
            }
            Err(e) => println!("{name:<18} the probe run refuses it ({e})"),
        }
        if let Some(p) = &proof {
            match verify_j(&t, &jt, p, Some(plan)) {
                Ok(()) => {
                    println!("{name:<18} the proof of [6] VERIFIED for it");
                    failures += 1;
                }
                Err(e) => println!("{name:<18} the proof of [6] is rejected for it ({})", e.chars().take(50).collect::<String>()),
            }
        }
    }
    // One cell of the honest trace changed, per new constraint.
    let later = (0..tr.cpu.values.len() / tr.cpu.width)
        .filter(|&r| tr.cpu.values[r * tr.cpu.width + SEL + 13] == Val::ONE)
        .nth(2)
        .expect("a later probe row");
    let w = tr.cpu.width;
    let tampers: [(&str, usize, usize); 4] = [
        // A child probes another pointer than its parent's field.
        ("forged_field", later, probe::P_F),
        // A segment ends without the nil below its fields.
        ("skipped_nil", later, probe::P_NILACT),
        // The ending segment's marker, claimed one more.
        ("forged_marker", later, FLD),
        // A probe row's count, skipped ahead.
        ("skipped_count", later, probe::P_CNT),
    ];
    let clone = |tr: &JTraces| JTraces {
        cpu: tr.cpu.clone(),
        mem: tr.mem.clone(),
        prog: tr.prog.clone(),
        roots: tr.roots.clone(),
        hdr: tr.hdr.clone(),
        tmpl: tr.tmpl.clone(),
        pop: tr.pop.clone(),
        instw: tr.instw.clone(),
        plan: tr.plan.clone(),
        pw: tr.pw.clone(),
        mem_cells: tr.mem_cells.clone(),
        regs: tr.regs.clone(),
    };
    for (name, r, col) in tampers {
        let mut bad = clone(&tr);
        let v = &mut bad.cpu.values[r * w + col];
        *v = if col == probe::P_NILACT { Val::ZERO } else { *v + Val::ONE };
        failures += report(name, prove_and_verify_j(&t, &jt, &bad, Some(&six)));
    }

    // Tampers no local constraint sees: each changes a provided count or a
    // chain flag, so only a bus balance can refuse it.
    // A surplus SEGEND: a later row offers its fields once more.
    {
        let mut bad = clone(&tr);
        bad.cpu.values[later * w + probe::P_NKIDS] += Val::ONE;
        failures += report("segend_surplus", prove_and_verify_j(&t, &jt, &bad, Some(&six)));
    }
    // A surplus PLAN row.
    {
        let mut bad = clone(&tr);
        bad.plan.as_mut().unwrap().values[0] += Val::ONE;
        failures += report("plan_surplus", prove_and_verify_j(&t, &jt, &bad, Some(&six)));
    }
    // A surplus field: a later row's POP chain offers a field once more.
    {
        let mut bad = clone(&tr);
        let np = bad.pop.values.len() / POP_W;
        match (0..np).find(|&q| bad.pop.values[q * POP_W] == f(later as u32) && bad.pop.values[q * POP_W + 7] == Val::ONE) {
            Some(q) => {
                bad.pop.values[q * POP_W + 6] += Val::ONE;
                failures += report("arg_surplus", prove_and_verify_j(&t, &jt, &bad, Some(&six)));
            }
            None => {
                println!("{:<16} NOT TESTED: no field popped at the later row", "arg_surplus");
                failures += 1;
            }
        }
    }
    // A dropped marker: one PW row switched off.
    {
        let mut bad = clone(&tr);
        let pw = bad.pw.as_mut().unwrap();
        let q = (0..pw.values.len() / probe::PW_W).find(|&q| pw.values[q * probe::PW_W + 5] == Val::ONE).unwrap();
        pw.values[q * probe::PW_W + 5] = Val::ZERO;
        failures += report("pw_dropped", prove_and_verify_j(&t, &jt, &bad, Some(&six)));
    }
    // A child's parent row redirected to an instantiation whose POP chain
    // holds the same pointer at the same index, the ARG and SEGEND counts
    // rebalanced: only SEGEND's key, the parent's segment, refuses it.
    {
        let rows = tr.cpu.values.len() / w;
        let np = tr.pop.values.len() / POP_W;
        let mut tested = false;
        'outer: for r in 0..rows {
            if tr.cpu.values[r * w + SEL + 13] != Val::ONE {
                continue;
            }
            let clkp = tr.cpu.values[r * w + probe::P_CLKP];
            let fld = tr.cpu.values[r * w + probe::S_BASE + 5];
            let pf = tr.cpu.values[r * w + probe::P_F];
            let Some(parent_pop) = (0..np).find(|&q| {
                tr.pop.values[q * POP_W] == clkp && tr.pop.values[q * POP_W + 2] == fld && tr.pop.values[q * POP_W + 7] == Val::ONE
            }) else {
                continue;
            };
            for q in 0..np {
                let c = tr.pop.values[q * POP_W];
                if c == clkp || tr.pop.values[q * POP_W + 7] != Val::ONE {
                    continue;
                }
                if tr.pop.values[q * POP_W + 2] == fld && tr.pop.values[q * POP_W + 4] == pf {
                    let mut bad = clone(&tr);
                    bad.cpu.values[r * w + probe::P_CLKP] = c;
                    bad.pop.values[q * POP_W + 6] += Val::ONE;
                    bad.pop.values[parent_pop * POP_W + 6] -= Val::ONE;
                    let pr = (0..rows).find(|&x| tr.cpu.values[x * w + J_CLK] == clkp).unwrap();
                    bad.cpu.values[pr * w + probe::P_NKIDS] -= Val::ONE;
                    failures += report("parent_redirected", prove_and_verify_j(&t, &jt, &bad, Some(&six)));
                    tested = true;
                    break 'outer;
                }
            }
        }
        if !tested {
            println!("{:<16} NOT TESTED: no instantiation shares a child's pointer", "parent_redirected");
            failures += 1;
        }
    }
    failures
}

fn lean_of(term: &str, run: &JRun, tr: &JTraces) -> String {
    let tb = Table {
        loaded: run.loaded.clone(),
        hd0: 0,
        stk0: 0,
        rows: tr.regs.clone(),
        mem: tr.mem_cells.clone(),
    };
    let mut s = lean_table(term, &tb);
    // With probe segments: the start rows, the last row, the fields.
    if let Some(p) = &run.probe {
        let mut p = p.clone();
        p.starts.push(tr.regs.len() as u32 - 1);
        s.push_str(&probe::lean_probe(&p));
    }
    s
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

/// `ski-air jets-measure TERM JETS TABLE`: run one term plain and jetted,
/// write the jetted table for Lean (`lake exe jets check-src`), and prove
/// and verify it.  A measurement: the jet file is not checked against a
/// statement here, as `ski-air jets` checks the corpus's.
pub fn measure(term_path: &std::path::Path, jets_path: &std::path::Path, table_out: &std::path::Path) -> Result<(), String> {
    let term = std::fs::read_to_string(term_path).map_err(|e| format!("{}: {e}", term_path.display()))?;
    let term = term.trim().to_string();
    let jets_text = std::fs::read_to_string(jets_path).map_err(|e| format!("{}: {e}", jets_path.display()))?;
    let t = parse(term.as_bytes(), &mut 0);
    let jt = parse_jets(&jets_text);
    let plain = run(&t);
    let jr = run_jets(&t, &jt, None);
    let tr = build_traces(&t, &jt, &jr);
    std::fs::write(table_out, lean_of(&term, &jr, &tr)).map_err(|e| format!("{}: {e}", table_out.display()))?;
    let (pop_h, instw_h) = (tr.pop.values.len() / POP_W, tr.instw.values.len() / INSTW_W);
    println!(
        "plain {} rows, {} cells; jetted {} rows, {} cells, {} instantiations; padded CPU {}, POP {}, INSTW {}",
        plain.rows.len(),
        plain.heap.len(),
        jr.rows.len(),
        jr.heap.len(),
        jr.insts,
        tr.regs.len(),
        pop_h,
        instw_h
    );
    match prove_and_verify_j(&t, &jt, &tr, None) {
        Outcome::Verified(p, v) => {
            println!("jetted: proved in {p:.2} s, verified in {v:.3} s");
            Ok(())
        }
        Outcome::Refused(e) | Outcome::Rejected(e) => Err(format!("the jetted table: {e}")),
    }
}

/// `ski-air jets CORPUS JETSDIR OUTDIR`: prove every corpus row jetted.
pub fn main(corpus: &str, corpus_path: &std::path::Path, dir: &std::path::Path, out: &std::path::Path) -> usize {
    let mut failures = 0;
    // The verifier's precondition: for each term it will prove, the jet file
    // is Lean's for that term, with licensed roots.  Each file is read once,
    // and Lean checks those bytes, piped: they are the ones used.
    let mut jet_texts = std::collections::HashMap::new();
    for line in corpus.lines().filter(|l| !l.trim().is_empty()) {
        let name = lean_words(line).first().copied().unwrap_or("").to_string();
        let text = match std::fs::read_to_string(dir.join(format!("{name}.jets"))) {
            Ok(t) => t,
            Err(e) => {
                println!("the jet file for {name}: {e}");
                return 1;
            }
        };
        if let Err(e) = lean_statement("jets", &["statement-stdin"], format!("{line}\n{text}").as_bytes()) {
            println!("the jet files are not Lean's for these terms: {e}");
            return 1;
        }
        jet_texts.insert(name, text);
    }
    let _ = corpus_path;
    let _ = dir;
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
        match prove_and_verify_j(&t, &jt, &tr, None) {
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
        failures += report("forged_write", prove_and_verify_j(&t, &jt, &tr, None));
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
        failures += report("unlicensed_root", prove_and_verify_j(&t, &jt, &tr, None));
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
        let line = corpus.lines().find(|l| lean_words(l).first() == Some(&"sumto_us")).unwrap_or("");
        let text = std::fs::read_to_string(&path).unwrap_or_default();
        match lean_statement("jets", &["statement-stdin"], format!("{line}\n{text}").as_bytes()) {
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
        let text = std::fs::read_to_string(bad.join("ksk.jets")).unwrap_or_default();
        match lean_statement("jets", &["statement-stdin"], format!("ksk 1 ``KSK\n{text}").as_bytes()) {
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
