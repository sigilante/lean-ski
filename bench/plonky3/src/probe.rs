//! Probe segments: the output bound, with jets (`Ski/AirProbe.lean`).
//!
//! A jetted table proves that a term halts.  To prove what it halts to, the
//! table reads the value by probes: the term is applied to marker atoms and
//! run until the head is the marker of the constructor it is; each field is
//! then probed in turn.  The public **plan** (`lake exe jets plan OUTCOME`,
//! `Air.planOf`) lists the segments, one per node of the outcome's probe
//! tree, depth first: each segment's first marker `base`, marker count `k`,
//! expected constructor `ctor` and field count `arity`, and the field of an
//! earlier segment it probes (`parent`, `field`).
//!
//! The CPU gains two kinds and the probe columns (after the jet columns):
//!
//! - **`PFIRST`**, the first row: it starts segment 0 on the loaded term.
//! - **`PLATER`**, the row where a segment ends and the next starts.  It
//!   reads the atom at the head, which must be the ending segment's marker
//!   `ctor + base`; pops its `arity` fields (the POP chain of `src/jets.rs`,
//!   whose rows provide `ARG(clk, i, x)`); reads a nil below them; and
//!   provides `SEGEND(segment, clk)`, with a count the prover commits to
//!   (honestly the segment's field count; any count provides only this
//!   tuple).
//!   The starting segment's term is its parent's field: `SEGEND(parent,
//!   clkp)` and `ARG(clkp, field, F)` are looked up.
//!
//! Both kinds look up the starting segment's `PLAN` row at the probe count
//! `cnt` (0 on the first row, one more after each probe row), and write the
//! markers and a stack of them: the `PW` chain, one row per marker `i`,
//! writes the atom `base + i` at `ctr + i` and `C (ctr + i) (ctr + k + i +
//! 1)` at `ctr + k + i`, and the CPU writes the nil at `ctr + 2k`.  The
//! next registers are `F`, `ctr + k`, `ctr + 2k + 1`: `Air.probeRow`.
//!
//! The last row has counted every segment (`cnt = n`) and ends the last
//! one: the atom at its head is the last segment's marker, and its stack is
//! a nil (the last segment in depth-first order has no fields).
//!
//! **Why the constraints are `Air.AcceptsP`.**  `cnt` starts at 0, grows by
//! one exactly on probe rows, and is `n` on the last row; a probe row looks
//! up `PLAN(cnt, …)`, which exists only for `cnt < n`.  So there are
//! exactly `n` probe rows, the `j`-th at `p j`, the first at row 0, and
//! `p n` is the last row.  Every other row is a transition, an
//! instantiation or a halted repeat, as in `src/jets.rs`.  Segment `j` ends
//! at row `p (j + 1)`: the `PLATER` row with `cnt = j + 1`, whose end check
//! looks up `PLAN(cnt - 1, …)`, or the last row.  Its fields `fld j` are
//! the POP chain's `x`s: exactly `arity` cells, each range-checked below the
//! counter, then a nil (`Air.endRow`).  A later segment's pointer is
//! `(fld parent)[field]`: `SEGEND` is provided only by `PLATER` rows, under
//! their own `clk`, which is unique, so `clkp` is the parent's end row, and
//! `ARG(clkp, field, F)` is provided only by that row's POP chain (an
//! instantiation's chain is under its own `clk`), at a position below the
//! arity.  So an accepted table satisfies `Air.AcceptsP`, and `lake exe jets
//! check-probe` checks that on every table proved here
//! (`Air.checkPA_decodes`).

use super::*;

pub const PLAN: &str = "plan";
pub const PWCH: &str = "pwch";
pub const SEGEND: &str = "segend";
const ARG: &str = "arg";
const POPCH: &str = "popch";

// ---------------------------------------------------------------------------
// The plan
// ---------------------------------------------------------------------------

/// A segment: `Air.Seg`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Seg {
    pub base: u32,
    pub k: u32,
    pub ctor: u32,
    pub arity: u32,
    pub parent: u32,
    pub field: u32,
}

/// A plan's text, as `lake exe jets plan` prints it.
pub fn parse_plan(text: &str) -> Result<Vec<Seg>, String> {
    let mut ls = text.lines();
    let h: Vec<&str> = ls.next().ok_or("an empty plan")?.split(' ').collect();
    if h.len() != 2 || h[0] != "plan" {
        return Err("a plan must start with `plan n`".into());
    }
    let n: usize = h[1].parse().map_err(|_| "a plan count")?;
    let mut plan = Vec::with_capacity(n);
    for _ in 0..n {
        let l = ls.next().ok_or("a truncated plan")?;
        let v: Vec<u32> = l.split(' ').map(|x| x.parse::<u32>()).collect::<Result<_, _>>().map_err(|_| format!("a bad segment: {l}"))?;
        if v.len() != 6 {
            return Err(format!("a bad segment: {l}"));
        }
        plan.push(Seg { base: v[0], k: v[1], ctor: v[2], arity: v[3], parent: v[4], field: v[5] });
    }
    if ls.next().is_some() {
        return Err("lines after the plan".into());
    }
    Ok(plan)
}

/// The plan of an outcome, from Lean: `lake exe jets plan OUTCOME`.
pub fn lean_plan(outcome: &[&str]) -> Result<(Vec<Seg>, String), String> {
    let mut args = vec!["plan"];
    args.extend_from_slice(outcome);
    let text = lean_statement("jets", &args, b"")?;
    Ok((parse_plan(&text)?, text))
}

/// What the CPU's last-row constraints need of the plan.
#[derive(Clone, Debug)]
pub struct ProbePub {
    /// The number of segments.
    pub n: u32,
    /// The last segment's marker, `ctor + base`.
    pub last_atom: u32,
}

impl ProbePub {
    /// The last segment must have no fields: in a depth-first plan it has
    /// no children to probe them.
    pub fn of(plan: &[Seg]) -> Result<ProbePub, String> {
        let last = plan.last().ok_or("an empty plan")?;
        if last.arity != 0 {
            return Err("the last segment has fields".into());
        }
        Ok(ProbePub { n: plan.len() as u32, last_atom: last.ctor + last.base })
    }
}

/// The PLAN table: `(j, base, k, ctor, arity, parent, field)`, padded with
/// copies of row 0.
pub fn plan_pre(plan: &[Seg]) -> Vec<[u32; 7]> {
    let mut rows: Vec<[u32; 7]> = plan
        .iter()
        .enumerate()
        .map(|(j, s)| [j as u32, s.base, s.k, s.ctor, s.arity, s.parent, s.field])
        .collect();
    let first = rows[0];
    rows.resize(pow2_at_least(rows.len(), MIN_LOG), first);
    rows
}

/// `Air.pcells`: the markers, then a stack of them, from `c`.
pub fn pcells(base: u32, k: u32, c: u32) -> Vec<Cell> {
    let mut cells: Vec<Cell> = (0..k).map(|i| Cell::Atom(base + i)).collect();
    cells.extend((0..k).map(|i| Cell::Cons(c + i, c + k + i + 1)));
    cells.push(Cell::Nil);
    cells
}

// ---------------------------------------------------------------------------
// The CPU's probe columns and constraints
// ---------------------------------------------------------------------------

/// The probe columns, after the jet columns: the probe count; the pointer
/// the starting segment probes; the starting segment's PLAN row; the ending
/// segment's; the rest of the ending stack; the nil read (flag, address,
/// range bits); the parent's end row; how many children read this row's
/// fields.
pub const P_CNT: usize = J_CLK + JET_WIDTH;
pub const P_F: usize = P_CNT + 1;
pub const S_BASE: usize = P_CNT + 2;
pub const E_BASE: usize = P_CNT + 8;
pub const E_REST: usize = P_CNT + 14;
pub const P_NILACT: usize = P_CNT + 15;
pub const P_NILADDR: usize = P_CNT + 16;
pub const P_CLKP: usize = P_CNT + 17;
pub const P_NKIDS: usize = P_CNT + 18;
pub const P_NILBITS: usize = P_CNT + 19;
pub const PROBE_WIDTH: usize = 19 + RANGE_BITS;

/// The CPU's probe constraints; returns the probe rows' parts of the next
/// head, stack and counter.
pub fn eval_cpu_probe<AB: PermutationAirBuilder + InteractionBuilder>(
    b: &mut AB,
    loc: &[AB::Expr],
    nxt: &[AB::Expr],
    p_first: AB::Expr,
    p_later: AB::Expr,
    ha: AB::Expr,
    pp: &ProbePub,
) -> (AB::Expr, AB::Expr, AB::Expr) {
    let one = AB::Expr::ONE;
    let c = |n: u32| AB::Expr::from_u32(n);
    let (hd, stk, ctr) = (loc[HD].clone(), loc[STK].clone(), loc[CTR].clone());
    let clk = loc[J_CLK].clone();
    let a0 = loc[FLD].clone();
    let cnt = loc[P_CNT].clone();
    let pf = loc[P_F].clone();
    let st: Vec<AB::Expr> = (0..6).map(|i| loc[S_BASE + i].clone()).collect();
    let en: Vec<AB::Expr> = (0..6).map(|i| loc[E_BASE + i].clone()).collect();
    let (s_base, s_k, s_par, s_fld) = (st[0].clone(), st[1].clone(), st[4].clone(), st[5].clone());
    let (e_base, e_ctor, e_ar) = (en[0].clone(), en[2].clone(), en[3].clone());
    let rest = loc[E_REST].clone();
    let (nilact, niladdr) = (loc[P_NILACT].clone(), loc[P_NILADDR].clone());
    let (clkp, nkids) = (loc[P_CLKP].clone(), loc[P_NKIDS].clone());
    let probe = p_first.clone() + p_later.clone();

    // The probe count: 0 first, one more after each probe row, `n` last.
    // The first probe row is the first row, and only it.
    b.when_first_row().assert_one(p_first.clone());
    b.when_first_row().assert_zero(cnt.clone());
    b.assert_zero(p_first.clone() * cnt.clone());
    b.when_transition().assert_eq(nxt[P_CNT].clone(), cnt.clone() + probe.clone());

    // The starting segment's PLAN row, at the count.
    let mut srow = vec![cnt.clone()];
    srow.extend(st.iter().cloned());
    b.push_interaction(PLAN, srow, Count::bounded(probe.clone(), 1));

    // A later probe row ends the segment before: its PLAN row; the atom at
    // the head (read by the CPU with tag 6) is its marker; exactly `arity`
    // fields, then a nil.
    let mut erow = vec![cnt.clone() - one.clone()];
    erow.extend(en.iter().cloned());
    b.push_interaction(PLAN, erow, Count::bounded(p_later.clone(), 1));
    b.assert_zero(p_later.clone() * (a0.clone() - e_ctor - e_base));
    b.push_interaction(POPCH, [clk.clone(), ctr.clone(), AB::Expr::ZERO, stk.clone()], Count::bounded(p_later.clone(), 1));
    b.push_interaction(POPCH, [clk.clone(), ctr.clone(), e_ar, rest.clone()], -Count::bounded(p_later.clone(), 1));
    b.assert_bool(nilact.clone());
    b.assert_zero(p_later.clone() * (one.clone() - nilact.clone()));
    b.assert_zero(p_later.clone() * (niladdr.clone() - rest));
    let mut val = AB::Expr::ZERO;
    for i in 0..RANGE_BITS {
        let bit = loc[P_NILBITS + i].clone();
        b.assert_bool(bit.clone());
        val = val + bit * c(1 << i);
    }
    b.assert_zero(nilact.clone() * (ctr.clone() - niladdr.clone() - one.clone() - val));
    b.push_interaction(BUS, [niladdr.clone(), c(4), AB::Expr::ZERO, AB::Expr::ZERO], Count::bounded(nilact.clone(), 1));
    // Its fields are there for its children to read.
    b.assert_zero(nkids.clone() * (one.clone() - p_later.clone()));
    b.push_interaction(SEGEND, [cnt.clone() - one.clone(), clk.clone()], Count::provided(-nkids));

    // The pointer the starting segment probes: the loaded term, or the
    // parent's field.
    b.assert_zero(p_first.clone() * (pf.clone() - hd));
    b.push_interaction(SEGEND, [s_par, clkp.clone()], Count::bounded(p_later.clone(), 1));
    b.push_interaction(ARG, [clkp, s_fld, pf.clone()], Count::bounded(p_later, 1));

    // The writes: the markers and their stack (the PW chain), and the nil.
    b.push_interaction(
        PWCH,
        [clk.clone(), ctr.clone(), s_base.clone(), s_k.clone(), AB::Expr::ZERO],
        Count::bounded(probe.clone(), 1),
    );
    b.push_interaction(PWCH, [clk, ctr.clone(), s_base, s_k.clone(), s_k.clone()], -Count::bounded(probe.clone(), 1));
    b.push_interaction(
        BUS,
        [ctr.clone() + s_k.clone() * c(2), c(4), AB::Expr::ZERO, AB::Expr::ZERO],
        Count::bounded(probe.clone(), 1),
    );

    // The last row: every segment counted, the last one ended at its
    // marker with a nil stack.
    {
        let mut t = b.when_last_row();
        t.assert_eq(cnt, c(pp.n));
        t.assert_one(ha);
        t.assert_eq(a0, c(pp.last_atom));
        t.assert_one(nilact);
        t.assert_eq(niladdr, stk);
    }

    (probe.clone() * pf, probe.clone() * (ctr + s_k.clone()), probe * (s_k * c(2) + one))
}

// ---------------------------------------------------------------------------
// The PLAN and PW tables
// ---------------------------------------------------------------------------

pub const PW_W: usize = 6;

#[derive(Clone, Debug)]
pub enum ProbeAir {
    Plan(Vec<[u32; 7]>),
    /// `clk c base k i act`: one marker and its stack cell.
    Pw,
}

impl ProbeAir {
    pub fn width(&self) -> usize {
        match self {
            ProbeAir::Plan(_) => 1,
            ProbeAir::Pw => PW_W,
        }
    }

    pub fn preprocessed<F: Field>(&self) -> Option<RowMajorMatrix<F>> {
        match self {
            ProbeAir::Plan(p) => Some(RowMajorMatrix::new(p.iter().flat_map(|r| r.iter().map(|&v| F::from_u32(v))).collect(), 7)),
            ProbeAir::Pw => None,
        }
    }

    pub fn preprocessed_width(&self) -> usize {
        match self {
            ProbeAir::Plan(_) => 7,
            ProbeAir::Pw => 0,
        }
    }

    pub fn eval<AB: PermutationAirBuilder + InteractionBuilder>(&self, b: &mut AB) {
        match self {
            ProbeAir::Plan(_) => {
                let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
                let main = b.main();
                let mult: AB::Expr = main.current_slice()[0].into();
                b.push_interaction(PLAN, pre, Count::provided(-mult));
            }
            ProbeAir::Pw => eval_pw(b),
        }
    }
}

/// PW: writes the atom `base + i` at `c + i` and `C (c + i) (c + k + i + 1)`
/// at `c + k + i`, one step of the chain from `0` to `k`.
fn eval_pw<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let (clk, c, base, k, i, act) = (l[0].clone(), l[1].clone(), l[2].clone(), l[3].clone(), l[4].clone(), l[5].clone());
    let one = AB::Expr::ONE;
    b.assert_bool(act.clone());
    b.push_interaction(PWCH, [clk.clone(), c.clone(), base.clone(), k.clone(), i.clone()], -Count::bounded(act.clone(), 1));
    b.push_interaction(
        PWCH,
        [clk, c.clone(), base.clone(), k.clone(), i.clone() + one.clone()],
        Count::bounded(act.clone(), 1),
    );
    b.push_interaction(BUS, [c.clone() + i.clone(), AB::Expr::from_u32(6), base + i.clone(), AB::Expr::ZERO], Count::bounded(act.clone(), 1));
    b.push_interaction(
        BUS,
        [c.clone() + k.clone() + i.clone(), AB::Expr::from_u32(5), c.clone() + i.clone(), c + k + i + one],
        Count::bounded(act, 1),
    );
}

// ---------------------------------------------------------------------------
// The run's probe rows, for the traces
// ---------------------------------------------------------------------------

/// A probe row: the segment it starts and the pointer it probes; for a
/// later one, the ending segment's popped cells `(s, x, s')` and rest, and
/// the parent's end row.
#[derive(Clone, Debug)]
pub struct ProbeRow {
    pub seg: u32,
    pub f: u32,
    pub end: Option<(Vec<(u32, u32, u32)>, u32)>,
    pub clkp: u32,
}

/// The probe side of a run: the probe rows by row index, the segments'
/// start rows (then the last row), and their fields.
#[derive(Clone, Debug)]
pub struct ProbeRun {
    pub plan: Vec<Seg>,
    pub rows: std::collections::HashMap<usize, ProbeRow>,
    pub starts: Vec<u32>,
    pub flds: Vec<Vec<u32>>,
}

/// Fill a row's probe columns; count its memory lookups into `mult`, its
/// PLAN rows into `plan_used`, and push its POP and PW rows.
#[allow(clippy::too_many_arguments)]
pub fn fill_row(
    pr: &ProbeRun,
    clk: usize,
    cnt: u32,
    regs: [u32; 3],
    last: bool,
    row: &mut [Val],
    pc: &mut [Val],
    mult: &mut [u32],
    plan_used: &mut std::collections::HashMap<[u32; 7], u32>,
    pop: &mut Vec<Val>,
    pw: &mut Vec<Val>,
    pop_w: usize,
) {
    let [hd, stk, ctr] = regs;
    let n = pr.plan.len();
    let pre = |j: usize| {
        let s = pr.plan[j];
        [j as u32, s.base, s.k, s.ctor, s.arity, s.parent, s.field]
    };
    pc[P_CNT - P_CNT] = f(cnt);
    let nil_read = |pc: &mut [Val], mult: &mut [u32], addr: u32| {
        assert!(addr < ctr, "a nil read at or above the counter");
        pc[P_NILACT - P_CNT] = Val::ONE;
        pc[P_NILADDR - P_CNT] = f(addr);
        let d = ctr - addr - 1;
        for q in 0..RANGE_BITS {
            pc[P_NILBITS - P_CNT + q] = f((d >> q) & 1);
        }
        mult[addr as usize] += 1;
    };
    if let Some(p) = pr.rows.get(&clk) {
        let j = p.seg as usize;
        assert_eq!(j as u32, cnt, "a probe row out of order");
        let s = pr.plan[j];
        let sp = pre(j);
        for q in 0..6 {
            pc[S_BASE - P_CNT + q] = f(sp[1 + q]);
        }
        *plan_used.entry(sp).or_default() += 1;
        pc[P_F - P_CNT] = f(p.f);
        row[SEL + 12] = Val::ZERO;
        row[SEL + 13] = Val::ZERO;
        match &p.end {
            None => row[SEL + 12] = Val::ONE,
            Some((pops, rest)) => {
                row[SEL + 13] = Val::ONE;
                let e = pr.plan[j - 1];
                let ep = pre(j - 1);
                for q in 0..6 {
                    pc[E_BASE - P_CNT + q] = f(ep[1 + q]);
                }
                *plan_used.entry(ep).or_default() += 1;
                // The atom at the head: the CPU's first read.
                assert!(hd < ctr);
                row[FLD] = f(e.ctor + e.base);
                row[FLD + 1] = Val::ZERO;
                let d = ctr - hd - 1;
                for q in 0..RANGE_BITS {
                    row[BITS + q] = f((d >> q) & 1);
                }
                mult[hd as usize] += 1;
                // The fields: each read by one child.
                for (i, &(sa, x, s2)) in pops.iter().enumerate() {
                    let mut r = vec![Val::ZERO; pop_w];
                    let vals = [clk as u32, ctr, i as u32, sa, x, s2, 1, 1];
                    for q in 0..8 {
                        r[q] = f(vals[q]);
                    }
                    assert!(sa < ctr, "a pop at or above the counter");
                    let d = ctr - sa - 1;
                    for q in 0..RANGE_BITS {
                        r[8 + q] = f((d >> q) & 1);
                    }
                    mult[sa as usize] += 1;
                    pop.extend(r);
                }
                pc[E_REST - P_CNT] = f(*rest);
                nil_read(pc, mult, *rest);
                pc[P_NKIDS - P_CNT] = f(e.arity);
                pc[P_CLKP - P_CNT] = f(p.clkp);
            }
        }
        // The writes.
        for i in 0..s.k {
            pw.extend([clk as u32, ctr, s.base, s.k, i, 1].map(f));
            mult[(ctr + i) as usize] += 1;
            mult[(ctr + s.k + i) as usize] += 1;
        }
        mult[(ctr + 2 * s.k) as usize] += 1;
    } else if last {
        assert_eq!(cnt as usize, n, "the last row before every segment ran");
        nil_read(pc, mult, stk);
    }
}

/// The probe side of the Lean table: the start rows, then the fields.
pub fn lean_probe(pr: &ProbeRun) -> String {
    let mut s = format!("starts {}\n", pr.starts.len());
    for x in &pr.starts {
        s.push_str(&format!("{x}\n"));
    }
    s.push_str(&format!("fields {}\n", pr.flds.len()));
    for fl in &pr.flds {
        s.push_str(&fl.len().to_string());
        for x in fl {
            s.push_str(&format!(" {x}"));
        }
        s.push('\n');
    }
    s
}
