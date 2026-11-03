//! The `dec` jet's table (`Ski/Circuit/DecAir.lean`, `Ski/DecJet.lean`):
//! one row per cell of the subject the jet reads.
//!
//! The jet decrements a stack noun `[n r]` encoded as a Scott noun
//! (`DecJet.encNn`: an atom's canonical bits as a Scott list under
//! `Atom`, a cell's halves under `Cell`).  The CPU's jet row sends the
//! subject's pointer on `decn` with the role `0`; the table verifies the
//! subject cell by cell with four kinds of row, each reading the cells of
//! one pattern through up to 25 range-checked lookups:
//!
//! - **CELL** (role 0: the subject; 1: the head; 2: a tail noun): the
//!   `Cell h t` wrapper, `K (S (K K) (S (K K) (S (S I (K h)) (K t))))`; it
//!   requests its halves on `decn` (the head with role 1 when it is the
//!   subject's, else 2).  The subject's row writes the output `Cell`
//!   wrapper at the call's counter `key`, receives the head's verdict on
//!   `decd` (`err`, and the cells the bits wrote), and sends the result's
//!   root and the new counter to the CPU on `decx`.  A head that is a
//!   cell is a crash: the row sends `err = 1`.
//! - **ATOM** (roles as CELL's): the `Atom b` wrapper, `S (K K) (S (K K) (S
//!   (K K) (S I (K b))))`; it starts the bits' chain on `decb` at `b`, in
//!   mode 0 with a borrow when it is the head (and writes the output `Atom`
//!   wrapper at `key + 7`), else in mode 1.  An atom subject is a crash:
//!   `errT` at `key`.
//! - **CONS**: one bit, `K (S (S I (K bit)) (K t))`, the bit `K` or `K I`;
//!   it peeks at `t` to know whether it is the last (a `K`, nil), which
//!   must then be set (canonical bits).  In mode 0 it takes the borrow
//!   step: a clear bit under borrow becomes `K`; the first set bit becomes
//!   `K I` over the input's tail, or is dropped when it is the top bit;
//!   the bits above are shared.  A rewritten bit's six cells go at `key +
//!   12 + 6·lvl` over the input's `S` and `S I` cells; the link to it is
//!   written by the row itself when the borrow ends there, else by the
//!   next row, which knows whether it is dropped.
//! - **NIL**: the end of an empty list, `K`; in mode 0 the head is `0`, a
//!   crash.
//!
//! Every pointer read lies below `key` (24-bit range checks), as the
//! machine's semantics requires; the outputs' cells point at the input's
//! verified cells and at the slots `K` (0), `I` (1), `K I` (2).

use super::*;
use p3_field::PrimeField32;

pub const DECN: &str = "decn";
pub const DECB: &str = "decb";
pub const DECD: &str = "decd";
pub const DECX: &str = "decx";

/// The head atom's bits beyond which the jet does not fire (`DecJet.W`).
pub const DEC_W: u32 = 32;

// The columns.
pub const KEY: usize = 0;
pub const KCELL: usize = 1;
pub const KATOM: usize = 2;
pub const KCONS: usize = 3;
pub const KNIL: usize = 4;
pub const RO: usize = 5;
pub const H0: usize = 6;
pub const H1: usize = 7;
pub const PC: usize = 8;
pub const LVL: usize = 9;
pub const BW: usize = 10;
pub const WC: usize = 11;
pub const BIT: usize = 12;
pub const ISLAST: usize = 13;
pub const NBW: usize = 14;
pub const DROPPED: usize = 15;
pub const WRITES: usize = 16;
pub const WL: usize = 17;
pub const WCN: usize = 18;
pub const NEXTL: usize = 19;
pub const PTR: usize = 20;
pub const ERR: usize = 21;
pub const MODE: usize = 22;
pub const CSEND: usize = 23;
pub const DONE0: usize = 24;
pub const DONE1: usize = 25;
pub const SUB: usize = 26;
pub const HC: usize = 27;
pub const ASUB: usize = 28;
pub const HAT: usize = 29;
pub const CW: usize = 30;
pub const CWL: usize = 31;
pub const CLK: usize = 32;
pub const NLK: usize = 33;
pub const SUBERR: usize = 34;
pub const CG: usize = 35;
pub const LB: usize = 36;
pub const NLB: usize = 5;
pub const NSLOT: usize = 25;
pub const ADDR: usize = LB + NLB;
pub const TAG: usize = ADDR + NSLOT;
pub const DFLD: usize = TAG + NSLOT;
pub const DBITS: usize = DFLD + 2 * NSLOT;
/// The columns before the blinding block.
pub const DEC_W_COLS: usize = DBITS + RANGE_BITS * NSLOT;
/// The blinding block: the edge `CPU —c— DEC`.
pub const DEC_BLOCKS: [(&str, bool); 1] = [("blind_c", false)];

/// Where a slot reads: the row's pointer, or a field of an earlier slot.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Src {
    P,
    F1(usize),
    F2(usize),
}

/// What tag a slot expects: a constant, the bit's (`3 - 2·bit`), or the
/// peeked tail's (`3 - 2·islast`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Tg {
    C(u32),
    BitTag,
    LastTag,
}

use Src::*;
use Tg::*;

/// The CELL pattern's slots.
pub const CELL_SLOTS: [(Src, Tg); 25] = [
    (P, C(3)), (F1(0), C(1)), (F2(0), C(3)), (F1(2), C(3)), (F1(3), C(0)), (F2(3), C(3)), (F1(5), C(1)),
    (F2(5), C(1)), (F2(2), C(3)), (F1(8), C(3)), (F1(9), C(0)), (F2(9), C(3)), (F1(11), C(1)), (F2(11), C(1)),
    (F2(8), C(3)), (F1(14), C(3)), (F1(15), C(0)), (F2(15), C(3)), (F1(17), C(3)), (F1(18), C(0)), (F2(18), C(2)),
    (F2(17), C(3)), (F1(21), C(1)), (F2(14), C(3)), (F1(23), C(1)),
];
/// The ATOM pattern's slots.
pub const ATOM_SLOTS: [(Src, Tg); 24] = [
    (P, C(3)), (F1(0), C(3)), (F1(1), C(0)), (F2(1), C(3)), (F1(3), C(1)), (F2(3), C(1)), (F2(0), C(3)),
    (F1(6), C(3)), (F1(7), C(0)), (F2(7), C(3)), (F1(9), C(1)), (F2(9), C(1)), (F2(6), C(3)), (F1(12), C(3)),
    (F1(13), C(0)), (F2(13), C(3)), (F1(15), C(1)), (F2(15), C(1)), (F2(12), C(3)), (F1(18), C(3)), (F1(19), C(0)),
    (F2(19), C(2)), (F2(18), C(3)), (F1(22), C(1)),
];
/// The CONS pattern's slots; slots 12 and 13 read the clear bit's `K` and
/// `I`, gated by `1 - bit`.
pub const CONS_SLOTS: [(Src, Tg); 17] = [
    (P, C(3)), (F1(0), C(1)), (F2(0), C(3)), (F1(2), C(3)), (F1(3), C(0)), (F2(3), C(3)), (F1(5), C(3)),
    (F1(6), C(0)), (F2(6), C(2)), (F2(5), C(3)), (F1(9), C(1)), (F2(9), BitTag), (F1(11), C(1)), (F2(11), C(2)),
    (F2(2), C(3)), (F1(14), C(1)), (F2(14), LastTag),
];
pub const CONS_GATED: [usize; 2] = [12, 13];

// The cells the patterns leave in the fields, by slot.
// CELL: a1 = f1_2, a2 = f1_8, s3 = f1_15, si = f1_17, kt = f2_14, h = f2_21, t = f2_23.
// ATOM: a1 = f1_0, a2 = f1_6, a3 = f1_12, si = f1_18, b = f2_22.
// CONS: s = f1_3, c5 = f1_5, h = f2_9, t = f2_14.

pub fn f1(j: usize) -> usize {
    DFLD + 2 * j
}
pub fn f2(j: usize) -> usize {
    DFLD + 2 * j + 1
}

/// **The table's constraints and messages**, in the order Lean's `decAir`
/// lists them.
pub fn eval_dec<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let one = AB::Expr::ONE;
    let c = |n: u32| AB::Expr::from_u32(n);
    let v = |i: usize| l[i].clone();
    let (key, kcell, katom, kcons, knil) = (v(KEY), v(KCELL), v(KATOM), v(KCONS), v(KNIL));
    let (ro, h0, h1, p, lvl, bw, wc) = (v(RO), v(H0), v(H1), v(PC), v(LVL), v(BW), v(WC));
    let (bit, islast, nbw, dropped, writes, wl, wcn, nextl, ptr, err, m) =
        (v(BIT), v(ISLAST), v(NBW), v(DROPPED), v(WRITES), v(WL), v(WCN), v(NEXTL), v(PTR), v(ERR), v(MODE));
    let (csend, done0, done1, sub, hc, asub, hat, cw, cwl, clk, nlk, suberr, cg) = (
        v(CSEND), v(DONE0), v(DONE1), v(SUB), v(HC), v(ASUB), v(HAT), v(CW), v(CWL), v(CLK), v(NLK), v(SUBERR), v(CG),
    );
    // One kind at most.
    for k in [KCELL, KATOM, KCONS, KNIL] {
        b.assert_bool(v(k));
    }
    let act = kcell.clone() + katom.clone() + kcons.clone() + knil.clone();
    b.assert_bool(act.clone());
    // The role: 0, 1 or 2, with its indicators.
    b.assert_bool(h0.clone());
    b.assert_bool(h1.clone());
    b.assert_zero(h0.clone() * h1.clone());
    b.assert_zero((kcell.clone() + katom.clone()) * (ro.clone() - (h1.clone() + c(2) * (one.clone() - h0.clone() - h1.clone()))));
    // The bit row's Booleans.
    for k in [BIT, ISLAST, BW, ERR, MODE] {
        b.assert_bool(v(k));
    }
    // Canonical: the last bit is set.
    b.assert_zero(kcons.clone() * islast.clone() * (one.clone() - bit.clone()));
    // The borrow step.
    b.assert_eq(nbw.clone(), bw.clone() * (one.clone() - bit.clone()));
    b.assert_eq(dropped.clone(), bw.clone() * bit.clone() * islast.clone());
    b.assert_eq(writes.clone(), bw.clone() - dropped.clone());
    b.assert_eq(wl.clone(), bw.clone() * bit.clone() * (one.clone() - islast.clone()));
    b.assert_eq(wcn.clone(), wc.clone() + c(6) * writes.clone());
    let a = key.clone() + c(12) + c(6) * lvl.clone();
    b.assert_eq(nextl.clone(), kcons.clone() * (one.clone() - dropped.clone()) * a.clone());
    b.assert_eq(ptr.clone(), kcons.clone() * (c(2) - c(2) * (bit.clone() + bw.clone() - c(2) * bit.clone() * bw.clone())));
    // The counts.
    b.assert_eq(csend.clone(), kcons.clone() * (one.clone() - islast.clone()));
    b.assert_eq(done0.clone(), kcons.clone() * islast.clone() * (one.clone() - m.clone()));
    b.assert_eq(done1.clone(), knil.clone() * (one.clone() - m.clone()));
    b.assert_eq(sub.clone(), kcell.clone() * h0.clone());
    b.assert_eq(hc.clone(), kcell.clone() * h1.clone());
    b.assert_eq(asub.clone(), katom.clone() * h0.clone());
    b.assert_eq(hat.clone(), katom.clone() * h1.clone());
    b.assert_eq(cw.clone(), kcons.clone() * writes.clone());
    b.assert_eq(cwl.clone(), kcons.clone() * wl.clone());
    b.assert_eq(clk.clone(), kcons.clone() * bw.clone());
    b.assert_eq(nlk.clone(), knil.clone() * bw.clone());
    b.assert_eq(suberr.clone(), sub.clone() * err.clone());
    b.assert_eq(cg.clone(), kcons.clone() * (one.clone() - bit.clone()));
    // The level below W in mode 0.
    let mut lv = AB::Expr::ZERO;
    for i in 0..NLB {
        b.assert_bool(v(LB + i));
        lv = lv + v(LB + i) * c(1 << i);
    }
    b.assert_zero(kcons.clone() * (one.clone() - m.clone()) * (lvl.clone() - lv));
    // The reads: each slot's address and tag, muxed by the kind; the
    // address below the key.
    let src = |s: Src| match s {
        P => p.clone(),
        F1(i) => v(f1(i)),
        F2(i) => v(f2(i)),
    };
    let tg = |t: Tg| match t {
        C(n) => c(n),
        BitTag => c(3) - c(2) * bit.clone(),
        LastTag => c(3) - c(2) * islast.clone(),
    };
    for j in 0..NSLOT {
        let mut addr = AB::Expr::ZERO;
        let mut tag = AB::Expr::ZERO;
        let mut actj = AB::Expr::ZERO;
        if let Some(&(s, t)) = CELL_SLOTS.get(j) {
            addr = addr + kcell.clone() * src(s);
            tag = tag + kcell.clone() * tg(t);
            actj = actj + kcell.clone();
        }
        if let Some(&(s, t)) = ATOM_SLOTS.get(j) {
            addr = addr + katom.clone() * src(s);
            tag = tag + katom.clone() * tg(t);
            actj = actj + katom.clone();
        }
        if let Some(&(s, t)) = CONS_SLOTS.get(j) {
            addr = addr + kcons.clone() * src(s);
            tag = tag + kcons.clone() * tg(t);
            actj = actj + if CONS_GATED.contains(&j) { cg.clone() } else { kcons.clone() };
        }
        if j == 0 {
            addr = addr + knil.clone() * p.clone();
            tag = tag + knil.clone() * c(1);
            actj = actj + knil.clone();
        }
        b.assert_eq(v(ADDR + j), addr);
        b.assert_eq(v(TAG + j), tag);
        let mut val = AB::Expr::ZERO;
        for i in 0..RANGE_BITS {
            let bitc = v(DBITS + j * RANGE_BITS + i);
            b.assert_bool(bitc.clone());
            val = val + bitc * c(1 << i);
        }
        b.assert_zero(actj.clone() * (key.clone() - v(ADDR + j) - one.clone() - val));
        b.push_interaction(BUS, [v(ADDR + j), v(TAG + j), v(f1(j)), v(f2(j))], Count::bounded(actj, 1));
    }
    // The needs: this row's, received; the halves', sent.
    b.push_interaction(DECN, [key.clone(), p.clone(), ro.clone()], -Count::bounded(kcell.clone() + katom.clone(), 1));
    b.push_interaction(DECN, [key.clone(), v(f2(21)), c(2) - h0.clone()], Count::bounded(kcell.clone(), 1));
    b.push_interaction(DECN, [key.clone(), v(f2(23)), c(2)], Count::bounded(kcell.clone(), 1));
    // The bits' chain.
    b.push_interaction(
        DECB,
        [key.clone(), v(f2(22)), one.clone() - h1.clone(), c(0), h1.clone(), c(0)],
        Count::bounded(katom.clone(), 1),
    );
    b.push_interaction(DECB, [key.clone(), p.clone(), m.clone(), lvl.clone(), bw.clone(), wc.clone()], -Count::bounded(kcons.clone(), 1));
    b.push_interaction(
        DECB,
        [key.clone(), v(f2(14)), m.clone(), lvl.clone() + one.clone(), nbw.clone(), wcn.clone()],
        Count::bounded(csend, 1),
    );
    b.push_interaction(DECB, [key.clone(), p.clone(), m.clone(), lvl.clone(), bw.clone(), wc.clone()], -Count::bounded(knil.clone(), 1));
    // The head's verdict.
    b.push_interaction(DECD, [key.clone(), err.clone(), wc.clone()], -Count::bounded(sub.clone(), 1));
    b.push_interaction(DECD, [key.clone(), c(0), wcn.clone()], Count::bounded(done0, 1));
    b.push_interaction(DECD, [key.clone(), c(1), wc.clone()], Count::bounded(done1, 1));
    b.push_interaction(DECD, [key.clone(), c(1), c(0)], Count::bounded(hc.clone(), 1));
    // The result, to the CPU.
    b.push_interaction(
        DECX,
        [key.clone(), key.clone() + c(12) * err.clone(), key.clone() + c(12) + wc.clone() + c(3) * err.clone()],
        Count::bounded(sub.clone(), 1),
    );
    b.push_interaction(DECX, [key.clone(), key.clone(), key.clone() + c(3)], Count::bounded(asub.clone(), 1));
    // The writes.
    let w = |b: &mut AB, addr: AB::Expr, x: AB::Expr, y: AB::Expr, count: AB::Expr| {
        b.push_interaction(BUS, [addr, c(3), x, y], Count::bounded(count, 1));
    };
    let k = |n: u32| key.clone() + c(n);
    // The subject's `Cell` wrapper at `key`.
    w(b, k(0), c(0), k(1), sub.clone());
    w(b, k(1), v(f1(2)), k(2), sub.clone());
    w(b, k(2), v(f1(8)), k(3), sub.clone());
    w(b, k(3), k(4), v(f2(14)), sub.clone());
    w(b, k(4), v(f1(15)), k(5), sub.clone());
    w(b, k(5), v(f1(17)), k(6), sub.clone());
    w(b, k(6), c(0), k(7), sub.clone());
    // `errT` at `key + 12` on a crash.
    w(b, k(12), c(0), k(13), suberr.clone());
    w(b, k(13), c(0), k(14), suberr.clone());
    w(b, k(14), c(0), c(1), suberr);
    // A cell head: its `Atom` wrapper's slots filled.
    for i in 7..12 {
        w(b, k(i), c(0), c(0), hc.clone());
    }
    // The head's `Atom` wrapper at `key + 7`.
    w(b, k(7), v(f1(0)), k(8), hat.clone());
    w(b, k(8), v(f1(6)), k(9), hat.clone());
    w(b, k(9), v(f1(12)), k(10), hat.clone());
    w(b, k(10), v(f1(18)), k(11), hat);
    // An atom subject: `errT` at `key`.
    w(b, k(0), c(0), k(1), asub.clone());
    w(b, k(1), c(0), k(2), asub.clone());
    w(b, k(2), c(0), c(1), asub);
    // A rewritten bit's `Cons` at `key + 12 + 6·lvl`.
    let ap = |n: u32| a.clone() + c(n);
    w(b, ap(0), c(0), ap(1), cw.clone());
    w(b, ap(1), ap(2), ap(5), cw.clone());
    w(b, ap(2), v(f1(3)), ap(3), cw.clone());
    w(b, ap(3), v(f1(5)), ap(4), cw.clone());
    w(b, ap(4), c(0), ptr, cw);
    w(b, ap(5), c(0), v(f2(14)), cwl);
    // The link to this bit, from the bit below or the `Atom` wrapper.
    w(b, key.clone() + c(11) + c(6) * lvl.clone(), c(0), nextl, clk);
    w(b, k(11), c(0), c(0), nlk);
}

// ---------------------------------------------------------------------------
// The jet's step: reading the subject, writing the outcome, recording the rows
// ---------------------------------------------------------------------------

/// A row of the table: the columns before the reads, and each slot's
/// `(address, tag, f1, f2)` when active.
#[derive(Clone, Debug)]
pub struct DecRow {
    pub kind: usize,
    pub ro: u32,
    pub m: u32,
    pub p: u32,
    pub lvl: u32,
    pub bw: u32,
    pub wc: u32,
    pub bit: u32,
    pub islast: u32,
    pub err: u32,
    pub slots: Vec<Option<(u32, u32, u32, u32)>>,
}

/// A call of the jet: its rows and the cells it writes from `key`.
#[derive(Clone, Debug)]
pub struct DecCall {
    pub key: u32,
    pub stk: u32,
    pub rows: Vec<DecRow>,
    pub cells: Vec<Cell>,
    pub root: u32,
}

struct Reader<'a> {
    heap: &'a [Cell],
    key: u32,
    rows: Vec<DecRow>,
    written: std::collections::BTreeMap<u32, Cell>,
}

impl<'a> Reader<'a> {
    fn get(&self, a: u32) -> Option<Cell> {
        self.heap.get(a as usize).copied()
    }
    fn app(&self, a: u32) -> Option<(u32, u32)> {
        match self.get(a)? {
            Cell::App(x, y) => Some((x, y)),
            _ => None,
        }
    }
    fn is(&self, a: u32, c: Cell) -> bool {
        self.get(a) == Some(c)
    }
    fn is_skk(&self, a: u32) -> bool {
        match self.app(a) {
            Some((s, kk)) => {
                self.is(s, Cell::S) && matches!(self.app(kk), Some((k1, k2)) if self.is(k1, Cell::K) && self.is(k2, Cell::K))
            }
            None => false,
        }
    }
    fn is_si(&self, a: u32) -> bool {
        matches!(self.app(a), Some((s, i)) if self.is(s, Cell::S) && self.is(i, Cell::I))
    }
    fn write(&mut self, a: u32, c: Cell) {
        let old = self.written.insert(a, c);
        assert!(old.is_none(), "a cell written twice");
    }
    /// The slots' tuples for a pattern at `p`, from the heap, or none when
    /// a cell is not the pattern's.
    fn slots(&self, p: u32, pat: &[(Src, Tg)], bit: u32, islast: u32, gated: &[usize]) -> Option<Vec<Option<(u32, u32, u32, u32)>>> {
        let mut out: Vec<Option<(u32, u32, u32, u32)>> = vec![None; NSLOT];
        for (j, &(s, t)) in pat.iter().enumerate() {
            let addr = match s {
                P => p,
                F1(i) => out[i]?.2,
                F2(i) => out[i]?.3,
            };
            let want = match t {
                C(n) => n,
                BitTag => 3 - 2 * bit,
                LastTag => 3 - 2 * islast,
            };
            if gated.contains(&j) && bit == 1 {
                // An inactive gated slot: its address and tag columns still hold
                // the muxed values (the field, 0 for a `K` bit, and the tag).
                out[j] = Some((addr, want, 0, 0));
                continue;
            }
            if addr >= self.key {
                return None;
            }
            let cell = self.get(addr)?;
            if cell.tag() != want {
                return None;
            }
            let (x, y) = cell.fields();
            out[j] = Some((addr, want, x, y));
        }
        Some(out)
    }
    fn push(&mut self, kind: usize, ro: u32, m: u32, p: u32, lvl: u32, bw: u32, wc: u32, bit: u32, islast: u32, err: u32,
        slots: Vec<Option<(u32, u32, u32, u32)>>) {
        self.rows.push(DecRow { kind, ro, m, p, lvl, bw, wc, bit, islast, err, slots });
    }
    /// A `Cell` wrapper at `p`: its reusable cells `(a1, a2, s3, si, kt, h, t)`.
    fn read_cell(&self, p: u32) -> Option<(u32, u32, u32, u32, u32, u32, u32)> {
        let (k0, y1) = self.app(p)?;
        let (a1, y2) = self.app(y1)?;
        let (a2, y3) = self.app(y2)?;
        let (p1, kt) = self.app(y3)?;
        let (s3, p2) = self.app(p1)?;
        let (k6, t) = self.app(kt)?;
        let (si, kh) = self.app(p2)?;
        let (k5, h) = self.app(kh)?;
        if self.is(k0, Cell::K) && self.is_skk(a1) && self.is_skk(a2) && self.is(s3, Cell::S) && self.is_si(si)
            && self.is(k5, Cell::K) && self.is(k6, Cell::K)
        {
            Some((a1, a2, s3, si, kt, h, t))
        } else {
            None
        }
    }
    /// An `Atom` wrapper at `p`: `(a1, a2, a3, si, b)`.
    fn read_atom(&self, p: u32) -> Option<(u32, u32, u32, u32, u32)> {
        let (a1, x1) = self.app(p)?;
        let (a2, x2) = self.app(x1)?;
        let (a3, x3) = self.app(x2)?;
        let (si, kb) = self.app(x3)?;
        let (k, b) = self.app(kb)?;
        if self.is_skk(a1) && self.is_skk(a2) && self.is_skk(a3) && self.is_si(si) && self.is(k, Cell::K) {
            Some((a1, a2, a3, si, b))
        } else {
            None
        }
    }
    /// A `Cons` at `p`: `(bit, s, c5, t)`.
    fn read_cons(&self, p: u32) -> Option<(bool, u32, u32, u32)> {
        let (k, c1) = self.app(p)?;
        let (c2, c3) = self.app(c1)?;
        let (s, c4) = self.app(c2)?;
        let (k3, t) = self.app(c3)?;
        let (c5, c6) = self.app(c4)?;
        let (k2, h) = self.app(c6)?;
        let bit = match self.get(h)? {
            Cell::K => true,
            Cell::App(f, x) if self.is(f, Cell::K) && self.is(x, Cell::I) => false,
            _ => return None,
        };
        if self.is(k, Cell::K) && self.is(s, Cell::S) && self.is(k3, Cell::K) && self.is_si(c5) && self.is(k2, Cell::K) {
            Some((bit, s, c5, t))
        } else {
            None
        }
    }
    /// The bits' chain from `b`: in mode 0 with the borrow, writing the
    /// rewritten bits; returns `(err, wc)`, or none when the list is not
    /// canonical, too long, or not a list.
    fn bits(&mut self, b: u32, m: u32) -> Option<(u32, u32)> {
        let (mut p, mut lvl, mut bw, mut wc) = (b, 0u32, 1 - m, 0u32);
        let mut fuel = self.heap.len() + 1;
        loop {
            fuel = fuel.checked_sub(1)?;
            if p >= self.key {
                return None;
            }
            if self.is(p, Cell::K) {
                let slots = self.slots(p, &[(P, C(1))], 0, 0, &[])?;
                self.push(KNIL, 0, m, p, lvl, bw, wc, 0, 0, 0, slots);
                if m == 0 {
                    // The head is `0`: a crash; the `Atom` wrapper's link is nil.
                    if bw == 1 {
                        self.write(self.key + 11, Cell::App(0, 0));
                    }
                    return Some((1, wc));
                }
                return Some((0, 0));
            }
            let (bit, s, c5, t) = self.read_cons(p)?;
            if m == 0 && lvl >= DEC_W {
                return None;
            }
            let islast = self.is(t, Cell::K);
            if islast && !bit {
                return None;
            }
            let (bit, islast) = (bit as u32, islast as u32);
            let slots = self.slots(p, &CONS_SLOTS, bit, islast, &CONS_GATED)?;
            let nbw = bw * (1 - bit);
            let dropped = bw * bit * islast;
            let writes = bw - dropped;
            let wl = bw * bit * (1 - islast);
            let o = bit + bw - 2 * bit * bw;
            let a = self.key + 12 + 6 * lvl;
            if bw == 1 {
                self.write(self.key + 11 + 6 * lvl, Cell::App(0, (1 - dropped) * a));
            }
            if writes == 1 {
                self.write(a, Cell::App(0, a + 1));
                self.write(a + 1, Cell::App(a + 2, a + 5));
                self.write(a + 2, Cell::App(s, a + 3));
                self.write(a + 3, Cell::App(c5, a + 4));
                self.write(a + 4, Cell::App(0, 2 - 2 * o));
            }
            if wl == 1 {
                self.write(a + 5, Cell::App(0, t));
            }
            self.push(KCONS, 0, m, p, lvl, bw, wc, bit, islast, 0, slots);
            wc += 6 * writes;
            if islast == 1 {
                return Some((0, if m == 0 { wc } else { 0 }));
            }
            p = t;
            lvl += 1;
            bw = nbw;
        }
    }
    /// A noun at `p` with the role `ro` (1: the head; 2: a tail): an atom
    /// or a cell; returns `(err, wc)` of a head.
    fn noun(&mut self, p: u32, ro: u32, depth: usize) -> Option<(u32, u32)> {
        if depth > self.heap.len() || p >= self.key {
            return None;
        }
        if let Some((a1, a2, a3, si, b)) = self.read_atom(p) {
            let slots = self.slots(p, &ATOM_SLOTS, 0, 0, &[])?;
            self.push(KATOM, ro, 0, p, 0, 0, 0, 0, 0, 0, slots);
            if ro == 1 {
                let k = self.key;
                self.write(k + 7, Cell::App(a1, k + 8));
                self.write(k + 8, Cell::App(a2, k + 9));
                self.write(k + 9, Cell::App(a3, k + 10));
                self.write(k + 10, Cell::App(si, k + 11));
                return self.bits(b, 0);
            }
            self.bits(b, 1)?;
            return Some((0, 0));
        }
        let (_, _, _, _, _, h, t) = self.read_cell(p)?;
        let slots = self.slots(p, &CELL_SLOTS, 0, 0, &[])?;
        self.push(KCELL, ro, 0, p, 0, 0, 0, 0, 0, 0, slots);
        if ro == 1 {
            let k = self.key;
            for i in 7..12 {
                self.write(k + i, Cell::App(0, 0));
            }
        }
        self.noun(h, 2, depth + 1)?;
        self.noun(t, 2, depth + 1)?;
        Some((if ro == 1 { 1 } else { 0 }, 0))
    }
    /// The subject at `p`: the result's root.
    fn subject(&mut self, p: u32) -> Option<u32> {
        let k = self.key;
        if self.read_atom(p).is_some() {
            let slots = self.slots(p, &ATOM_SLOTS, 0, 0, &[])?;
            let (_, _, _, _, b) = self.read_atom(p)?;
            self.push(KATOM, 0, 0, p, 0, 0, 0, 0, 0, 0, slots);
            self.bits(b, 1)?;
            self.write(k, Cell::App(0, k + 1));
            self.write(k + 1, Cell::App(0, k + 2));
            self.write(k + 2, Cell::App(0, 1));
            return Some(k);
        }
        let (a1, a2, s3, si, kt, h, t) = self.read_cell(p)?;
        let slots = self.slots(p, &CELL_SLOTS, 0, 0, &[])?;
        let at = self.rows.len();
        self.push(KCELL, 0, 0, p, 0, 0, 0, 0, 0, 0, slots);
        self.write(k, Cell::App(0, k + 1));
        self.write(k + 1, Cell::App(a1, k + 2));
        self.write(k + 2, Cell::App(a2, k + 3));
        self.write(k + 3, Cell::App(k + 4, kt));
        self.write(k + 4, Cell::App(s3, k + 5));
        self.write(k + 5, Cell::App(si, k + 6));
        self.write(k + 6, Cell::App(0, k + 7));
        let (err, wc) = self.noun(h, 1, 0)?;
        self.noun(t, 2, 0)?;
        self.rows[at].err = err;
        self.rows[at].wc = wc;
        if err == 1 {
            self.write(k + 12, Cell::App(0, k + 13));
            self.write(k + 13, Cell::App(0, k + 14));
            self.write(k + 14, Cell::App(0, 1));
        }
        Some(k + 12 * err)
    }
}

/// **The jet's step** at `(hd, stk)` (`DecJet.decRow`): when the head is
/// the atom `j`, the slots are in place, and the stack's first cell points
/// at a well-formed subject whose head atom fits; the next head and stack,
/// the cells written from the counter, and the call's rows.
pub fn dec_step(heap: &[Cell], hd: u32, stk: u32, j: u32) -> Option<(u32, u32, Vec<Cell>, DecCall)> {
    match heap.get(hd as usize) {
        Some(&Cell::Atom(a)) if a == j => {}
        _ => return None,
    }
    if heap.len() < 3 || heap[0] != Cell::K || heap[1] != Cell::I || heap[2] != Cell::App(0, 1) {
        return None;
    }
    let Cell::Cons(p, rest) = *heap.get(stk as usize)? else { return None };
    let key = heap.len() as u32;
    let mut r = Reader { heap, key, rows: Vec::new(), written: std::collections::BTreeMap::new() };
    let root = r.subject(p)?;
    // The written cells are contiguous from the key.
    let mut cells = Vec::with_capacity(r.written.len());
    for (i, (&a, &c)) in r.written.iter().enumerate() {
        if a != key + i as u32 {
            return None;
        }
        cells.push(c);
    }
    let call = DecCall { key, stk, rows: r.rows, cells: cells.clone(), root };
    Some((root, rest, cells, call))
}

// ---------------------------------------------------------------------------
// The trace
// ---------------------------------------------------------------------------

/// A row's columns before the blinding block, and the memory tuples it
/// sends (reads and writes), for the memory's multiplicities.
pub fn dec_row_values(call: &DecCall, row: &DecRow) -> (Vec<u32>, Vec<[u32; 4]>) {
    let mut v = vec![0u32; DEC_W_COLS];
    let key = call.key;
    v[KEY] = key;
    v[row.kind] = 1;
    let (kcell, katom, kcons, knil) = ((row.kind == KCELL) as u32, (row.kind == KATOM) as u32, (row.kind == KCONS) as u32, (row.kind == KNIL) as u32);
    v[RO] = row.ro;
    let (h0, h1) = if kcell + katom == 1 { ((row.ro == 0) as u32, (row.ro == 1) as u32) } else { (0, 0) };
    v[H0] = h0;
    v[H1] = h1;
    v[PC] = row.p;
    v[LVL] = row.lvl;
    v[BW] = row.bw;
    v[WC] = row.wc;
    v[BIT] = row.bit;
    v[ISLAST] = row.islast;
    let (bit, bw, islast, m) = (row.bit, row.bw, row.islast, row.m);
    let nbw = bw * (1 - bit);
    let dropped = bw * bit * islast;
    let writes = bw - dropped;
    let wl = bw * bit * (1 - islast);
    let wcn = row.wc + 6 * writes;
    let a = key + 12 + 6 * row.lvl;
    let nextl = kcons * (1 - dropped) * a;
    let ptr = kcons * (2 - 2 * (bit + bw - 2 * bit * bw));
    v[NBW] = nbw;
    v[DROPPED] = dropped;
    v[WRITES] = writes;
    v[WL] = wl;
    v[WCN] = wcn;
    v[NEXTL] = nextl;
    v[PTR] = ptr;
    v[ERR] = row.err;
    v[MODE] = m;
    v[CSEND] = kcons * (1 - islast);
    v[DONE0] = kcons * islast * (1 - m);
    v[DONE1] = knil * (1 - m);
    v[SUB] = kcell * h0;
    v[HC] = kcell * h1;
    v[ASUB] = katom * h0;
    v[HAT] = katom * h1;
    v[CW] = kcons * writes;
    v[CWL] = kcons * wl;
    v[CLK] = kcons * bw;
    v[NLK] = knil * bw;
    v[SUBERR] = v[SUB] * row.err;
    v[CG] = kcons * (1 - bit);
    if kcons == 1 && m == 0 {
        for i in 0..NLB {
            v[LB + i] = (row.lvl >> i) & 1;
        }
    }
    let mut mem: Vec<[u32; 4]> = Vec::new();
    for j in 0..NSLOT {
        if let Some((addr, tag, x, y)) = row.slots[j] {
            v[ADDR + j] = addr;
            v[TAG + j] = tag;
            v[f1(j)] = x;
            v[f2(j)] = y;
            let active = !(kcons == 1 && CONS_GATED.contains(&j) && bit == 1);
            if active {
                assert!(addr < key, "a read at or above the key");
                let d = key - addr - 1;
                for i in 0..RANGE_BITS {
                    v[DBITS + j * RANGE_BITS + i] = (d >> i) & 1;
                }
                mem.push([addr, tag, x, y]);
            }
        }
    }
    let f = |j: usize, which: usize| if which == 1 { v[f1(j)] } else { v[f2(j)] };
    let mut w = |count: u32, addr: u32, x: u32, y: u32| {
        if count == 1 {
            mem.push([addr, 3, x, y]);
        }
    };
    let k = |n: u32| key + n;
    w(v[SUB], k(0), 0, k(1));
    w(v[SUB], k(1), f(2, 1), k(2));
    w(v[SUB], k(2), f(8, 1), k(3));
    w(v[SUB], k(3), k(4), f(14, 2));
    w(v[SUB], k(4), f(15, 1), k(5));
    w(v[SUB], k(5), f(17, 1), k(6));
    w(v[SUB], k(6), 0, k(7));
    w(v[SUBERR], k(12), 0, k(13));
    w(v[SUBERR], k(13), 0, k(14));
    w(v[SUBERR], k(14), 0, 1);
    for i in 7..12 {
        w(v[HC], k(i), 0, 0);
    }
    w(v[HAT], k(7), f(0, 1), k(8));
    w(v[HAT], k(8), f(6, 1), k(9));
    w(v[HAT], k(9), f(12, 1), k(10));
    w(v[HAT], k(10), f(18, 1), k(11));
    w(v[ASUB], k(0), 0, k(1));
    w(v[ASUB], k(1), 0, k(2));
    w(v[ASUB], k(2), 0, 1);
    w(v[CW], a, 0, a + 1);
    w(v[CW], a + 1, a + 2, a + 5);
    w(v[CW], a + 2, f(3, 1), a + 3);
    w(v[CW], a + 3, f(5, 1), a + 4);
    w(v[CW], a + 4, 0, ptr);
    w(v[CWL], a + 5, 0, f(14, 2));
    w(v[CLK], key + 11 + 6 * row.lvl, 0, nextl);
    w(v[NLK], k(11), 0, 0);
    (v, mem)
}

/// The table for the calls, padded to `2^min_log` rows or the next power
/// of two with zero rows; the memory multiplicities bumped for each read
/// and write.
pub fn dec_trace(calls: &[DecCall], min_log: usize, mult: &mut [u32]) -> RowMajorMatrix<Val> {
    let n: usize = calls.iter().map(|c| c.rows.len()).sum();
    let h = n.max(1 << min_log).next_power_of_two();
    let mut values = Vec::with_capacity(h * DEC_W_COLS);
    for call in calls {
        for row in &call.rows {
            let (v, mem) = dec_row_values(call, row);
            for [addr, tag, x, y] in mem {
                let cell = mult.get(addr as usize);
                assert!(cell.is_some(), "a tuple past the memory");
                let _ = (tag, x, y);
                mult[addr as usize] += 1;
            }
            values.extend(v.iter().map(|&x| Val::from_u32(x)));
        }
    }
    values.resize(h * DEC_W_COLS, Val::ZERO);
    RowMajorMatrix::new(values, DEC_W_COLS)
}

#[allow(dead_code)]
pub fn canonical(v: Val) -> u32 {
    v.as_canonical_u32()
}
