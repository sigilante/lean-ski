//! A zero-knowledge proof of a composed statement, checked against Lean
//! (`Ski/Composed.lean`).
//!
//! Part II composes proofs of atoms under `∧` and `∨`; `Ski/Compose.lean`
//! compiles a formula to one evaluation statement: public terms
//! `P₀ … Pₙ₋₁` (a check of the formula over hidden bits, and a guard per
//! atom), each of which must evaluate to `K` on the literal bits `β` and a
//! hidden term `w`.  The statement is the composed machine
//! `CompM.cMachine`, written by `lake exe composed emit` as `public.txt`:
//! the slot cells `K`, `I`, `A 0 1`; one cell per bit, blank; the witness
//! region, blank; then the bits' encoding and, for each term, the term and
//! its application to the bits and the witness, whose address is the
//! segment's **root**; then a nil.
//!
//! **The verifier runs `lake exe composed statement` on `public.txt` first**
//! (`lean_statement`), and refuses it unless it is exactly the composed
//! machine of the formula and region size it names (`CompM.cMachine_public`).
//!
//! Five tables under one batch STARK with the hiding PCS of `src/sudoku.rs`:
//!
//! - **CPU** and **memory**, at heights the statement fixes (`log R M`,
//!   default `2^11`).  A new kind, **`RESTART`**,
//!   ends a segment and starts the next: it reads `K` at the head and a nil
//!   at the stack, as `HK1` does, and moves to the next segment's root over
//!   the public nil, the counter unchanged.  Its selector is a restart
//!   column, outside the kinds' one-hot, so tables without segments keep
//!   their layout.  A segment counter starts at 0,
//!   grows by one on each restart, and is `n - 1` on the last row, which is
//!   `HK1`.  So the table has `n` segments, each ending at `K` over the
//!   empty stack (`CompM.AcceptsC`).
//! - **SEGS** `(j, root_j)`, preprocessed from the statement: a restart
//!   looks up `(count + 1, root)`, so segment `j + 1` starts at root `j + 1`.
//! - **Program**: the public cells, with their addresses, preprocessed.
//! - **Witness** (`src/witness.rs`): one row per bit cell and per region
//!   cell.  A bit row is in bit mode, `K` or `A 0 1`; a region row is `S`,
//!   `K`, `I`, or an application of two cells below it.
//!
//! **Why an accepted table has a realizer of the formula.**  The program and
//! witness lookups name every address below the first counter, so the
//! memory's prefix is `cMachine ρ shp region Ps` for the bits `ρ` and the
//! region the witness rows give, the bits literal and the region
//! well-formed.  With the transition, halting and restart constraints the
//! table satisfies `CompM.AcceptsC`, so each term evaluates to `K` on the
//! bits and the witness (`CompM.composed_sound`), which is the formula's
//! statement, and its bits and witness read back as a realizer
//! (`CompM.checkC_realizes`, via `Compose.real_of_accepted`).  `lake exe
//! composed check` decides it on every table proved here.  That the prover
//! *knows* them is the STARK's knowledge soundness, assumed.
//!
//! **Hiding** is the Sudoku proof's: salted commitments and random
//! codewords, the statement's heights, and two blinding messages.  Where each segment
//! ends is a private row index; the roots are public.  The guess test
//! replays the transcript and recomputes the witness table's terminal for
//! the true bits and region: it must not match, and must match with the
//! blinding off.
//!
//! **Predicates.**  A statement may instead be a predicate over literal
//! bits, `predicate V x n` (`Ski/Predicate.lean`): one term, `[ρ w] V x ρ`,
//! whose verifier reads the `n` bits, constrained to `K` or `K I`, and not
//! the witness; an accepted proof has bits on which `V` accepts `x`
//! (`Circuit.predExport_sound`).  The machinery below is the same.
//!
//! **What the caller must do.**  The statement names its own formula: the
//! verifier prints it, and whoever reads the verdict compares it with the
//! formula they meant.  The Lean tables hold the witness in the clear and
//! are the prover's.

use super::*;
use p3_lookup::Count;
use p3_uni_stark::StarkGenericConfig;
use sudoku::{blind_tuple, make_zk_config, postcard_size, report, set_blind, widen, ZkConfig, PUBLIC_SEED};
use witness::{witness_rows, WitTAir, WT_BLIND};

pub const SEGS: &str = "segs";

/// The CPU's restart columns: the restart selector (outside the kinds, so
/// tables without segments keep their layout), the segment count, and the
/// next root.
pub const RESTART_WIDTH: usize = 3;

/// What the CPU's constraints need of the statement.
#[derive(Clone, Debug)]
pub struct RestartPub {
    /// The number of segments.
    pub n: u32,
    /// The nil's address: every segment starts over it.
    pub nil: u32,
}

/// The CPU's restart constraints; returns the restart rows' parts of the
/// next head and stack.  `base` is the first restart column, the selector.
pub fn eval_cpu_restart<AB: PermutationAirBuilder + InteractionBuilder>(
    b: &mut AB,
    loc: &[AB::Expr],
    nxt: &[AB::Expr],
    rs: AB::Expr,
    base: usize,
    rp: &RestartPub,
) -> (AB::Expr, AB::Expr) {
    let one = AB::Expr::ONE;
    let (cnt, root) = (loc[base + 1].clone(), loc[base + 2].clone());
    b.when_first_row().assert_zero(cnt.clone());
    b.when_transition().assert_eq(nxt[base + 1].clone(), cnt.clone() + rs.clone());
    b.when_last_row().assert_eq(cnt.clone(), AB::Expr::from_u32(rp.n - 1));
    // The next segment's root, looked up by its index.
    b.push_interaction(SEGS, [cnt + one, root.clone()], Count::bounded(rs.clone(), 1));
    (rs.clone() * root, rs * AB::Expr::from_u32(rp.nil))
}

/// SEGS: preprocessed `(j, root_j)`, each provided as often as its committed
/// multiplicity says.
#[derive(Clone, Debug)]
pub struct SegsAir {
    pub pre: Vec<[u32; 2]>,
}

pub fn eval_segs<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
    let main = b.main();
    let mult: AB::Expr = main.current_slice()[0].into();
    b.push_interaction(SEGS, pre, Count::provided(-mult));
}

// ---------------------------------------------------------------------------
// The statement
// ---------------------------------------------------------------------------

/// The CPU and memory heights a statement takes when it names none; a
/// statement may name others with a `log R M` line, within
/// `LOG_BOUNDS`.
const LOG_ROWS: usize = 11;
const LOG_MEM: usize = 11;
const LOG_BOUNDS: std::ops::RangeInclusive<usize> = 8..=20;
pub(crate) const LOG_WIT: usize = 8;
/// The least height the hiding PCS commits (`src/witness.rs`).
pub(crate) const LOG_MIN: usize = 8;

pub struct Public {
    /// The statement's first line: `formula …` or `predicate V x n`.
    pub(crate) header: String,
    pub(crate) w: u32,
    /// The CPU's and the memory's log heights.
    pub(crate) log_rows: usize,
    pub(crate) log_mem: usize,
    /// POP's and INSTW's log heights, for the circuit with jets
    /// (`log R M Lp Li`); none for the composed circuit.
    pub(crate) budgets: Option<(usize, usize)>,
    pub(crate) nbits: u32,
    pub(crate) roots: Vec<u32>,
    pub(crate) nil: u32,
    pub(crate) hd0: u32,
    pub(crate) stk0: u32,
    pub(crate) ctr0: u32,
    pub(crate) cells: Vec<Option<Cell>>,
    /// The statement's bytes, as Lean checked them.
    pub(crate) text: String,
}

pub(crate) fn parse_cell(l: &str) -> Result<Cell, String> {
    let w: Vec<&str> = l.split(' ').collect();
    let n = |i: usize| w.get(i).and_then(|x| x.parse::<u32>().ok()).ok_or_else(|| format!("a bad cell: {l}"));
    Ok(match w[0] {
        "S" => Cell::S,
        "K" => Cell::K,
        "I" => Cell::I,
        "N" => Cell::Nil,
        "A" => Cell::App(n(1)?, n(2)?),
        "C" => Cell::Cons(n(1)?, n(2)?),
        "X" => Cell::Atom(n(1)?),
        _ => return Err(format!("a bad cell: {l}")),
    })
}

pub(crate) fn nums(l: &str, key: &str) -> Result<Vec<u32>, String> {
    let rest = l.strip_prefix(&format!("{key} ")).ok_or_else(|| format!("expected `{key} …`, found {l:?}"))?;
    rest.split(' ').map(|x| x.parse().map_err(|_| format!("a bad number in {l:?}"))).collect()
}

/// A statement file's text, parsed.
pub fn parse_public(text: &str) -> Result<Public, String> {
    let mut ls = text.lines();
    let mut next = || ls.next().ok_or_else(|| "a truncated statement".to_string());
    let header = next()?.to_string();
    if !(header.starts_with("formula ") || header.starts_with("predicate ")) {
        return Err("expected `formula …` or `predicate …`".into());
    }
    let w = nums(next()?, "W")?;
    let mut l = next()?;
    let (log_rows, log_mem, budgets) = if l.starts_with("log ") {
        let lg = nums(l, "log")?;
        l = next()?;
        let ok = |x: u32| LOG_BOUNDS.contains(&(x as usize));
        match lg[..] {
            [r, m] if ok(r) && ok(m) && (r, m) != (LOG_ROWS as u32, LOG_MEM as u32) => (r as usize, m as usize, None),
            [r, m, lp, li] if ok(r) && ok(m) && ok(lp) && ok(li) => {
                (r as usize, m as usize, Some((lp as usize, li as usize)))
            }
            _ => return Err("a bad `log` line".into()),
        }
    } else {
        (LOG_ROWS, LOG_MEM, None)
    };
    let nbits = nums(l, "bits")?;
    let roots = nums(next()?, "roots")?;
    let nil = nums(next()?, "nil")?;
    let regs: Vec<u32> = next()?.split(' ').map(|x| x.parse().map_err(|_| "a bad register".to_string())).collect::<Result<_, _>>()?;
    if w.len() != 1 || nbits.len() != 1 || nil.len() != 1 || regs.len() != 3 || roots.is_empty() {
        return Err("a malformed header".into());
    }
    let (w, nbits, nil) = (w[0], nbits[0], nil[0]);
    let mut cells = Vec::with_capacity(regs[2] as usize);
    for _ in 0..regs[2] {
        let l = next()?;
        cells.push(if l == "W" { None } else { Some(parse_cell(l)?) });
    }
    // Necessary, not sufficient: `lake exe composed statement` checks the rest.
    for (i, c) in cells.iter().enumerate() {
        let blank = (i as u32) >= 3 && (i as u32) < 3 + nbits + w;
        if c.is_none() != blank {
            return Err("the bits and the region are not exactly the blank cells".into());
        }
    }
    if nbits + w > 1 << LOG_WIT {
        return Err("too many private cells".into());
    }
    Ok(Public { header, w, log_rows, log_mem, budgets, nbits, roots, nil, hd0: regs[0], stk0: regs[1], ctr0: regs[2], cells, text: text.to_string() })
}

/// A witness file: one line per bit (`1`, `0`, or any cell, for the tamper
/// test), then the region's cells.
pub fn read_witness(p: &Public, path: &std::path::Path) -> Result<Vec<Cell>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let ls: Vec<&str> = text.lines().filter(|l| !l.is_empty()).collect();
    if ls.len() != (p.nbits + p.w) as usize {
        return Err(format!("{}: {} lines, not {}", path.display(), ls.len(), p.nbits + p.w));
    }
    ls.iter()
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
        .collect()
}

/// The initial heap for the private cells (bits, then region).
pub(crate) fn heap_of(p: &Public, private: &[Cell]) -> Vec<Cell> {
    p.cells.iter().enumerate().map(|(i, c)| c.unwrap_or_else(|| private[i - 3])).collect()
}

pub(crate) fn program_of(p: &Public) -> Vec<[u32; 5]> {
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
    pre.resize(pow2_at_least(pre.len(), LOG_MIN), [0, 0, 0, 0, 0]);
    pre
}

/// The private addresses: the bits, in bit mode, then the region.
pub(crate) fn wit_pre(p: &Public) -> Vec<[u32; 3]> {
    let mut pre: Vec<[u32; 3]> = (0..p.nbits).map(|i| [3 + i, 1, 1]).collect();
    pre.extend((0..p.w).map(|i| [3 + p.nbits + i, 1, 0]));
    pre.resize(1 << LOG_WIT, [0, 0, 0]);
    pre
}

pub(crate) fn segs_pre(p: &Public) -> Vec<[u32; 2]> {
    let mut pre: Vec<[u32; 2]> = p.roots.iter().enumerate().map(|(j, &r)| [j as u32, r]).collect();
    let first = pre[0];
    pre.resize(pow2_at_least(pre.len(), LOG_MIN), first);
    pre
}

fn airs(p: &Public) -> Vec<SkiAir> {
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
        }),
        SkiAir::Mem(MemAir { blind: true }),
        SkiAir::Prog(ProgAir { pre: program_of(p) }),
        SkiAir::WitT(WitTAir { pre: wit_pre(p) }),
        SkiAir::Segs(SegsAir { pre: segs_pre(p) }),
    ]
}

// ---------------------------------------------------------------------------
// The run: one segment per root
// ---------------------------------------------------------------------------

pub struct CTable {
    rows: Vec<[u32; 3]>,
    /// The rows that end a segment and start the next.
    restarts: Vec<usize>,
    mem: Vec<Cell>,
    run_rows: usize,
    run_mem: usize,
}

/// The run from the statement's heap, segment by segment: each runs to a
/// halt, and the halted row starts the next segment, wherever it halted.
/// `None` when it does not fit the heights.
fn table(p: &Public, mut heap: Vec<Cell>) -> Option<CTable> {
    let mut rows = Vec::new();
    let mut restarts = Vec::new();
    for (j, &root) in p.roots.iter().enumerate() {
        let (mut hd, mut stk) = (root, p.nil);
        loop {
            if rows.len() >= 1 << p.log_rows {
                return None;
            }
            rows.push([hd, stk, heap.len() as u32]);
            match step(&heap, hd, stk) {
                None => break,
                Some((h, s, ws)) => {
                    heap.extend(ws);
                    hd = h;
                    stk = s;
                }
            }
        }
        if j + 1 < p.roots.len() {
            restarts.push(rows.len() - 1);
        }
    }
    let (run_rows, run_mem) = (rows.len(), heap.len());
    if run_mem > 1 << p.log_mem {
        return None;
    }
    let last = *rows.last().unwrap();
    rows.resize(1 << p.log_rows, last);
    heap.resize(1 << p.log_mem, Cell::Nil);
    Some(CTable { rows, restarts, mem: heap, run_rows, run_mem })
}

/// Each segment's last row: its head and stack cells.
fn ends(tb: &CTable) -> Vec<(Cell, Cell)> {
    let mut v: Vec<(Cell, Cell)> = tb
        .restarts
        .iter()
        .map(|&r| (tb.mem[tb.rows[r][0] as usize], tb.mem[tb.rows[r][1] as usize]))
        .collect();
    let [hd, stk, _] = *tb.rows.last().unwrap();
    v.push((tb.mem[hd as usize], tb.mem[stk as usize]));
    v
}

fn traces(p: &Public, tb: &CTable, blind: bool) -> [RowMajorMatrix<Val>; 5] {
    let mut mult = vec![0u32; tb.mem.len()];
    let cpu0 = cpu_trace(&tb.rows, &tb.mem, &mut mult);
    let mut cpu = widen(cpu0, 2 * BLIND_WIDTH + RESTART_WIDTH);
    let w = cpu.width;
    let base = CPU_WIDTH + 2 * BLIND_WIDTH;
    // The restart rows: the kind the row classified as becomes RESTART (its
    // reads are HK1's when the segment ended at K over a nil), and the
    // segment count and next root.
    let mut cnt = 0u32;
    let mut used: std::collections::HashMap<[u32; 2], u32> = std::collections::HashMap::new();
    for i in 0..tb.rows.len() {
        let r = &mut cpu.values[i * w..(i + 1) * w];
        r[base + 1] = f(cnt);
        if tb.restarts.contains(&i) {
            for k in 0..NKINDS {
                r[SEL + k] = Val::ZERO;
            }
            r[base] = Val::ONE;
            let next = p.roots[cnt as usize + 1];
            r[base + 2] = f(next);
            *used.entry([cnt + 1, next]).or_default() += 1;
            cnt += 1;
        }
    }
    let pre = program_of(p);
    for r in &pre {
        if r[4] == 1 {
            mult[r[0] as usize] += 1;
        }
    }
    let addrs: Vec<u32> = wit_pre(p).iter().filter(|r| r[1] == 1).map(|r| r[0]).collect();
    let mut wit = witness_rows(&addrs, 1 << LOG_WIT, &tb.mem, &mut mult);
    let mut mem = Vec::with_capacity(tb.mem.len() * 5);
    for (i, cell) in tb.mem.iter().enumerate() {
        let (a, b) = cell.fields();
        mem.extend([f(i as u32), f(cell.tag()), f(a), f(b), f(mult[i])]);
    }
    let mut mem = widen(RowMajorMatrix::new(mem, 5), BLIND_WIDTH);
    if blind {
        let (ba, bb) = (blind_tuple(), blind_tuple());
        set_blind(&mut wit, WT_BLIND, ba);
        set_blind(&mut cpu, CPU_BLA, ba);
        set_blind(&mut cpu, CPU_BLB, bb);
        set_blind(&mut mem, 5, bb);
    }
    // SEGS multiplicities, on each tuple's first row.
    let sp = segs_pre(p);
    let mut seen = std::collections::HashSet::new();
    let segs = sp.iter().map(|r| if seen.insert(*r) { f(*used.get(r).unwrap_or(&0)) } else { Val::ZERO }).collect();
    [cpu, mem, RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1), wit, RowMajorMatrix::new(segs, 1)]
}

/// The table in `lake exe composed check`'s format.
fn lean_table(p: &Public, tb: &CTable) -> String {
    let mut s = format!("{}\nW {}\n{}\n", p.header, p.w, tb.mem.len());
    for cell in &tb.mem {
        s.push_str(&cell.lean());
        s.push('\n');
    }
    // The ends: each restart row, then the last row.
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

// ---------------------------------------------------------------------------
// Proving and verifying
// ---------------------------------------------------------------------------

fn heights(p: &Public, zk: usize) -> [usize; 5] {
    let lg = |n: usize| p3_util::log2_strict_usize(n);
    [p.log_rows + zk, p.log_mem + zk, lg(program_of(p).len()) + zk, LOG_WIT + zk, lg(segs_pre(p).len()) + zk]
}

/// A composed proof.
type CProof = p3_batch_stark::BatchProof<ZkConfig>;

/// Prove the traces: the proof and the seconds it took, setup included.
fn prove(p: &Public, tr: &[RowMajorMatrix<Val>; 5]) -> Result<(CProof, f64), String> {
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = make_zk_config(None);
        let a = airs(p);
        let t0 = Instant::now();
        let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&make_zk_config(Some(PUBLIC_SEED)), &a, &heights(p, config.is_zk()))
            .map_err(|e| format!("setup: {e:?}"))?;
        let trs: Vec<&RowMajorMatrix<Val>> = tr.iter().collect();
        let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &trs, &vec![vec![]; 5]), &pd)
            .map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    match proved {
        Ok(r) => r,
        Err(e) => Err(format!("panic: {}", panic_text(&e))),
    }
}

/// **The verifier**: the public statement and the proof, nothing else.  It
/// rebuilds its AIRs and preprocessed commitments from the statement and
/// accepts only the statement's heights.
fn verify(p: &Public, proof: &CProof) -> Result<(), String> {
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let v_config = make_zk_config(Some(PUBLIC_SEED));
        let v_airs = airs(p);
        // The AIRs it verifies with are the Lean circuit for the statement:
        // Lean compares their symbolic export with `Circuit.compAirs`.
        lean_statement("circuit", &["compare-composed", "-"], export_airs(p, &v_airs).as_bytes())?;
        let want = heights(p, v_config.is_zk());
        if proof.degree_bits != want {
            return Err(format!("heights {:?}, the statement's are {want:?}", proof.degree_bits));
        }
        let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &want)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        verify_batch(&v_config, &v_airs, proof, &vec![vec![]; 5], &v_data.common).map_err(|e| format!("verify: {e:?}"))
    }));
    match verified {
        Ok(r) => r,
        Err(e) => Err(format!("verifier panic: {}", panic_text(&e))),
    }
}

fn prove_and_verify(p: &Public, tr: &[RowMajorMatrix<Val>; 5]) -> (Outcome, usize) {
    let (proof, prove_s) = match prove(p, tr) {
        Ok(r) => r,
        Err(e) => return (Outcome::Refused(e), 0),
    };
    let size = postcard_size(&proof);
    let t1 = Instant::now();
    match verify(p, &proof) {
        Ok(()) => (Outcome::Verified(prove_s, t1.elapsed().as_secs_f64()), size),
        Err(e) => (Outcome::Rejected(e), size),
    }
}

/// The statement's bytes, read once and checked by Lean over stdin, then
/// parsed: what Lean checked is what the verifier uses.
/// The composed verifier's five AIRs for a statement, in the export format
/// of `src/export.rs`, after the statement's text (`lake exe circuit
/// compare-composed` reads both).
pub fn export_composed(text: &str) -> Result<String, String> {
    let p = parse_public(text)?;
    Ok(export_airs(&p, &airs(&p)))
}

fn export_airs(p: &Public, v_airs: &[SkiAir]) -> String {
    let mut s = format!("public {}\n{}", p.text.lines().count(), p.text);
    if !p.text.ends_with('\n') {
        s.push('\n');
    }
    for (n, a) in ["cpu", "mem", "prog", "wit", "segs"].iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

pub(crate) fn checked_public(path: &std::path::Path) -> Result<Public, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    lean_statement("composed", &["statement", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    parse_public(&text)
}

/// `ski-air composed-prove PUBLIC WITNESS PROOF [TABLE]`: prove the composed
/// statement for the prover's bits and region, write the proof (and the
/// Lean table), and check the proof verifies.
pub fn composed_prove(public: &std::path::Path, wit: &std::path::Path, proof_out: &std::path::Path, table_out: Option<&std::path::Path>) -> Result<(), String> {
    let p = checked_public(public)?;
    let private = read_witness(&p, wit)?;
    let tb = table(&p, heap_of(&p, &private)).ok_or("the run does not fit the statement's heights")?;
    let e = ends(&tb);
    if let Some(j) = e.iter().position(|&x| x != (Cell::K, Cell::Nil)) {
        return Err(format!("segment {j} ends at {:?}, not K over a nil: the witness does not satisfy the statement", e[j]));
    }
    if let Some(t) = table_out {
        std::fs::write(t, lean_table(&p, &tb)).map_err(|e| format!("{}: {e}", t.display()))?;
    }
    let (proof, prove_s) = prove(&p, &traces(&p, &tb, true))?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    verify(&p, &proof)?;
    println!(
        "proved {} rows, {} memory cells, {} segments, in {prove_s:.2} s; proof {} bytes -> {}",
        tb.run_rows,
        tb.run_mem,
        p.roots.len(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// `ski-air composed-verify PUBLIC PROOF`: **the standalone verifier**.  Lean
/// checks the statement's bytes; the proof, read from its file, must be one
/// byte string and verify against the statement alone.
pub fn composed_verify(public: &std::path::Path, proof_in: &std::path::Path) -> Result<(), String> {
    let p = checked_public(public)?;
    let bytes = std::fs::read(proof_in).map_err(|e| format!("{}: {e}", proof_in.display()))?;
    let (proof, rest): (CProof, &[u8]) = postcard::take_from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    if !rest.is_empty() {
        return Err(format!("{} bytes after the proof", rest.len()));
    }
    let t0 = Instant::now();
    verify(&p, &proof)?;
    println!(
        "VERIFIED: the proof checks against the statement {} ({} segments; {:.3} s)",
        p.header,
        p.roots.len(),
        t0.elapsed().as_secs_f64()
    );
    Ok(())
}

/// The guess test: the witness table's published terminal, against a replay
/// with the true bits and region, unblinded.  Must not match when the
/// proof is blinded, and must match when it is not.
fn guess_matches(p: &Public, private: &[Cell], blind: bool) -> bool {
    use p3_batch_stark::{BatchShape, BatchVerifierTranscript};
    use p3_lookup::{LogUpGadget, LookupProtocol};
    let tb = table(p, heap_of(p, private)).expect("the honest run fits");
    let tr = traces(p, &tb, blind);
    let config = make_zk_config(None);
    let a = airs(p);
    let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&make_zk_config(Some(PUBLIC_SEED)), &a, &heights(p, config.is_zk()))
        .expect("setup");
    let trs: Vec<&RowMajorMatrix<Val>> = tr.iter().collect();
    let pvs: Vec<Vec<Val>> = vec![vec![]; 5];
    let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &trs, &pvs), &pd).expect("prove");
    let v_config = make_zk_config(Some(PUBLIC_SEED));
    let v_airs = airs(p);
    let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &proof.degree_bits).expect("verifier setup");
    verify_batch(&v_config, &v_airs, &proof, &pvs, &v_data.common).expect("the honest proof verifies");
    let common = &v_data.common;
    let shape = BatchShape {
        trace_widths: v_airs.iter().map(|x| <SkiAir as BaseAir<Val>>::width(x)).collect(),
        public_value_counts: vec![0; 5],
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
    t.main_phase(proof.commitments.main.clone(), &pvs);
    t.preprocessed_phase(common.preprocessed.as_ref().map(|g| g.commitment.clone()));
    let chs = t.lookup_phase(&common.lookups, &LogUpGadget::new(), proof.lookup_pow_witness).expect("lookup challenges");
    t.abort();
    let published = proof.lookup_terminals[3].as_ref().expect("a witness terminal").0;
    let pre = <SkiAir as BaseAir<Val>>::preprocessed_trace(&v_airs[3]).expect("witness addresses");
    let addrs: Vec<u32> = wit_pre(p).iter().filter(|r| r[1] == 1).map(|r| r[0]).collect();
    let mut mult = vec![0u32; tb.mem.len()];
    let guess_trace = witness_rows(&addrs, 1 << LOG_WIT, &tb.mem, &mut mult);
    let guess = LogUpGadget::new()
        .generate_permutation::<Val, Challenge>(&guess_trace, &Some(pre), &[], &common.lookups[3], &chs[3])
        .1
        .expect("a terminal")
        .0;
    guess == published
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

/// `ski-air composed DIR OUTDIR`: DIR holds `lake exe composed emit`'s
/// directories, one per example formula.
pub fn main(dir: &std::path::Path, out: &std::path::Path) -> usize {
    let mut failures = 0;
    let mut names: Vec<String> = match std::fs::read_dir(dir) {
        Ok(rd) => rd.filter_map(|e| e.ok()).filter(|e| e.path().is_dir()).map(|e| e.file_name().to_string_lossy().into_owned()).collect(),
        Err(e) => {
            println!("{}: {e}", dir.display());
            return 1;
        }
    };
    names.sort();
    for name in names {
        let d = dir.join(&name);
        let text = match std::fs::read_to_string(d.join("public.txt")) {
            Ok(t) => t,
            Err(e) => {
                println!("{name}/public.txt: {e}");
                failures += 1;
                continue;
            }
        };
        match lean_statement("composed", &["statement", "-"], text.as_bytes()) {
            Err(e) => {
                println!("{name}/public.txt is not a statement: {e}");
                failures += 1;
                continue;
            }
            Ok(_) => println!("{name}: its statement (checked by Lean)"),
        }
        let p = match parse_public(&text) {
            Ok(p) => p,
            Err(e) => {
                println!("{name}: {e}");
                failures += 1;
                continue;
            }
        };
        println!(
            "  {} public cells, {} bits, a region of {}, {} segments; heights 2^{} rows, 2^{} memory, 2^{LOG_WIT} witness",
            p.cells.len() as u32 - p.nbits - p.w,
            p.nbits,
            p.w,
            p.roots.len(),
            p.log_rows,
            p.log_mem
        );
        let private = match read_witness(&p, &d.join("witness.txt")) {
            Ok(r) => r,
            Err(e) => {
                println!("  {e}");
                failures += 1;
                continue;
            }
        };
        let Some(tb) = table(&p, heap_of(&p, &private)) else {
            println!("  honest: the run does not fit the statement's heights");
            failures += 1;
            continue;
        };
        if ends(&tb).iter().any(|&e| e != (Cell::K, Cell::Nil)) {
            println!("  honest: a segment ends at {:?}, not K over a nil", ends(&tb));
            failures += 1;
            continue;
        }
        std::fs::write(out.join(format!("composed_{name}.txt")), lean_table(&p, &tb)).unwrap();
        match prove_and_verify(&p, &traces(&p, &tb, true)) {
            (Outcome::Verified(ps, vs), size) => println!(
                "  honest           {} rows, {} memory cells; prove {ps:.2} s, verify {vs:.3} s, proof {} KiB  verified",
                tb.run_rows,
                tb.run_mem,
                size / 1024
            ),
            (Outcome::Refused(e) | Outcome::Rejected(e), _) => {
                println!("  honest: FAILED: {e}");
                failures += 1;
            }
        }
        let matched = guess_matches(&p, &private, true);
        let control = guess_matches(&p, &private, false);
        println!(
            "  guess test       the true bits and region, against the published witness terminal: {}; unblinded: {}",
            if matched { "MATCH (the terminal leaks)" } else { "no match" },
            if control { "match" } else { "NO MATCH (the test shows nothing)" }
        );
        if matched || !control {
            failures += 1;
        }
        for tname in ["clear", "wrong", "nonbool", "forged"] {
            let r = match read_witness(&p, &d.join(format!("witness_{tname}.txt"))) {
                Ok(r) => r,
                Err(e) => {
                    println!("  {e}");
                    failures += 1;
                    continue;
                }
            };
            let Some(tb_t) = table(&p, heap_of(&p, &r)) else {
                println!("  {tname}: the run does not fit the heights");
                failures += 1;
                continue;
            };
            std::fs::write(out.join(format!("tampered_composed_{name}_{tname}.txt")), lean_table(&p, &tb_t)).unwrap();
            let note = match ends(&tb_t).iter().position(|&e| e != (Cell::K, Cell::Nil)) {
                Some(j) => format!("segment {j} ends at {:?}", ends(&tb_t)[j]),
                None => "every segment ends at K over a nil".to_string(),
            };
            print!("  ");
            failures += report(tname, &note, prove_and_verify(&p, &traces(&p, &tb_t, true)).0);
        }
    }
    failures
}
