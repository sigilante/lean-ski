//! A zero-knowledge proof of knowledge of a hidden term, checked against
//! Lean (`Ski/Witness.lean`).
//!
//! Part II's atoms are NP relations given by verifier terms: `w` realizes
//! `atom V x` when `V x w` evaluates to `K`.  The statement is the witness
//! machine `Wit.wMachine`, written by `lake exe witness emit` as
//! `public.txt`: a region of `W` cells at addresses `0 … W - 1`, blank, the
//! witness; then `V x` and its application to the region's last cell, with
//! an empty stack.  The verifier sees every cell but the region.
//!
//! **The verifier runs `lake exe witness statement` on `public.txt` first**
//! (`lean_statement`), and refuses it unless it is exactly the witness
//! machine of the atom and region size it names.  By `Wit.wMachine_public`,
//! the blank-region heap states the machine for every region of that size.
//!
//! Four tables under one batch STARK with the hiding PCS of `src/sudoku.rs`:
//!
//! - **CPU** and **memory** at fixed heights (`LOG_ROWS`, `LOG_MEM`,
//!   constants of prover and verifier).  The last row is the halting kind
//!   `HK1`: `K` at the head and a nil at the stack, so the run evaluates to
//!   `K`.
//! - **Program**: the public cells, with their addresses, preprocessed.
//! - **Witness**: one row per region address (preprocessed), committing the
//!   cell there: flags for `S`, `K`, `I` and an application, exactly one set
//!   on an active row, and an application's two pointers, each range-checked
//!   twice, as a 24-bit number and as `i - a - 1`, so `a < i`.  Each row looks
//!   up its cell in memory.
//!
//! **Why an accepted table has a realizer in its region.**  The program and
//! witness lookups name every address below the first counter, so the
//! memory table's prefix is `wMachine ws (V x)` for the region `ws` the
//! witness rows give, and every region cell is `S`, `K`, `I` or an
//! application of two cells below it (`Wit.WF`).  A pointer `a` with
//! `a < 2^24` and `i - a - 1` below `2^24` in the field is below `i`, since
//! `i < 2^LOG_WIT` and the difference would otherwise wrap past `p - 2^24`.
//! With the transition and halting constraints, the table satisfies
//! `Air.AcceptsFrom` from that machine and ends at `K` with an empty stack,
//! which `Wit.wit_realizes` turns into a realizer of the atom.  `lake exe
//! witness check` decides it (`Wit.witCheck_realizes`) on every table proved
//! here.  That the prover *knows* the realizer is the STARK's knowledge
//! soundness, assumed.
//!
//! **What the caller must do.**  The statement names its own atom: the
//! verifier prints `V` and `x`, and whoever reads the verdict must compare
//! them with the atom they meant.  The Lean check reads the whole table,
//! region included, so the tables this program writes, like
//! `witness.txt`, are the prover's and must not be published.
//!
//! **Hiding.**  As in `src/sudoku.rs`: salted commitments and random
//! codewords for the traces, fixed heights, and two blinding messages, from
//! the witness table to the CPU and from the CPU to memory, which make the
//! three private lookup terminals uniform subject to their public sum.  The
//! guess test replays the transcript and recomputes the witness table's
//! terminal for the true region: it must not match.

use super::*;
use p3_lookup::Count;
use p3_uni_stark::StarkGenericConfig;
use crate::seed::{BlindStream, PcsStreams, ProverSeed};
use sudoku::{blind_tuple, public_zk_config, secret_zk_config, postcard_size, report, run_from, set_blind, widen, ZkConfig};

// ---------------------------------------------------------------------------
// The statement
// ---------------------------------------------------------------------------

/// The heights of the CPU and memory tables, fixed for every statement.
const LOG_ROWS: usize = 10;
const LOG_MEM: usize = 10;
/// The witness table's height, and the least height of any table, `2^9`:
/// the quotient's openings need `3 · queries + 8` mask points, 308 at the
/// benchmark setting, above the hiding PCS's own
/// `2 · (queries + 4 · opening points)`, 216.
const LOG_WIT: usize = 9;
const LOG_MIN: usize = 9;
/// The region's cells at most (`WitAir`'s `W ≤ 2^8`).
const MAX_REGION: u32 = 1 << 8;

/// The witness table's committed columns: four flags, the two pointers,
/// four 24-bit decompositions, then the blinding message.
const WT_FLAGS: usize = 0;
const WT_A: usize = 4;
const WT_B: usize = 5;
const WT_BITS: usize = 6;
pub const WT_BLIND: usize = WT_BITS + 4 * RANGE_BITS;
pub const WT_W: usize = WT_BLIND + BLIND_WIDTH;

/// The public part of the statement: `public.txt`.
pub struct Public {
    v: String,
    x: String,
    w: u32,
    hd0: u32,
    stk0: u32,
    ctr0: u32,
    /// The initial heap, `None` in the region.
    cells: Vec<Option<Cell>>,
    /// The statement's bytes, as Lean checked them.
    text: String,
}

fn parse_cell(l: &str) -> Result<Cell, String> {
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

/// A statement file's text, parsed.
pub fn parse_public(text: &str) -> Result<Public, String> {
    let mut ls = text.lines();
    let mut field = |key: &str| -> Result<String, String> {
        let l = ls.next().ok_or("a truncated statement")?;
        l.strip_prefix(&format!("{key} ")).map(String::from).ok_or_else(|| format!("expected `{key} …`, found {l:?}"))
    };
    let v = field("V")?;
    let x = field("x")?;
    let w: u32 = field("W")?.parse().map_err(|_| "a bad region size")?;
    let regs: Vec<u32> = ls
        .next()
        .ok_or("a truncated statement")?
        .split(' ')
        .map(|x| x.parse().map_err(|_| "a bad register".to_string()))
        .collect::<Result<_, _>>()?;
    if regs.len() != 3 {
        return Err("expected `hd stk ctr`".into());
    }
    let mut cells = Vec::with_capacity(regs[2] as usize);
    for l in ls.by_ref().take(regs[2] as usize) {
        cells.push(if l == "W" { None } else { Some(parse_cell(l)?) });
    }
    if cells.len() != regs[2] as usize {
        return Err("a truncated heap".into());
    }
    // Necessary, not sufficient: `lake exe witness statement` checks the rest.
    for (i, c) in cells.iter().enumerate() {
        if c.is_none() != ((i as u32) < w) {
            return Err("the region is not exactly the blank cells".into());
        }
    }
    if w == 0 || w > MAX_REGION {
        return Err(format!("a region of {w} cells"));
    }
    Ok(Public { v, x, w, hd0: regs[0], stk0: regs[1], ctr0: regs[2], cells, text: text.to_string() })
}

/// A region file: `W` cells, one per line.
pub fn read_region(path: &std::path::Path) -> Result<Vec<Cell>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    text.lines().filter(|l| !l.is_empty()).map(parse_cell).collect()
}

/// The initial heap for a region.
fn heap_of(p: &Public, region: &[Cell]) -> Vec<Cell> {
    assert_eq!(region.len(), p.w as usize, "a region of the statement's size");
    p.cells.iter().enumerate().map(|(i, c)| c.unwrap_or_else(|| region[i])).collect()
}

/// The program table: the public cells with their addresses, padded with
/// inactive rows to at least `2^LOG_MIN`.
fn program_of(p: &Public) -> Vec<[u32; 5]> {
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

/// The witness table's preprocessed columns: the region's addresses,
/// active, none in bit mode.
fn wit_pre(p: &Public) -> Vec<[u32; 3]> {
    let mut pre: Vec<[u32; 3]> = (0..p.w).map(|i| [i, 1, 0]).collect();
    pre.resize(1 << LOG_WIT, [0, 0, 0]);
    pre
}

/// The witness verifier's four AIRs for a statement, in the export format
/// of `src/export.rs`, after the statement's text (`lake exe circuit
/// compare-witness` reads both).
pub fn export_witness(text: &str) -> Result<String, String> {
    let p = parse_public(text)?;
    Ok(export_airs(&p, &airs(&p)))
}

fn export_airs(p: &Public, v_airs: &[SkiAir]) -> String {
    let mut s = format!("public {}\n{}", p.text.lines().count(), p.text);
    if !p.text.ends_with('\n') {
        s.push('\n');
    }
    for (n, a) in ["cpu", "mem", "prog", "wit"].iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

/// The verifier's AIRs, from the public statement alone.
fn airs(p: &Public) -> Vec<SkiAir> {
    vec![
        SkiAir::Cpu(CpuAir { hd0: p.hd0, stk0: p.stk0, ctr0: p.ctr0, accept: None, accept_k: true, blind: true, jets: false, probe: None, restart: None, p2: None }),
        SkiAir::Mem(MemAir { blind: true }),
        SkiAir::Prog(ProgAir { pre: program_of(p) }),
        SkiAir::WitT(WitTAir { pre: wit_pre(p) }),
    ]
}

// ---------------------------------------------------------------------------
// The witness table
// ---------------------------------------------------------------------------

/// The witness table: preprocessed `(addr, active, bit)`, committed the
/// cell at `addr`.
#[derive(Clone, Debug)]
pub struct WitTAir {
    pub pre: Vec<[u32; 3]>,
}

/// Each active row is the cell at its address: `S`, `K`, `I`, or `A a b`
/// with `a` and `b` below the address.  A row in bit mode is a Scott
/// Boolean: `K`, or `A 0 1` (`K I`, the slot cells at 0 and 1).
pub fn eval_witt<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let pre: Vec<AB::Expr> = b.preprocessed().current_slice().iter().map(|&v| v.into()).collect();
    let main = b.main();
    let l: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let (addr, act, bit) = (pre[0].clone(), pre[1].clone(), pre[2].clone());
    let one = AB::Expr::ONE;
    let fl: Vec<AB::Expr> = (0..4).map(|q| l[WT_FLAGS + q].clone()).collect();
    for q in 0..4 {
        b.assert_bool(fl[q].clone());
    }
    // Exactly one kind on an active row, none on padding.
    b.assert_eq(fl[0].clone() + fl[1].clone() + fl[2].clone() + fl[3].clone(), act.clone());
    let app = fl[3].clone();
    let (pa, pb) = (l[WT_A].clone(), l[WT_B].clone());
    // A combinator's fields are zero, as memory holds them.
    b.assert_zero((one.clone() - app.clone()) * pa.clone());
    b.assert_zero((one.clone() - app.clone()) * pb.clone());
    // An application's pointers: each below 2^24, and below the address.
    let num = |k: usize| {
        let mut v = AB::Expr::ZERO;
        for i in 0..RANGE_BITS {
            v = v + l[WT_BITS + k * RANGE_BITS + i].clone() * AB::Expr::from_u32(1 << i);
        }
        v
    };
    for i in 0..4 * RANGE_BITS {
        b.assert_bool(l[WT_BITS + i].clone());
    }
    b.assert_zero(app.clone() * (pa.clone() - num(0)));
    b.assert_zero(app.clone() * (addr.clone() - pa.clone() - one.clone() - num(1)));
    b.assert_zero(app.clone() * (pb.clone() - num(2)));
    b.assert_zero(app.clone() * (addr.clone() - pb.clone() - one.clone() - num(3)));
    // Bit mode: no `S`, no `I`, and an application is `A 0 1`.
    b.assert_zero(bit.clone() * (fl[0].clone() + fl[2].clone()));
    b.assert_zero(bit.clone() * pa.clone());
    b.assert_zero(bit * (pb.clone() - app.clone()));
    let tag = fl[1].clone() + fl[2].clone() * AB::Expr::from_u32(2) + app * AB::Expr::from_u32(3);
    b.push_interaction(BUS, [addr, tag, pa, pb], Count::bounded(act, 1));
    blind_msg(b, &l, WT_BLIND, BLIND_A, true);
}

/// The witness trace of a region: its cells, flagged and decomposed.
fn witness_trace(p: &Public, mem: &[Cell], mult: &mut [u32]) -> RowMajorMatrix<Val> {
    let addrs: Vec<u32> = (0..p.w).collect();
    witness_rows(&addrs, 1 << LOG_WIT, mem, mult)
}

/// The witness rows for the cells at `addrs`, one per row, padded to
/// `height` rows.
pub(crate) fn witness_rows(addrs: &[u32], height: usize, mem: &[Cell], mult: &mut [u32]) -> RowMajorMatrix<Val> {
    let mut v = vec![Val::ZERO; height * WT_W];
    for (row, &a) in addrs.iter().enumerate() {
        let i = a as usize;
        let r = &mut v[row * WT_W..(row + 1) * WT_W];
        let c = mem[i];
        let k = match c {
            Cell::S => 0,
            Cell::K => 1,
            Cell::I => 2,
            Cell::App(..) => 3,
            // A cell no witness may hold: the trace sets no flag, and the
            // flag sum refuses it.
            _ => 4,
        };
        if k < 4 {
            r[WT_FLAGS + k] = Val::ONE;
        }
        if let Cell::App(a, b) = c {
            r[WT_A] = f(a);
            r[WT_B] = f(b);
            // Honest decompositions when the pointers are below `i`; a
            // forged forward pointer gets the wrapped difference's low bits,
            // which the constraint refuses.
            let d = |x: u32| (i as u32).wrapping_sub(x).wrapping_sub(1);
            for (q, val) in [a, d(a), b, d(b)].into_iter().enumerate() {
                for bit in 0..RANGE_BITS {
                    r[WT_BITS + q * RANGE_BITS + bit] = f((val >> bit) & 1);
                }
            }
        }
        mult[i] += 1;
    }
    RowMajorMatrix::new(v, WT_W)
}

// ---------------------------------------------------------------------------
// The run and its traces
// ---------------------------------------------------------------------------

pub struct WitTable {
    rows: Vec<[u32; 3]>,
    mem: Vec<Cell>,
    run_rows: usize,
    run_mem: usize,
}

/// The table of the run from `heap`, at the statement's heights.  `None`
/// when the run does not fit them.
fn table(p: &Public, heap: Vec<Cell>) -> Option<WitTable> {
    let (mut rows, mut mem) = run_from(heap, p.hd0, p.stk0);
    let (run_rows, run_mem) = (rows.len(), mem.len());
    if run_rows > 1 << LOG_ROWS || run_mem > 1 << LOG_MEM {
        return None;
    }
    let last = *rows.last().unwrap();
    rows.resize(1 << LOG_ROWS, last);
    mem.resize(1 << LOG_MEM, Cell::Nil);
    Some(WitTable { rows, mem, run_rows, run_mem })
}

/// The last row's head and stack cells.
fn last_cells(tb: &WitTable) -> (Cell, Cell) {
    let [hd, stk, _] = *tb.rows.last().unwrap();
    (tb.mem[hd as usize], tb.mem[stk as usize])
}

/// The four traces, with the blinding messages in row 0 (or, for the
/// guess test's control, with the blinding off).
fn traces(p: &Public, tb: &WitTable, bs: BlindStream) -> [RowMajorMatrix<Val>; 4] {
    traces_b(p, tb, true, bs)
}

fn traces_b(p: &Public, tb: &WitTable, blind: bool, bs: BlindStream) -> [RowMajorMatrix<Val>; 4] {
    let mut mult = vec![0u32; tb.mem.len()];
    let mut cpu = widen(cpu_trace(&tb.rows, &tb.mem, &mut mult), 2 * BLIND_WIDTH);
    let pre = program_of(p);
    for r in &pre {
        if r[4] == 1 {
            mult[r[0] as usize] += 1;
        }
    }
    let mut wit = witness_trace(p, &tb.mem, &mut mult);
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
    [cpu, mem, RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1), wit]
}

/// `ski-air witness-dump PUBLIC REGION DIR`: the honest run's table
/// (`DIR/run.txt`, `lake exe witness check`'s format) and its private
/// traces, CPU, memory and witness, unblinded and blinded
/// (`NAME.blind.txt`, under a fresh seed), for Lean's comparisons (`lake
/// exe witness check-tables`, `check-blind`).
pub fn witness_dump(public: &std::path::Path, region: &std::path::Path, dir: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("witness", &["statement", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public(&text)?;
    let reg = read_region(region)?;
    let tb = table(&p, heap_of(&p, &reg)).ok_or("the run does not fit the statement's heights")?;
    if last_cells(&tb) != (Cell::K, Cell::Nil) {
        return Err(format!("the run ends at {:?}, not K over a nil", last_cells(&tb)));
    }
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    std::fs::write(dir.join("run.txt"), lean_table(&p, &tb)).map_err(|e| format!("run.txt: {e}"))?;
    for (blind, suffix) in [(false, ""), (true, ".blind")] {
        let (bs, _) = ProverSeed::fresh().split();
        let tr = traces_b(&p, &tb, blind, bs);
        for (k, name) in [(0usize, "cpu"), (1, "mem"), (3, "wit")] {
            crate::write_trace(dir, &format!("{name}{suffix}"), &tr[k])?;
        }
    }
    println!("{} rows, {} memory cells -> {}", tb.run_rows, tb.run_mem, dir.display());
    Ok(())
}

/// The table in `lake exe witness check`'s format.
fn lean_table(p: &Public, tb: &WitTable) -> String {
    let mut s = format!("V {}\nx {}\nW {}\n{}\n", p.v, p.x, p.w, tb.mem.len());
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

/// The heights the statement fixes, in the hiding configuration.
fn heights(p: &Public, zk: usize) -> [usize; 4] {
    let prog_log = p3_util::log2_strict_usize(program_of(p).len());
    [LOG_ROWS + zk, LOG_MEM + zk, prog_log + zk, LOG_WIT + zk]
}

/// Prove the traces, then verify the proof against the public statement
/// alone, at the statement's heights.
fn prove_and_verify(p: &Public, traces: &[RowMajorMatrix<Val>; 4], ps: PcsStreams) -> (Outcome, usize) {
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = secret_zk_config(ps);
        let a = airs(p);
        let degrees = heights(p, config.is_zk());
        let t0 = Instant::now();
        let prover_data = ProverData::<ZkConfig>::from_airs_and_degrees(&public_zk_config(), &a, &degrees)
            .map_err(|e| format!("setup: {e:?}"))?;
        let tr: Vec<&RowMajorMatrix<Val>> = traces.iter().collect();
        let pvs = crate::stmt::public_values(&a);
        let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &tr, &pvs), &prover_data)
            .map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    let (proof, prove_s) = match proved {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => return (Outcome::Refused(e), 0),
        Err(e) => return (Outcome::Refused(format!("panic: {}", panic_text(&e))), 0),
    };
    let size = postcard_size(&proof);
    let t1 = Instant::now();
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let v_config = public_zk_config();
        let v_airs = airs(p);
        // The AIRs it verifies with are the Lean circuit for the statement:
        // Lean compares their symbolic export with `Circuit.witAirs`.
        lean_statement("circuit", &["compare-witness", "-"], export_airs(p, &v_airs).as_bytes())?;
        let want = heights(p, v_config.is_zk());
        if proof.degree_bits != want {
            return Err(format!("heights {:?}, the statement's are {want:?}", proof.degree_bits));
        }
        let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &want)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        let r = verify_batch(&v_config, &v_airs, &proof, &crate::stmt::public_values(&v_airs), &v_data.common).map_err(|e| format!("verify: {e:?}"));
        r?;
        // The challenge β must be generic (`Ski/ZK/Reject.lean`).
        crate::reject::check_beta(&v_airs, &proof)?;
        crate::fsbudget::budget!("witness", &v_airs, &proof, &v_data.common, v_config, p3_uni_stark::OpeningShape::hiding(4));
        Ok(())
    }));
    let outcome = match verified {
        Ok(Ok(())) => Outcome::Verified(prove_s, t1.elapsed().as_secs_f64()),
        Ok(Err(e)) => Outcome::Rejected(e),
        Err(e) => Outcome::Rejected(format!("verifier panic: {}", panic_text(&e))),
    };
    (outcome, size)
}

/// The guess test: prove honestly, replay the transcript as a verifier
/// would, and recompute the witness table's terminal for the true region
/// with the blinding columns zero.  Returns whether it matches the published
/// terminal: it must be false, and true with the blinding off, or the test
/// shows nothing.
fn guess_matches(p: &Public, region: &[Cell], blind: bool) -> bool {
    use p3_batch_stark::{BatchShape, BatchVerifierTranscript};
    use p3_lookup::{LogUpGadget, LookupProtocol};
    let tb = table(p, heap_of(p, region)).expect("the honest run fits");
    let (bs, ps) = ProverSeed::fresh().split();
    let tr = traces_b(p, &tb, blind, bs);
    let config = secret_zk_config(ps);
    let a = airs(p);
    let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&public_zk_config(), &a, &heights(p, config.is_zk()))
        .expect("setup");
    let trs: Vec<&RowMajorMatrix<Val>> = tr.iter().collect();
    let pvs: Vec<Vec<Val>> = crate::stmt::public_values(&a);
    let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &trs, &pvs), &pd).expect("prove");
    let v_config = public_zk_config();
    let v_airs = airs(p);
    let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &proof.degree_bits).expect("verifier setup");
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
    let published = proof.lookup_terminals[3].as_ref().expect("a witness terminal").0;
    let pre = <SkiAir as BaseAir<Val>>::preprocessed_trace(&v_airs[3]).expect("witness addresses");
    // The guess: the true region, unblinded.
    let mut mult = vec![0u32; tb.mem.len()];
    let guess_trace = witness_trace(p, &tb.mem, &mut mult);
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

/// `ski-air witness DIR OUTDIR`: DIR holds `lake exe witness emit`'s
/// directories, one per example atom.
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
        // The verifier's precondition: the statement is Lean's.  Read once;
        // Lean checks these bytes, piped, which are the ones parsed.
        let text = match std::fs::read_to_string(d.join("public.txt")) {
            Ok(t) => t,
            Err(e) => {
                println!("{name}/public.txt: {e}");
                failures += 1;
                continue;
            }
        };
        match lean_statement("witness", &["statement", "-"], text.as_bytes()) {
            Err(e) => {
                println!("{name}/public.txt is not a statement: {e}");
                failures += 1;
                continue;
            }
            Ok(msg) => println!("{name}: {}", msg.trim().rsplit(": ").next().unwrap_or("")),
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
            "  {} public cells, a region of {}; heights 2^{LOG_ROWS} rows, 2^{LOG_MEM} memory, 2^{LOG_WIT} witness",
            p.cells.len() - p.w as usize,
            p.w
        );
        let region = match read_region(&d.join("witness.txt")) {
            Ok(r) => r,
            Err(e) => {
                println!("  {e}");
                failures += 1;
                continue;
            }
        };
        let Some(tb) = table(&p, heap_of(&p, &region)) else {
            println!("  honest: the run does not fit the statement's heights");
            failures += 1;
            continue;
        };
        if last_cells(&tb) != (Cell::K, Cell::Nil) {
            println!("  honest: the run ends at {:?}, not K over a nil", last_cells(&tb));
            failures += 1;
            continue;
        }
        std::fs::write(out.join(format!("witness_{name}.txt")), lean_table(&p, &tb)).unwrap();
        let (bs, ps) = ProverSeed::fresh().split();
        match prove_and_verify(&p, &traces(&p, &tb, bs), ps) {
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
        let matched = guess_matches(&p, &region, true);
        let control = guess_matches(&p, &region, false);
        println!(
            "  guess test       the true region, guessed against the published witness terminal: {}; unblinded: {}",
            if matched { "MATCH (the terminal leaks)" } else { "no match" },
            if control { "match" } else { "NO MATCH (the test shows nothing)" }
        );
        if matched || !control {
            failures += 1;
        }
        // A term that realizes nothing, run honestly: the run does not end at K.
        for (tname, file) in [("wrong", "witness_wrong.txt"), ("forged", "witness_forged.txt")] {
            let r = match read_region(&d.join(file)) {
                Ok(r) => r,
                Err(e) => {
                    println!("  {e}");
                    failures += 1;
                    continue;
                }
            };
            let tb_t = table(&p, heap_of(&p, &r)).expect("the tampered run fits");
            let (h, s) = last_cells(&tb_t);
            std::fs::write(out.join(format!("tampered_witness_{name}_{tname}.txt")), lean_table(&p, &tb_t)).unwrap();
            print!("  ");
            failures += report(tname, &format!("ends at {h:?} over {s:?}"), { let (bs, ps) = ProverSeed::fresh().split(); prove_and_verify(&p, &traces(&p, &tb_t, bs), ps).0 });
        }
    }
    failures
}
