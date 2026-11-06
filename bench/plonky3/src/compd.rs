//! A composed statement with the `dec` jet (`Ski/ComposedDText.lean`,
//! `Ski/DecJet.lean`), proved with Plonky3.
//!
//! The statement is `lake exe composed emit-dec`'s: the composed machine of
//! an open verifier whose jet is the atom `J` (`ComposedDText.publicTextD`),
//! `λ β w. CHECK_p (J w)`, the hidden term `w` in the region the subject
//! `[n r]`.  The machine runs as the composed one does, and at `J` with the
//! subject's pointer on the stack it takes the jet's step
//! (`DecJet.decRow`, `src/decair.rs`): it reads the subject cell by cell and
//! writes the decrement, or `errT`, at the counter.
//!
//! Six tables: the composed circuit's five (CPU, memory, program, witness,
//! segments), the CPU carrying the jet's row, and the jet's table DEC, one
//! row per cell pattern of the subject, private, with a blinding block for
//! the blinding tree's edge `CPU —c— DEC`.

use super::*;
use crate::seed::{BlindStream, PcsStreams, ProverSeed};
use composed::{nums, parse_cell, RestartPub, SegsAir, RESTART_WIDTH};
use decair::{dec_step, dec_trace, DecCall};
use p3_uni_stark::StarkGenericConfig;
use sudoku::{blind_tuple, public_zk_config, secret_zk_config, set_blind, widen, ZkConfig};
use witness::{witness_rows, WitTAir, WT_BLIND};

/// The CPU's jet columns: `DECSEL`, the blinding block it sends to DEC on
/// `blind_c`, then the result's root and the new counter, received from
/// DEC on `decx`.
pub const DEC_CPU_WIDTH: usize = 1 + BLIND_WIDTH + 2;

/// What the CPU's jet row needs of the statement: the jet's atom.
#[derive(Clone, Debug)]
pub struct DecPub {
    pub j: u32,
}

/// The jet row's constraints and messages; returns its parts of the next
/// head, stack and counter.  The row's reads are the CPU's reads 0 and 1:
/// the atom `J` at the head and the stack cell `cons p rest`.
pub fn eval_cpu_dec<AB: PermutationAirBuilder + InteractionBuilder>(
    b: &mut AB,
    loc: &[AB::Expr],
    dsel: AB::Expr,
    base: usize,
    dp: &DecPub,
) -> (AB::Expr, AB::Expr, AB::Expr) {
    let c = |n: u32| AB::Expr::from_u32(n);
    let ctr = loc[CTR].clone();
    let (a0, a1, rest) = (loc[FLD].clone(), loc[FLD + 2].clone(), loc[FLD + 3].clone());
    let (droot, dctr) = (loc[base + 1 + BLIND_WIDTH].clone(), loc[base + 2 + BLIND_WIDTH].clone());
    b.assert_zero(dsel.clone() * (a0 - c(dp.j)));
    // The slots: `K`, `I`, `K I` at 0, 1, 2.
    b.push_interaction(BUS, [c(0), c(1), c(0), c(0)], Count::bounded(dsel.clone(), 1));
    b.push_interaction(BUS, [c(1), c(2), c(0), c(0)], Count::bounded(dsel.clone(), 1));
    b.push_interaction(BUS, [c(2), c(3), c(0), c(1)], Count::bounded(dsel.clone(), 1));
    // The subject's need, and the result.
    b.push_interaction(decair::DECN, [ctr.clone(), a1, c(0)], Count::bounded(dsel.clone(), 1));
    b.push_interaction(decair::DECX, [ctr.clone(), droot.clone(), dctr.clone()], -Count::bounded(dsel.clone(), 1));
    // The blinding tree's edge to DEC.
    blind_msg(b, loc, base + 1, BLIND_C, true);
    (dsel.clone() * droot, dsel.clone() * rest, dsel * (dctr - ctr))
}

// ---------------------------------------------------------------------------
// The statement
// ---------------------------------------------------------------------------

pub struct DPublic {
    header: String,
    dp: DecPub,
    w: u32,
    logs: [usize; 3],
    nbits: u32,
    roots: Vec<u32>,
    nil: u32,
    hd0: u32,
    stk0: u32,
    ctr0: u32,
    cells: Vec<Option<Cell>>,
    text: String,
}

/// The statement's text, parsed; `lake exe composed statement-dec` checks
/// it is exactly the statement it names.
pub fn parse_public_d(text: &str) -> Result<DPublic, String> {
    let mut ls = text.lines();
    let mut next = || ls.next().ok_or_else(|| "a truncated statement".to_string());
    let header = next()?.to_string();
    let hw: Vec<&str> = header.split(' ').collect();
    let num = |x: &str| x.parse::<u32>().map_err(|_| "a bad header".to_string());
    // `decpre p J` (one verifier, `λ β w. CHECK_p (J w)`), `decterm J` (the
    // verifiers the heap holds, `Ski/DecTermText.lean`) or `dectermS J` (the
    // same, the heap shared: `Ski/HeapShared.lean`); either way the circuit
    // is the heap's, and Lean's `statement-dec` checks the text.
    let dp = match (hw.len(), hw.first().copied()) {
        (3, Some("decpre")) => DecPub { j: num(hw[2])? },
        (2, Some("decterm")) | (2, Some("dectermS")) => DecPub { j: num(hw[1])? },
        _ => return Err("expected `decpre p J`, `decterm J` or `dectermS J`".into()),
    };
    let w = nums(next()?, "W")?;
    let lg = nums(next()?, "log")?;
    if lg.len() != 3 || lg.iter().any(|&x| !(9..=22).contains(&x)) {
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
    let logs = [lg[0] as usize, lg[1] as usize, lg[2] as usize];
    Ok(DPublic { header, dp, w, logs, nbits, roots, nil, hd0: regs[0], stk0: regs[1], ctr0: regs[2], cells, text: text.to_string() })
}

fn program_of(p: &DPublic) -> Vec<[u32; 5]> {
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
    pre.resize(pow2_at_least(pre.len(), 9), [0, 0, 0, 0, 0]);
    pre
}

fn log_wit(p: &DPublic) -> usize {
    p3_util::log2_strict_usize(pow2_at_least((p.nbits + p.w) as usize, 9))
}

fn wit_pre(p: &DPublic) -> Vec<[u32; 3]> {
    let mut pre: Vec<[u32; 3]> = (0..p.nbits).map(|i| [3 + i, 1, 1]).collect();
    pre.extend((0..p.w).map(|i| [3 + p.nbits + i, 1, 0]));
    pre.resize(1 << log_wit(p), [0, 0, 0]);
    pre
}

fn segs_pre(p: &DPublic) -> Vec<[u32; 2]> {
    let mut pre: Vec<[u32; 2]> = p.roots.iter().enumerate().map(|(j, &r)| [j as u32, r]).collect();
    let first = pre[0];
    pre.resize(pow2_at_least(pre.len(), 9), first);
    pre
}

fn airs(p: &DPublic) -> Vec<SkiAir> {
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
            p2: None,
            dec: Some(p.dp.clone()),
        }),
        SkiAir::Mem(MemAir { blind: true }),
        SkiAir::Prog(ProgAir { pre: program_of(p) }),
        SkiAir::WitT(WitTAir { pre: wit_pre(p) }),
        SkiAir::Segs(SegsAir { pre: segs_pre(p) }),
        SkiAir::Dec,
    ]
}

// ---------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------

struct DTable {
    rows: Vec<[u32; 3]>,
    restarts: Vec<usize>,
    /// The jet's rows and their calls.
    calls: Vec<(usize, DecCall)>,
    mem: Vec<Cell>,
    run_rows: usize,
    run_mem: usize,
}

fn table(p: &DPublic, mut heap: Vec<Cell>) -> Result<DTable, String> {
    let (mut rows, mut restarts, mut calls) = (Vec::new(), Vec::new(), Vec::new());
    for (jx, &root) in p.roots.iter().enumerate() {
        let (mut hd, mut stk) = (root, p.nil);
        loop {
            if rows.len() >= 1 << 22 {
                return Err("the run exceeds 2^22 rows".into());
            }
            rows.push([hd, stk, heap.len() as u32]);
            if let Some((h, s, ws, call)) = dec_step(&heap, hd, stk, p.dp.j) {
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
    let dec_rows: usize = calls.iter().map(|(_, c)| c.rows.len()).sum();
    if run_rows > 1 << p.logs[0] || run_mem > 1 << p.logs[1] || dec_rows > 1 << p.logs[2] {
        return Err(format!(
            "the run ({run_rows} rows, {run_mem} memory cells, {} jet calls, {dec_rows} jet rows) does not fit the statement's heights {:?}",
            calls.len(),
            p.logs
        ));
    }
    let last = *rows.last().unwrap();
    rows.resize(1 << p.logs[0], last);
    heap.resize(1 << p.logs[1], Cell::Nil);
    Ok(DTable { rows, restarts, calls, mem: heap, run_rows, run_mem })
}

fn traces(p: &DPublic, tb: &DTable, blind: bool, bs: BlindStream) -> Vec<RowMajorMatrix<Val>> {
    let mut mult = vec![0u32; tb.mem.len()];
    let cpu0 = cpu_trace(&tb.rows, &tb.mem, &mut mult);
    let mut cpu = widen(cpu0, 2 * BLIND_WIDTH + RESTART_WIDTH + DEC_CPU_WIDTH);
    let w = cpu.width;
    let rbase = CPU_WIDTH + 2 * BLIND_WIDTH;
    let dbase = rbase + RESTART_WIDTH;
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
    // jet's instead, and reads the stack cell too, and the slots.
    for (i, call) in &tb.calls {
        let r = &mut cpu.values[i * w..(i + 1) * w];
        for k in 0..NKINDS {
            r[SEL + k] = Val::ZERO;
        }
        r[dbase] = Val::ONE;
        r[FLD] = f(p.dp.j);
        r[dbase + 1 + BLIND_WIDTH] = f(call.root);
        r[dbase + 2 + BLIND_WIDTH] = f(call.key + call.cells.len() as u32);
        let Cell::Cons(a, b) = tb.mem[call.stk as usize] else { unreachable!("a jet call's stack cell") };
        r[FLD + 2] = f(a);
        r[FLD + 3] = f(b);
        let d = call.key - call.stk - 1;
        for k in 0..RANGE_BITS {
            r[BITS + RANGE_BITS + k] = f((d >> k) & 1);
        }
        mult[call.stk as usize] += 1;
        for a in 0..3 {
            mult[a] += 1;
        }
    }
    // DEC.
    let calls: Vec<DecCall> = tb.calls.iter().map(|(_, c)| c.clone()).collect();
    let mut dec = widen(dec_trace(&calls, p.logs[2], &mut mult), BLIND_WIDTH);
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
        // The jet table's edge: CPU —c— DEC.
        let tc = blind_tuple(&mut rng);
        set_blind(&mut cpu, dbase + 1, tc);
        set_blind(&mut dec, decair::DEC_W_COLS, tc);
    }
    let sp = segs_pre(p);
    let mut seen = std::collections::HashSet::new();
    let segs = sp.iter().map(|r| if seen.insert(*r) { f(*used.get(r).unwrap_or(&0)) } else { Val::ZERO }).collect();
    vec![cpu, mem, RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1), wit, RowMajorMatrix::new(segs, 1), dec]
}

fn heights(p: &DPublic, zk: usize) -> Vec<usize> {
    let lg = |n: usize| p3_util::log2_strict_usize(n);
    vec![p.logs[0] + zk, p.logs[1] + zk, lg(program_of(p).len()) + zk, log_wit(p) + zk, lg(segs_pre(p).len()) + zk, p.logs[2] + zk]
}

/// The verifier's six AIRs for a statement, in the export format of
/// `src/export.rs`, after the statement's text.
fn export_airs(p: &DPublic, v_airs: &[SkiAir]) -> String {
    let mut s = format!("public {}\n{}", p.text.lines().count(), p.text);
    if !p.text.ends_with('\n') {
        s.push('\n');
    }
    for (n, a) in ["cpu", "mem", "prog", "wit", "segs", "dec"].iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

/// `ski-air export-compd PUBLIC`.
pub fn export_compd(text: &str) -> Result<String, String> {
    let p = parse_public_d(text)?;
    Ok(export_airs(&p, &airs(&p)))
}

type DProof = p3_batch_stark::BatchProof<ZkConfig>;

fn prove(p: &DPublic, tr: &[RowMajorMatrix<Val>], ps: PcsStreams) -> Result<(DProof, f64), String> {
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
/// circuit (`lake exe circuit compare-compd`), and accepts only the
/// statement's heights.
fn verify(p: &DPublic, proof: &DProof) -> Result<(), String> {
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let v_config = public_zk_config();
        let v_airs = airs(p);
        lean_statement("circuit", &["compare-compd", "-"], export_airs(p, &v_airs).as_bytes())?;
        let want = heights(p, v_config.is_zk());
        if proof.degree_bits != want {
            return Err(format!("heights {:?}, the statement's are {want:?}", proof.degree_bits));
        }
        let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &want)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        let r = verify_batch(&v_config, &v_airs, proof, &crate::stmt::public_values(&v_airs), &v_data.common)
            .map_err(|e| format!("verify: {e:?}"));
        r?;
        crate::reject::check_beta(&v_airs, proof)?;
        crate::fsbudget::budget!("compd", &v_airs, proof, &v_data.common, v_config, p3_uni_stark::OpeningShape::hiding(4));
        Ok(())
    }));
    match verified {
        Ok(r) => r,
        Err(e) => Err(format!("verifier panic: {}", panic_text(&e))),
    }
}

/// The witness file's private cells: the bits (`1`, `0`, or a cell), then
/// the region's cells.
fn private_of(p: &DPublic, wit: &std::path::Path) -> Result<Vec<Cell>, String> {
    let wtext = std::fs::read_to_string(wit).map_err(|e| format!("{}: {e}", wit.display()))?;
    let ls: Vec<&str> = wtext.lines().filter(|l| !l.is_empty()).collect();
    if ls.len() != (p.nbits + p.w) as usize {
        return Err(format!("{}: {} lines, not {}", wit.display(), ls.len(), p.nbits + p.w));
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

fn table_of(p: &DPublic, wit: &std::path::Path) -> Result<DTable, String> {
    let private = private_of(p, wit)?;
    let heap: Vec<Cell> = p.cells.iter().enumerate().map(|(i, c)| c.unwrap_or_else(|| private[i - 3])).collect();
    let tb = table(p, heap)?;
    let [hd, stk, _] = tb.rows[tb.run_rows - 1];
    if (tb.mem[hd as usize], tb.mem[stk as usize]) != (Cell::K, Cell::Nil) {
        return Err("the run does not end at K over a nil: the witness does not satisfy the statement".into());
    }
    Ok(tb)
}

/// The table in `lake exe composed check`'s format.
fn lean_table(p: &DPublic, tb: &DTable) -> String {
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

/// `ski-air compd-measure PUBLIC WITNESS`: the honest run's counts, without
/// a proof: machine rows, memory cells, jet calls and the jet table's rows.
pub fn compd_measure(public: &std::path::Path, wit: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-dec", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_d(&text)?;
    let tb = table_of(&p, wit)?;
    let dec_rows: usize = tb.calls.iter().map(|(_, c)| c.rows.len()).sum();
    println!(
        "{}: run of {} rows, {} memory cells, {} jet calls, {} jet rows",
        p.header, tb.run_rows, tb.run_mem, tb.calls.len(), dec_rows
    );
    Ok(())
}

/// `ski-air compd-prove PUBLIC WITNESS PROOF [--table=PATH]`: prove the
/// statement for the prover's region, write the proof, and check it
/// verifies.
pub fn compd_prove(public: &std::path::Path, wit: &std::path::Path, proof_out: &std::path::Path,
    table_out: Option<&std::path::Path>) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-dec", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_d(&text)?;
    let tb = table_of(&p, wit)?;
    if let Some(t) = table_out {
        std::fs::write(t, lean_table(&p, &tb)).map_err(|e| format!("{}: {e}", t.display()))?;
    }
    let (proof, prove_s) = crate::reject::until_generic(&airs(&p), || {
        let (bs, ps) = ProverSeed::fresh().split();
        prove(&p, &traces(&p, &tb, true, bs), ps)
    })?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    let t1 = Instant::now();
    verify(&p, &proof)?;
    let verify_s = t1.elapsed().as_secs_f64();
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    let dec_rows: usize = tb.calls.iter().map(|(_, c)| c.rows.len()).sum();
    println!(
        "{}: proved {} rows ({} jet calls, {} jet rows), {} memory cells, in {prove_s:.2} s; verified in {:.3} s; proof {} bytes -> {}",
        p.header,
        tb.run_rows,
        tb.calls.len(),
        dec_rows,
        tb.run_mem,
        verify_s,
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// `ski-air compd-verify PUBLIC PROOF`: check the statement, then the proof
/// against the AIRs built from it alone.
pub fn compd_verify(public: &std::path::Path, proof: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    let bytes = std::fs::read(proof).map_err(|e| format!("{}: {e}", proof.display()))?;
    lean_statement("composed", &["statement-dec", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_d(&text)?;
    let (proof, rest): (DProof, &[u8]) = postcard::take_from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    if !rest.is_empty() {
        return Err(format!("{} bytes after the proof", rest.len()));
    }
    let t0 = Instant::now();
    verify(&p, &proof)?;
    println!("{}: VERIFIED in {:.3} s", p.header, t0.elapsed().as_secs_f64());
    Ok(())
}

/// `ski-air compd-dump PUBLIC WITNESS DIR`: the honest run's table
/// (`DIR/run.txt`) and the private traces, unblinded, one file per table
/// (`DIR/{cpu,mem,wit,dec}.txt`).
pub fn compd_dump(public: &std::path::Path, wit: &std::path::Path, dir: &std::path::Path) -> Result<(), String> {
    let text = std::fs::read_to_string(public).map_err(|e| format!("{}: {e}", public.display()))?;
    lean_statement("composed", &["statement-dec", "-"], text.as_bytes()).map_err(|e| format!("statement: {e}"))?;
    let p = parse_public_d(&text)?;
    let tb = table_of(&p, wit)?;
    std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    std::fs::write(dir.join("run.txt"), lean_table(&p, &tb)).map_err(|e| format!("run.txt: {e}"))?;
    let (bs, _) = ProverSeed::fresh().split();
    let tr = traces(&p, &tb, false, bs);
    for (k, name) in [(0usize, "cpu"), (1, "mem"), (3, "wit"), (5, "dec")] {
        crate::write_trace(dir, name, &tr[k])?;
    }
    println!("{}: run of {} rows, {} jet calls -> {}", p.header, tb.run_rows, tb.calls.len(), dir.display());
    Ok(())
}
