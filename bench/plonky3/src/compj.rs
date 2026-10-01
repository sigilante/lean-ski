//! The composed circuit with jets: a zero-knowledge proof of a composed
//! statement whose run instantiates licensed templates (Avon's
//! `docs/ZK-JETS.md`), checked against Lean (`Ski/Circuit/CompJAir.lean`).
//!
//! Ten tables under one batch STARK with the hiding PCS of `src/sudoku.rs`:
//! the composed circuit's five (`src/composed.rs`: CPU, memory, program,
//! witness, segments) and the jet circuit's five (`src/jets.rs`: ROOTS,
//! HDR, TMPL, POP, INSTW).
//!
//! - **The CPU** is both CPUs at once: the corpus CPU's 121 columns, the
//!   jet columns (121–130, with the `INST` kind), three blinding blocks
//!   (131–145: `blind_a` received from the witness table, `blind_b` sent to
//!   memory, `blind_c` sent to POP), and the restart columns (146–148).
//!   Segments restart over the public nil at each root, and a segment's run
//!   instantiates at the licensed roots of the statement's jet table.
//! - **The jet table** is the statement's, computed by Lean over the
//!   statement's blank heap under the closure rule (`lake exe skilark
//!   cjets`, `Air.jetTableC`): its roots are licensed over every filled heap
//!   (`Air.jetStmtC_sound`).  The verifier sends Lean the statement, the
//!   jet table and its AIRs (`lake exe circuit compare-compJ SRC -`): Lean
//!   checks the table (`Air.jetStmtC`, over the templates of the SKIjack
//!   source `SRC`) and that the AIRs are `Circuit.compJAirs` of both.
//! - **Heights** are public budgets: the CPU's and memory's are the
//!   statement's (`log R M`); POP's and INSTW's, `2^LP` and `2^LI`, are the
//!   verifier's arguments.  The provider tables are padded to `2^8`, as the
//!   hiding PCS needs.
//! - **The blinding tree** has eight private tables and seven tuples:
//!   `WIT —a— CPU —b— MEM`, `CPU —c— POP —d— INSTW —e— TMPL —f— HDR —g—
//!   ROOTS`, each tuple sent from one end and received at the other
//!   (`Circuit.tree_hides`, `Circuit.transcript_zkN`).
//!
//! This is the circuit as data and its honest prover (milestone 4 of the
//! design).  Its soundness (`compJExport_sound`), completeness and zero
//! knowledge theorems are milestones 5–7.

use super::*;
use composed::{checked_public, heap_of, parse_public, program_of, read_witness, segs_pre, wit_pre, Public, RestartPub, SegsAir, LOG_MIN, LOG_WIT, RESTART_WIDTH};
use jets::{counts, hdr_pre_min, parse_jets, roots_pre_min, run_seg, tmpl_pre_min, InstInfo, JetAir, JetTable, Op, INSTW_W, POP_W};
use p3_uni_stark::StarkGenericConfig;
use sudoku::{blind_tuple, make_zk_config, set_blind, widen, ZkConfig, PUBLIC_SEED};
use witness::{witness_rows, WitTAir, WT_BLIND};

const NAMES: [&str; 10] = ["cpu", "mem", "prog", "wit", "segs", "roots", "hdr", "tmpl", "pop", "instw"];

/// The bounds on POP's and INSTW's log heights, the statement's for the
/// CPU and memory (`composed::LOG_BOUNDS`): at least `2^8` for the hiding
/// PCS, at most `2^20` for the height bound (`ZK-JETS.md` §4).
pub const LOG_BOUNDS: std::ops::RangeInclusive<usize> = 8..=20;

/// POP's and INSTW's log heights: public budgets.
#[derive(Clone, Copy, Debug)]
pub struct JLogs {
    pub lp: usize,
    pub li: usize,
}

/// The CPU's first blinding column and first restart column.
const CJ_BL: usize = CPU_WIDTH + JET_WIDTH;
const CJ_RS: usize = CJ_BL + 3 * BLIND_WIDTH;

fn airs(p: &Public, jt: &JetTable) -> Vec<SkiAir> {
    vec![
        SkiAir::Cpu(CpuAir {
            hd0: p.hd0,
            stk0: p.stk0,
            ctr0: p.ctr0,
            accept: None,
            accept_k: true,
            blind: true,
            jets: true,
            probe: None,
            restart: Some(RestartPub { n: p.roots.len() as u32, nil: p.nil }),
        }),
        SkiAir::Mem(MemAir { blind: true }),
        SkiAir::Prog(ProgAir { pre: program_of(p) }),
        SkiAir::WitT(WitTAir { pre: wit_pre(p) }),
        SkiAir::Segs(SegsAir { pre: segs_pre(p) }),
        SkiAir::Jet(JetAir::Roots(roots_pre_min(jt, LOG_MIN), true)),
        SkiAir::Jet(JetAir::Hdr(hdr_pre_min(jt, LOG_MIN), true)),
        SkiAir::Jet(JetAir::Tmpl(tmpl_pre_min(jt, LOG_MIN), true)),
        SkiAir::Jet(JetAir::Pop(true)),
        SkiAir::Jet(JetAir::Instw(true)),
    ]
}

/// The verifier's AIRs, after the statement's text and the jet table's, in
/// the export format of `src/export.rs` (`lake exe circuit compare-compJ`
/// reads all three).
fn export_airs(p: &Public, jtext: &str, v_airs: &[SkiAir]) -> String {
    let mut s = format!("public {}\n{}", p.text.lines().count(), p.text);
    if !p.text.ends_with('\n') {
        s.push('\n');
    }
    s.push_str(&format!("jets {}\n{}", jtext.lines().count(), jtext));
    if !jtext.ends_with('\n') {
        s.push('\n');
    }
    for (n, a) in NAMES.iter().zip(v_airs.iter()) {
        s.push_str(&super::export::export_air(n, a));
    }
    s
}

/// `ski-air export-compj PUBLIC JETS`.
pub fn export_compj(ptext: &str, jtext: &str) -> Result<String, String> {
    let p = parse_public(ptext)?;
    let jt = parse_jets(jtext);
    Ok(export_airs(&p, jtext, &airs(&p, &jt)))
}

// ---------------------------------------------------------------------------
// The run: one jetted segment per root
// ---------------------------------------------------------------------------

struct CJRun {
    rows: Vec<([u32; 3], Option<InstInfo>)>,
    /// The rows that end a segment and start the next.
    restarts: Vec<usize>,
    heap: Vec<Cell>,
    insts: usize,
}

/// The run from the statement's heap, segment by segment, each to a halt
/// at `K` over a nil, instantiating at every licensed root with enough
/// arguments; the halted row of each segment but the last starts the next.
fn run(p: &Public, jt: &JetTable, mut heap: Vec<Cell>) -> Result<CJRun, String> {
    let roots: std::collections::HashMap<u32, u32> = jt.roots.iter().copied().collect();
    let mut rows = Vec::new();
    let mut restarts = Vec::new();
    let mut insts = 0;
    for (j, &root) in p.roots.iter().enumerate() {
        let (mut hd, mut stk) = (root, p.nil);
        if !run_seg(&mut heap, &mut hd, &mut stk, &roots, jt, &mut None, &mut rows, &mut insts) {
            return Err(format!("segment {j} runs past {} rows", jets::MAX_STATES));
        }
        rows.push(([hd, stk, heap.len() as u32], None));
        let end = (heap[hd as usize], heap[stk as usize]);
        if end != (Cell::K, Cell::Nil) {
            return Err(format!("segment {j} ends at {end:?}, not K over a nil: the witness does not satisfy the statement"));
        }
        if j + 1 < p.roots.len() {
            restarts.push(rows.len() - 1);
        }
    }
    if rows.len() > 1 << p.log_rows {
        return Err(format!("{} rows, over the statement's 2^{}", rows.len(), p.log_rows));
    }
    if heap.len() > 1 << p.log_mem {
        return Err(format!("{} memory cells, over the statement's 2^{}", heap.len(), p.log_mem));
    }
    Ok(CJRun { rows, restarts, heap, insts })
}

// ---------------------------------------------------------------------------
// Traces
// ---------------------------------------------------------------------------

/// Zero rows to `2^lg`, or `None` when the rows do not fit.
fn pad_to(mut v: Vec<Val>, w: usize, lg: usize) -> Option<RowMajorMatrix<Val>> {
    if v.len() / w > 1 << lg {
        return None;
    }
    v.resize((1 << lg) * w, Val::ZERO);
    Some(RowMajorMatrix::new(v, w))
}

/// The ten traces, the blinding tuples drawn when `blind`.
fn traces(p: &Public, jt: &JetTable, r: &CJRun, lg: JLogs, blind: bool) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    use std::collections::{HashMap, HashSet};
    let k = 1usize << p.log_rows;
    let msize = 1usize << p.log_mem;
    let mut mem_cells = r.heap.clone();
    mem_cells.resize(msize, Cell::Nil);
    let mut mult = vec![0u32; msize];
    let roots_p = roots_pre_min(jt, LOG_MIN);
    let hdrs = hdr_pre_min(jt, LOG_MIN);
    let tmpls = tmpl_pre_min(jt, LOG_MIN);
    let restarts: HashSet<usize> = r.restarts.iter().copied().collect();

    let w = CJ_RS + RESTART_WIDTH;
    let mut cpu = Vec::with_capacity(k * w);
    let mut roots_used: HashMap<[u32; 2], u32> = HashMap::new();
    let mut hdr_used: HashMap<[u32; 7], u32> = HashMap::new();
    let mut tmpl_used: HashMap<[u32; 11], u32> = HashMap::new();
    let mut segs_used: HashMap<[u32; 2], u32> = HashMap::new();
    let mut pop = Vec::new();
    let mut instw = Vec::new();
    let mut cnt = 0u32;
    let last = r.rows.last().unwrap().0;
    for clk in 0..k {
        let (regs, info) = if clk < r.rows.len() { r.rows[clk].clone() } else { (last, None) };
        let [hd, stk, ctr] = regs;
        // The machine rows by `cpu_trace`, the INST rows by hand.
        let mut row = match &info {
            None => cpu_trace(&[regs], &mem_cells, &mut mult).values,
            Some(_) => {
                let mut x = vec![Val::ZERO; CPU_WIDTH];
                x[HD] = f(hd);
                x[STK] = f(stk);
                x[CTR] = f(ctr);
                x[SEL + 11] = Val::ONE;
                x
            }
        };
        // The jet columns, POP's and INSTW's rows: as `jets::build_traces`.
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
            let first = tmpls.iter().position(|t| t[0] == ii.g).unwrap_or(0);
            for (jx, (cell, xa, xb)) in ii.cells.iter().enumerate() {
                let tr = tmpls[first + jx];
                assert_eq!((tr[0], tr[1]), (ii.g, jx as u32));
                *tmpl_used.entry(tr).or_default() += 1;
                let (a, b) = cell.fields();
                let mut vals = [0u32; INSTW_W];
                vals[0] = clk as u32;
                vals[1] = ctr;
                vals[2..13].copy_from_slice(&tr[0..11]);
                vals[13] = a;
                vals[14] = b;
                vals[15] = *xa;
                vals[16] = *xb;
                vals[17] = 1;
                assert_eq!(cell.tag(), tr[2]);
                mult[(ctr + jx as u32) as usize] += 1;
                instw.extend(vals.iter().map(|&v| f(v)));
            }
        }
        row.extend(jc);
        row.extend(vec![Val::ZERO; 3 * BLIND_WIDTH]);
        // The restart columns: as `composed::traces`.
        let mut rc = [Val::ZERO, f(cnt), Val::ZERO];
        if restarts.contains(&clk) {
            for q in 0..NKINDS {
                row[SEL + q] = Val::ZERO;
            }
            rc[0] = Val::ONE;
            let next = p.roots[cnt as usize + 1];
            rc[2] = f(next);
            *segs_used.entry([cnt + 1, next]).or_default() += 1;
            cnt += 1;
        }
        row.extend(rc);
        debug_assert_eq!(row.len(), w);
        cpu.extend(row);
    }
    let mut cpu = RowMajorMatrix::new(cpu, w);
    let mut pop = widen(pad_to(pop, POP_W, lg.lp).ok_or(format!("POP's rows do not fit 2^{}", lg.lp))?, 2 * BLIND_WIDTH);
    let mut instw = widen(pad_to(instw, INSTW_W, lg.li).ok_or(format!("INSTW's rows do not fit 2^{}", lg.li))?, 2 * BLIND_WIDTH);

    // The program's public cells and the witness's private ones, looked up.
    let pre = program_of(p);
    for row in &pre {
        if row[4] == 1 {
            mult[row[0] as usize] += 1;
        }
    }
    let addrs: Vec<u32> = wit_pre(p).iter().filter(|row| row[1] == 1).map(|row| row[0]).collect();
    let mut wit = witness_rows(&addrs, 1 << LOG_WIT, &mem_cells, &mut mult);
    let mut mem = Vec::with_capacity(msize * 5);
    for (i, cell) in mem_cells.iter().enumerate() {
        let (a, b) = cell.fields();
        mem.extend([f(i as u32), f(cell.tag()), f(a), f(b), f(mult[i])]);
    }
    let mut mem = widen(RowMajorMatrix::new(mem, 5), BLIND_WIDTH);
    let mut roots = widen(counts(&roots_p, &roots_used), BLIND_WIDTH);
    let mut hdr = widen(counts(&hdrs, &hdr_used), 2 * BLIND_WIDTH);
    let mut tmpl = widen(counts(&tmpls, &tmpl_used), 2 * BLIND_WIDTH);
    let sp = segs_pre(p);
    let segs = counts(&sp, &segs_used);
    if blind {
        let [ta, tb, tc, td, te, tf, tg] = std::array::from_fn(|_| blind_tuple());
        set_blind(&mut wit, WT_BLIND, ta);
        set_blind(&mut cpu, CJ_BL, ta);
        set_blind(&mut cpu, CJ_BL + BLIND_WIDTH, tb);
        set_blind(&mut mem, 5, tb);
        set_blind(&mut cpu, CJ_BL + 2 * BLIND_WIDTH, tc);
        set_blind(&mut pop, POP_W, tc);
        set_blind(&mut pop, POP_W + BLIND_WIDTH, td);
        set_blind(&mut instw, INSTW_W, td);
        set_blind(&mut instw, INSTW_W + BLIND_WIDTH, te);
        set_blind(&mut tmpl, 1, te);
        set_blind(&mut tmpl, 1 + BLIND_WIDTH, tf);
        set_blind(&mut hdr, 1, tf);
        set_blind(&mut hdr, 1 + BLIND_WIDTH, tg);
        set_blind(&mut roots, 1, tg);
    }
    Ok(vec![cpu, mem, RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1), wit, segs, roots, hdr, tmpl, pop, instw])
}

// ---------------------------------------------------------------------------
// Proving and verifying
// ---------------------------------------------------------------------------

fn heights(p: &Public, jt: &JetTable, lg: JLogs, zk: usize) -> Vec<usize> {
    let l = |n: usize| p3_util::log2_strict_usize(n);
    vec![
        p.log_rows,
        p.log_mem,
        l(program_of(p).len()),
        LOG_WIT,
        l(segs_pre(p).len()),
        l(roots_pre_min(jt, LOG_MIN).len()),
        l(hdr_pre_min(jt, LOG_MIN).len()),
        l(tmpl_pre_min(jt, LOG_MIN).len()),
        lg.lp,
        lg.li,
    ]
    .into_iter()
    .map(|h| h + zk)
    .collect()
}

type CJProof = p3_batch_stark::BatchProof<ZkConfig>;

fn prove(p: &Public, jt: &JetTable, lg: JLogs, tr: &[RowMajorMatrix<Val>]) -> Result<(CJProof, f64), String> {
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = make_zk_config(None);
        let a = airs(p, jt);
        let t0 = Instant::now();
        let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&make_zk_config(Some(PUBLIC_SEED)), &a, &heights(p, jt, lg, config.is_zk()))
            .map_err(|e| format!("setup: {e:?}"))?;
        let trs: Vec<&RowMajorMatrix<Val>> = tr.iter().collect();
        let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &trs, &vec![vec![]; NAMES.len()]), &pd)
            .map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    match proved {
        Ok(r) => r,
        Err(e) => Err(format!("panic: {}", panic_text(&e))),
    }
}

/// **The verifier**: the statement, the jet table, the budgets and the
/// source the templates come from (a relative `src` is read from the
/// lean-ski root, where `lean_statement` runs Lean; the templates only
/// propose roots, which Lean licenses whatever proposed them).  Lean checks the jet table and that the
/// AIRs are `Circuit.compJAirs`; the proof must have the budgeted heights.
fn verify(p: &Public, jtext: &str, src: &str, lg: JLogs, proof: &CJProof) -> Result<(), String> {
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let jt = parse_jets(jtext);
        let v_config = make_zk_config(Some(PUBLIC_SEED));
        let v_airs = airs(p, &jt);
        lean_statement("circuit", &["compare-compJ", src, "-"], export_airs(p, jtext, &v_airs).as_bytes())?;
        let want = heights(p, &jt, lg, v_config.is_zk());
        if proof.degree_bits != want {
            return Err(format!("heights {:?}, the budget's are {want:?}", proof.degree_bits));
        }
        let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &want)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        verify_batch(&v_config, &v_airs, proof, &vec![vec![]; NAMES.len()], &v_data.common).map_err(|e| format!("verify: {e:?}"))
    }));
    match verified {
        Ok(r) => r,
        Err(e) => Err(format!("verifier panic: {}", panic_text(&e))),
    }
}

fn read(path: &std::path::Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))
}

/// The run as a table in `lake exe composed check-cj`'s format (the
/// composed checker's, `CompM.checkCJ`): the memory, the segments' ends,
/// and the rows, padded as the CPU and memory traces are.
fn lean_table(p: &Public, r: &CJRun) -> String {
    let k = 1usize << p.log_rows;
    let mut mem = r.heap.clone();
    mem.resize(1 << p.log_mem, Cell::Nil);
    let mut s = format!("{}\nW {}\n{}\n", p.header, p.w, mem.len());
    for cell in &mem {
        s.push_str(&cell.lean());
        s.push('\n');
    }
    let mut ends: Vec<usize> = r.restarts.clone();
    ends.push(k - 1);
    s.push_str(&format!("ends {}\n", ends.len()));
    for e in ends {
        s.push_str(&format!("{e}\n"));
    }
    s.push_str(&format!("{k}\n"));
    let last = r.rows.last().unwrap().0;
    for i in 0..k {
        let [h, st, c] = if i < r.rows.len() { r.rows[i].0 } else { last };
        s.push_str(&format!("{h} {st} {c}\n"));
    }
    s
}

/// `ski-air compj-prove PUBLIC JETS SRC LP LI WITNESS PROOF [TABLE]`: prove
/// the statement with jets for the prover's bits and region, write the
/// proof (and the Lean table), and check it verifies.
pub fn compj_prove(public: &std::path::Path, jets_path: &std::path::Path, src: &str, lg: JLogs, wit: &std::path::Path, proof_out: &std::path::Path, table_out: Option<&std::path::Path>) -> Result<(), String> {
    let p = checked_public(public)?;
    let jtext = read(jets_path)?;
    let jt = parse_jets(&jtext);
    let private = read_witness(&p, wit)?;
    let r = run(&p, &jt, heap_of(&p, &private))?;
    if let Some(t) = table_out {
        std::fs::write(t, lean_table(&p, &r)).map_err(|e| format!("{}: {e}", t.display()))?;
    }
    let tr = traces(&p, &jt, &r, lg, true)?;
    let (proof, prove_s) = prove(&p, &jt, lg, &tr)?;
    let bytes = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    std::fs::write(proof_out, &bytes).map_err(|e| format!("{}: {e}", proof_out.display()))?;
    let t1 = Instant::now();
    verify(&p, &jtext, src, lg, &proof)?;
    let npop = r.rows.iter().filter_map(|x| x.1.as_ref()).map(|ii| ii.pops.len()).sum::<usize>();
    let ninstw = r.rows.iter().filter_map(|x| x.1.as_ref()).map(|ii| ii.cells.len()).sum::<usize>();
    println!(
        "proved {} CPU rows ({} instantiations), {} POP, {} INSTW, {} memory cells, {} segments; heights 2^{} 2^{} 2^{} 2^{}; prove {prove_s:.2} s, verify {:.2} s; proof {} bytes -> {}",
        r.rows.len(),
        r.insts,
        npop,
        ninstw,
        r.heap.len(),
        p.roots.len(),
        p.log_rows,
        p.log_mem,
        lg.lp,
        lg.li,
        t1.elapsed().as_secs_f64(),
        bytes.len(),
        proof_out.display()
    );
    Ok(())
}

/// `ski-air compj-verify PUBLIC JETS SRC LP LI PROOF`: the standalone
/// verifier.  Lean checks the statement's bytes, then the jet table and the
/// AIRs; the proof, one byte string, must verify.
pub fn compj_verify(public: &std::path::Path, jets_path: &std::path::Path, src: &str, lg: JLogs, proof_in: &std::path::Path) -> Result<(), String> {
    let p = checked_public(public)?;
    let jtext = read(jets_path)?;
    let bytes = std::fs::read(proof_in).map_err(|e| format!("{}: {e}", proof_in.display()))?;
    let (proof, rest): (CJProof, &[u8]) = postcard::take_from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    if !rest.is_empty() {
        return Err(format!("{} bytes after the proof", rest.len()));
    }
    let t0 = Instant::now();
    verify(&p, &jtext, src, lg, &proof)?;
    println!(
        "VERIFIED: the proof checks against the statement {} with its jet table ({} segments; {:.2} s)",
        p.header,
        p.roots.len(),
        t0.elapsed().as_secs_f64()
    );
    Ok(())
}

/// A prover that skips the blinding, or blinds with mismatched tuples, for
/// the tamper test: the proof must not verify when the tree does not
/// balance.
pub fn compj_tamper(public: &std::path::Path, jets_path: &std::path::Path, src: &str, lg: JLogs, wit: &std::path::Path) -> Result<(), String> {
    let p = checked_public(public)?;
    let jtext = read(jets_path)?;
    let jt = parse_jets(&jtext);
    let private = read_witness(&p, wit)?;
    let r = run(&p, &jt, heap_of(&p, &private))?;
    let mut tr = traces(&p, &jt, &r, lg, true)?;
    // Break edge `e`: INSTW sends a tuple TMPL does not receive.
    set_blind(&mut tr[9], INSTW_W + BLIND_WIDTH, blind_tuple());
    match prove(&p, &jt, lg, &tr) {
        Err(e) => {
            println!("REFUSED: the prover fails on an unbalanced blinding tree ({e})");
            Ok(())
        }
        Ok((proof, _)) => match verify(&p, &jtext, src, lg, &proof) {
            Err(e) => {
                println!("REJECTED: an unbalanced blinding tree does not verify ({e})");
                Ok(())
            }
            Ok(()) => Err("an unbalanced blinding tree verified".into()),
        },
    }
}
