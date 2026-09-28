//! A zero-knowledge proof of a Sudoku solution, checked against Lean.
//!
//! The statement is `Stmt.stmtMachine` of `Ski/Statement.lean` for the
//! puzzle's formula (`Sudoku.sudokuExpr`), written by `lake exe sudoku emit`
//! as `public.txt`: the slot cells `K`, `I`, `A 0 1` at 0, 1, 2; the 729
//! input cells at 3 to 731, blank; then the compiled formula applied to the
//! markers, the atoms labelled `ACC` = 731 and `REJ` = 732 (labels, not
//! addresses).  The verifier sees every cell but the inputs.
//!
//! **The verifier trusts `public.txt` only after `lake exe sudoku statement`
//! accepts it**: the file must be exactly the statement of the puzzle on its
//! first line.  This program reads the file as given; a file with the
//! markers exchanged would let a wrong grid verify.  By
//! `Stmt.stmtMachine_public`, the blank-input heap states `stmtMachine ρ`
//! for every `ρ`.
//!
//! Four tables under one batch STARK with a hiding PCS:
//!
//! - **CPU** and **memory**, as for the corpus, at fixed heights
//!   (`LOG_ROWS`, `LOG_MEM`, constants of prover and verifier), so the
//!   heights say nothing about the witness.  The last row must read the atom
//!   `ACC` at the head.
//! - **Program**: the public cells, with their addresses, preprocessed.
//! - **Witness**: one committed bit per input, and a preprocessed address.
//!   Each row is the memory cell `K` (bit 1) or `A 0 1` (bit 0): an input is
//!   a Scott Boolean and nothing else.
//!
//! The program and witness lookups name every address below the first
//! counter, so the memory table's prefix is `stmtMachine ρ` for the inputs
//! `ρ` the witness bits give.  With the transition and halting constraints,
//! a table the verifier accepts satisfies `Air.AcceptsFrom` from that
//! machine and reads `ACC` at the head of its last row, which is what
//! `Sudoku.sudoku_sound` turns into a solution.  `lake exe sudoku check`
//! decides it (`Sudoku.sudokuCheck_sound`) on every table proved here.
//!
//! **Blinding.**  Plonky3 publishes each table's LogUp terminal, its whole
//! lookup sum, in the clear, and its hiding PCS does not mask it.  The
//! witness table's terminal is a function of the inputs under challenges a
//! verifier replays, so unblinded it lets anyone check a guessed grid.  Two
//! buses of their own carry blinding messages, each a fresh uniform 4-tuple
//! with count one: `blind_a` from the witness table to the CPU, `blind_b`
//! from the CPU to memory.  Each adds `1/(prefix - combine(tuple))` to one
//! table's terminal and takes it from another's.  `combine` weights the
//! tuple's four base-field entries by powers of a challenge, which span the
//! degree-4 extension unless the challenge falls in a proper subfield, so
//! the term is uniform over the extension field but for a negligible
//! chance.  So the three private terminals are uniform subject to their
//! sum, which is minus the program table's, which the verifier computes
//! anyway.  The buses are separate (p3-lookup gives each its own prefix), so
//! the messages cannot stand in for a memory entry.  `guess_matches`
//! checks this: the true inputs, guessed against the published witness
//! terminal, must not match.

use super::*;
use p3_uni_stark::StarkGenericConfig;
use p3_fri::HidingFriPcs;
use p3_merkle_tree::MerkleTreeHidingMmcs;
use rand::rngs::StdRng;
use rand::{RngExt, SeedableRng};
use p3_field::PrimeField32;

// ---------------------------------------------------------------------------
// The hiding configuration
// ---------------------------------------------------------------------------

type HidingValMmcs = MerkleTreeHidingMmcs<
    <Val as Field>::Packing,
    <Val as Field>::Packing,
    MyHash,
    MyCompress,
    StdRng,
    2,
    8,
    4,
>;
type HidingChallengeMmcs = ExtensionMmcs<Val, Challenge, HidingValMmcs>;
type HidingPcs = HidingFriPcs<Val, Dft, HidingValMmcs, HidingChallengeMmcs, StdRng>;
type ZkConfig = StarkConfig<HidingPcs, Challenge, Challenger>;

/// Random codewords that mask the committed polynomials: at least the
/// challenge field's degree, as `HidingFriPcs` requires.
const RANDOM_CODEWORDS: usize = 4;

/// The corpus's FRI parameters, with salted Merkle leaves and random
/// codewords.  With `seed`, the salts and codewords are drawn from a public
/// seed; without, from the operating system's generator.
///
/// The preprocessed tables are public, and the verifier must rebuild their
/// commitment, but the hiding MMCS salts every commitment.  So both sides
/// commit the preprocessed tables under the public seed `PUBLIC_SEED`
/// (`ProverData::from_airs_and_degrees`), and the prover commits its traces
/// under a configuration seeded by the operating system.  Opening and
/// verifying draw no randomness from the MMCS.
fn make_zk_config(seed: Option<u64>) -> ZkConfig {
    let rng = || match seed {
        Some(s) => StdRng::seed_from_u64(s),
        None => rand::make_rng::<StdRng>(),
    };
    let perm = default_babybear_poseidon2_16();
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let val_mmcs = HidingValMmcs::new(hash, compress, 0, rng());
    let challenge_mmcs = HidingChallengeMmcs::new(val_mmcs.clone());
    let fri = FriParameters::new_benchmark(challenge_mmcs);
    let pcs = HidingPcs::new(Dft::default(), val_mmcs, fri, RANDOM_CODEWORDS, rng());
    ZkConfig::new(pcs, Challenger::new(perm))
}

/// The seed of the public preprocessed commitment.
const PUBLIC_SEED: u64 = 0;

// ---------------------------------------------------------------------------
// The statement
// ---------------------------------------------------------------------------

/// The heights of the CPU and memory tables, fixed by the statement.
const LOG_ROWS: usize = 16;
const LOG_MEM: usize = 16;
/// The witness table: 729 inputs in 1024 rows.
const LOG_WIT: usize = 10;

/// The public part of the statement: `public.txt`.
pub struct Public {
    puzzle: String,
    acc: u32,
    rej: u32,
    hd0: u32,
    stk0: u32,
    ctr0: u32,
    wit_lo: u32,
    wit_n: u32,
    /// The initial heap, `None` at the inputs.
    cells: Vec<Option<Cell>>,
}

fn parse_cell(l: &str) -> Cell {
    let w: Vec<&str> = l.split_whitespace().collect();
    let n = |i: usize| w[i].parse::<u32>().expect("a number");
    match w[0] {
        "S" => Cell::S,
        "K" => Cell::K,
        "I" => Cell::I,
        "N" => Cell::Nil,
        "A" => Cell::App(n(1), n(2)),
        "C" => Cell::Cons(n(1), n(2)),
        "X" => Cell::Atom(n(1)),
        _ => panic!("bad cell {l}"),
    }
}

pub fn read_public(path: &std::path::Path) -> Public {
    let text = std::fs::read_to_string(path).expect("public.txt");
    let mut ls = text.lines();
    let puzzle = ls.next().unwrap().trim().to_string();
    let h: Vec<u32> = ls.next().unwrap().split_whitespace().map(|x| x.parse().unwrap()).collect();
    let n: usize = ls.next().unwrap().trim().parse().unwrap();
    let cells: Vec<Option<Cell>> = ls
        .take(n)
        .map(|l| if l.trim() == "W" { None } else { Some(parse_cell(l)) })
        .collect();
    assert_eq!(cells.len(), n);
    let p = Public {
        puzzle,
        acc: h[0],
        rej: h[1],
        hd0: h[2],
        stk0: h[3],
        ctr0: h[4],
        wit_lo: h[5],
        wit_n: h[6],
        cells,
    };
    assert_eq!(p.ctr0 as usize, n);
    // Necessary, not sufficient: `lake exe sudoku statement` checks the rest.
    // Slot variables are the two constants and the inputs, so the markers
    // must lie at or past `wit_n + 2`, as `Stmt.stmt_sound` requires.
    assert!(p.acc != p.rej && p.acc >= p.wit_n + 2 && p.rej >= p.wit_n + 2);
    for (i, c) in p.cells.iter().enumerate() {
        let w = (i as u32) >= p.wit_lo && (i as u32) < p.wit_lo + p.wit_n;
        assert_eq!(c.is_none(), w, "the inputs are exactly the blank cells");
    }
    p
}

pub fn read_bits(path: &std::path::Path) -> Vec<bool> {
    let text = std::fs::read_to_string(path).expect("witness");
    text.trim().bytes().map(|b| b == b'1').collect()
}

/// The initial heap for the inputs `bits`: `K` for true, `A 0 1` for false.
fn heap_of(p: &Public, bits: &[bool]) -> Vec<Cell> {
    assert_eq!(bits.len(), p.wit_n as usize);
    p.cells
        .iter()
        .enumerate()
        .map(|(i, c)| match c {
            Some(c) => *c,
            None => {
                if bits[i - p.wit_lo as usize] {
                    Cell::K
                } else {
                    Cell::App(0, 1)
                }
            }
        })
        .collect()
}

/// The program table: the public cells with their addresses, padded with
/// inactive rows.
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
    pre.resize(pre.len().next_power_of_two(), [0, 0, 0, 0, 0]);
    pre
}

/// The witness table's preprocessed columns: the input addresses.
fn wit_pre(p: &Public) -> Vec<[u32; 2]> {
    let mut pre: Vec<[u32; 2]> = (0..p.wit_n).map(|n| [p.wit_lo + n, 1]).collect();
    pre.resize(1 << LOG_WIT, [0, 0]);
    pre
}

/// The verifier's AIRs, from the public statement alone.
fn airs(p: &Public) -> Vec<SkiAir> {
    vec![
        SkiAir::Cpu(CpuAir { hd0: p.hd0, stk0: p.stk0, ctr0: p.ctr0, accept: Some(p.acc), blind: true }),
        SkiAir::Mem(MemAir { blind: true }),
        SkiAir::Prog(ProgAir { pre: program_of(p) }),
        SkiAir::Wit(WitAir { pre: wit_pre(p) }),
    ]
}

// ---------------------------------------------------------------------------
// The run and its traces
// ---------------------------------------------------------------------------

/// The machine from the statement's registers over `heap`, to a halt.
fn run_from(mut heap: Vec<Cell>, mut hd: u32, mut stk: u32) -> (Vec<[u32; 3]>, Vec<Cell>) {
    let mut rows = Vec::new();
    loop {
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
    (rows, heap)
}

pub struct SudokuTable {
    /// Registers of every row, padded with the halted state.
    rows: Vec<[u32; 3]>,
    /// The memory table, padded with empty stacks.
    mem: Vec<Cell>,
    /// Rows and memory cells before padding.
    run_rows: usize,
    run_mem: usize,
}

/// The table of the run from `heap`, at the statement's heights.  `None`
/// when the run does not fit them.
fn table(p: &Public, heap: Vec<Cell>) -> Option<SudokuTable> {
    let (mut rows, mut mem) = run_from(heap, p.hd0, p.stk0);
    let (run_rows, run_mem) = (rows.len(), mem.len());
    if run_rows > 1 << LOG_ROWS || run_mem > 1 << LOG_MEM {
        return None;
    }
    let last = *rows.last().unwrap();
    rows.resize(1 << LOG_ROWS, last);
    mem.resize(1 << LOG_MEM, Cell::Nil);
    Some(SudokuTable { rows, mem, run_rows, run_mem })
}

/// The head cell of the last row.
fn last_head(tb: &SudokuTable) -> Cell {
    tb.mem[tb.rows.last().unwrap()[0] as usize]
}

/// A fresh blinding tuple, uniform over the field, from the operating
/// system's generator.
fn blind_tuple() -> [Val; BLIND_LEN] {
    let mut rng = rand::make_rng::<StdRng>();
    core::array::from_fn(|_| Val::from_u32(rng.random_range(0..Val::ORDER_U32)))
}

/// `m` with `extra` zero columns appended to every row.
fn widen(m: RowMajorMatrix<Val>, extra: usize) -> RowMajorMatrix<Val> {
    let w = m.width;
    let mut v = Vec::with_capacity(m.values.len() / w * (w + extra));
    for row in m.values.chunks(w) {
        v.extend_from_slice(row);
        v.extend(std::iter::repeat_n(Val::ZERO, extra));
    }
    RowMajorMatrix::new(v, w + extra)
}

/// Write a blinding message, `tuple` with its flag set, into row 0 at `col`.
fn set_blind(m: &mut RowMajorMatrix<Val>, col: usize, tuple: [Val; BLIND_LEN]) {
    m.values[col..col + BLIND_LEN].copy_from_slice(&tuple);
    m.values[col + BLIND_LEN] = Val::ONE;
}

/// The four traces.  A witness bit is 1 exactly when the memory holds `K` at
/// its input address.  Row 0 of the witness, CPU and memory tables carries
/// the blinding messages: fresh tuples `A` (witness to CPU) and `B` (CPU to
/// memory).
fn sudoku_traces(p: &Public, tb: &SudokuTable) -> [RowMajorMatrix<Val>; 4] {
    let mut mult = vec![0u32; tb.mem.len()];
    let mut cpu = widen(cpu_trace(&tb.rows, &tb.mem, &mut mult), 2 * BLIND_WIDTH);
    let pre = program_of(p);
    for r in &pre {
        if r[4] == 1 {
            mult[r[0] as usize] += 1;
        }
    }
    let ww = 1 + BLIND_WIDTH;
    let mut wit = vec![Val::ZERO; (1 << LOG_WIT) * ww];
    for n in 0..p.wit_n {
        let a = (p.wit_lo + n) as usize;
        wit[n as usize * ww] = f((tb.mem[a] == Cell::K) as u32);
        mult[a] += 1;
    }
    let mut wit = RowMajorMatrix::new(wit, ww);
    let mut mem = Vec::with_capacity(tb.mem.len() * 5);
    for (i, cell) in tb.mem.iter().enumerate() {
        let (a, b) = cell.fields();
        mem.extend([f(i as u32), f(cell.tag()), f(a), f(b), f(mult[i])]);
    }
    let mut mem = widen(RowMajorMatrix::new(mem, 5), BLIND_WIDTH);
    let (ba, bb) = (blind_tuple(), blind_tuple());
    set_blind(&mut wit, 1, ba);
    set_blind(&mut cpu, CPU_BLA, ba);
    set_blind(&mut cpu, CPU_BLB, bb);
    set_blind(&mut mem, 5, bb);
    [
        cpu,
        mem,
        RowMajorMatrix::new(vec![Val::ZERO; pre.len()], 1),
        wit,
    ]
}

/// The table in `lake exe sudoku check`'s format.
fn lean_table(p: &Public, tb: &SudokuTable) -> String {
    let mut s = format!("{}\n{} {}\n{}\n", p.puzzle, p.acc, p.rej, tb.mem.len());
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

/// Prove the traces, then verify the proof against the public statement
/// alone.  The verifier rebuilds its AIRs and preprocessed commitments from
/// `public.txt` and accepts only the statement's heights.
fn prove_and_verify_zk(p: &Public, traces: &[RowMajorMatrix<Val>; 4]) -> (Outcome, usize) {
    let log = |m: &RowMajorMatrix<Val>| p3_util::log2_strict_usize(m.values.len() / m.width);
    let proved = catch_unwind(AssertUnwindSafe(|| {
        let config = make_zk_config(None);
        let a = airs(p);
        let zk = config.is_zk();
        let degrees: Vec<usize> = traces.iter().map(|m| log(m) + zk).collect();
        let t0 = Instant::now();
        let prover_data =
            ProverData::<ZkConfig>::from_airs_and_degrees(&make_zk_config(Some(PUBLIC_SEED)), &a, &degrees)
            .map_err(|e| format!("setup: {e:?}"))?;
        let tr: Vec<&RowMajorMatrix<Val>> = traces.iter().collect();
        let pvs = vec![vec![]; 4];
        let instances = StarkInstance::new_multiple(&a, &tr, &pvs);
        let proof =
            prove_batch(&config, &instances, &prover_data).map_err(|e| format!("prove: {e:?}"))?;
        Ok::<_, String>((proof, t0.elapsed().as_secs_f64()))
    }));
    let (proof, prove_s) = match proved {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => return (Outcome::Refused(e), 0),
        Err(e) => return (Outcome::Refused(format!("panic: {}", panic_text(&e))), 0),
    };
    let size = postcard_size(&proof);

    // The verifier: the public statement, the proof, nothing else.
    let t1 = Instant::now();
    let verified = catch_unwind(AssertUnwindSafe(|| {
        let v_config = make_zk_config(Some(PUBLIC_SEED));
        let v_airs = airs(p);
        let zk = v_config.is_zk();
        let prog_log = p3_util::log2_strict_usize(program_of(p).len());
        let want = [LOG_ROWS + zk, LOG_MEM + zk, prog_log + zk, LOG_WIT + zk];
        if proof.degree_bits != want {
            return Err(format!("heights {:?}, the statement's are {want:?}", proof.degree_bits));
        }
        let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &want)
            .map_err(|e| format!("verifier setup: {e:?}"))?;
        let pvs = vec![vec![]; 4];
        verify_batch(&v_config, &v_airs, &proof, &pvs, &v_data.common)
            .map_err(|e| format!("verify: {e:?}"))
    }));
    let outcome = match verified {
        Ok(Ok(())) => Outcome::Verified(prove_s, t1.elapsed().as_secs_f64()),
        Ok(Err(e)) => Outcome::Rejected(e),
        Err(e) => Outcome::Rejected(format!("verifier panic: {}", panic_text(&e))),
    };
    (outcome, size)
}

/// The proof's size in bytes, serialized.
fn postcard_size<T: serde::Serialize>(proof: &T) -> usize {
    postcard::to_allocvec(proof).map(|v| v.len()).unwrap_or(0)
}

// ---------------------------------------------------------------------------
// The guess test: the lookup terminals must not confirm a guessed witness
// ---------------------------------------------------------------------------

/// Plonky3 publishes each table's LogUp terminal, its whole lookup sum, in
/// the clear.  Unblinded, the witness table's terminal is a function of the
/// inputs under challenges the verifier replays, so a verifier could check
/// a guessed grid against it.  This proves honestly, verifies, replays the
/// transcript as a verifier would, and recomputes the witness terminal for
/// the true inputs with the blinding columns zero.  It returns whether that
/// guess matches the published terminal, which must be false.
fn guess_matches(p: &Public, bits: &[bool]) -> bool {
    use p3_batch_stark::{BatchShape, BatchVerifierTranscript};
    use p3_lookup::{LogUpGadget, LookupProtocol};
    let tb = table(p, heap_of(p, bits)).expect("the honest run fits");
    let traces = sudoku_traces(p, &tb);
    let log = |m: &RowMajorMatrix<Val>| p3_util::log2_strict_usize(m.values.len() / m.width);
    let config = make_zk_config(None);
    let a = airs(p);
    let degrees: Vec<usize> = traces.iter().map(|m| log(m) + config.is_zk()).collect();
    let pd = ProverData::<ZkConfig>::from_airs_and_degrees(&make_zk_config(Some(PUBLIC_SEED)), &a, &degrees)
        .expect("setup");
    let tr: Vec<&RowMajorMatrix<Val>> = traces.iter().collect();
    let pvs: Vec<Vec<Val>> = vec![vec![]; 4];
    let proof = prove_batch(&config, &StarkInstance::new_multiple(&a, &tr, &pvs), &pd).expect("prove");

    // The verifier's side: the statement and the proof.
    let v_config = make_zk_config(Some(PUBLIC_SEED));
    let v_airs = airs(p);
    let v_data = ProverData::<ZkConfig>::from_airs_and_degrees(&v_config, &v_airs, &proof.degree_bits)
        .expect("verifier setup");
    verify_batch(&v_config, &v_airs, &proof, &pvs, &v_data.common).expect("the honest proof verifies");
    let common = &v_data.common;
    let shape = BatchShape {
        trace_widths: v_airs.iter().map(|x| <SkiAir as BaseAir<Val>>::width(x)).collect(),
        public_value_counts: vec![0; 4],
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
    let chs = t
        .lookup_phase(&common.lookups, &LogUpGadget::new(), proof.lookup_pow_witness)
        .expect("lookup challenges");
    t.abort();
    let published = proof.lookup_terminals[3].as_ref().expect("a witness terminal").0;

    let pre = <SkiAir as BaseAir<Val>>::preprocessed_trace(&v_airs[3]).expect("witness addresses");
    let ww = 1 + BLIND_WIDTH;
    let mut w = vec![Val::ZERO; (1 << LOG_WIT) * ww];
    for (i, &b) in bits.iter().enumerate() {
        w[i * ww] = f(b as u32);
    }
    let guess = LogUpGadget::new()
        .generate_permutation::<Val, Challenge>(&RowMajorMatrix::new(w, ww), &Some(pre), &[], &common.lookups[3], &chs[3])
        .1
        .expect("a terminal")
        .0;
    guess == published
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

/// `ski-air sudoku DIR OUTDIR`: DIR holds `lake exe sudoku emit`'s files.
pub fn main(dir: &std::path::Path, out: &std::path::Path) -> usize {
    let p = read_public(&dir.join("public.txt"));
    let mut failures = 0;
    println!(
        "sudoku: {} public cells, {} inputs, markers {} and {}; heights 2^{LOG_ROWS} rows, 2^{LOG_MEM} memory, 2^{LOG_WIT} inputs",
        p.cells.len() - p.wit_n as usize,
        p.wit_n,
        p.acc,
        p.rej
    );

    // The honest proof.
    let bits = read_bits(&dir.join("witness.txt"));
    let tb = table(&p, heap_of(&p, &bits)).expect("the honest run fits the statement's heights");
    assert_eq!(last_head(&tb), Cell::Atom(p.acc), "the honest run reaches the accepting marker");
    std::fs::write(out.join("sudoku.txt"), lean_table(&p, &tb)).unwrap();
    let tr = sudoku_traces(&p, &tb);
    match prove_and_verify_zk(&p, &tr) {
        (Outcome::Verified(ps, vs), size) => println!(
            "honest           {} rows, {} memory cells; prove {ps:.2} s, verify {vs:.3} s, proof {} KiB  verified",
            tb.run_rows,
            tb.run_mem,
            size / 1024
        ),
        (Outcome::Refused(e) | Outcome::Rejected(e), _) => {
            println!("honest: FAILED: {e}");
            failures += 1;
        }
    }

    // The guess test.
    let matched = guess_matches(&p, &bits);
    println!(
        "guess test       the true inputs, guessed against the published witness terminal: {}",
        if matched { "MATCH (the terminal leaks)" } else { "no match" }
    );
    if matched {
        failures += 1;
    }

    // Tampered tables: each proof must be rejected, and each Lean table.
    println!("\ntampered (each proof must be rejected by the verifier):");
    // A wrong grid, run honestly: the formula is false, so the run ends at
    // the rejecting marker.
    let swapped = read_bits(&dir.join("witness_swapped.txt"));
    let tb_s = table(&p, heap_of(&p, &swapped)).expect("the swapped run fits");
    let ends = last_head(&tb_s);
    std::fs::write(out.join("tampered_sudoku_swapped.txt"), lean_table(&p, &tb_s)).unwrap();
    failures += report("swapped", &format!("ends at {ends:?}"), prove_and_verify_zk(&p, &sudoku_traces(&p, &tb_s)).0);
    // An input that is not a Boolean: the first input cell is `I`.
    let mut heap = heap_of(&p, &bits);
    heap[p.wit_lo as usize] = Cell::I;
    let tb_f = table(&p, heap).expect("the forged run fits");
    let ends = last_head(&tb_f);
    std::fs::write(out.join("tampered_sudoku_forged_input.txt"), lean_table(&p, &tb_f)).unwrap();
    failures += report("forged_input", &format!("ends at {ends:?}"), prove_and_verify_zk(&p, &sudoku_traces(&p, &tb_f)).0);
    failures
}

fn report(name: &str, note: &str, o: Outcome) -> usize {
    match o {
        Outcome::Rejected(e) => {
            println!("{name:<16} {note}; rejected by the verifier ({})", e.chars().take(60).collect::<String>());
            0
        }
        Outcome::Verified(..) => {
            println!("{name:<16} {note}; ACCEPTED");
            1
        }
        Outcome::Refused(e) => {
            println!("{name:<16} {note}; NOT TESTED: the prover refused ({})", e.chars().take(50).collect::<String>());
            1
        }
    }
}
