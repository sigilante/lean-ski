//! The Poseidon2 table (`Ski/Circuit/P2Air.lean`): one row per permutation.
//!
//! The first 650 columns are the sixteen inputs, then for each round what
//! it commits: the initial external layer's new state; for a full round,
//! the sixteen cubes `x = a^3` of `a = s + c`, then the sixteen S-box
//! outputs `y = x x a`, then the external layer's new state; for a partial
//! round, the first entry's cube and output, then the internal layer's new
//! state.  The last state is the output.  Two more columns hold the call's
//! key and an activity bit.  The constraints are emitted in the order Lean's `P2Air.gen`
//! builds them, and the linear layers are Plonky3's generic ones
//! (`GenericPoseidon2LinearLayersBabyBear`), so the export compared with
//! Lean (`lake exe circuit compare-p2`) also checks the specification's
//! linear layers against those, as polynomials.  An active row receives a
//! call's sixteen inputs on `p2v` and sends its sixteen outputs on `p2w`,
//! each `(key, e, value)`, the key the call's counter (`src/compp.rs`).

use super::*;
use p3_baby_bear::{
    GenericPoseidon2LinearLayersBabyBear as Layers, BABYBEAR_POSEIDON2_RC_16_EXTERNAL_FINAL as RC_FINAL,
    BABYBEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL as RC_INITIAL, BABYBEAR_POSEIDON2_RC_16_INTERNAL as RC_INTERNAL,
};
use p3_poseidon2::GenericPoseidon2LinearLayers;
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

/// The committed columns, then the call's key (its counter) and whether the
/// row is active.
pub const P2_COLS: usize = 650;
pub const P2_KEY: usize = P2_COLS;
pub const P2_ACT: usize = P2_COLS + 1;
pub const P2_WIDTH: usize = P2_COLS + 2;

/// The rounds' values for one input, in column order, and the output.
fn row_values(input: [Val; 16]) -> (Vec<Val>, [Val; 16]) {
    let mut row: Vec<Val> = input.to_vec();
    let mut st = input;
    Layers::external_linear_layer(&mut st);
    row.extend_from_slice(&st);
    let full = |row: &mut Vec<Val>, st: &mut [Val; 16], rc: &[Val; 16]| {
        let mut post = [Val::ZERO; 16];
        let mut cubes = [Val::ZERO; 16];
        for i in 0..16 {
            let a = st[i] + rc[i];
            cubes[i] = a * a * a;
            post[i] = cubes[i] * cubes[i] * a;
        }
        row.extend_from_slice(&cubes);
        row.extend_from_slice(&post);
        Layers::external_linear_layer(&mut post);
        row.extend_from_slice(&post);
        *st = post;
    };
    for rc in RC_INITIAL.iter() {
        full(&mut row, &mut st, rc);
    }
    for &c in RC_INTERNAL.iter() {
        let a = st[0] + c;
        let x = a * a * a;
        let y = x * x * a;
        row.push(x);
        row.push(y);
        st[0] = y;
        Layers::internal_linear_layer(&mut st);
        row.extend_from_slice(&st);
    }
    for rc in RC_FINAL.iter() {
        full(&mut row, &mut st, rc);
    }
    assert_eq!(row.len(), P2_COLS);
    (row, st)
}

/// The table for `rows` inputs, each with its key and activity, padded to
/// `2^min_log` rows or the next power of two by the permutation of zero,
/// inactive.  Each output is checked against Plonky3's permutation.
pub fn p2_trace_keyed(rows: &[([Val; 16], u32, u32)], min_log: usize) -> RowMajorMatrix<Val> {
    let perm = default_babybear_poseidon2_16();
    let h = rows.len().max(1 << min_log).next_power_of_two();
    let mut values = Vec::with_capacity(h * P2_WIDTH);
    for r in 0..h {
        let (input, key, act) = rows.get(r).copied().unwrap_or(([Val::ZERO; 16], 0, 0));
        let (row, out) = row_values(input);
        let mut want = input;
        perm.permute_mut(&mut want);
        assert_eq!(out, want, "the table's rounds are Plonky3's permutation");
        values.extend_from_slice(&row);
        values.push(Val::from_u32(key));
        values.push(Val::from_u32(act));
    }
    RowMajorMatrix::new(values, P2_WIDTH)
}

/// The constraints, in `P2Air.gen`'s order, and the message on `p2`.
pub fn eval_p2<AB: PermutationAirBuilder + InteractionBuilder>(b: &mut AB) {
    let main = b.main();
    let loc: Vec<AB::Expr> = main.current_slice().iter().map(|&v| v.into()).collect();
    let cols = |k: usize| -> [AB::Expr; 16] { std::array::from_fn(|i| loc[k + i].clone()) };
    // A linear layer at column `k`: each new entry minus its expression.
    fn lin<AB: AirBuilder>(b: &mut AB, loc: &[AB::Expr], k: usize, new: &[AB::Expr; 16]) {
        for i in 0..16 {
            b.assert_zero(loc[k + i].clone() - new[i].clone());
        }
    }
    let mut st = cols(0);
    let mut k = 16;
    let mut e = st.clone();
    Layers::external_linear_layer(&mut e);
    lin(b, &loc, k, &e);
    st = cols(k);
    k += 16;
    let full = |b: &mut AB, st: &mut [AB::Expr; 16], k: &mut usize, rc: &[Val; 16]| {
        for i in 0..16 {
            let a = st[i].clone() + AB::Expr::from_u32(rc[i].as_canonical_u32());
            let x = loc[*k + i].clone();
            b.assert_zero(x.clone() - a.clone() * a.clone() * a.clone());
            b.assert_zero(loc[*k + 16 + i].clone() - x.clone() * x * a);
        }
        let mut e = cols(*k + 16);
        Layers::external_linear_layer(&mut e);
        lin(b, &loc, *k + 32, &e);
        *st = cols(*k + 32);
        *k += 48;
    };
    for rc in RC_INITIAL.iter() {
        full(b, &mut st, &mut k, rc);
    }
    for &c in RC_INTERNAL.iter() {
        let a = st[0].clone() + AB::Expr::from_u32(c.as_canonical_u32());
        let x = loc[k].clone();
        b.assert_zero(x.clone() - a.clone() * a.clone() * a.clone());
        b.assert_zero(loc[k + 1].clone() - x.clone() * x * a);
        let mut e = st.clone();
        e[0] = loc[k + 1].clone();
        Layers::internal_linear_layer(&mut e);
        lin(b, &loc, k + 2, &e);
        st = cols(k + 2);
        k += 18;
    }
    for rc in RC_FINAL.iter() {
        full(b, &mut st, &mut k, rc);
    }
    assert_eq!(k, P2_COLS);
    // The call's inputs received, its outputs sent, keyed by its counter.
    let (key, act) = (loc[P2_KEY].clone(), loc[P2_ACT].clone());
    b.assert_bool(act.clone());
    let ins = cols(0);
    for e in 0..16 {
        b.push_interaction(compp::P2V, [key.clone(), AB::Expr::from_u32(e as u32), ins[e].clone()], -Count::bounded(act.clone(), 1));
    }
    for e in 0..16 {
        b.push_interaction(compp::P2W, [key.clone(), AB::Expr::from_u32(e as u32), st[e].clone()], Count::bounded(act.clone(), 1));
    }
}

/// `ski-air p2-bench N`: a table of `N` permutations alone (all inactive),
/// its AIR compared with Lean's, proved and verified.
pub fn p2_bench(n: usize, tamper: bool) -> Result<(), String> {
    let airs = vec![SkiAir::P2];
    lean_statement("circuit", &["compare-p2", "-"], export::export_air("p2", &airs[0]).as_bytes())?;
    let rows: Vec<([Val; 16], u32, u32)> =
        (0..n).map(|r| (std::array::from_fn(|i| Val::from_u64((r * 16 + i) as u64 * 2654435761 % 2013265921)), 0, 0)).collect();
    let t0 = Instant::now();
    let mut tr = p2_trace_keyed(&rows, 8);
    if tamper {
        // The first row's first output, off by one: the row no longer computes Poseidon2.
        tr.values[P2_COLS - 16] += Val::ONE;
    }
    let gen_s = t0.elapsed().as_secs_f64();
    let config = make_config();
    let degrees = [p3_util::log2_strict_usize(tr.values.len() / P2_WIDTH)];
    let pd = ProverData::<Config>::from_airs_and_degrees(&config, &airs, &degrees).map_err(|e| format!("setup: {e:?}"))?;
    // The table alone has no public values (the statement digest rides on a CPU).
    let pvs: Vec<Vec<Val>> = vec![vec![]];
    let t1 = Instant::now();
    let proved = catch_unwind(AssertUnwindSafe(|| prove_batch(&config, &StarkInstance::new_multiple(&airs, &[&tr], &pvs), &pd)));
    let proof = match proved {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => return Err(format!("prove: {e:?}")),
        Err(e) => return Err(format!("prover panic: {}", panic_text(&e))),
    };
    let prove_s = t1.elapsed().as_secs_f64();
    let t2 = Instant::now();
    let v_config = make_config();
    let v_data = ProverData::<Config>::from_airs_and_degrees(&v_config, &airs, &proof.degree_bits).map_err(|e| format!("verifier setup: {e:?}"))?;
    verify_batch(&v_config, &airs, &proof, &pvs, &v_data.common).map_err(|e| format!("verify: {e:?}"))?;
    let verify_s = t2.elapsed().as_secs_f64();
    let size = postcard::to_allocvec(&proof).map(|v| v.len()).unwrap_or(0);
    println!(
        "p2: {n} permutations, {} rows x {P2_WIDTH} columns; trace {gen_s:.2} s, prove {prove_s:.2} s, verify {verify_s:.3} s, proof {size} bytes; VERIFIED",
        tr.values.len() / P2_WIDTH
    );
    Ok(())
}
