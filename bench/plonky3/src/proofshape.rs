//! **The proof's bytes against the model's view** (`ski-air proof-shape`).
//!
//! Lean's transcript theorems simulate a view: the PCS's view, the
//! challenges, the published private and public LogUp terminals, and the
//! tables' heights (`Ski/ZK/TranscriptN.lean`, `Ski/ZK/Heights.lean`).  A
//! released proof is a postcard encoding of Plonky3's `BatchProof`.  This
//! gate reads a hiding proof and accounts for every byte:
//!
//! - the bytes are exactly one `BatchProof`, and encoding it again gives
//!   the same bytes, so no byte sits outside its fields;
//! - each field is a part of the view: the commitments, the opened values
//!   and the opening proof are the PCS's view; `lookup_terminals` the
//!   terminals, one per table; `degree_bits` the heights, which the
//!   verifier pins to the statement's; the two proof-of-work witnesses are
//!   the unique values the verifier accepts after the transcript before
//!   them, so a function of the view;
//! - the challenges are not in the bytes: the verifier draws them.
//!
//! It prints each field's byte count.  Proofs of one statement differ in
//! size only in the opening proof: Plonky3's multi-openings send each
//! shared Merkle digest once, and how many paths share a digest depends on
//! the query positions, Fiat–Shamir challenges the simulator draws too.

use super::*;
use sudoku::ZkConfig;

type HProof = p3_batch_stark::BatchProof<ZkConfig>;

fn size<T: serde::Serialize>(x: &T) -> Result<usize, String> {
    postcard::to_allocvec(x).map(|v| v.len()).map_err(|e| format!("serialize: {e}"))
}

/// `ski-air proof-shape PROOF`: account for every byte of a hiding proof.
pub fn proof_shape(proof_in: &std::path::Path) -> Result<(), String> {
    let bytes = std::fs::read(proof_in).map_err(|e| format!("{}: {e}", proof_in.display()))?;
    let (proof, rest): (HProof, &[u8]) = postcard::take_from_bytes(&bytes).map_err(|e| format!("deserialize: {e}"))?;
    if !rest.is_empty() {
        return Err(format!("{} bytes after the proof", rest.len()));
    }
    let again = postcard::to_allocvec(&proof).map_err(|e| format!("serialize: {e}"))?;
    if again != bytes {
        return Err("the bytes are not the proof's own encoding".into());
    }
    if proof.commitments.random.is_none() {
        return Err("no randomization commitment: not a hiding proof".into());
    }
    if proof.lookup_terminals.len() != proof.degree_bits.len() {
        return Err(format!(
            "{} terminals for {} tables",
            proof.lookup_terminals.len(),
            proof.degree_bits.len()
        ));
    }
    let fields: [(&str, usize, &str); 7] = [
        ("commitments", size(&proof.commitments)?, "the PCS's view"),
        ("opened_values", size(&proof.opened_values)?, "the PCS's view"),
        ("opening_proof", size(&proof.opening_proof)?, "the PCS's view"),
        ("lookup_terminals", size(&proof.lookup_terminals)?, "the terminals, one per table"),
        ("degree_bits", size(&proof.degree_bits)?, "the heights, pinned to the statement's"),
        ("lookup_pow_witness", size(&proof.lookup_pow_witness)?, "unique given the transcript"),
        ("ood_pow_witness", size(&proof.ood_pow_witness)?, "unique given the transcript"),
    ];
    let total: usize = fields.iter().map(|f| f.1).sum();
    if total != bytes.len() {
        return Err(format!("the fields' {total} bytes are not the proof's {}", bytes.len()));
    }
    for (name, n, what) in fields {
        println!("  {name:<20} {n:>9} bytes  {what}");
    }
    // The opening proof: the opened values, fixed by the statement's shape
    // and the query count, and the Merkle multi-proofs, whose shared
    // digests depend on the query positions.
    let (rand_open, fri) = &proof.opening_proof;
    let mut values = size(rand_open)? + size(&fri.final_poly)?;
    let mut merkle = size(&fri.commit_phase_commits)?;
    let mut other = size(&fri.batch_pow_witness)? + size(&fri.commit_pow_witnesses)? + size(&fri.query_pow_witness)?;
    for o in &fri.input_openings {
        values += size(&o.opened_values)?;
        merkle += size(&o.opening_proof)?;
    }
    for st in &fri.commit_phase_openings {
        values += size(&st.sibling_values)?;
        merkle += size(&st.opening_proof)?;
    }
    // The vectors' length prefixes.
    other += size(&fri.input_openings.len())? + size(&fri.commit_phase_openings.len())?;
    println!("    opened values {values} bytes; Merkle digests {merkle} bytes; witnesses and lengths {other} bytes");
    if values + merkle + other != fields[2].1 {
        return Err(format!("the opening proof's parts, {} bytes, are not its {}", values + merkle + other, fields[2].1));
    }
    println!(
        "ACCOUNTED: {} bytes, every one in a field of the view; {} tables, heights 2^{:?}",
        bytes.len(),
        proof.degree_bits.len(),
        proof.degree_bits
    );
    Ok(())
}
