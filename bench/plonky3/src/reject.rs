//! Rejecting the non-generic LogUp challenge (Lean: `Ski/ZK/Reject.lean`).
//!
//! The lookups share one combiner `β` in `F_p[x]/(x^4 - 11)`.  For `β` in
//! `F_p(x^2)`, its `x^1` and `x^3` coefficients zero, a blinding tuple's
//! LogUp term is no bijection onto the field, and the published terminals
//! need not hide the private ones (`Circuit.generic_iff`).  Whether `β` is
//! one of those `p^2` of `p^4` values is public.  So:
//!
//! - every hiding verifier replays `β` and rejects a proof whose `β` is not
//!   generic (`check_beta`), the test Lean's `genB` makes;
//! - the honest prover, on drawing one, proves again from a fresh seed
//!   (`until_generic`).
//!
//! The transcripts then range over the generic `β` only, and Lean's
//! `transcript_zkG` simulates them without the `p^2/p^4` term.  An honest
//! proof's `β` is non-generic with probability about `2^-62`, so the retry
//! is never expected to run, and every proof that verified before still
//! verifies.

use super::*;
use p3_batch_stark::{BatchProof, BatchShape, BatchVerifierTranscript};
use p3_field::BasedVectorSpace;
use p3_lookup::LogUpGadget;
use p3_uni_stark::StarkGenericConfig;
use sudoku::{public_zk_config, ZkConfig};

/// **`genB`**: `β` has a coefficient at `x^1` or `x^3`.
pub(crate) fn generic(beta: Challenge) -> bool {
    let c = <Challenge as BasedVectorSpace<Val>>::as_basis_coefficients_slice(&beta);
    c[1] != Val::ZERO || c[3] != Val::ZERO
}

/// The lookups' combiner `β`, replayed from the statement's AIRs and the
/// proof as the verifier draws it.  Every lookup's challenge pair is
/// `(bus prefix, β)`, so each odd entry must be the same `β`.
pub(crate) fn proof_beta(airs: &[SkiAir], proof: &BatchProof<ZkConfig>) -> Result<Challenge, String> {
    let config = public_zk_config();
    let data = ProverData::<ZkConfig>::from_airs_and_degrees(&config, airs, &proof.degree_bits)
        .map_err(|e| format!("setup: {e:?}"))?;
    let common = &data.common;
    let pvs = crate::stmt::public_values(airs);
    let shape = BatchShape {
        trace_widths: airs.iter().map(|x| <SkiAir as BaseAir<Val>>::width(x)).collect(),
        public_value_counts: crate::stmt::public_value_counts(airs),
        preprocessed_widths: airs.iter().map(|x| <SkiAir as BaseAir<Val>>::preprocessed_width(x)).collect(),
        has_preprocessed_commitment: true,
        num_lookup_instances: common.lookups.iter().filter(|l| !l.is_empty()).count(),
        lookup_pow_bits: config.lookup_proof_of_work_bits(),
        has_randomization_commitment: true,
        ood_pow_bits: config.ood_proof_of_work_bits(),
    };
    let mut ch = config.initialise_challenger();
    let mut t = BatchVerifierTranscript::<Challenger, Val, Challenge, _>::new(&mut ch, shape);
    t.instance_bindings(&proof.degree_bits);
    t.main_phase(proof.commitments.main.clone(), &pvs);
    t.preprocessed_phase(common.preprocessed.as_ref().map(|g| g.commitment.clone()));
    let chs = t
        .lookup_phase(&common.lookups, &LogUpGadget::new(), proof.lookup_pow_witness)
        .map_err(|e| format!("lookup challenges: {e:?}"))?;
    t.abort();
    let betas: Vec<Challenge> = chs.iter().flat_map(|c| c.iter().skip(1).step_by(2).copied()).collect();
    let beta = *betas.first().ok_or("no lookup challenges")?;
    if betas.iter().any(|&b| b != beta) {
        return Err("the lookups' combiners differ".into());
    }
    Ok(beta)
}

/// **The verifier's test**, after the proof verifies: its `β` is generic.
pub(crate) fn check_beta(airs: &[SkiAir], proof: &BatchProof<ZkConfig>) -> Result<(), String> {
    if generic(proof_beta(airs, proof)?) {
        Ok(())
    } else {
        Err("the LogUp challenge β is in F_p(x^2), where the blinding does not hide".into())
    }
}

/// **The prover's retry**: `attempt` draws a fresh seed and proves; a proof
/// whose `β` is not generic is discarded, and the prover tries again.
pub(crate) fn until_generic<T>(
    airs: &[SkiAir],
    mut attempt: impl FnMut() -> Result<(BatchProof<ZkConfig>, T), String>,
) -> Result<(BatchProof<ZkConfig>, T), String> {
    loop {
        let (proof, x) = attempt()?;
        if generic(proof_beta(airs, &proof)?) {
            return Ok((proof, x));
        }
        eprintln!("the LogUp challenge β is in F_p(x^2): proving again from a fresh seed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generic_is_genb() {
        let e = |a: [u32; 4]| Challenge::from_basis_coefficients_fn(|i| Val::from_u32(a[i]));
        assert!(!generic(e([0, 0, 0, 0])));
        assert!(!generic(e([5, 0, 7, 0])));
        assert!(generic(e([0, 1, 0, 0])));
        assert!(generic(e([0, 0, 0, 1])));
        assert!(generic(e([3, 2, 1, 9])));
    }
}
