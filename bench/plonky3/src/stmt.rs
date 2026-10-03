//! The statement, bound into the transcript.
//!
//! Plonky3's transcript absorbs the batch's shape, the degree bits, the
//! commitments and each instance's public values before any challenge, but
//! not the constants inside the AIRs: the CPU's start head, stack and
//! counter, its accepting marker, the probe and restart parameters.  A
//! prover that names its statement after seeing the challenges could then
//! solve for such a constant.  So every proof carries, as the CPU
//! instance's public values, a Poseidon2 digest of everything the AIRs hold
//! (`digest`), and the verifier recomputes it from the AIRs it builds from
//! the statement: a proof checks against one statement only.
//!
//! The encoding destructures every AIR exhaustively, so a field added to
//! an AIR fails to compile until it is encoded.  Each part is tagged and
//! length-prefixed, and each `u32` is two 16-bit halves, so the encoding is
//! injective.  The preprocessed tables are encoded too, though their
//! commitment is absorbed already.

use p3_field::PrimeCharacteristicRing;
use p3_symmetric::CryptographicHasher;

use crate::composed::{RestartPub, SegsAir};
use crate::jets::JetAir;
use crate::probe::{ProbeAir, ProbePub};
use crate::witness::WitTAir;
use crate::{CpuAir, MemAir, MyHash, ProgAir, SkiAir, Val, WitAir};

/// The digest's length: the CPU instance's public values.
pub(crate) const STMT_LEN: usize = 8;

fn word(out: &mut Vec<u32>, w: u32) {
    out.push(w);
}

fn rows<const W: usize>(out: &mut Vec<u32>, tag: u32, rs: &[[u32; W]]) {
    out.push(tag);
    out.push(W as u32);
    out.push(rs.len() as u32);
    for r in rs {
        out.extend_from_slice(r);
    }
}

fn opt(out: &mut Vec<u32>, o: Option<u32>) {
    match o {
        None => out.push(0),
        Some(v) => {
            out.push(1);
            out.push(v);
        }
    }
}

fn encode(a: &SkiAir, out: &mut Vec<u32>) {
    match a {
        SkiAir::Cpu(c) => {
            let CpuAir { hd0, stk0, ctr0, accept, accept_k, blind, jets, probe, restart, p2 } = c;
            word(out, 1);
            word(out, *hd0);
            word(out, *stk0);
            word(out, *ctr0);
            opt(out, *accept);
            word(out, *accept_k as u32);
            word(out, *blind as u32);
            word(out, *jets as u32);
            match probe {
                None => word(out, 0),
                Some(ProbePub { n, last_atom }) => {
                    word(out, 1);
                    word(out, *n);
                    word(out, *last_atom);
                }
            }
            match restart {
                None => word(out, 0),
                Some(RestartPub { n, nil }) => {
                    word(out, 1);
                    word(out, *n);
                    word(out, *nil);
                }
            }
            // The Poseidon2 jet's atom and the comb's root, only when the CPU
            // carries its row, so every other statement's digest is
            // unchanged; the marker is no AIR's tag, so the encoding still
            // parses one way.
            if let Some(crate::compp::P2Pub { j, root }) = p2 {
                word(out, 0x7032_6a74);
                word(out, *j);
                word(out, *root);
            }
        }
        SkiAir::Mem(MemAir { blind }) => {
            word(out, 2);
            word(out, *blind as u32);
        }
        SkiAir::Prog(ProgAir { pre }) => rows(out, 3, pre),
        SkiAir::Wit(WitAir { pre }) => rows(out, 4, pre),
        SkiAir::Jet(j) => match j {
            JetAir::Roots(pre, b) => {
                rows(out, 5, pre);
                word(out, *b as u32);
            }
            JetAir::Hdr(pre, b) => {
                rows(out, 6, pre);
                word(out, *b as u32);
            }
            JetAir::Tmpl(pre, b) => {
                rows(out, 7, pre);
                word(out, *b as u32);
            }
            JetAir::Pop(b) => {
                word(out, 8);
                word(out, *b as u32);
            }
            JetAir::Instw(b) => {
                word(out, 9);
                word(out, *b as u32);
            }
        },
        SkiAir::Probe(p) => match p {
            ProbeAir::Plan(pre) => rows(out, 10, pre),
            ProbeAir::Pw => word(out, 11),
        },
        SkiAir::WitT(WitTAir { pre }) => rows(out, 12, pre),
        SkiAir::Segs(SegsAir { pre }) => rows(out, 13, pre),
        SkiAir::P2 => word(out, 14),
        SkiAir::P2In => word(out, 15),
        SkiAir::P2Out => word(out, 16),
        SkiAir::P2Idx(pre) => rows(out, 17, pre),
    }
}

/// The statement's digest: every AIR's data, in batch order.
pub(crate) fn digest(airs: &[SkiAir]) -> [Val; STMT_LEN] {
    let mut words = vec![0x736b_6931, airs.len() as u32];
    for a in airs {
        encode(a, &mut words);
    }
    let hash = MyHash::new(p3_baby_bear::default_babybear_poseidon2_16());
    hash.hash_iter(
        words
            .iter()
            .flat_map(|&w| [Val::from_u32(w & 0xffff), Val::from_u32(w >> 16)]),
    )
}

/// The public values of a batch: the digest on the CPU instance, first.
pub(crate) fn public_values(airs: &[SkiAir]) -> Vec<Vec<Val>> {
    assert!(matches!(airs.first(), Some(SkiAir::Cpu(_))), "the CPU instance comes first");
    let mut pvs = vec![vec![]; airs.len()];
    pvs[0] = digest(airs).to_vec();
    pvs
}

/// The public value counts, for a transcript replay: each AIR's own.
pub(crate) fn public_value_counts(airs: &[SkiAir]) -> Vec<usize> {
    airs.iter().map(|a| <SkiAir as p3_air::BaseAir<Val>>::num_public_values(a)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cpu(hd0: u32, accept: Option<u32>) -> SkiAir {
        SkiAir::Cpu(CpuAir {
            hd0,
            stk0: 1,
            ctr0: 2,
            accept,
            accept_k: false,
            blind: true,
            jets: false,
            probe: None,
            restart: None,
            p2: None,
        })
    }

    /// The CPU's constants, which no preprocessed table holds, each move the digest.
    #[test]
    fn the_digest_binds_the_cpu_constants() {
        let base = digest(&[cpu(5, Some(7))]);
        assert_ne!(base, digest(&[cpu(6, Some(7))]));
        assert_ne!(base, digest(&[cpu(5, Some(8))]));
        assert_ne!(base, digest(&[cpu(5, None)]));
        // `None` and `Some(0)` encode apart.
        assert_ne!(digest(&[cpu(5, None)]), digest(&[cpu(5, Some(0))]));
    }

    /// A table's rows are length-prefixed: splitting them differently moves the digest.
    #[test]
    fn the_digest_separates_tables() {
        let a = [cpu(0, None), SkiAir::Prog(ProgAir { pre: vec![[1, 2, 3, 4, 5]] }), SkiAir::Wit(WitAir { pre: vec![] })];
        let b = [cpu(0, None), SkiAir::Prog(ProgAir { pre: vec![] }), SkiAir::Wit(WitAir { pre: vec![] })];
        assert_ne!(digest(&a), digest(&b));
        let c = [cpu(0, None), SkiAir::Mem(MemAir { blind: false })];
        let d = [cpu(0, None), SkiAir::Mem(MemAir { blind: true })];
        assert_ne!(digest(&c), digest(&d));
    }

    #[test]
    fn the_digest_is_on_the_cpu_instance() {
        let pvs = public_values(&[cpu(0, None), SkiAir::Mem(MemAir { blind: false })]);
        assert_eq!(pvs[0].len(), STMT_LEN);
        assert!(pvs[1].is_empty());
        assert_eq!(public_value_counts(&[cpu(0, None), SkiAir::Mem(MemAir { blind: false })]), vec![STMT_LEN, 0]);
    }
}
