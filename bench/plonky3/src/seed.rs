//! The prover's secret randomness: one 128-bit seed per proof.
//!
//! Every hiding draw of a proof comes from one seed, taken fresh from the
//! operating system for that proof and never reused: the blinding tuples of
//! the LogUp sums, the salts of the Merkle leaves, and the random codewords
//! that mask the committed polynomials.  ChaCha20 expands it, one stream per
//! use, so no two uses share key stream.  The public commitment
//! of the preprocessed tables keeps its public seed (`PUBLIC_SEED`), which
//! the verifier must reproduce.
//!
//! The Lean theorems count over uniform randomness (`tree_hides`,
//! `masks_hide`, `transcript_zkN`); this file is where that becomes an
//! assumption, that ChaCha20 under a 128-bit seed is indistinguishable from
//! uniform.  The seed is outside the statement, and no kernel entropy event
//! feeds it.

use chacha20::ChaCha20Rng;
use core::convert::Infallible;
use rand::rngs::{StdRng, SysRng};
use rand::{SeedableRng, TryCryptoRng, TryRng};

/// A proof's secret seed.  Fresh per proof and used once: `split`
/// consumes it, so two proofs cannot share a stream by construction.  Two
/// proofs under one seed would publish the difference of their traces, the
/// masking being linear.
///
/// Its 128 bits bound a single key search at `2^128`; against `N` proofs at
/// once, whose opened salts are known ChaCha20 output, a batch search costs
/// about `2^128 / N`.  The seed is not wiped from memory: it lives on in the
/// key streams, and a reader of the prover's memory already has the witness.
pub(crate) struct ProverSeed([u8; 16]);

/// The ChaCha20 stream ids, one per use.
const BLIND: u64 = 1;
const SALTS: u64 = 2;
const CODEWORDS: u64 = 3;

/// Fills the high half of the ChaCha20 key: the seed is 128 bits, the key
/// 256, and this constant separates ski-air's use of a seed from any other.
const DOMAIN: [u8; 16] = *b"ski-air prover\x00\x01";

/// The blinding stream of a proof: its LogUp blinding tuples.
pub(crate) struct BlindStream(pub(crate) ChaCha20Rng);

/// The PCS streams of a proof: its leaf salts and its masking codewords.
pub(crate) struct PcsStreams {
    pub(crate) salts: ChaCha20Rng,
    pub(crate) codewords: ChaCha20Rng,
}

impl ProverSeed {
    /// A fresh seed from the operating system.
    pub(crate) fn fresh() -> Self {
        let mut s = [0u8; 16];
        SysRng.try_fill_bytes(&mut s).expect("the operating system's generator");
        ProverSeed(s)
    }

    fn stream(&self, id: u64) -> ChaCha20Rng {
        let mut key = [0u8; 32];
        key[..16].copy_from_slice(&self.0);
        key[16..].copy_from_slice(&DOMAIN);
        let mut r = ChaCha20Rng::from_seed(key);
        r.set_stream(id);
        r
    }

    /// The proof's three streams, consuming the seed.
    pub(crate) fn split(self) -> (BlindStream, PcsStreams) {
        (
            BlindStream(self.stream(BLIND)),
            PcsStreams { salts: self.stream(SALTS), codewords: self.stream(CODEWORDS) },
        )
    }
}

/// The generator type of the hiding PCS and MMCS: the public seed's, or a
/// ChaCha20 stream.  A stream is secret when it is one of a proof's; a clone
/// of a hiding MMCS forks its generator by seeding a ChaCha20 stream from it
/// (`SeedableRng::from_rng`), and a fork is exactly as secret as its parent,
/// so the public configuration's forks are public.
pub(crate) enum ProverRng {
    Public(StdRng),
    Stream(ChaCha20Rng),
}

impl ProverRng {
    pub(crate) fn public(seed: u64) -> Self {
        ProverRng::Public(StdRng::seed_from_u64(seed))
    }
}

impl TryRng for ProverRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        match self {
            ProverRng::Public(r) => r.try_next_u32(),
            ProverRng::Stream(r) => r.try_next_u32(),
        }
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        match self {
            ProverRng::Public(r) => r.try_next_u64(),
            ProverRng::Stream(r) => r.try_next_u64(),
        }
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        match self {
            ProverRng::Public(r) => r.try_fill_bytes(dst),
            ProverRng::Stream(r) => r.try_fill_bytes(dst),
        }
    }
}

impl TryCryptoRng for ProverRng {}

impl SeedableRng for ProverRng {
    type Seed = [u8; 32];

    fn from_seed(seed: [u8; 32]) -> Self {
        ProverRng::Stream(ChaCha20Rng::from_seed(seed))
    }
}
