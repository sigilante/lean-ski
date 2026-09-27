//! The guest: reduce one term and commit the statement: the input's
//! digest, the contraction count, and the digest of the result's shared
//! form (`ski::Shared`).
use risc0_zkvm::guest::env;
use risc0_zkvm::sha::{Impl, Sha256};

fn main() {
    let mode: u8 = env::read();
    let fuel: u64 = env::read();
    let len: u32 = env::read();
    let mut src = vec![0u8; len as usize];
    env::read_slice(&mut src);
    let digest = *Impl::hash_bytes(&src);
    let term = ski::parse(&src);
    let c0 = env::cycle_count();
    let result = term.and_then(|t| ski::reduce(mode, fuel, t));
    let c1 = env::cycle_count();
    let (count, out) = match result {
        Some((n, v)) => (Some(n), v.shared().bytes),
        None => (None, Vec::new()),
    };
    env::commit(&(digest, count, *Impl::hash_bytes(&out)));
    // The reduction's own cycles (parsing excluded), for the host's report;
    // written to stdout, outside the journal and the statement.
    env::write(&(c1 - c0));
}
