//! Cost of proving SKI reduction on RISC Zero.
//!
//! For every corpus row (`lake env lean --run bench/Dump.lean`), and for
//! each reducer (tree rewriting as `runF`, the write-once heap machine as
//! `mrunC`), the host checks the native port against the reference
//! contraction count, executes the guest to count cycles, and with
//! `--prove` produces and verifies a receipt.
//!
//! Usage: `host CORPUS [--native | --prove]`; `--native` runs the
//! conformance check and reports the shared form's size, without the zkVM.

use methods::{SKI_GUEST_ELF, SKI_GUEST_ID};
use risc0_zkvm::sha::{Digest, Impl, Sha256};
use risc0_zkvm::{default_executor, default_prover, ExecutorEnv};
use std::time::Instant;

const FUEL: u64 = 5_000_000;

fn env<'a>(mode: u8, src: &[u8], out: &'a mut Vec<u8>) -> ExecutorEnv<'a> {
    ExecutorEnv::builder()
        .stdout(out)
        .write(&mode)
        .unwrap()
        .write(&FUEL)
        .unwrap()
        .write(&(src.len() as u32))
        .unwrap()
        .write_slice(src)
        .build()
        .unwrap()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let corpus = std::fs::read_to_string(&args[1]).expect("corpus file");
    let prove = args.iter().any(|a| a == "--prove");
    let native = args.iter().any(|a| a == "--native");
    let mut bad = 0;
    println!(
        "{:<16} {:>6} {:>6} {:>5} {:>11} {:>11} {:>8} {:>4} {:>9} {:>9}",
        "row", "leaves", "steps", "mode", "cycles", "reduce", "red/step", "segs", "prove_s", "seal_B"
    );
    for line in corpus.lines() {
        let mut parts = line.split_whitespace();
        let (name, steps, src) = match (parts.next(), parts.next(), parts.next()) {
            (Some(n), Some(s), Some(t)) => (n, s.parse::<u64>().unwrap(), t.as_bytes()),
            _ => continue,
        };
        let leaves = src.iter().filter(|&&b| b != b'`').count();
        let tree = ski::run(ski::MODE_TREE, FUEL, src);
        let heap = ski::run(ski::MODE_HEAP, FUEL, src);
        // Conformance: both ports reach the reference count, and their
        // values are equal as graphs, compared without unsharing.
        let ok = match (&tree, &heap) {
            (Some((n, v)), Some((m, w))) if *n == steps && *m == steps => {
                ski::graph_eq(&v.term(), &w.term(), 10_000_000) == Some(true)
            }
            _ => false,
        };
        if !ok {
            println!("FAIL {name}: tree {:?} heap {:?} reference {steps}",
                tree.as_ref().map(|p| p.0), heap.as_ref().map(|p| p.0));
            bad += 1;
            continue;
        }
        let expect = |mode: u8| -> Digest {
            let v = if mode == ski::MODE_TREE { &tree } else { &heap };
            *Impl::hash_bytes(&v.as_ref().unwrap().1.shared().bytes)
        };
        if native {
            for (v, label) in [(&tree, "tree"), (&heap, "heap")] {
                let bytes = v.as_ref().unwrap().1.shared().bytes.len();
                println!("{name:<16} {leaves:>6} {steps:>6} {label:>5} shared form {bytes} bytes");
            }
            continue;
        }
        for (mode, label) in [(ski::MODE_TREE, "tree"), (ski::MODE_HEAP, "heap")] {
            let mut out = Vec::new();
            let info = default_executor().execute(env(mode, src, &mut out), SKI_GUEST_ELF).unwrap();
            let words: Vec<u32> =
                out.chunks(4).map(|c| u32::from_le_bytes(c.try_into().unwrap())).collect();
            let net: u64 = risc0_zkvm::serde::from_slice(&words).unwrap();
            let (din, count, dout): (Digest, Option<u64>, Digest) = info.journal.decode().unwrap();
            assert_eq!(din, *Impl::hash_bytes(src), "{name} {label}: input digest");
            assert_eq!(count, Some(steps), "{name} {label}: guest count");
            assert_eq!(dout, expect(mode), "{name} {label}: result");
            let cycles = info.cycles();
            let (secs, size) = if prove {
                let t0 = Instant::now();
                let mut sink = Vec::new();
                let receipt =
                    default_prover().prove(env(mode, src, &mut sink), SKI_GUEST_ELF).unwrap().receipt;
                let secs = t0.elapsed().as_secs_f64();
                receipt.verify(SKI_GUEST_ID).unwrap();
                let size = receipt.seal_size();
                (format!("{secs:.1}"), format!("{size}"))
            } else {
                ("-".into(), "-".into())
            };
            println!(
                "{:<16} {:>6} {:>6} {:>5} {:>11} {:>11} {:>8} {:>4} {:>9} {:>9}",
                name, leaves, steps, label, cycles, net, net / steps, info.segments.len(), secs, size
            );
        }
    }
    if bad > 0 {
        std::process::exit(1);
    }
}
