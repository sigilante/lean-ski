//! The per-round Fiat–Shamir budget of a batch proof.
//!
//! Plonky3 derives every challenge by hashing the transcript, so a cheating
//! prover can retry each round, and the proof is as strong as its weakest
//! round: `λ` bits means each attempt at that round succeeds with
//! probability at most `2^-λ`, and the round's proof-of-work multiplies an
//! attempt's cost by `2^b`.  `p3-security` grades each round of a single
//! instance.  A batch proof checks one constraint identity per AIR at one
//! out-of-domain point and runs one low-degree test over every committed
//! column, so this module composes the rounds for the batch:
//!
//! - `ali`, the random combination of each AIR's constraints: a union over
//!   the AIRs, so `p3-security`'s bound at the total constraint count;
//! - `deep-ali`, the out-of-domain point: a union over the AIRs of each
//!   AIR's bound at its own trace length, degree and quotient chunks;
//! - `logup`, the lookup challenges: Lean's `logup_accept`,
//!   `M (W + 2) / |EF|`, `M` every interaction of every row of every table;
//! - the low-degree test, its batching combination and the hash collision
//!   cap, from `p3-security` for one instance at the longest trace,
//!   batching every column of the batch (`p3_batch_stark::num_batched_openings`).
//!
//! The constraint degree is bounded by the quotient's chunk count
//! (`2^lq + 1`), which only overstates the out-of-domain error.  The proven
//! regimes (unique and list decoding) and the conjectured one are reported;
//! the proven figures rest on the published proximity-gap bounds, the
//! conjectured on the random-words conjecture, and both on the hash behaving
//! as a random oracle.

use p3_air::symbolic::AirLayout;
use p3_air::{Air, BaseAir};
use p3_batch_stark::symbolic::{get_log_num_quotient_chunks_for_domain, get_symbolic_constraints};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::PrimeCharacteristicRing;
use p3_lookup::{InteractionSymbolicBuilder, LogUpGadget, Lookup};
use p3_security::air::composition_error;
use p3_security::deep::deep_ali_error;
use p3_security::error::ErrorBits;
use p3_security::fri::FriRegime;
use p3_security::grinding::{boost, GrindingSites};
use p3_security::proximity::list_size_ldr_m;
use p3_security::report::{Regime, RegimeReport, ALI_LABEL, DEEP_LABEL};
use p3_security::shape::{InstanceShape, StarkAirParams};
use p3_security::stark::{conjectured_security_report, proven_security_report};
use p3_uni_stark::OpeningShape;

use crate::{Challenge, Val};

/// Set when a budget was printed, so `fs-budget` can say when none was.
pub(crate) static EMITTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// `log2 |EF|`, BabyBear's quartic extension: `4 log2 p`.
fn ef_bits() -> f64 {
    4.0 * (2013265921f64).log2()
}

/// What the budget needs of one proof.
#[derive(Clone, Copy)]
pub(crate) struct BatchShape<'a> {
    /// Each instance's committed degree bits (`BatchProof::degree_bits`).
    pub degree_bits: &'a [usize],
    /// Each instance's lookups (`CommonData::lookups`).
    pub lookups: &'a [&'a [Lookup<Val>]],
    /// Each instance's preprocessed width, `0` for none.
    pub preprocessed_widths: &'a [usize],
    /// Whether the PCS hides, and with how many random codewords.
    pub openings: OpeningShape,
    pub fri: FriRegime,
    pub grinding: GrindingSites,
    /// Collision resistance of the commitment hash, in bits.
    pub collision_bits: usize,
}

/// One instance, as the rounds see it.
struct Inst {
    num_constraints: usize,
    air: StarkAirParams,
    log_len: usize,
    batched: usize,
    interactions: usize,
    width: usize,
}

fn instances<A>(airs: &[A], s: &BatchShape) -> Vec<Inst>
where
    A: BaseAir<Val> + Air<InteractionSymbolicBuilder<Val, Challenge>>,
{
    let zk = usize::from(s.openings.is_zk());
    airs.iter()
        .enumerate()
        .map(|(i, air)| {
            let layout = AirLayout {
                preprocessed_width: s.preprocessed_widths[i],
                main_width: air.width(),
                num_public_values: air.num_public_values(),
                num_periodic_columns: air.num_periodic_columns(),
                ..Default::default()
            };
            let lookups = s.lookups[i];
            let gadget = LogUpGadget::new();
            let (base, ext) =
                get_symbolic_constraints::<Val, Challenge, A, _>(air, layout, lookups, &gadget);
            // The trace domain before the hiding PCS doubles it.
            let log_h = s.degree_bits[i] - zk;
            let domain = TwoAdicMultiplicativeCoset::new(Val::ONE, log_h).expect("a two-adic domain");
            let lq = get_log_num_quotient_chunks_for_domain::<Val, Challenge, A, _>(
                air, layout, domain, lookups, zk, &gadget,
            );
            let chunks = 1usize << (lq + zk);
            let main_next = !air.main_next_row_columns().is_empty();
            let pre_next = !air.preprocessed_next_row_columns().is_empty();
            let batched = p3_batch_stark::num_batched_openings(
                air.width(),
                main_next,
                s.preprocessed_widths[i],
                pre_next,
                chunks,
                lookups.len(),
                4,
                s.openings,
            );
            let interactions = lookups.iter().map(|l| l.elements.len()).sum::<usize>();
            let width = lookups
                .iter()
                .flat_map(|l| l.elements.iter().map(|e| e.len()))
                .max()
                .unwrap_or(0);
            Inst {
                num_constraints: base.len() + ext.len(),
                air: StarkAirParams {
                    num_constraints: base.len() + ext.len(),
                    // The quotient has `2^lq` chunks before hiding, so the
                    // constraint degree is at most `2^lq + 1`.
                    max_constraint_degree: (1usize << lq) + 1,
                    num_quotient_chunks: chunks,
                    // The permutation trace of an AIR with lookups is opened at `ζ` and `ζ g`.
                    max_combo: if main_next || pre_next || !lookups.is_empty() { 2 } else { 1 },
                },
                log_len: s.degree_bits[i],
                batched,
                interactions: interactions << log_h,
                width,
            }
        })
        .collect()
}

/// `-log2` of a sum of errors given in bits.
fn sum_bits(bits: impl Iterator<Item = f64>) -> f64 {
    let e: f64 = bits.map(|b| (-b).exp2()).sum();
    if e <= 0.0 { f64::INFINITY } else { -e.log2() }
}

/// One regime's rounds for the batch, from `p3-security`'s report for the
/// combined instance: its ALI and DEEP terms replaced by the batch's, and
/// the LogUp term added.
fn regime_rounds(rep: &RegimeReport, insts: &[Inst], list: f64, s: &BatchShape, logup: f64) -> Vec<(String, f64)> {
    let modulus = ef_bits().floor() as usize;
    let total_constraints: usize = insts.iter().map(|i| i.num_constraints).sum();
    let ali = composition_error(total_constraints, list, modulus).bits();
    let deep = sum_bits(insts.iter().map(|i| {
        let shape = InstanceShape {
            log_trace_length: i.log_len,
            modulus_bits: modulus,
            collision_resistance: s.collision_bits,
            num_batched_functions: 1,
        };
        deep_ali_error(&i.air, &shape, list).bits()
    }));
    let deep = boost(ErrorBits::from_log2(deep), s.grinding.out_of_domain).bits();
    let mut rounds = vec![("ali".to_string(), ali), ("deep-ali (out-of-domain)".to_string(), deep)];
    for t in rep.terms() {
        if t.label != ALI_LABEL && t.label != DEEP_LABEL {
            rounds.push((t.label.to_string(), t.bits.bits()));
        }
    }
    // In a list-decoding regime the commitment fixes only a list of `list`
    // candidate traces, and LogUp's bound holds for each: a union over them.
    rounds.push(("logup (Lean: logup_accept)".to_string(), logup - list.log2()));
    rounds
}

/// The rounds of every regime, for given FRI parameters and grinding.
fn evaluate(insts: &[Inst], s: &BatchShape, fri: &FriRegime, g: &GrindingSites) -> Vec<(String, Vec<(String, f64)>)> {
    let modulus = ef_bits().floor() as usize;
    let max_log = insts.iter().map(|i| i.log_len).max().unwrap_or(0);
    let combined = StarkAirParams {
        num_constraints: insts.iter().map(|i| i.num_constraints).sum(),
        max_constraint_degree: insts.iter().map(|i| i.air.max_constraint_degree).max().unwrap_or(1),
        num_quotient_chunks: insts.iter().map(|i| i.air.num_quotient_chunks).max().unwrap_or(1),
        max_combo: insts.iter().map(|i| i.air.max_combo).max().unwrap_or(1),
    };
    let shape = InstanceShape {
        log_trace_length: max_log,
        modulus_bits: modulus,
        collision_resistance: s.collision_bits,
        num_batched_functions: insts.iter().map(|i| i.batched).sum(),
    };
    // LogUp: `M (W + 2) / |EF|` (`logup_accept`), ground by the lookup site.
    let m: usize = insts.iter().map(|i| i.interactions).sum();
    let w = insts.iter().map(|i| i.width).max().unwrap_or(0).max(1);
    let logup = if m == 0 {
        f64::INFINITY
    } else {
        ef_bits() - ((m * (w + 2)) as f64).log2() + g.lookup_challenge as f64
    };
    let s2 = BatchShape { grinding: *g, ..*s };
    let proven = proven_security_report(fri, &combined, &shape, &[], g);
    let conj = conjectured_security_report(fri, &combined, &shape, &[], g);
    let mut regimes = vec![("proven, unique decoding".to_string(), regime_rounds(&proven.udr, insts, 1.0, &s2, logup))];
    if let Some(ldr) = &proven.ldr {
        if let Regime::ListDecoding { m: mm } = ldr.regime {
            regimes.push((
                format!("proven, list decoding (m = {mm})"),
                regime_rounds(ldr, insts, list_size_ldr_m(fri.log_blowup, mm), &s2, logup),
            ));
        }
    }
    regimes.push(("conjectured (random words)".to_string(), regime_rounds(&conj, insts, 1.0, &s2, logup)));
    regimes
}

fn weakest(rounds: &[(String, f64)]) -> (String, f64) {
    rounds
        .iter()
        .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
        .map(|(l, b)| (l.clone(), *b))
        .unwrap()
}

/// The proof-of-work bits a round needs to reach `target`, `None` for a
/// round no grinding site serves.
fn grind_site(label: &str) -> Option<&'static str> {
    if label.starts_with("logup") {
        Some("lookup")
    } else if label.starts_with("deep-ali") {
        Some("out-of-domain")
    } else if label == "batch-combination" {
        Some("batch")
    } else if label == "ldt-query-phase" {
        Some("FRI query")
    } else if label == "ldt-commit-phase" {
        Some("FRI commit (each round)")
    } else {
        None
    }
}

fn grinding_needed(rounds: &[(String, f64)], target: f64) -> String {
    let mut out = Vec::new();
    for (label, bits) in rounds {
        if *bits < target {
            match grind_site(label) {
                Some(site) => out.push(format!("{site} +{}", (target - bits).ceil() as usize)),
                None => out.push(format!("{label} short by {:.1}, no grinding site", target - bits)),
            }
        }
    }
    if out.is_empty() { "nothing more".to_string() } else { out.join(", ") }
}

/// Print the budget of a batch proof, and what reaching 100 and 128 bits
/// would take.
pub(crate) fn report<A>(name: &str, airs: &[A], s: &BatchShape)
where
    A: BaseAir<Val> + Air<InteractionSymbolicBuilder<Val, Challenge>>,
{
    let insts = instances(airs, s);
    let max_log = insts.iter().map(|i| i.log_len).max().unwrap_or(0);
    let m: usize = insts.iter().map(|i| i.interactions).sum();
    let w = insts.iter().map(|i| i.width).max().unwrap_or(0).max(1);
    println!(
        "{name}: {} AIRs, longest trace 2^{max_log}, {} constraints, {} batched columns, \
         LogUp M = {m} messages of width at most {w}; FRI rate 2^-{}, {} queries, grinding: \
         query {}, commit {}, batch {}, out-of-domain {}, lookup {}",
        insts.len(),
        insts.iter().map(|i| i.num_constraints).sum::<usize>(),
        insts.iter().map(|i| i.batched).sum::<usize>(),
        s.fri.log_blowup,
        s.fri.num_queries,
        s.fri.query_pow_bits,
        s.fri.commit_pow_bits,
        s.grinding.batch_combination,
        s.grinding.out_of_domain,
        s.grinding.lookup_challenge,
    );
    if s.openings.is_zk() {
        println!("  {}", margin_text(s.degree_bits, s.fri.num_queries).1);
    }
    let regimes = evaluate(&insts, s, &s.fri, &s.grinding);
    for (title, rounds) in &regimes {
        let (bind, bits) = weakest(rounds);
        println!("  {title}: {bits:.1} bits, bound by {bind}");
        for (label, b) in rounds {
            println!("    {label:<34} {b:>7.1}");
        }
    }
    for target in [100.0, 128.0] {
        println!("  to reach {target} bits (\"+n\": grinding bits over the present setting):");
        // Conjectured: grinding at the current FRI parameters.
        let conj = &regimes.last().unwrap().1;
        println!("    conjectured, these FRI parameters: {}", grinding_needed(conj, target));
        // Proven: the fewest queries at each rate whose proven low-degree
        // test reaches the target, then the grinding the other rounds need.
        for lb in 1..=3usize {
            let mut found = None;
            // Query grinding and commit grinding stay at their present
            // settings; a higher rate than the present one always fits the quotient.
            for q in 1..=1000usize {
                let fri = FriRegime { log_blowup: lb, num_queries: q, ..s.fri };
                let ev = evaluate(&insts, s, &fri, &s.grinding);
                let best = ev[..ev.len() - 1]
                    .iter()
                    .max_by(|a, b| {
                        let fa = a.1.iter().find(|r| r.0 == "low-degree-test").map_or(0.0, |r| r.1);
                        let fb = b.1.iter().find(|r| r.0 == "low-degree-test").map_or(0.0, |r| r.1);
                        fa.partial_cmp(&fb).unwrap()
                    })
                    .unwrap();
                let ldt = best.1.iter().find(|r| r.0 == "low-degree-test").map_or(0.0, |r| r.1);
                if ldt >= target {
                    found = Some((q, best.0.clone(), best.1.clone()));
                    break;
                }
            }
            match found {
                Some((q, title, rounds)) => println!(
                    "    proven, rate 2^-{lb}: {q} queries ({title}; query grinding {}, commit {}), then {}",
                    s.fri.query_pow_bits,
                    s.fri.commit_pow_bits,
                    grinding_needed(&rounds, target)
                ),
                None => println!("    proven, rate 2^-{lb}: the low-degree test stays below {target} bits within 1000 queries"),
            }
        }
    }
}

/// After a successful verification under `ski-air fs-budget …`, print the
/// proof's per-round budget.  Both configurations build their FRI
/// parameters with `crate::fri_params`; the out-of-domain and
/// lookup grinding are read from the configuration.
/// **The masking margin** (`masks_hide`, `Ski/ZK/MaskOOD.lean`): a table
/// of `n` rows, masked by `n` random rows, hides its openings when
/// `|S| + 4 |Z| <= n`, `S` the base-field points of the view and `Z` the two
/// out-of-domain points, four coordinates each.  A query opens each
/// column at one point, so the column openings need `q + 8`.  The quotient
/// needs more: its chunks are committed at the committed trace's height, so a
/// query opens them at the trace's point `x`, where they recombine to a
/// function of the trace at `x` and at its next row `g x`
/// (`pcsCloseN_quot`, `Ski/ZK/MaskQuot.lean`): two points a query,
/// `2q + 8`.  Plonky3's `HidingFriPcs` asks `2 (queries + 4 · opening
/// points)`.  Under hiding a table's degree bits count its rows and as
/// many random rows: the trace has half.  Whether the smallest table meets
/// all three, and the line saying so.
pub(crate) fn margin_text(degree_bits: &[usize], queries: usize) -> (bool, String) {
    let columns = queries + 4 * 2;
    let quotient = 2 * queries + 4 * 2;
    let p3 = 2 * (queries + 4 * 2);
    let min_log = degree_bits.iter().copied().min().unwrap_or(1).saturating_sub(1);
    let n = 1usize << min_log;
    let need = columns.max(quotient).max(p3);
    if n >= need {
        (true, format!(
            "masking margin met: the smallest table 2^{min_log} = {n} rows; the column openings need {columns}, \
             the quotient's {quotient}, HidingFriPcs {p3}; {} to spare",
            n - need
        ))
    } else {
        (false, format!(
            "masking margin NOT MET: the smallest table 2^{min_log} = {n} rows; the column openings need {columns}, \
             the quotient's {quotient}, HidingFriPcs {p3}"
        ))
    }
}

/// `ski-air mask-margin PROOF...`: the masking margin of hiding proofs,
/// from their tables' heights alone, which each verifier pins to its
/// statement's.  Fails if any proof misses it.
pub fn mask_margin(paths: &[String]) -> Result<(), String> {
    let queries = crate::fri_params(()).num_queries;
    let mut ok = true;
    for path in paths {
        let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
        let (proof, _): (p3_batch_stark::BatchProof<crate::sudoku::ZkConfig>, &[u8]) =
            postcard::take_from_bytes(&bytes).map_err(|e| format!("{path}: deserialize: {e}"))?;
        let (met, line) = margin_text(&proof.degree_bits, queries);
        println!("{path}: {line}");
        ok &= met;
    }
    if ok { Ok(()) } else { Err("a proof misses the masking margin".into()) }
}

macro_rules! budget {
    ($name:expr, $airs:expr, $proof:expr, $common:expr, $config:expr, $openings:expr) => {
        if crate::fs_budget_on() {
            use p3_batch_stark::StarkGenericConfig as _;
            let common = $common;
            let n = $airs.len();
            let pre: Vec<usize> = (0..n)
                .map(|i| {
                    common
                        .preprocessed
                        .as_ref()
                        .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                        .unwrap_or(0)
                })
                .collect();
            let lk: Vec<&[p3_lookup::Lookup<crate::Val>]> = common.lookups.iter().map(|l| l.as_ref()).collect();
            let fri = crate::fri_params(());
            let mut g = fri.grinding_sites();
            g.out_of_domain = $config.ood_proof_of_work_bits();
            g.lookup_challenge = $config.lookup_proof_of_work_bits();
            crate::fsbudget::EMITTED.store(true, std::sync::atomic::Ordering::Relaxed);
            crate::fsbudget::report(
                $name,
                $airs,
                &crate::fsbudget::BatchShape {
                    degree_bits: &$proof.degree_bits,
                    lookups: &lk,
                    preprocessed_widths: &pre,
                    openings: $openings,
                    fri: fri.security_regime(),
                    grinding: g,
                    // A digest of eight BabyBear elements: 8 log2 p ≈ 247 bits.
                    collision_bits: 123,
                },
            );
        }
    };
}
pub(crate) use budget;

#[cfg(test)]
mod margin_tests {
    use super::margin_text;

    /// At 100 queries the bound is HidingFriPcs's 216 rows: 2^8 meets it,
    /// 2^7 does not; the degree bits count the random rows too.  At 203
    /// queries it is 422, which 2^9 meets.
    #[test]
    fn the_margin_is_the_smallest_tables() {
        assert!(margin_text(&[12, 9, 11], 100).0);
        assert!(!margin_text(&[12, 8, 11], 100).0);
        assert!(margin_text(&[10], 100).1.contains("296 to spare"));
        assert!(margin_text(&[10], 203).0);
        assert!(margin_text(&[10], 248).0);
        assert!(!margin_text(&[10], 249).0);
    }
}
