//! The circuit, exported symbolically, for Lean to compare with its own
//! (`Ski/Circuit/`).
//!
//! Plonky3's `InteractionSymbolicBuilder` runs an AIR's `eval` once over
//! symbolic columns and records every constraint and every bus interaction
//! it emits.  This prints them, with the preprocessed tables, in a text
//! format `lake exe circuit compare` reads: so what Lean proves about is
//! checked to be what the verifier runs.
//!
//! **The format.**  One AIR after another: `air NAME`, `width W pre P`,
//! `constraints N` and `N` lines, one expression each; `interactions M` and
//! `M` lines `BUS WEIGHT COUNT ; FIELD ; FIELD …`; `pretrace R` and `R`
//! lines of `P` numbers.  An expression is in prefix form over the tokens
//! `+ - * n` (add, subtract, multiply, negate), `m<o>.<i>` (main column
//! `i` at row offset `o`), `p<o>.<i>` (preprocessed), `F`, `L`, `T` (the
//! first-row, last-row and transition selectors) and `c<v>` (a constant,
//! canonical).

use super::*;
use p3_air::symbolic::{BaseEntry, BaseLeaf, SymbolicExpr, SymbolicExpression};
use p3_air::AirLayout;
use p3_field::PrimeField32;
use p3_lookup::symbolic::InteractionSymbolicBuilder;

fn expr(e: &SymbolicExpression<Val>, out: &mut String) {
    match e {
        SymbolicExpr::Leaf(l) => match l {
            BaseLeaf::Variable(v) => match v.entry {
                BaseEntry::Main { offset } => out.push_str(&format!("m{offset}.{} ", v.index)),
                BaseEntry::Preprocessed { offset } => out.push_str(&format!("p{offset}.{} ", v.index)),
                other => panic!("an unexpected variable {other:?}"),
            },
            BaseLeaf::IsFirstRow => out.push_str("F "),
            BaseLeaf::IsLastRow => out.push_str("L "),
            BaseLeaf::IsTransition => out.push_str("T "),
            BaseLeaf::Constant(c) => out.push_str(&format!("c{} ", c.as_canonical_u32())),
        },
        SymbolicExpr::Add { x, y, .. } => {
            out.push_str("+ ");
            expr(x, out);
            expr(y, out);
        }
        SymbolicExpr::Sub { x, y, .. } => {
            out.push_str("- ");
            expr(x, out);
            expr(y, out);
        }
        SymbolicExpr::Mul { x, y, .. } => {
            out.push_str("* ");
            expr(x, out);
            expr(y, out);
        }
        SymbolicExpr::Neg { x, .. } => {
            out.push_str("n ");
            expr(x, out);
        }
    }
}

fn one(e: &SymbolicExpression<Val>) -> String {
    let mut s = String::new();
    expr(e, &mut s);
    s.trim_end().to_string()
}

/// One AIR, exported.
pub fn export_air(name: &str, air: &SkiAir) -> String {
    let width = <SkiAir as BaseAir<Val>>::width(air);
    let pre_width = <SkiAir as BaseAir<Val>>::preprocessed_width(air);
    // The CPU's public values are the statement digest (`stmt`), which no
    // constraint reads; the Lean circuit has none.
    let layout = AirLayout {
        preprocessed_width: pre_width,
        main_width: width,
        num_public_values: <SkiAir as BaseAir<Val>>::num_public_values(air),
        ..Default::default()
    };
    let b = InteractionSymbolicBuilder::<Val, Challenge>::from_air(air, layout);
    assert!(b.local_interactions().is_empty() && b.exclusive_interactions().is_empty());
    assert!(b.indexed_reads().is_empty() && b.indexed_tables().is_empty());
    assert!(b.extension_constraints().is_empty());
    let cs = b.base_constraints();
    let is = b.global_interactions();
    let mut s = format!("air {name}\nwidth {width} pre {pre_width}\nconstraints {}\n", cs.len());
    for c in &cs {
        s.push_str(&one(c));
        s.push('\n');
    }
    s.push_str(&format!("interactions {}\n", is.len()));
    for i in is {
        s.push_str(&format!("{} {} {}", i.bus_name, i.count_weight, one(&i.count)));
        for f in &i.fields {
            s.push_str(" ; ");
            s.push_str(&one(f));
        }
        s.push('\n');
    }
    match <SkiAir as BaseAir<Val>>::preprocessed_trace(air) {
        Some(m) => {
            let rows = m.values.len() / pre_width.max(1);
            s.push_str(&format!("pretrace {rows}\n"));
            for r in 0..rows {
                let row: Vec<String> = (0..pre_width).map(|c| m.values[r * pre_width + c].as_canonical_u32().to_string()).collect();
                s.push_str(&row.join(" "));
                s.push('\n');
            }
        }
        None => s.push_str("pretrace 0\n"),
    }
    s
}

/// A term in the corpus syntax, as `parse` reads it.
pub fn unparse(t: &Term, out: &mut String) {
    match t {
        Term::S => out.push('S'),
        Term::K => out.push('K'),
        Term::I => out.push('I'),
        Term::Atom(n) => out.push_str(&format!("X{n}")),
        Term::App(f, a) => {
            out.push('`');
            unparse(f, out);
            unparse(a, out);
        }
    }
}

/// The corpus circuit's three AIRs for a term, in the export format.
pub fn export_airs(t: &Term, airs: &[SkiAir]) -> String {
    let mut term = String::new();
    unparse(t, &mut term);
    let names = ["cpu", "mem", "prog"];
    let mut s = format!("term {term}\n");
    for (n, a) in names.iter().zip(airs.iter()) {
        s.push_str(&export_air(n, a));
    }
    s
}

/// `ski-air export-base TERM`: the corpus circuit's three AIRs for a term,
/// as the verifier builds them (`verifier_airs`).
pub fn export_base(term: &str) -> String {
    let t = parse(term.as_bytes(), &mut 0);
    export_airs(&t, &verifier_airs(&t))
}
