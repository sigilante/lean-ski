#!/usr/bin/env bash
# Repository discipline gates, after lean-nock's.  Exits nonzero on the first
# violation.  Ski/Audit.lean enforces the axiom footprints at build time; these
# gates catch what elaboration cannot see.
set -uo pipefail
fail=0
note() { printf '  %s\n' "$*"; }
bad()  { printf 'GATE FAILURE: %s\n' "$*"; fail=1; }

# Every Lean source in the three projects: the core, coverage/ and zk/.
SRC="Ski/ Main.lean Ski.lean coverage/SkiCoverage coverage/SkiCoverage.lean zk/SkiZk zk/SkiZk.lean"

echo "== gate 1: no sorry, no axiom declarations, no native_decide =="
if grep -rnE '(^|[^`[:alnum:]_])sorry([^[:alnum:]_]|$)' $SRC 2>/dev/null \
     | grep -v '`' | grep -vE '^[^:]+:[0-9]+: *--' | grep -q .; then
  bad "sorry found"
fi
if grep -rn '^axiom' $SRC 2>/dev/null | grep -q .; then bad "axiom declaration found"; fi
if grep -rn 'native_decide' $SRC 2>/dev/null | grep -v '`' | grep -q .; then
  bad "native_decide found (no bridge module exists yet)"
fi
[ $fail -eq 0 ] && note "ok"

echo "== gate 2: no panic!, no partial def =="
if grep -rn 'panic!' $SRC 2>/dev/null | grep -v '`' | grep -q .; then bad "panic! found"; fi
if grep -rnE '^[[:space:]]*(private |protected )?partial def' $SRC 2>/dev/null | grep -q .; then
  bad "partial def found"
fi
[ $fail -eq 0 ] && note "ok — every function is total"

echo "== gate 3: generated modules match the generator =="
# The generated set: four core modules and the coverage project's sources.
# The generator runs into a scratch copy of the tree's generated files;
# the committed files are compared against its output and always restored,
# so a gate never rewrites the tree.
gen_core="Ski/Scott.lean Ski/Corpus.lean Ski/Table.lean Ski/Source.lean"
if [ -x /Users/neal/SKIlark/.venv/bin/python ]; then
  tmp=$(mktemp -d)
  mkdir -p "$tmp/committed/Ski" "$tmp/committed/coverage"
  for f in $gen_core; do /bin/cp "$f" "$tmp/committed/$f"; done
  /bin/cp -R coverage/SkiCoverage coverage/SkiCoverage.lean "$tmp/committed/coverage/"
  if /Users/neal/SKIlark/.venv/bin/python scripts/emit.py >/dev/null 2>&1; then
    mkdir -p "$tmp/emitted/Ski" "$tmp/emitted/coverage"
    for f in $gen_core; do /bin/cp "$f" "$tmp/emitted/$f"; done
    /bin/cp -R coverage/SkiCoverage coverage/SkiCoverage.lean "$tmp/emitted/coverage/"
    if diff -r -q "$tmp/committed" "$tmp/emitted" >/dev/null; then
      note "ok — Scott, Corpus, Table, Source and the coverage project are what emit.py emits"
    else
      diff -r -q "$tmp/committed" "$tmp/emitted" | sed 's/^/  /'
      bad "generated modules differ from scripts/emit.py's output"
    fi
  else
    bad "scripts/emit.py failed"
  fi
  # restore the committed files exactly
  for f in $gen_core; do /bin/cp "$tmp/committed/$f" "$f"; done
  /bin/rm -rf coverage/SkiCoverage
  /bin/cp -R "$tmp/committed/coverage/SkiCoverage" coverage/
  /bin/cp "$tmp/committed/coverage/SkiCoverage.lean" coverage/SkiCoverage.lean
  /bin/rm -rf "$tmp"
else
  note "skipped — skijack not available here; generated modules taken as committed"
fi

echo "== gate 4: every jetted corpus table passes the jet checker =="
# lake exe jetcost runs each corpus term jetted at the licensed roots and
# checks the table with Air.checkJA; it exits nonzero on any rejection or
# a value whose head and arity differ from the plain run's.
if lake exe jetcost >/dev/null 2>&1; then
  note "ok — Air.checkJA accepts every jetted corpus table"
else
  bad "lake exe jetcost failed"
fi

echo "== gate 5: the Rust corpus circuit is the Lean circuit =="
# ski-air export-base prints the three AIRs the verifier builds for a term,
# as Plonky3's symbolic builder records them; lake exe circuit compare checks
# they have the normal forms of Circuit.baseAirs, the hypothesis of
# Circuit.export_sound and Circuit.export_complete.  A doctored export must
# be refused.
ski=bench/plonky3/target/release/ski-air
if command -v cargo >/dev/null 2>&1 \
   && (cd bench/plonky3 && cargo build --release >/dev/null 2>&1) \
   && lake build circuit >/dev/null 2>&1; then
  exp=$(mktemp)
  for f in skks ik sumto_us; do
    t=$(head -1 "bench/plonky3/tables/$f.txt")
    if "$ski" export-base "$t" > "$exp" && .lake/build/bin/circuit compare "$exp" | tail -1 | grep -q '^MATCH'; then
      note "ok — $f: the Rust circuit is Circuit.baseAirs"
    else
      bad "$f: the Rust circuit differs from Circuit.baseAirs"
    fi
  done
  for f in or and; do
    if "$ski" export-composed "release/composed/$f/public.txt" > "$exp.c" \
       && .lake/build/bin/circuit compare-composed "$exp.c" | tail -1 | grep -q '^MATCH'; then
      note "ok — composed $f: the Rust circuit is Circuit.compAirs"
    else
      bad "composed $f: the Rust circuit differs from Circuit.compAirs"
    fi
  done
  for f in neg sat; do
    if "$ski" export-witness "bench/plonky3/witness/$f/public.txt" > "$exp.c" \
       && .lake/build/bin/circuit compare-witness "$exp.c" | tail -1 | grep -q '^MATCH'; then
      note "ok — witness $f: the Rust circuit is Circuit.witAirs"
    else
      bad "witness $f: the Rust circuit differs from Circuit.witAirs"
    fi
  done
  if "$ski" export-sudoku "bench/plonky3/sudoku/public.txt" > "$exp.c" \
     && .lake/build/bin/circuit compare-sudoku "$exp.c" | tail -1 | grep -q '^MATCH'; then
    note "ok — sudoku: the Rust circuit is Circuit.sudAirs"
  else
    bad "sudoku: the Rust circuit differs from Circuit.sudAirs"
  fi
  if "$ski" export-jets "$(cat release/sumto/sumto_us.term)" release/sumto/jets/sumto_us.jets > "$exp.c" \
     && .lake/build/bin/circuit compare-jets "$exp.c" | tail -1 | grep -q '^MATCH'; then
    note "ok — jets sumto_us: the Rust circuit is Circuit.jetAirs"
  else
    bad "jets sumto_us: the Rust circuit differs from Circuit.jetAirs"
  fi
  if "$ski" export-probe "$(cat release/sumto/sumto_us.term)" release/sumto/jets/sumto_us.jets val 6 > "$exp.p" \
     && .lake/build/bin/circuit compare-probe "$exp.p" | tail -1 | grep -q '^MATCH'; then
    note "ok — probes sumto_us: the Rust circuit is Circuit.probeAirs"
  else
    bad "probes sumto_us: the Rust circuit differs from Circuit.probeAirs"
  fi
  # another outcome's plan: the circuit must differ
  sed 's/^outcome val 6$/outcome val 5/' "$exp.p" > "$exp.pbad"
  if .lake/build/bin/circuit compare-probe "$exp.pbad" | tail -1 | grep -q '^MATCH'; then
    bad "another outcome's plan was accepted"
  else
    note "ok — another outcome's plan is refused"
  fi
  /bin/rm -f "$exp.p" "$exp.pbad"
  # doctor one template row's tag: the jet table must differ
  awk '/^air tmpl/ { t = 1 } t && /^pretrace/ { p = 1; print; next } p && !d { $3 = $3 + 1; d = 1 } { print }' \
    "$exp.c" > "$exp.cbad"
  if .lake/build/bin/circuit compare-jets "$exp.cbad" | tail -1 | grep -q '^MATCH'; then
    bad "a doctored jet table was accepted"
  else
    note "ok — a doctored jet table is refused"
  fi
  /bin/rm -f "$exp.c" "$exp.cbad"
  # doctor one constant in the CPU's constraints: it must differ
  awk '!d && / c1$/ { sub(/ c1$/, " c2"); d = 1 } { print }' "$exp" > "$exp.bad"
  if .lake/build/bin/circuit compare "$exp.bad" | tail -1 | grep -q '^MATCH'; then
    bad "a doctored export was accepted"
  else
    note "ok — a doctored export is refused"
  fi
  /bin/rm -f "$exp" "$exp.bad"
else
  note "skipped — cargo or the circuit exe unavailable"
fi

if [ $fail -ne 0 ]; then echo; echo "GATES FAILED"; exit 1; fi
echo "ALL GATES PASSED"
