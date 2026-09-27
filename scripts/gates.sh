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

echo "== gate 2: no panic! anywhere =="
if grep -rn 'panic!' $SRC 2>/dev/null | grep -v '`' | grep -q .; then bad "panic! found"; fi
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

if [ $fail -ne 0 ]; then echo; echo "GATES FAILED"; exit 1; fi
echo "ALL GATES PASSED"
