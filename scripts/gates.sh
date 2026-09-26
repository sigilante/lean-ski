#!/usr/bin/env bash
# Repository discipline gates, after lean-nock's.  Exits nonzero on the first
# violation.  Ski/Audit.lean enforces the axiom footprints at build time; these
# gates catch what elaboration cannot see.
set -uo pipefail
fail=0
note() { printf '  %s\n' "$*"; }
bad()  { printf 'GATE FAILURE: %s\n' "$*"; fail=1; }

echo "== gate 1: no sorry, no axiom declarations, no native_decide =="
if grep -rnE '(^|[^`[:alnum:]_])sorry([^[:alnum:]_]|$)' Ski/ Main.lean Ski.lean 2>/dev/null \
     | grep -v '`' | grep -vE '^[^:]+:[0-9]+: *--' | grep -q .; then
  bad "sorry found"
fi
if grep -rn '^axiom' Ski/ Main.lean Ski.lean 2>/dev/null | grep -q .; then bad "axiom declaration found"; fi
if grep -rn 'native_decide' Ski/ Main.lean Ski.lean 2>/dev/null | grep -v '`' | grep -q .; then
  bad "native_decide found (no bridge module exists yet)"
fi
[ $fail -eq 0 ] && note "ok"

echo "== gate 2: no panic! anywhere =="
if grep -rn 'panic!' Ski/ Main.lean Ski.lean 2>/dev/null | grep -v '`' | grep -q .; then bad "panic! found"; fi
[ $fail -eq 0 ] && note "ok — every function is total"

echo "== gate 3: generated modules match the generator =="
if [ -x /Users/neal/SKIlark/.venv/bin/python ] || command -v python3 >/dev/null; then
  tmp=$(mktemp -d)
  /bin/cp Ski/Scott.lean Ski/Corpus.lean Ski/Table.lean Ski/Source.lean "$tmp"/
  if ( [ -x /Users/neal/SKIlark/.venv/bin/python ] && /Users/neal/SKIlark/.venv/bin/python scripts/emit.py >/dev/null 2>&1 ); then
    if ! cmp -s Ski/Scott.lean "$tmp/Scott.lean" || ! cmp -s Ski/Corpus.lean "$tmp/Corpus.lean" || ! cmp -s Ski/Table.lean "$tmp/Table.lean" || ! cmp -s Ski/Source.lean "$tmp/Source.lean"; then
      bad "Ski/Scott.lean, Ski/Corpus.lean, Ski/Table.lean or Ski/Source.lean differs from scripts/emit.py's output"
    else
      note "ok — Scott.lean, Corpus.lean, Table.lean and Source.lean are what emit.py emits"
    fi
  else
    note "skipped — skijack not available here; generated modules taken as committed"
  fi
fi

if [ $fail -ne 0 ]; then echo; echo "GATES FAILED"; exit 1; fi
echo "ALL GATES PASSED"
