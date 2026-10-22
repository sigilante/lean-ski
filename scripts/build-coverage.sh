#!/usr/bin/env bash
# Build the coverage project one module at a time.  Each module is a
# kernel check of one suite; built in parallel their memory adds up past a
# CI runner's, built in sequence each holds only its own.  The audit, which
# imports them all, comes last.
#
# With --ci, skip the heavy modules (those SkiCoverage/AuditHeavy.lean
# imports, which peak at 6.7 to 13 GiB) and their audit, and build the rest
# and SkiCoverage.Audit, for a machine with less than about 14 GiB.
# Without it, build everything, as CI does; run it locally before pushing
# a change to the generated coverage files.
set -euo pipefail
ci=0
if [ "${1:-}" = "--ci" ]; then ci=1; fi
cd "$(dirname "$0")/../coverage"
heavy=$(grep '^import SkiCoverage\.' SkiCoverage/AuditHeavy.lean | sed 's/^import //')
lake build Ski
for m in $(grep '^import SkiCoverage\.' SkiCoverage.lean | sed 's/^import //' \
             | grep -v -e '^SkiCoverage.Audit$' -e '^SkiCoverage.AuditHeavy$'); do
  if [ $ci -eq 1 ] && printf '%s\n' $heavy | grep -qx "$m"; then
    echo "== $m: skipped (heavy; built locally)"
    continue
  fi
  echo "== $m"
  lake build "$m"
done
if [ $ci -eq 1 ]; then
  lake build SkiCoverage.Audit
else
  lake build
fi
