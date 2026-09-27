#!/usr/bin/env bash
# Build the coverage project one module at a time.  Each module is a
# kernel check of one suite; built in parallel their memory adds up past a
# CI runner's, built in sequence each holds only its own.  The audit, which
# imports them all, comes last.
set -euo pipefail
cd "$(dirname "$0")/../coverage"
lake build Ski
for m in $(grep '^import SkiCoverage\.' SkiCoverage.lean | sed 's/^import //' | grep -v '^SkiCoverage.Audit$'); do
  echo "== $m"
  lake build "$m"
done
lake build
