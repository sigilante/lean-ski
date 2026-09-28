#!/usr/bin/env bash
# Produce the release: `3 sumto`, run by Avon, proved by ski-air, checked by
# Lean.  The producer's side; release/verify.sh is the verifier's.
#
#   1. Lean: the corpus row `sumto_us` (bench/Dump.lean) and its jet table
#      (`lake exe jets emit`: the licensed roots and jets of the loaded term);
#   2. Avon: the jetted witness, `avon witness --jet-table` (AVON_DIR,
#      default ~/avon), the table of rows and memory;
#   3. Lean: `lake exe jets check` accepts Avon's table (Air.checkJA_sound);
#   4. ski-air: `jet-prove` proves Avon's table and writes the proof;
#      `jet-verify` checks it from the public files alone.
#
# Run from anywhere; writes release/sumto/.  One job at a time.

set -euo pipefail
cd "$(dirname "$0")/.."
AVON_DIR=${AVON_DIR:-$HOME/avon}
R=release/sumto
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT

echo "--- Lean: the term and its jet table"
lake build jets > /dev/null
lake env lean --run bench/Dump.lean | grep '^sumto_us ' > "$R/corpus.txt"
awk '{print $3}' "$R/corpus.txt" > "$R/sumto_us.term"
lake exe jets emit "$tmp/jets" > /dev/null
mkdir -p "$R/jets"
/bin/cp "$tmp/jets/sumto_us.jets" "$R/jets/sumto_us.jets"

echo "--- Avon: the jetted witness"
make -C "$AVON_DIR" > /dev/null
"$AVON_DIR/build/avon" witness --jet-table="$R/jets/sumto_us.jets" "$R/sumto_us.term" \
    > "$R/sumto_us.table" 2> "$tmp/avon.err"
cat "$tmp/avon.err"

echo "--- Lean: Avon's table against the AIR with instantiation rows"
lake exe jets check "$R/sumto_us.table"

echo "--- ski-air: prove Avon's table; verify the proof alone"
(cd bench/plonky3 && cargo build --release --quiet)
bench/plonky3/target/release/ski-air jet-prove "$R/sumto_us.term" "$R/jets/sumto_us.jets" \
    "$R/sumto_us.table" "$R/sumto_us.proof"
bench/plonky3/target/release/ski-air jet-verify "$R/corpus.txt" "$R/jets" sumto_us "$R/sumto_us.proof"
