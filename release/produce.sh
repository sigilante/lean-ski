#!/usr/bin/env bash
# Produce the release: `3 sumto`, run by Avon, proved by ski-air, checked by
# Lean; and its output, `[6]`, bound by probe segments Avon also runs.  The producer's side;
# release/verify.sh is the verifier's.
#
#   1. Lean: the corpus row `sumto_us` (bench/Dump.lean) and its jet table
#      (`lake exe jets emit`: the licensed roots and jets of the loaded term);
#   2. Avon: the jetted witness, `avon witness --jet-table` (AVON_DIR,
#      default ~/avon), the table of rows and memory;
#   3. Lean: `lake exe jets check` accepts Avon's table (Air.checkJA_sound);
#   4. ski-air: `jet-prove` proves Avon's table and writes the proof;
#      `jet-verify` checks it from the public files alone;
#   5. the output, bound: Lean writes the plan of `[6]` (`lake exe jets plan
#      val 6`); Avon runs the term's probe segments for it (`avon witness
#      --jet-table --plan`); Lean's `jets check-probe --row sumto_us`
#      accepts Avon's table (Air.checkPA_decodes); ski-air's own probe run
#      writes the same table, byte for byte; `probe-prove-table` proves
#      Avon's table, and `probe-verify` checks the proof;
#   6. the Omega forgery (release/forgeries/omega): its hand-written table,
#      proved over the forged jet table, which Lean's check refuses;
#   7. composed statements (release/composed): Lean emits each example's
#      statement and witness; ski-air composed-prove proves it in zero
#      knowledge.  The witness stays in a temporary directory, and the
#      proofs are randomized (hiding), so they do not regenerate byte for
#      byte; any proof composed-verify accepts is as good.
#   8. a SKIlark predicate (release/skilark/split8): the SKIjack source of
#      `split` for 8 bits, from SKIlark (`python -m
#      skilark.zk 8`, SKILARK_PY, default ~/SKIlark/.venv/bin/python; the
#      committed source when it is absent); Lean compiles it and emits the
#      statement `x = 200` and the witness `a = 123, b = 77`, at heights
#      2^17 and 2^18; ski-air composed-prove proves it.  The witness stays
#      in a temporary directory.
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
lake exe jets check --row sumto_us "$R/sumto_us.table"

echo "--- ski-air: prove Avon's table; verify the proof alone"
(cd bench/plonky3 && cargo build --release --quiet)
bench/plonky3/target/release/ski-air jet-prove "$R/sumto_us.term" "$R/jets/sumto_us.jets" \
    "$R/sumto_us.table" "$R/sumto_us.proof"
bench/plonky3/target/release/ski-air jet-verify "$R/corpus.txt" "$R/jets" sumto_us "$R/sumto_us.proof"

echo "--- Lean and Avon: the output, bound: probe segments for [6]"
lake exe jets plan val 6 > "$tmp/plan.txt"
"$AVON_DIR/build/avon" witness --jet-table="$R/jets/sumto_us.jets" --plan="$tmp/plan.txt" \
    "$R/sumto_us.term" > "$R/sumto_us.probe.table" 2> "$tmp/avon.err"
cat "$tmp/avon.err"
lake exe jets check-probe --row sumto_us "$R/sumto_us.probe.table" val 6

echo "--- ski-air: its own probe run agrees with Avon's; prove Avon's table"
bench/plonky3/target/release/ski-air probe-prove "$R/sumto_us.term" "$R/jets/sumto_us.jets" \
    "$tmp/own.table" "$tmp/own.proof" val 6 > /dev/null
cmp "$tmp/own.table" "$R/sumto_us.probe.table"
bench/plonky3/target/release/ski-air probe-prove-table "$R/sumto_us.term" "$R/jets/sumto_us.jets" \
    "$R/sumto_us.probe.table" "$R/sumto_us.probe.proof" val 6
cmp "$tmp/own.proof" "$R/sumto_us.probe.proof"
bench/plonky3/target/release/ski-air probe-verify "$R/corpus.txt" "$R/jets" sumto_us \
    "$R/sumto_us.probe.proof" val 6

echo "--- the Omega forgery: a halting proof over a forged jet table"
F=release/forgeries/omega
if lake exe jets check "$F/omega.table" > /dev/null; then
    echo "Lean accepted the Omega table" >&2
    exit 1
fi
bench/plonky3/target/release/ski-air jet-prove "$F/omega.term" "$F/forged.jets" "$F/omega.table" "$F/omega.proof"

echo "--- composed statements in zero knowledge"
lake build composed > /dev/null
lake exe composed emit "$tmp/composed" > /dev/null
for n in or and; do
    mkdir -p "release/composed/$n"
    /bin/cp "$tmp/composed/$n/public.txt" "release/composed/$n/public.txt"
    bench/plonky3/target/release/ski-air composed-prove "release/composed/$n/public.txt" \
        "$tmp/composed/$n/witness.txt" "release/composed/$n/$n.proof"
done

echo "--- a SKIlark predicate in zero knowledge: vsplit, x = 200 in 8 bits"
S=release/skilark/split8
mkdir -p "$S"
PY=${SKILARK_PY:-$HOME/SKIlark/.venv/bin/python}
if [ -x "$PY" ]; then
    "$PY" -m skilark.zk 8 > "$S/source.ski"
else
    echo "no SKIlark at $PY: keeping the committed $S/source.ski"
fi
lake build skilark > /dev/null
lake exe skilark emit "$S/source.ski" 8 200 123 77 17 18 "$tmp/skilark"
/bin/cp "$tmp/skilark/public.txt" "$S/public.txt"
bench/plonky3/target/release/ski-air composed-prove "$S/public.txt" "$tmp/skilark/witness.txt" "$S/split8.proof"
