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
#      predicate statement `x = 200` and the witness, the 16 bits of
#      `a = 123, b = 77`, at heights
#      2^17 and 2^18; ski-air composed-prove proves it.  The witness stays
#      in a temporary directory.
#   9. a committed split (release/skilark/csplit8): SKIlark's `python -m
#      skilark.zk csplit 8 8` (or the committed source); Lean emits the
#      statement x = 200 with the knapsack commitment of a = 123 and
#      r = 181 under the weights of seed 1, and the witness, the bits of
#      a, b = 77 and r, at heights 2^19 and 2^20; ski-air composed-prove
#      proves it.
#  10. a Sudoku (release/sudoku): Lean emits the statement of Wikipedia's
#      puzzle and the witness, its solution (`lake exe sudoku emit`);
#      ski-air sudoku-prove proves it in zero knowledge.  The witness stays
#      in a temporary directory.
#  11. split8 and csplit8 with jets, under hiding (release/skilark/*/jets):
#      Lean writes the statement with jets, its heights and POP's and
#      INSTW's budgets public (`lake exe composed budget`: log R M Lp Li;
#      split8 at 2^17 2^18 2^14 2^14, csplit8 at 2^18 2^19 2^17 2^17), and
#      its jet table from the source's templates (`lake exe skilark
#      cjets`, Air.jetTableC); Avon writes the witness table (`avon
#      witness --statement`, Avon's milestone 8); Lean's `composed check-cj`
#      accepts it (CompM.checkCJ_sound); ski-air compj-prove-table proves
#      Avon's table under hiding and compj-verify checks the proof.
#
# Stages: `release/produce.sh [STAGE…]` runs the named ones, of sumto,
# composed, split8, csplit8, sudoku, jets; all by default.  The proofs are
# randomized, so a stage rewrites its own and leaves the others' bytes.
# Run from anywhere; writes release/sumto/.  One job at a time.

set -euo pipefail
cd "$(dirname "$0")/.."
AVON_DIR=${AVON_DIR:-$HOME/avon}
R=release/sumto
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
STAGES=" ${*:-sumto composed split8 csplit8 sudoku jets} "
want() { case "$STAGES" in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
for st in $STAGES; do
    case " sumto composed split8 csplit8 sudoku jets " in *" $st "*) ;; *) echo "no stage $st" >&2; exit 2 ;; esac
done
(cd bench/plonky3 && cargo build --release --quiet)
A=bench/plonky3/target/release/ski-air
PY=${SKILARK_PY:-$HOME/SKIlark/.venv/bin/python}

if want sumto; then
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

fi

if want composed; then
echo "--- composed statements in zero knowledge"
lake build composed > /dev/null
lake exe composed emit "$tmp/composed" > /dev/null
for n in or and; do
    mkdir -p "release/composed/$n"
    /bin/cp "$tmp/composed/$n/public.txt" "release/composed/$n/public.txt"
    bench/plonky3/target/release/ski-air composed-prove "release/composed/$n/public.txt" \
        "$tmp/composed/$n/witness.txt" "release/composed/$n/$n.proof"
done

fi

if want split8; then
echo "--- a SKIlark predicate in zero knowledge: vsplitB, x = 200 over 16 literal bits"
S=release/skilark/split8
mkdir -p "$S"
if [ -x "$PY" ]; then
    "$PY" -m skilark.zk 8 > "$S/source.ski"
else
    echo "no SKIlark at $PY: keeping the committed $S/source.ski"
fi
lake build skilark > /dev/null
lake exe skilark emit "$S/source.ski" 8 200 123 77 17 18 "$tmp/skilark"
/bin/cp "$tmp/skilark/public.txt" "$S/public.txt"
bench/plonky3/target/release/ski-air composed-prove "$S/public.txt" "$tmp/skilark/witness.txt" "$S/split8.proof"

fi

if want csplit8; then
echo "--- a committed split in zero knowledge: a + b = 200, a in a toy knapsack commitment c = 255"
S=release/skilark/csplit8
mkdir -p "$S"
if [ -x "$PY" ]; then
    "$PY" -m skilark.zk csplit 8 8 > "$S/source.ski"
else
    echo "no SKIlark at $PY: keeping the committed $S/source.ski"
fi
lake exe skilark cemit "$S/source.ski" 8 8 1 200 123 77 181 19 20 "$tmp/csplit"
/bin/cp "$tmp/csplit/public.txt" "$S/public.txt"
bench/plonky3/target/release/ski-air composed-prove "$S/public.txt" "$tmp/csplit/witness.txt" "$S/csplit8.proof"
fi

if want sudoku; then
echo "--- a Sudoku in zero knowledge: Wikipedia's puzzle"
lake build sudoku > /dev/null
lake exe sudoku emit "$tmp/sudoku" > /dev/null
mkdir -p release/sudoku
/bin/cp "$tmp/sudoku/public.txt" release/sudoku/public.txt
"$A" sudoku-prove release/sudoku/public.txt "$tmp/sudoku/witness.txt" release/sudoku/sudoku.proof
"$A" sudoku-verify release/sudoku/public.txt release/sudoku/sudoku.proof
fi

if want jets; then
echo "--- split8 and csplit8 with jets, under hiding: Avon writes the witness, ski-air proves it"
# Avon with milestone 8 (`avon witness --statement`): AVON_DIR's checkout
make -C "$AVON_DIR" > /dev/null
lake build skilark composed > /dev/null
# name, its emit command's arguments and the plain statement's heights, the jet statement's heights and budgets
for c in "split8:emit:8 200 123 77:17 18:14 14" "csplit8:cemit:8 8 1 200 123 77 181:18 19:17 17"; do
    IFS=: read -r name cmd args lg bud <<< "$c"
    S=release/skilark/$name
    mkdir -p "$S/jets"
    # shellcheck disable=SC2086
    lake exe skilark "$cmd" "$S/source.ski" $args $lg "$tmp/$name" > /dev/null
    # shellcheck disable=SC2086
    lake exe composed budget "$tmp/$name/public.txt" $bud "$S/jets/public.txt"
    lake exe skilark cjets "$S/source.ski" "$S/jets/public.txt" "$S/jets/$name.jets" | tail -n 1
    "$AVON_DIR/build/avon" witness --statement="$S/jets/public.txt" --jet-table="$S/jets/$name.jets" \
        "$tmp/$name/witness.txt" > "$tmp/$name.table" 2> "$tmp/avon.err"
    cat "$tmp/avon.err"
    lake exe composed check-cj "$S/source.ski" "$S/jets/public.txt" "$tmp/$name.table" | grep -E '^(ACCEPT|REJECT)' | cut -c1-120
    "$A" compj-prove-table "$S/jets/public.txt" "$S/jets/$name.jets" "$S/source.ski" "$tmp/$name.table" \
        "$S/jets/$name.proof"
    "$A" compj-verify "$S/jets/public.txt" "$S/jets/$name.jets" "$S/source.ski" "$S/jets/$name.proof" | cut -c1-80
done
fi
