#!/usr/bin/env bash
# Verify the release: a proof that `3 sumto` evaluates, from a clean
# lean-ski checkout.  Needs elan (Lean) and cargo (Rust); nothing else, and
# no part of Avon.  See release/README.md for what is verified.
#
#   1. the term in release/sumto/corpus.txt is lean-ski's corpus row
#      `sumto_us`, the compiled `3 sumto` (bench/Dump.lean prints it);
#   2. ski-air jet-verify: Lean's `lake exe jets statement` checks the jet
#      file against that term and licenses its roots (Air.rootsOKB), then
#      the proof is verified against the term and the jet file;
#   3. two forgeries must be refused: the proof with one byte changed, and
#      the proof offered for another term;
#   4. Lean's own check of Avon's witness table (Air.checkJA_sound).
#
# Exits nonzero on any failure.

set -euo pipefail
cd "$(dirname "$0")/.."
R=release/sumto
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
ok() { printf 'ok   %s\n' "$*"; }
no() { printf 'FAIL %s\n' "$*"; exit 1; }

echo "--- building the Lean checkers and the verifier (first run: minutes)"
lake build jets > /dev/null
(cd bench/plonky3 && cargo build --release --quiet)
SKI_AIR=bench/plonky3/target/release/ski-air

echo "--- 1. the term is lean-ski's 3 sumto"
lake env lean --run bench/Dump.lean > "$tmp/corpus.txt"
grep '^sumto_us ' "$tmp/corpus.txt" | cmp -s - "$R/corpus.txt" \
    && ok "release/sumto/corpus.txt is the corpus row sumto_us" \
    || no "release/sumto/corpus.txt is not the corpus row sumto_us"

echo "--- 2. the proof"
"$SKI_AIR" jet-verify "$R/corpus.txt" "$R/jets" sumto_us "$R/sumto_us.proof" \
    && ok "the proof verifies" || no "the proof does not verify"

echo "--- 3. forgeries are refused"
/bin/cp "$R/sumto_us.proof" "$tmp/flipped.proof"
size=$(wc -c < "$tmp/flipped.proof")
off=$((size / 2))
byte=$(dd if="$tmp/flipped.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
    | dd of="$tmp/flipped.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
cmp -s "$tmp/flipped.proof" "$R/sumto_us.proof" && no "the byte flip changed nothing"
if "$SKI_AIR" jet-verify "$R/corpus.txt" "$R/jets" sumto_us "$tmp/flipped.proof" > "$tmp/flip.log"; then
    no "a proof with one byte changed verified"
else
    ok "a proof with one byte changed is refused ($(head -c 70 "$tmp/flip.log"))"
fi
grep '^compiled_up ' "$tmp/corpus.txt" > "$tmp/other.txt"
lake exe jets emit "$tmp/jets" > /dev/null
if "$SKI_AIR" jet-verify "$tmp/other.txt" "$tmp/jets" compiled_up "$R/sumto_us.proof" > "$tmp/other.log"; then
    no "the proof verified for another term"
else
    ok "the proof offered for another term is refused ($(head -c 70 "$tmp/other.log"))"
fi

echo "--- 4. Lean's check of Avon's witness table"
lake exe jets check "$R/sumto_us.table" | grep -q '^ACCEPT' \
    && ok "lake exe jets check accepts the witness table" \
    || no "lake exe jets check rejects the witness table"

echo "VERIFIED: release/sumto"
