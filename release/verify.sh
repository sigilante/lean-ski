#!/usr/bin/env bash
# Verify the release: proofs that `3 sumto` evaluates and decodes to `[6]`,
# from a clean lean-ski checkout.  Needs elan (Lean) and cargo (Rust); nothing else, and
# no part of Avon.  See release/README.md for what is verified.
#
#   1. the term in release/sumto/corpus.txt is lean-ski's corpus row
#      `sumto_us`, the compiled `3 sumto` (bench/Dump.lean prints it);
#   2. ski-air jet-verify: Lean's `lake exe jets statement` checks the jet
#      file against that term and licenses its roots (Air.rootsOKB), then
#      the proof is verified against the term and the jet file;
#   3. forgeries must be refused: the proof with one byte changed, the
#      proof offered for another term, the proof with a byte appended, a
#      name that is a path, and a proof that Omega halts, made over a forged
#      jet table, offered directly and through a FIFO that answers Lean's
#      read and the verifier's differently;
#   4. Lean's own check of Avon's witness table (Air.checkJA_sound);
#   5. the output: ski-air probe-verify checks the probe proof against the
#      term, the jet file and Lean's plan of `[6]`; offered for `[5]` or for
#      the error outcome, or with one byte changed, it is refused; the
#      halting proof offered as a probe proof is refused; Lean's
#      `jets check-probe` accepts the probe table for `[6]` alone
#      (Air.checkPA_decodes).
#
# Exits nonzero on any failure.

set -euo pipefail
cd "$(dirname "$0")/.."
R=release/sumto
tmp=$(mktemp -d)
trap '/bin/rm -rf "$tmp"' EXIT
failed=0
ok() { printf 'ok   %s\n' "$*"; }
# With VERIFY_ALL=1 every check runs and the exit comes at the end.
no() { printf 'FAIL %s\n' "$*"; failed=1; [ -n "${VERIFY_ALL:-}" ] || exit 1; }

echo "--- building the Lean checkers and the verifier (first run: minutes)"
lake build jets > /dev/null
(cd bench/plonky3 && cargo build --release --locked --quiet)
SKI_AIR=${SKI_AIR:-bench/plonky3/target/release/ski-air}

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

/bin/cp "$R/sumto_us.proof" "$tmp/longer.proof"
printf 'x' >> "$tmp/longer.proof"
if "$SKI_AIR" jet-verify "$R/corpus.txt" "$R/jets" sumto_us "$tmp/longer.proof" > "$tmp/longer.log"; then
    no "the proof with a byte appended verified"
else
    ok "the proof with a byte appended is refused ($(head -c 70 "$tmp/longer.log"))"
fi
# A name that is a path would let Lean's check and the verifier's reader
# open different files; names are identifiers, on both sides.  The honest
# jet file sits where each side would look (DIR/<path>.jets for Lean,
# <path>.jets for the reader), so only the name check can refuse this.
abs="$tmp/abs/sumto_us"
mkdir -p "$(dirname "$abs")" "$tmp/jd$(dirname "$abs")"
/bin/cp "$R/jets/sumto_us.jets" "$abs.jets"
/bin/cp "$R/jets/sumto_us.jets" "$tmp/jd$abs.jets"
sed "s#^sumto_us #$abs #" "$R/corpus.txt" > "$tmp/abs.txt"
if "$SKI_AIR" jet-verify "$tmp/abs.txt" "$tmp/jd" "$abs" "$R/sumto_us.proof" > "$tmp/abs.log"; then
    no "a name that is a path was accepted"
else
    ok "a name that is a path is refused ($(head -c 70 "$tmp/abs.log"))"
fi

# The Omega forgery (release/forgeries/omega): a proof that SII(SII), which
# diverges, halts, made over a forged jet table.  Offered with the forged
# table it is refused by Lean's statement check; offered through a FIFO
# that gives the honest table first and the forged one second, it must be
# refused too: the verifier reads each file once, and Lean checks a copy of
# those bytes.
F=release/forgeries/omega
mkdir -p "$tmp/fj"
/bin/cp "$F/forged.jets" "$tmp/fj/omega.jets"
if "$SKI_AIR" jet-verify "$F/corpus.txt" "$tmp/fj" omega "$F/omega.proof" > "$tmp/fj.log"; then
    no "the Omega forgery verified with its forged jet table"
else
    ok "the Omega forgery with its forged jet table is refused ($(head -c 60 "$tmp/fj.log"))"
fi
mkdir -p "$tmp/fifo"
mkfifo "$tmp/fifo/omega.jets"
# The writer holds no output of this script, and is stopped, with the cat it
# may be blocked in (a verifier that reads once never opens the FIFO again).
( exec > /dev/null 2>&1
  cat "$F/honest.jets" > "$tmp/fifo/omega.jets"
  cat "$F/forged.jets" > "$tmp/fifo/omega.jets" ) &
writer=$!
stop_writer() {
    pkill -P "$writer" 2>/dev/null || true
    kill "$writer" 2>/dev/null || true
    wait "$writer" 2>/dev/null || true
}
if "$SKI_AIR" jet-verify "$F/corpus.txt" "$tmp/fifo" omega "$F/omega.proof" > "$tmp/fifo.log"; then
    stop_writer
    no "the Omega forgery verified through a FIFO (honest table, then forged)"
else
    stop_writer
    ok "the Omega forgery through a FIFO is refused ($(head -c 60 "$tmp/fifo.log"))"
fi

# A table's first line is the term Lean's checks read; it must be the
# corpus row's, byte for byte, or they speak of another term.
term_is_sumto() {
    head -n 1 "$1" | cmp -s - <(awk '{print $3}' "$R/corpus.txt")
}

echo "--- 4. Lean's check of Avon's witness table"
term_is_sumto "$R/sumto_us.table" \
    && ok "the witness table's term is the corpus row's" \
    || no "the witness table's term is not the corpus row's"
lake exe jets check "$R/sumto_us.table" | grep -q '^ACCEPT' \
    && ok "lake exe jets check accepts the witness table" \
    || no "lake exe jets check rejects the witness table"

echo "--- 5. the output, bound: 3 sumto decodes to [6]"
P="$R/sumto_us.probe.proof"
"$SKI_AIR" probe-verify "$R/corpus.txt" "$R/jets" sumto_us "$P" val 6 \
    && ok "the probe proof verifies: the term decodes to [6]" || no "the probe proof does not verify"
for claim in "val 5" "err" "val 6 0" "val 06"; do
    # shellcheck disable=SC2086
    if "$SKI_AIR" probe-verify "$R/corpus.txt" "$R/jets" sumto_us "$P" $claim > "$tmp/claim.log"; then
        no "the probe proof verified for the outcome $claim"
    else
        ok "the probe proof offered for $claim is refused ($(head -c 60 "$tmp/claim.log"))"
    fi
done
/bin/cp "$P" "$tmp/pflip.proof"
size=$(wc -c < "$tmp/pflip.proof")
off=$((size / 3))
byte=$(dd if="$tmp/pflip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
    | dd of="$tmp/pflip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
cmp -s "$tmp/pflip.proof" "$P" && no "the byte flip changed nothing"
if "$SKI_AIR" probe-verify "$R/corpus.txt" "$R/jets" sumto_us "$tmp/pflip.proof" val 6 > "$tmp/pflip.log"; then
    no "a probe proof with one byte changed verified"
else
    ok "a probe proof with one byte changed is refused ($(head -c 60 "$tmp/pflip.log"))"
fi
if "$SKI_AIR" probe-verify "$R/corpus.txt" "$R/jets" sumto_us "$R/sumto_us.proof" val 6 > "$tmp/halt.log"; then
    no "the halting proof verified as a probe proof"
else
    ok "the halting proof offered as a probe proof is refused ($(head -c 60 "$tmp/halt.log"))"
fi
term_is_sumto "$R/sumto_us.probe.table" \
    && ok "the probe table's term is the corpus row's" \
    || no "the probe table's term is not the corpus row's"
lake exe jets check-probe "$R/sumto_us.probe.table" val 6 | grep -q '^ACCEPT' \
    && ok "lake exe jets check-probe accepts the probe table for [6]" \
    || no "lake exe jets check-probe rejects the probe table for [6]"
if lake exe jets check-probe "$R/sumto_us.probe.table" val 5 > "$tmp/c5.log"; then
    no "lake exe jets check-probe accepts the probe table for [5]"
else
    grep -q '^REJECT' "$tmp/c5.log" \
        && ok "lake exe jets check-probe rejects the probe table for [5]" \
        || no "lake exe jets check-probe fails on the probe table for [5] without rejecting it"
fi

[ "$failed" = 0 ] || { echo "NOT VERIFIED: release/sumto"; exit 1; }
echo "VERIFIED: release/sumto"
