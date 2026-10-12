#!/usr/bin/env bash
# Verify the release: proofs that `3 sumto` evaluates and decodes to `[6]`,
# from a clean lean-ski checkout.  Needs elan (Lean) and cargo (Rust); nothing else, and
# no part of Avon.  See release/README.md for what is verified.
#
#   1. the term in release/sumto/corpus.txt is lean-ski's corpus row
#      `sumto_us`, the compiled `3 sumto` (bench/Dump.lean prints it);
#   2. ski-air jet-verify: Lean's `lake exe jets statement` checks the jet
#      file against that term and licenses its roots (Air.rootsOKB), Lean's
#      `lake exe circuit compare-jets` checks that the AIRs it verifies with
#      are Circuit.jetAirs (so Circuit.jetExport_sound applies), then the
#      proof is verified against the term and the jet file;
#   3. forgeries must be refused: the proof with one byte changed, the
#      proof offered for another term, the proof with a byte appended, a
#      name that is a path, and a proof that Omega halts, made over a forged
#      jet table, offered directly and through a FIFO that answers Lean's
#      read and the verifier's differently;
#   4. Lean's own check of the witness table (Air.checkJA_sound);
#   5. the output: ski-air probe-verify checks the probe proof against the
#      term, the jet file and Lean's plan of `[6]`, its AIRs Lean's
#      Circuit.probeAirs (`compare-probe`, so Circuit.probeExport_sound
#      applies); offered for `[5]` or for
#      the error outcome, or with one byte changed, it is refused; the
#      halting proof offered as a probe proof is refused; Lean's
#      `jets check-probe` accepts the probe table for `[6]` alone
#      (Air.checkPA_decodes);
#   6. composed statements in zero knowledge (release/composed): for the ∨
#      and the ∧ of two atoms, the statement is Lean's, and ski-air
#      composed-verify checks the proof from its file; with one byte
#      changed, a byte appended, a doctored statement, or offered for the
#      other formula, it is refused; and with the digest of its statement
#      with one CPU constant changed, every AIR as given, it is refused
#      (`composed-digest-bound`): the CPU's start registers and acceptance
#      flag sit in no committed table, so the digest is what binds them;
#   7. a SKIlark predicate in zero knowledge (release/skilark/split8): Lean
#      compiles the SKIjack source of `split` and checks that the statement
#      is the predicate `vsplitB` for x = 200 over 16 literal bits (`lake
#      exe skilark statement`), and refuses it as x = 201 or x = 712; ski-air
#      composed-verify checks the proof; with one byte changed, it is
#      refused;
#   8. a committed split (release/skilark/csplit8): Lean compiles the
#      SKIjack source of `csplit` and checks that the statement is the
#      predicate `vcsplitB` for x = 200 and the knapsack commitment c that
#      commitment.txt names, over 24 literal bits, weights from seed 1
#      (`lake exe skilark cstatement`), and refuses it for c + 1; the
#      producer drew the witness, and so c, in secret; ski-air composed-verify
#      checks the proof; with one byte changed, it is refused;
#   9. a Sudoku in zero knowledge (release/sudoku): the statement is Lean's
#      of Wikipedia's puzzle (`lake exe sudoku emit`, and `lake exe sudoku
#      statement` through the verifier); ski-air sudoku-verify checks the
#      proof; with one byte changed, a byte appended, or a doctored
#      statement, it is refused;
#  10. split8 with jets, under hiding (release/skilark/split8/jets): Lean
#      checks that the statement with jets is vsplitB's for x = 200 (`lake
#      exe skilark statement`), with its budgets; ski-air compj-verify
#      checks the proof, after Lean's statement check, its check of the jet
#      table (Air.jetStmtC: the roots licensed over every filled heap) and
#      its comparison of the ten AIRs with Circuit.compJAirs.  With one byte
#      changed, offered for the plain statement, for a statement with
#      another budget, or with the jet table Lean computes without the
#      closure rule, it is refused;
#  11. csplit8 with jets (release/skilark/csplit8/jets), the same; about
#      8 s.  QUICK=1 skips it;
#  12. the Poseidon2 jet (release/p2): the statements are Lean's (`lake exe
#      composed emit-p2`; the hand-off's, which commit to a fresh secret
#      value with fresh randomness, by `check-handoff`); ski-air
#      compp-verify checks the
#      proof of `p2pre h`, and refuses it with one byte changed, a byte
#      appended, a doctored statement, for Lean's statement of another `h`
#      at the same heights, or for another statement; the hidden
#      hand-off's two proofs over one commitment verify as a chain
#      (`compp-chain`, Circuit.p2commit_chainB), and the chain is refused
#      with the proofs swapped, paired with `p2pre`, or through FIFOs that
#      give Lean's check one statement and the verifier another.
#  13. a poke whose event is an entropy reply, its bits private
#      (release/entropy): Lean compiles the kernel and the checks from
#      source.ski and checks each statement (`lake exe entropy statement`,
#      Circuit.entropyExport_sound): some 128 literal bits, given to the
#      kernel as the reply [0 [0 bits]], make `bootok` (and `firstset`)
#      accept the poke; each statement is refused read as the other's;
#      ski-air composed-verify checks both proofs, and refuses each with a
#      byte changed and each offered for the other's statement; and
#      `composed-digest-bound` refuses bootok's with the digest of its
#      statement with a CPU constant changed.
#  14. the masking margin (`ski-air mask-margin`): every zero-knowledge
#      proof's smallest table has the random rows `masks_hide` needs,
#      |S| + 4|Z| <= n, and Plonky3's HidingFriPcs's 2 (queries + 8).
#
# Each refusal must give its expected reason (`refused`): a proof refused
# by the statement check where the proof check should refuse it fails.
#
# Exits nonzero on any failure.

set -euo pipefail
cd "$(dirname "$0")/.."
R=release/sumto
tmp=$(mktemp -d)
# FIFO writers (the subshells below), stopped on every exit: each is frozen
# first, so it cannot start its next cat, then its cat and itself killed.
writers=""
stop_writers() {
    for w in $writers; do
        kill -STOP "$w" 2>/dev/null || true
        pkill -P "$w" 2>/dev/null || true
        kill -KILL "$w" 2>/dev/null || true
        wait "$w" 2>/dev/null || true
    done
    writers=""
}
trap 'stop_writers; /bin/rm -rf "$tmp"' EXIT
trap 'exit 130' INT TERM
failed=0
ok() { printf 'ok   %s\n' "$*"; }
# With VERIFY_ALL=1 every check runs and the exit comes at the end.
no() { printf 'FAIL %s\n' "$*"; failed=1; [ -n "${VERIFY_ALL:-}" ] || exit 1; }
# A refusal for its reason: the command failed, and its log must match the
# pattern (grep -E), so a forgery refused by the wrong check does not pass.
# A changed byte may also leave a proof that parses with bytes after it,
# which the changed-byte checks accept as the reason too.
refused() {   # LOG PATTERN WHAT
    local why
    why=$(grep -E -m 1 -e "$2" "$1" | head -c 70 || true)
    if [ -n "$why" ]; then
        ok "$3 ($why)"
    else
        no "$3, but not for the expected reason ($(tail -n 1 "$1" | head -c 80))"
    fi
}

echo "--- building the Lean checkers and the verifier (first run: minutes)"
lake build jets circuit composed skilark sudoku entropy > /dev/null
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
    refused "$tmp/flip.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "a proof with one byte changed is refused"
fi
grep '^compiled_up ' "$tmp/corpus.txt" > "$tmp/other.txt"
lake exe jets emit "$tmp/jets" > /dev/null
if "$SKI_AIR" jet-verify "$tmp/other.txt" "$tmp/jets" compiled_up "$R/sumto_us.proof" > "$tmp/other.log"; then
    no "the proof verified for another term"
else
    refused "$tmp/other.log" 'heights \[' "the proof offered for another term is refused"
fi

/bin/cp "$R/sumto_us.proof" "$tmp/longer.proof"
printf 'x' >> "$tmp/longer.proof"
if "$SKI_AIR" jet-verify "$R/corpus.txt" "$R/jets" sumto_us "$tmp/longer.proof" > "$tmp/longer.log"; then
    no "the proof with a byte appended verified"
else
    refused "$tmp/longer.log" 'bytes after the proof' "the proof with a byte appended is refused"
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
    refused "$tmp/abs.log" 'a name must be an identifier' "a name that is a path is refused"
fi

# The Omega forgery (release/forgeries/omega): a proof that SII(SII), which
# diverges, halts, made over a forged jet table.  Offered with the forged
# table it is refused by Lean's statement check; offered through a FIFO
# that gives the honest table first and the forged one second, it must be
# refused too: the verifier reads each file once, and Lean checks a copy of
# those bytes.  The honest table licenses nothing (Omega's only templates
# are bare combinators, which make no jet), and ski-air refuses a table
# with no rows, so the refusal alone would not tell one read from two.
# The writer marks each table read: the honest one must be, and the
# forged one must not.
F=release/forgeries/omega
mkdir -p "$tmp/fj"
/bin/cp "$F/forged.jets" "$tmp/fj/omega.jets"
if "$SKI_AIR" jet-verify "$F/corpus.txt" "$tmp/fj" omega "$F/omega.proof" > "$tmp/fj.log"; then
    no "the Omega forgery verified with its forged jet table"
else
    refused "$tmp/fj.log" 'statement: NOT THE JET FILE' "the Omega forgery with its forged jet table is refused"
fi
mkdir -p "$tmp/fifo"
mkfifo "$tmp/fifo/omega.jets"
# The writer holds no output of this script, and is stopped, with the cat it
# may be blocked in (a verifier that reads once never opens the FIFO again).
( exec > /dev/null 2>&1
  cat "$F/honest.jets" > "$tmp/fifo/omega.jets"
  : > "$tmp/fifo.honest"
  cat "$F/forged.jets" > "$tmp/fifo/omega.jets"
  : > "$tmp/fifo.forged" ) &
writers=$!
if "$SKI_AIR" jet-verify "$F/corpus.txt" "$tmp/fifo" omega "$F/omega.proof" > "$tmp/fifo.log"; then
    stop_writers
    no "the Omega forgery verified through a FIFO (honest table, then forged)"
else
    sleep 1   # time for the writer to mark a second read, had there been one
    stop_writers
    refused "$tmp/fifo.log" 'verify: [A-Z]|deserialize: |a jet table with no rows' "the Omega forgery through a FIFO is refused"
fi
if [ -e "$tmp/fifo.honest" ] && [ ! -e "$tmp/fifo.forged" ]; then
    ok "the verifier read the FIFO once: the honest table, never the forged one"
else
    no "the verifier did not read the FIFO exactly once (honest read: $([ -e "$tmp/fifo.honest" ] && echo yes || echo no), forged read: $([ -e "$tmp/fifo.forged" ] && echo yes || echo no))"
fi

# A table's first line is the term Lean's checks read; it must be the
# corpus row's, byte for byte, or they speak of another term.
term_is_sumto() {
    head -n 1 "$1" | cmp -s - <(awk '{print $3}' "$R/corpus.txt")
}

echo "--- 4. Lean's check of the witness table"
term_is_sumto "$R/sumto_us.table" \
    && ok "the witness table's term is the corpus row's" \
    || no "the witness table's term is not the corpus row's"
lake exe jets check --row sumto_us "$R/sumto_us.table" | grep -q '^ACCEPT' \
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
        refused "$tmp/claim.log" 'verify: [A-Z]|deserialize: |plan: NO PLAN FOR' "the probe proof offered for $claim is refused"
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
    refused "$tmp/pflip.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "a probe proof with one byte changed is refused"
fi
if "$SKI_AIR" probe-verify "$R/corpus.txt" "$R/jets" sumto_us "$R/sumto_us.proof" val 6 > "$tmp/halt.log"; then
    no "the halting proof verified as a probe proof"
else
    refused "$tmp/halt.log" 'heights \[' "the halting proof offered as a probe proof is refused"
fi
term_is_sumto "$R/sumto_us.probe.table" \
    && ok "the probe table's term is the corpus row's" \
    || no "the probe table's term is not the corpus row's"
lake exe jets check-probe --row sumto_us "$R/sumto_us.probe.table" val 6 | grep -q '^ACCEPT' \
    && ok "lake exe jets check-probe accepts the probe table for [6]" \
    || no "lake exe jets check-probe rejects the probe table for [6]"
if lake exe jets check-probe --row sumto_us "$R/sumto_us.probe.table" val 5 > "$tmp/c5.log"; then
    no "lake exe jets check-probe accepts the probe table for [5]"
else
    grep -q '^REJECT' "$tmp/c5.log" \
        && ok "lake exe jets check-probe rejects the probe table for [5]" \
        || no "lake exe jets check-probe fails on the probe table for [5] without rejecting it"
fi
# A true table for another term: compiled_up also decodes to [6].  Bound to
# the row, Lean refuses it; the term check above refuses it too.
if lake exe jets check-probe --row compiled_up "$R/sumto_us.probe.table" val 6 > "$tmp/row.log"; then
    no "lake exe jets check-probe accepted the table as another row's"
else
    grep -q '^NOT THE TERM OF compiled_up' "$tmp/row.log" \
        && ok "lake exe jets check-probe refuses the table as another row's" \
        || no "lake exe jets check-probe fails on the table as another row's without refusing it"
fi

echo "--- 6. composed statements in zero knowledge: the ∨ and the ∧ of two atoms"
lake build composed > /dev/null
lake exe composed emit "$tmp/composed" > /dev/null
for n in or and; do
    C=release/composed/$n
    cmp -s "$tmp/composed/$n/public.txt" "$C/public.txt" \
        && ok "release/composed/$n/public.txt is Lean's statement of its formula" \
        || no "release/composed/$n/public.txt is not Lean's statement"
    "$SKI_AIR" composed-verify "$C/public.txt" "$C/$n.proof" > "$tmp/cv.log" \
        && ok "the $n proof verifies from its file ($(head -c 60 "$tmp/cv.log"))" \
        || no "the $n proof does not verify ($(head -c 80 "$tmp/cv.log"))"
    /bin/cp "$C/$n.proof" "$tmp/cflip.proof"
    size=$(wc -c < "$tmp/cflip.proof")
    off=$((size / 2))
    byte=$(dd if="$tmp/cflip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
        | dd of="$tmp/cflip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
    cmp -s "$tmp/cflip.proof" "$C/$n.proof" && no "the byte flip changed nothing"
    if "$SKI_AIR" composed-verify "$C/public.txt" "$tmp/cflip.proof" > "$tmp/cf.log"; then
        no "the $n proof with one byte changed verified"
    else
        refused "$tmp/cf.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the $n proof with one byte changed is refused"
    fi
    /bin/cp "$C/$n.proof" "$tmp/clong.proof"
    printf 'x' >> "$tmp/clong.proof"
    if "$SKI_AIR" composed-verify "$C/public.txt" "$tmp/clong.proof" > "$tmp/cl.log"; then
        no "the $n proof with a byte appended verified"
    else
        refused "$tmp/cl.log" 'bytes after the proof' "the $n proof with a byte appended is refused"
    fi
    # A bit cell exposed as K: the statement check refuses the doctored file.
    sed '10s/^W$/K/' "$C/public.txt" > "$tmp/cpub.txt"
    if "$SKI_AIR" composed-verify "$tmp/cpub.txt" "$C/$n.proof" > "$tmp/cp.log"; then
        no "the $n proof verified against a doctored statement"
    else
        refused "$tmp/cp.log" 'statement: NOT A STATEMENT' "the $n proof against a doctored statement is refused"
    fi
done
if "$SKI_AIR" composed-verify release/composed/and/public.txt release/composed/or/or.proof > "$tmp/cx.log"; then
    no "the ∨ proof verified for the ∧ statement"
else
    refused "$tmp/cx.log" 'verify: [A-Z]|deserialize: ' "the ∨ proof offered for the ∧ statement is refused"
fi
# The CPU's start head, stack and counter and its acceptance flag sit in no
# committed table; the statement's digest carries them.  Every AIR as given,
# the digest of the statement with one of them changed: refused.
for n in or and; do
    "$SKI_AIR" composed-digest-bound "release/composed/$n/public.txt" "release/composed/$n/$n.proof" > "$tmp/db.log" \
        && grep -q '^BOUND' "$tmp/db.log" \
        && ok "the $n proof is refused with the digest of its statement with any CPU constant changed" \
        || no "the $n proof is not bound to its CPU constants ($(tail -n 1 "$tmp/db.log" | head -c 80))"
done

echo "--- 7. a SKIlark predicate in zero knowledge: vsplitB, x = 200 over 16 literal bits"
lake build skilark > /dev/null
S=release/skilark/split8
lake exe skilark statement "$S/source.ski" 8 200 "$S/public.txt" > "$tmp/ss.log" \
    && ok "$(head -c 100 "$tmp/ss.log")" \
    || no "release/skilark/split8/public.txt is not the statement of its source ($(head -c 80 "$tmp/ss.log"))"
if lake exe skilark statement "$S/source.ski" 8 201 "$S/public.txt" > "$tmp/ss2.log"; then
    no "the statement read as x = 201"
else
    ok "the statement is not the one for x = 201 ($(head -c 60 "$tmp/ss2.log"))"
fi
if lake exe skilark statement "$S/source.ski" 8 712 "$S/public.txt" > "$tmp/ss3.log"; then
    no "the statement read as x = 712, which 8 bits cannot hold"
else
    refused "$tmp/ss3.log" 'NOT A STATEMENT: x = 712' "the statement is refused as x = 712"
fi
"$SKI_AIR" composed-verify "$S/public.txt" "$S/split8.proof" > "$tmp/sv.log" \
    && ok "the split8 proof verifies from its file" \
    || no "the split8 proof does not verify ($(head -c 80 "$tmp/sv.log"))"
/bin/cp "$S/split8.proof" "$tmp/sflip.proof"
size=$(wc -c < "$tmp/sflip.proof")
off=$((size / 2))
byte=$(dd if="$tmp/sflip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
    | dd of="$tmp/sflip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
if "$SKI_AIR" composed-verify "$S/public.txt" "$tmp/sflip.proof" > "$tmp/sf.log"; then
    no "the split8 proof with one byte changed verified"
else
    refused "$tmp/sf.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the split8 proof with one byte changed is refused"
fi

echo "--- 8. a committed split: a + b = 200, a in a toy knapsack commitment"
S=release/skilark/csplit8
C=$(cat "$S/commitment.txt")
case "$C" in ''|*[!0-9]*) no "release/skilark/csplit8/commitment.txt names no commitment"; C=0 ;; esac
lake exe skilark cstatement "$S/source.ski" 8 8 1 200 "$C" "$S/public.txt" > "$tmp/cs.log" \
    && ok "$(head -c 100 "$tmp/cs.log")" \
    || no "release/skilark/csplit8/public.txt is not the statement of its source ($(head -c 80 "$tmp/cs.log"))"
if lake exe skilark cstatement "$S/source.ski" 8 8 1 200 $((C + 1)) "$S/public.txt" > "$tmp/cs2.log"; then
    no "the statement read as c = $((C + 1))"
else
    ok "the statement is not the one for c = $((C + 1)) ($(head -c 60 "$tmp/cs2.log"))"
fi
"$SKI_AIR" composed-verify "$S/public.txt" "$S/csplit8.proof" > "$tmp/cv8.log" \
    && ok "the csplit8 proof verifies from its file" \
    || no "the csplit8 proof does not verify ($(head -c 80 "$tmp/cv8.log"))"
/bin/cp "$S/csplit8.proof" "$tmp/cflip8.proof"
size=$(wc -c < "$tmp/cflip8.proof")
off=$((size / 2))
byte=$(dd if="$tmp/cflip8.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
    | dd of="$tmp/cflip8.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
if "$SKI_AIR" composed-verify "$S/public.txt" "$tmp/cflip8.proof" > "$tmp/cf8.log"; then
    no "the csplit8 proof with one byte changed verified"
else
    refused "$tmp/cf8.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the csplit8 proof with one byte changed is refused"
fi

flip() {   # copy $1 to $2 with its middle byte changed
    /bin/cp "$1" "$2"
    local size off byte
    size=$(wc -c < "$2")
    off=$((size / 2))
    byte=$(dd if="$2" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
        | dd of="$2" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
}

echo "--- 9. a Sudoku in zero knowledge: Wikipedia's puzzle"
lake build sudoku > /dev/null
lake exe sudoku emit "$tmp/sudoku" > /dev/null
U=release/sudoku
cmp -s "$tmp/sudoku/public.txt" "$U/public.txt" \
    && ok "release/sudoku/public.txt is Lean's statement of the puzzle" \
    || no "release/sudoku/public.txt is not Lean's statement"
"$SKI_AIR" sudoku-verify "$U/public.txt" "$U/sudoku.proof" > "$tmp/uv.log" \
    && ok "the Sudoku proof verifies from its file ($(head -c 60 "$tmp/uv.log"))" \
    || no "the Sudoku proof does not verify ($(head -c 80 "$tmp/uv.log"))"
flip "$U/sudoku.proof" "$tmp/uflip.proof"
if "$SKI_AIR" sudoku-verify "$U/public.txt" "$tmp/uflip.proof" > "$tmp/uf.log"; then
    no "the Sudoku proof with one byte changed verified"
else
    refused "$tmp/uf.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the Sudoku proof with one byte changed is refused"
fi
/bin/cp "$U/sudoku.proof" "$tmp/ulong.proof"
printf '\0' >> "$tmp/ulong.proof"
if "$SKI_AIR" sudoku-verify "$U/public.txt" "$tmp/ulong.proof" > "$tmp/ul.log"; then
    no "the Sudoku proof with a byte appended verified"
else
    refused "$tmp/ul.log" 'bytes after the proof' "the Sudoku proof with a byte appended is refused"
fi
sed '$d' "$U/public.txt" > "$tmp/upub.txt"
if "$SKI_AIR" sudoku-verify "$tmp/upub.txt" "$U/sudoku.proof" > "$tmp/up.log"; then
    no "the Sudoku proof verified against a doctored statement"
else
    refused "$tmp/up.log" 'statement: NOT A STATEMENT' "the Sudoku proof against a doctored statement is refused"
fi

echo "--- 10. split8 with jets, under hiding"
S=release/skilark/split8
J=$S/jets
lake exe skilark statement "$S/source.ski" 8 200 "$J/public.txt" > "$tmp/js.log" \
    && ok "$(head -c 100 "$tmp/js.log") … $(grep -o 'budgets 2^[0-9]* and 2^[0-9]*' "$tmp/js.log")" \
    || no "release/skilark/split8/jets/public.txt is not the statement of its source ($(head -c 80 "$tmp/js.log"))"
if lake exe skilark statement "$S/source.ski" 8 201 "$J/public.txt" > "$tmp/js2.log"; then
    no "the statement with jets read as x = 201"
else
    ok "the statement with jets is not the one for x = 201"
fi
"$SKI_AIR" compj-verify "$J/public.txt" "$J/split8.jets" "$S/source.ski" "$J/split8.proof" > "$tmp/jv.log" \
    && ok "the split8 proof with jets verifies from its files ($(head -c 40 "$tmp/jv.log"))" \
    || no "the split8 proof with jets does not verify ($(head -c 80 "$tmp/jv.log"))"
flip "$J/split8.proof" "$tmp/jflip.proof"
if "$SKI_AIR" compj-verify "$J/public.txt" "$J/split8.jets" "$S/source.ski" "$tmp/jflip.proof" > "$tmp/jf.log"; then
    no "the split8 proof with jets, one byte changed, verified"
else
    refused "$tmp/jf.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the split8 proof with jets, one byte changed, is refused"
fi
if "$SKI_AIR" compj-verify "$S/public.txt" "$J/split8.jets" "$S/source.ski" "$J/split8.proof" > "$tmp/jp.log"; then
    no "the split8 proof with jets verified against the plain statement"
else
    refused "$tmp/jp.log" 'statement: NOT A STATEMENT WITH JETS' "the split8 proof with jets is refused for the plain statement"
fi
sed '3s/^log \([0-9]*\) \([0-9]*\) \([0-9]*\) /log \1 \2 15 /' "$J/public.txt" > "$tmp/jbud.txt"
if cmp -s "$tmp/jbud.txt" "$J/public.txt"; then
    no "could not change the budget of release/skilark/split8/jets/public.txt"
elif "$SKI_AIR" compj-verify "$tmp/jbud.txt" "$J/split8.jets" "$S/source.ski" "$J/split8.proof" > "$tmp/jb.log"; then
    no "the split8 proof with jets verified for another budget"
else
    refused "$tmp/jb.log" 'heights \[' "the split8 proof with jets is refused for POP's budget 2^15"
fi
lake exe skilark cjets "$S/source.ski" "$J/public.txt" "$tmp/norule.jets" --no-rule > /dev/null
if "$SKI_AIR" compj-verify "$J/public.txt" "$tmp/norule.jets" "$S/source.ski" "$J/split8.proof" > "$tmp/jn.log"; then
    no "the split8 proof with jets verified with the jet table without the closure rule"
else
    refused "$tmp/jn.log" "NOT THE STATEMENT'S JET TABLE" "the jet table without the closure rule is refused"
fi

if [ -z "${QUICK:-}" ]; then
echo "--- 11. csplit8 with jets, under hiding (about 8 s; QUICK=1 skips it)"
S=release/skilark/csplit8
J=$S/jets
C=$(cat "$J/commitment.txt")
case "$C" in ''|*[!0-9]*) no "release/skilark/csplit8/jets/commitment.txt names no commitment"; C=0 ;; esac
lake exe skilark cstatement "$S/source.ski" 8 8 1 200 "$C" "$J/public.txt" > "$tmp/jcs.log" \
    && ok "$(head -c 100 "$tmp/jcs.log") … $(grep -o 'budgets 2^[0-9]* and 2^[0-9]*' "$tmp/jcs.log")" \
    || no "release/skilark/csplit8/jets/public.txt is not the statement of its source ($(head -c 80 "$tmp/jcs.log"))"
"$SKI_AIR" compj-verify "$J/public.txt" "$J/csplit8.jets" "$S/source.ski" "$J/csplit8.proof" > "$tmp/jcv.log" \
    && ok "the csplit8 proof with jets verifies from its files ($(head -c 40 "$tmp/jcv.log"))" \
    || no "the csplit8 proof with jets does not verify ($(head -c 80 "$tmp/jcv.log"))"
flip "$J/csplit8.proof" "$tmp/jcflip.proof"
if "$SKI_AIR" compj-verify "$J/public.txt" "$J/csplit8.jets" "$S/source.ski" "$tmp/jcflip.proof" > "$tmp/jcf.log"; then
    no "the csplit8 proof with jets, one byte changed, verified"
else
    refused "$tmp/jcf.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the csplit8 proof with jets, one byte changed, is refused"
fi
else
echo "--- 11. csplit8 with jets: skipped (QUICK=1)"
fi

echo "--- 12. the Poseidon2 jet: a preimage, and a hidden hand-off over a commitment"
P=release/p2
mkdir -p "$tmp/p2"
lake exe composed emit-p2 "$tmp/p2" > /dev/null
cmp -s "$tmp/p2/p2pre.public.txt" "$P/p2pre.public.txt" \
    && ok "release/p2/p2pre.public.txt is Lean's statement" \
    || no "release/p2/p2pre.public.txt is not Lean's statement"
# The hand-off commits to a fresh, secret value with fresh randomness, so
# Lean cannot re-emit its statements; it checks that they are exactly its
# two statements for the commitment they name, with the documented
# patterns and heights.
lake exe composed check-handoff "$P/handoff1.public.txt" "$P/handoff2.public.txt" > "$tmp/hc.log" \
    && grep -q '^OK HANDOFF' "$tmp/hc.log" \
    && ok "release/p2/handoff1 and handoff2 are Lean's hand-off statements for their commitment" \
    || no "release/p2/handoff1 and handoff2 are not Lean's hand-off statements ($(tail -n 1 "$tmp/hc.log"))"
# The commitment is not the tests' fixed value and randomness's.
lake exe composed emit-handoff "$tmp/p2" > /dev/null
cmp -s "$tmp/p2/handoff1.public.txt" "$P/handoff1.public.txt" \
    && no "release/p2's hand-off commits with the fixed test randomness" \
    || ok "release/p2's hand-off does not commit with the fixed test randomness"
"$SKI_AIR" compp-verify "$P/p2pre.public.txt" "$P/p2pre.proof" > "$tmp/pv.log" \
    && ok "the p2pre proof verifies ($(head -c 60 "$tmp/pv.log"))" \
    || no "the p2pre proof does not verify ($(head -c 80 "$tmp/pv.log"))"
flip "$P/p2pre.proof" "$tmp/pflip.proof"
if "$SKI_AIR" compp-verify "$P/p2pre.public.txt" "$tmp/pflip.proof" > "$tmp/pf.log" 2>&1; then
    no "the p2pre proof with one byte changed verified"
else
    refused "$tmp/pf.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the p2pre proof with one byte changed is refused"
fi
/bin/cp "$P/p2pre.proof" "$tmp/plong.proof"
printf 'x' >> "$tmp/plong.proof"
if "$SKI_AIR" compp-verify "$P/p2pre.public.txt" "$tmp/plong.proof" > "$tmp/pl.log" 2>&1; then
    no "the p2pre proof with a byte appended verified"
else
    refused "$tmp/pl.log" 'bytes after the proof' "the p2pre proof with a byte appended is refused"
fi
# The first bit cell (line 11, address 3) exposed as K.
sed '11s/^W$/K/' "$P/p2pre.public.txt" > "$tmp/ppub.txt"
if cmp -s "$tmp/ppub.txt" "$P/p2pre.public.txt"; then
    no "could not doctor release/p2/p2pre.public.txt"
elif "$SKI_AIR" compp-verify "$tmp/ppub.txt" "$P/p2pre.proof" > "$tmp/pp.log" 2>&1; then
    no "the p2pre proof verified against a doctored statement"
else
    refused "$tmp/pp.log" 'statement: NOT A STATEMENT' "the p2pre proof against a doctored statement is refused"
fi
# A statement Lean accepts, at the same heights, for another h (test vector
# 0): neither the statement check nor the heights refuse it, so only the
# proof's binding to its statement can.
mkdir -p "$tmp/p2/other"
lake exe composed emit-p2 "$tmp/p2/other" 0 > /dev/null
if ! lake exe composed statement-p2 "$tmp/p2/other/p2pre.public.txt" | grep -q '^OK p2pre'; then
    no "Lean does not accept the p2pre statement for test vector 0"
elif [ "$(sed -n 3p "$tmp/p2/other/p2pre.public.txt")" != "$(sed -n 3p "$P/p2pre.public.txt")" ] ||
        cmp -s "$tmp/p2/other/p2pre.public.txt" "$P/p2pre.public.txt"; then
    no "the statement for test vector 0 is not another h at the same heights"
elif "$SKI_AIR" compp-verify "$tmp/p2/other/p2pre.public.txt" "$P/p2pre.proof" > "$tmp/ph.log" 2>&1; then
    no "the p2pre proof verified for another h"
else
    refused "$tmp/ph.log" 'verify: [A-Z]|deserialize: ' "the p2pre proof offered for another h, at the same heights, is refused"
fi
if "$SKI_AIR" compp-verify "$P/handoff1.public.txt" "$P/p2pre.proof" > "$tmp/po.log" 2>&1; then
    no "the p2pre proof verified for the hand-off's first statement"
else
    refused "$tmp/po.log" 'heights \[' "the p2pre proof offered for another statement is refused"
fi
"$SKI_AIR" compp-chain "$P/handoff1.public.txt" "$P/handoff1.proof" "$P/handoff2.public.txt" "$P/handoff2.proof" \
    > "$tmp/ch.log" && grep -q '^CHAIN OK' "$tmp/ch.log" \
    && ok "the hand-off's two proofs verify as a chain ($(grep '^CHAIN OK' "$tmp/ch.log" | head -c 60))" \
    || no "the hand-off does not verify as a chain ($(tail -n 1 "$tmp/ch.log" | head -c 80))"
if "$SKI_AIR" compp-chain "$P/handoff1.public.txt" "$P/handoff2.proof" "$P/handoff2.public.txt" "$P/handoff1.proof" \
    > "$tmp/chs.log" 2>&1; then
    no "the chain verified with the proofs swapped"
else
    refused "$tmp/chs.log" 'verify: [A-Z]|deserialize: ' "the chain with the proofs swapped is refused"
fi
if "$SKI_AIR" compp-chain "$P/p2pre.public.txt" "$P/p2pre.proof" "$P/handoff2.public.txt" "$P/handoff2.proof" \
    > "$tmp/chp.log" 2>&1; then
    no "a chain of p2pre and p2commit verified"
else
    refused "$tmp/chp.log" 'chain: NOT A CHAIN' "a chain paired with p2pre is refused"
fi
# FIFOs that give a hand-off statement on the first read and p2pre's on the
# second, offered with p2pre's proof twice: the verifier reads each file once
# and checks the chain and the proofs on those bytes, so it must refuse.
mkfifo "$tmp/p2/f1" "$tmp/p2/f2"
( exec > /dev/null 2>&1
  cat "$P/handoff1.public.txt" > "$tmp/p2/f1"; cat "$P/p2pre.public.txt" > "$tmp/p2/f1" ) &
writers=$!
( exec > /dev/null 2>&1
  cat "$P/handoff2.public.txt" > "$tmp/p2/f2"; cat "$P/p2pre.public.txt" > "$tmp/p2/f2" ) &
writers="$writers $!"
if "$SKI_AIR" compp-chain "$tmp/p2/f1" "$P/p2pre.proof" "$tmp/p2/f2" "$P/p2pre.proof" > "$tmp/chf.log" 2>&1; then
    stop_writers
    no "the chain verified through FIFOs (a hand-off to Lean, p2pre to the verifier)"
else
    stop_writers
    refused "$tmp/chf.log" 'heights \[' "the chain through FIFOs is refused"
fi

echo "--- 13. a poke whose event is an entropy reply, its 128 bits private"
E=release/entropy
for n in bootok firstset; do
    lake exe entropy statement "$E/source.ski" "$n" "$E/$n.public.txt" > "$tmp/es.log" 2> /dev/null \
        && ok "$(head -c 100 "$tmp/es.log")" \
        || no "release/entropy/$n.public.txt is not the $n statement of its source ($(head -c 80 "$tmp/es.log"))"
    "$SKI_AIR" composed-verify "$E/$n.public.txt" "$E/$n.proof" > "$tmp/ev.log" \
        && ok "the $n proof verifies from its file" \
        || no "the $n proof does not verify ($(head -c 80 "$tmp/ev.log"))"
done
"$SKI_AIR" composed-digest-bound "$E/bootok.public.txt" "$E/bootok.proof" > "$tmp/edb.log" \
    && grep -q '^BOUND' "$tmp/edb.log" \
    && ok "the bootok proof is refused with the digest of its statement with any CPU constant changed" \
    || no "the bootok proof is not bound to its CPU constants ($(tail -n 1 "$tmp/edb.log" | head -c 80))"
for pair in "bootok firstset" "firstset bootok"; do
    set -- $pair
    if lake exe entropy statement "$E/source.ski" "$2" "$E/$1.public.txt" > "$tmp/ex.log" 2> /dev/null; then
        no "the $1 statement read as $2's"
    else
        refused "$tmp/ex.log" 'NOT THIS STATEMENT' "the $1 statement is not $2's"
    fi
    if "$SKI_AIR" composed-verify "$E/$2.public.txt" "$E/$1.proof" > "$tmp/ex2.log"; then
        no "the $1 proof verified for the $2 statement"
    else
        refused "$tmp/ex2.log" 'verify: [A-Z]|deserialize: ' "the $1 proof offered for the $2 statement is refused"
    fi
    /bin/cp "$E/$1.proof" "$tmp/eflip.proof"
    size=$(wc -c < "$tmp/eflip.proof")
    off=$((size / 2))
    byte=$(dd if="$tmp/eflip.proof" bs=1 skip=$off count=1 2>/dev/null | od -An -tu1 | tr -d ' ')
    printf '%b' "$(printf '\\0%03o' $(( (byte + 1) % 256 )))" \
        | dd of="$tmp/eflip.proof" bs=1 seek=$off count=1 conv=notrunc 2>/dev/null
    if "$SKI_AIR" composed-verify "$E/$1.public.txt" "$tmp/eflip.proof" > "$tmp/ef.log"; then
        no "the $1 proof with one byte changed verified"
    else
        refused "$tmp/ef.log" 'verify: [A-Z]|deserialize: |bytes after the proof' "the $1 proof with one byte changed is refused"
    fi
done

echo "--- 14. the masking margin of every zero-knowledge proof"
# Random rows hide a table's openings when |S| + 4|Z| <= n (masks_hide);
# the margin reads each proof's heights, which the steps above pin to its
# statement's.
zk=$(find release/composed release/skilark release/sudoku release/p2 release/entropy -name '*.proof' | sort)
# shellcheck disable=SC2086
"$SKI_AIR" mask-margin $zk > "$tmp/mm.log" \
    && ok "every zero-knowledge proof meets the masking margin ($(grep -c 'margin met' "$tmp/mm.log") proofs; $(grep -o '[0-9]* to spare' "$tmp/mm.log" | sort -n | head -n 1) at the least)" \
    || no "a proof misses the masking margin ($(grep -m 1 'NOT MET' "$tmp/mm.log" | head -c 100))"

[ "$failed" = 0 ] || { echo "NOT VERIFIED: release"; exit 1; }
echo "VERIFIED: release/sumto, release/composed, release/skilark (with jets${QUICK:+, csplit8 skipped}), release/sudoku, release/p2 and release/entropy"
