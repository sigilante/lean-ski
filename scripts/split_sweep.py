#!/usr/bin/env python3
"""Every witness of the released split predicates, run by Avon.

    scripts/split_sweep.py AVON [split8|csplit8] [--jobs N]

A run's length depends on its witness, so a statement whose heights are to
say nothing of its witness must hold the run of every one.  This runs each
witness of `release/skilark/split8` (all 65,536 pairs of 8-bit numbers; the
predicate accepts exactly the 201 with a + b = 200) or of
`release/skilark/csplit8` (the 51,456 pairs (a, r) with a in 0..200 and r
in 0..255, b = 200 - a, each under the statement of its own commitment),
plain and with jets, through `avon witness --statement`, and prints the
range of each count and the least power of two that holds it.  The heights
in release/produce.sh are those powers.

AVON is the avon binary (from the separate Avon repository).  Lean's
`skilark` executable must be built (`lake build skilark`).  On ten cores
split8 takes about 6 minutes and csplit8 about 40.
"""
import concurrent.futures as cf
import math
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SKILARK = os.path.join(ROOT, ".lake/build/bin/skilark")
WEIGHTS = [61, 13, 14, 5, 59, 34, 24, 10, 18, 50, 3, 51, 26, 6, 57, 6]   # seed 1
# Measuring heights: the circuit's caps, so no run is cut short.
PLAIN, JETS = "log 20 20 14 14", "log 20 20 18 18"


def commitment(a, r):
    return (sum(WEIGHTS[i] * (a >> i & 1) for i in range(8))
            + sum(WEIGHTS[8 + i] * (r >> i & 1) for i in range(8)))


def witness(a, b, r=None):
    bits = []
    for i in range(8):
        bits += [a >> i & 1, b >> i & 1]
    if r is not None:
        bits += [r >> i & 1 for i in range(8)]
    return "".join(f"{x}\n" for x in bits) + "S\n"


def statements(tmp, name, emit_args, src):
    """The plain and jet statements at the measuring heights, and the jet table."""
    out = os.path.join(tmp, "emit")
    subprocess.run([SKILARK, "cemit" if name == "csplit8" else "emit", src, *emit_args, "20", "20", out],
                   cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    lines = open(os.path.join(out, "public.txt")).read().split("\n")
    (i,) = [k for k, line in enumerate(lines) if line.startswith("log ")]
    paths = {}
    for kind, log in (("plain", PLAIN), ("jets", JETS)):
        lines[i] = log
        paths[kind] = os.path.join(tmp, f"{kind}.txt")
        open(paths[kind], "w").write("\n".join(lines))
    paths["jet table"] = os.path.join(tmp, "jets.jets")
    subprocess.run([SKILARK, "cjets", src, paths["jets"], paths["jet table"]],
                   cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    paths["no jets"] = os.path.join(tmp, "empty.jets")
    open(paths["no jets"], "w").write("roots 0\njets 0\n")
    return paths


def run(avon, st, wit_text, tmp, key):
    """Avon's counts of the plain and the jetted run, or None if rejected."""
    wit = os.path.join(tmp, f"w{key}.txt")
    open(wit, "w").write(wit_text)
    counts = []
    for pub, jt in ((st["plain"], st["no jets"]), (st["jets"], st["jet table"])):
        p = subprocess.run([avon, "witness", "--statement=" + pub, "--jet-table=" + jt, wit],
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        if p.returncode:
            os.remove(wit)
            if "does not satisfy" in p.stderr:
                return None
            sys.exit(f"avon: {p.stderr.strip()}")
        f = p.stderr.split("\n")[-2].split()
        counts.append({f[k]: int(f[k + 1]) for k in range(0, len(f), 2)})
    os.remove(wit)
    return counts


def main():
    if len(sys.argv) < 3 or sys.argv[2] not in ("split8", "csplit8"):
        sys.exit(__doc__)
    avon, name = os.path.abspath(sys.argv[1]), sys.argv[2]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else os.cpu_count()
    src = os.path.join(ROOT, f"release/skilark/{name}/source.ski")
    results = []
    with tempfile.TemporaryDirectory() as tmp:
        if name == "split8":
            st = statements(tmp, name, ["8", "200", "123", "77"], src)
            cases = [(a, b) for a in range(256) for b in range(256)]
            work = lambda ab: (ab, run(avon, st, witness(*ab), tmp, f"{ab[0]}_{ab[1]}"))
        else:
            rep = {}
            for a in range(201):
                for r in range(256):
                    rep.setdefault(commitment(a, r), (a, r))
            sts = {}
            for c, (a, r) in sorted(rep.items()):
                d = os.path.join(tmp, f"c{c}")
                os.mkdir(d)
                sts[c] = statements(d, name, ["8", "8", "1", "200", str(a), str(200 - a), str(r)], src)
            cases = [(a, r) for a in range(201) for r in range(256)]
            work = lambda ar: (ar, run(avon, sts[commitment(*ar)], witness(ar[0], 200 - ar[0], ar[1]),
                                       tmp, f"{ar[0]}_{ar[1]}"))
        with cf.ThreadPoolExecutor(jobs) as ex:
            results = list(ex.map(work, cases, chunksize=64))
    accepted = [(w, c) for w, c in results if c is not None]
    print(f"{name}: {len(accepted)} of {len(results)} witnesses accepted")
    if name == "split8":
        sums = sorted({a + b for (a, b), _ in accepted})
        print(f"  accepted sums a + b: {sums}")
    if len(accepted) != (201 if name == "split8" else 51456):
        sys.exit("  not the expected witnesses")
    for i, kind in enumerate(("plain", "jets")):
        for key in ("rows", "cells") + (("pops", "written") if kind == "jets" else ()):
            v = [c[i][key] for _, c in accepted]
            print(f"  {kind:5} {key:7} {min(v):>9,} to {max(v):>9,}: 2^{math.ceil(math.log2(max(v) + 1))}")


if __name__ == "__main__":
    main()
