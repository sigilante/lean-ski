"""The differential test of the front end (`Ski/Front.lean`) against `skijack`.

Every corpus and script file the coverage project compiles (`scripts/emit.py`:
the four script files and the twenty-one `skijack` corpus files, the four it
refuses included), in both lexicons, as written and with each line deleted in
turn.  On each program it compares four things:

- the compilation: refused, or the names compiled (`compileWith`;
  `skijack.compile(check=False)`);
- every term, by name;
- the checker's verdict: Stage A, generation and Stage B pass (`checkPass`;
  `skijack`'s `check`, `generate` and `typecheck`, as `expand_program` runs
  them);
- the checked compilation, refused or its terms (`checkedWith`;
  `skijack.compile(check=True)`).

It prints the number of programs and of disagreements, and exits 1 on any
disagreement.  From the repository root:

    lake build front
    PYTHONPATH=$HOME/skijack/python python3 scripts/differential.py

`skijack` needs `aviary_kernel` (its dependency `aviary-kernel`) installed.
At `skijack` `e978e58`: 1,260 programs (630 a lexicon), 0 disagreements,
about 60 s on an M4 Max.

`--eta` compiles with η-lifting on both sides (`skijack.compile(eta=True)`,
`Front.compileWith … true`), over the same files and the released sources
η-lifting compiles: `release/skilark/{split8,csplit8}/source.ski` and
`release/entropy/source.ski`, in the ASCII lexicon.

`--skijack DIR` names another `skijack` checkout (its `python` directory),
`--limit N` sets Python's recursion limit (default 1000, Python's own, which
`Front.walkDepth` models), and `-v` prints every disagreement in full.  The
Lean side runs `.lake/build/bin/front FILE LEXICON` (`bench/Front.lean`) once
per program; `skijack` runs in this process.
"""
import argparse, os, pathlib, re, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
ap.add_argument("--skijack", default=str(pathlib.Path.home() / "skijack/python"))
ap.add_argument("--limit", type=int, default=1000)
ap.add_argument("-v", action="store_true")
ap.add_argument("--eta", action="store_true")
args = ap.parse_args()
sys.path.insert(0, args.skijack)
import skijack
from skijack import expand as X
from aviary_kernel.terms import Atom

CORPUS = pathlib.Path(args.skijack) / "skijack/corpus"
FRONT = ROOT / ".lake/build/bin/front"
SCRIPTS = ["coverage", "macros", "level1", "generate"]
STEMS = ["sec1-nat", "kernel-events", "ascii-digits", "sec2-c", "sec3-swap", "interp-t3",
         "interp-whnff", "interp-whnff-written", "interp-whnff-written-loop", "scry-wfn",
         "level1-flipa", "parse-chars", "scry-block", "scry-ns", "scry-wfq", "tower",
         "words-to-numbers",
         # the four skijack refuses
         "misc-forms", "sec4-interp", "sec5-lookup", "syntax3-resolver"]
RELEASED = ["release/skilark/split8/source.ski", "release/skilark/csplit8/source.ski",
            "release/entropy/source.ski"]


def to_unicode(t):
    """A script file's Unicode spelling, as `scripts/emit.py` writes it."""
    t = (t.replace("===", "≡").replace(":=", "≔").replace("|>", "▹").replace("->", "→")
         .replace("\\", "λ").replace("--", "⍝"))
    t = re.sub(r"(\d+)@", r"\1⊑", t)
    t = t.replace("|-", "⊢").replace("?^", "∵").replace("=>", "↦").replace("@[]", "₍₎")
    t = re.sub(r"@(\d+)", lambda m: "".join(chr(0x2080 + int(c)) for c in m.group(1)), t)
    for a, b in [("B", "∘"), ("C", "⇄"), ("W", "⋈"), ("Y", "Υ")]:
        t = re.sub(r"(?<![A-Za-z0-9_'])" + a + r"(?![A-Za-z0-9_'])", b, t)
    return t


def inputs():
    """(label, lexicon, text) for every input file."""
    for s in SCRIPTS:
        text = (ROOT / "scripts" / f"{s}.ski").read_text(encoding="utf-8")
        yield f"scripts/{s}.ski", "ascii", text
        yield f"scripts/{s}.ski", "unicode", to_unicode(text)
    for s in STEMS:
        for lex in ("ascii", "unicode"):
            yield f"corpus/{s}.{lex}.ski", lex, (CORPUS / f"{s}.{lex}.ski").read_text(encoding="utf-8")
    if args.eta:
        for s in RELEASED:
            yield s, "ascii", (ROOT / s).read_text(encoding="utf-8")


def prefix(t):
    """`t` in prefix form, as `bench/Front.lean` prints it."""
    out, todo = [], [t]
    while todo:
        t = todo.pop()
        if isinstance(t, Atom):
            out.append(t.name if t.name in ("S", "K", "I") else f"?{t.name}?")
        else:
            out.append("`")
            todo += [t.arg, t.fn]
    return "".join(out)


def show(label, terms):
    if terms is None:
        return [f"{label} refused"]
    return [f"{label} ok {len(terms)}"] + [f"{n} {prefix(terms[n])}" for n in sorted(terms)]


def verdict(text, lex):
    """`skijack`'s checker: parse, Stage A, generation, Stage B, as
    `expand_program` runs them before it expands."""
    try:
        program = skijack.parse(text, lex)
        defined = {d.name for d in program.decls
                   if isinstance(d, (skijack.ast.Equation, skijack.ast.Def,
                                     skijack.ast.Core, skijack.ast.Macro))}
        mentioned = X._mentions(program.decls, set())
        prelude = X.PRELUDE_NAMES + tuple(n for n in X.NAT_NAMES
                                          if n in mentioned and n not in defined)
        X._check(program, prelude)
        program = X._generate(program)
        skijack.typecheck(program, prelude, generated=True)
    except Exception:
        return False
    return True


def terms(text, lex, check):
    try:
        return skijack.compile(text, lexicon=lex, check=check, eta=args.eta).terms
    except Exception:
        return None


def python_side(text, lex):
    return (show("compile", terms(text, lex, False))
            + [f"check {'pass' if verdict(text, lex) else 'fail'}"]
            + show("checked", terms(text, lex, True)))


def lean_side(path, lex):
    r = subprocess.run([str(FRONT), path, lex] + (["eta"] if args.eta else []),
                       capture_output=True, text=True, timeout=600)
    if r.returncode != 0:
        return [f"front exited {r.returncode}: {r.stderr.strip()}"]
    return r.stdout.splitlines()


def first_diff(a, b):
    """The first output line where `a` and `b` differ, and each one's."""
    n = max(len(a), len(b))
    a, b = a + ["<end>"] * (n - len(a)), b + ["<end>"] * (n - len(b))
    return next((i, x, y) for i, (x, y) in enumerate(zip(a, b)) if x != y)


def main():
    if not FRONT.exists():
        sys.exit(f"{FRONT} missing: run `lake build front` first")
    sys.setrecursionlimit(args.limit)
    start = time.time()
    programs = bad = 0
    tally, per_lex = {}, {}
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "program.ski")
        for label, lex, text in inputs():
            lines = text.splitlines(keepends=True)
            for k in [None, *range(len(lines))]:
                src = text if k is None else "".join(lines[:k] + lines[k + 1:])
                with open(path, "w", encoding="utf-8", newline="") as f:
                    f.write(src)
                py, ln = python_side(src, lex), lean_side(path, lex)
                programs += 1
                per_lex[lex] = per_lex.get(lex, 0) + 1
                outcome = (py[0].split()[1], next(l for l in py if l.startswith("check ")).split()[1])
                tally[outcome] = tally.get(outcome, 0) + 1
                if py != ln:
                    bad += 1
                    i, x, y = first_diff(py, ln)
                    where = "as written" if k is None else f"line {k + 1} deleted"
                    print(f"DISAGREE {label} ({lex}), {where}: line {i + 1} of the output")
                    print(f"  skijack: {x[:160]}")
                    print(f"  front:   {y[:160]}")
                    if args.v:
                        print("\n".join(f"  < {l[:160]}" for l in py))
                        print("\n".join(f"  > {l[:160]}" for l in ln))
    print(f"{programs} programs, {bad} disagreements, {time.time() - start:.0f} s")
    print("  " + ", ".join(f"{lex} {n}" for lex, n in per_lex.items()))
    for (c, v), n in sorted(tally.items()):
        print(f"  compile {c}, check {v}: {n}")
    sys.exit(1 if bad else 0)


main()
