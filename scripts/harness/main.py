"""The differential harness of #13 (ADR-2026-10-30-2049): it runs the corpus
of `tests/fir/` on `fir-ref` and as native code from `funk build`.

Usage: main.py --funk FUNK --fir-ref FIR_REF --generated DIR CORPUS

It checks that `funk verify` and `fir-ref validate` accept every module of
the corpus and every module in DIR, which holds what the Rust generator
printed, and that they reject every must-reject text with the same
verdict. Then it runs each test of the corpus, and reports each check as
passed, failed or invalid. It exits with 0 when every check passed, 1 when
one failed or was invalid, and 2 on a usage error or a tool it cannot run.
`scripts/check-harness.sh` builds the tools and runs it.
"""

import argparse
import sys
import tempfile
from pathlib import Path

import corpus
from checks import Harness
from refine import FAILED
from report import Report


def arguments(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(prog="harness", description=__doc__.split("\n")[0])
    p.add_argument("--funk", required=True, help="the funk executable")
    p.add_argument("--fir-ref", required=True, help="the fir-ref executable")
    p.add_argument(
        "--generated",
        required=True,
        type=Path,
        help="a directory of .fir modules that the Rust generator printed",
    )
    p.add_argument("corpus", type=Path, help="the corpus, tests/fir")
    return p.parse_args(argv)


def check(args: argparse.Namespace, work: Path, report: Report):
    c = corpus.load(args.corpus)
    for e in c.errors:
        report.add(FAILED, "corpus format", e)
    h = Harness(args.funk, args.fir_ref, work, report)
    accepted = {m.name: h.accepted(m.name, m.path) for m in c.modules}
    for name, path in c.inputs:
        h.accepted(name, path)
    generated = sorted(args.generated.glob("*.fir"))
    if not generated:
        report.add(FAILED, "generated modules", f"{args.generated} holds none")
    passed = sum(h.accepted(f"generated/{p.name}", p, quiet=True) for p in generated)
    report.note(
        f"funk verify and fir-ref validate accept {passed} of the"
        f" {len(generated)} modules from the Rust generator"
    )
    for i, r in enumerate(c.rejects):
        h.rejected(r, i)
    for m in c.modules:
        h.tests(m, accepted[m.name])


def main(argv: list[str]) -> int:
    args = arguments(argv)
    # Values of wide types have many digits.
    sys.set_int_max_str_digits(0)
    report = Report(sys.stdout)
    with tempfile.TemporaryDirectory(prefix="fir-harness.") as work:
        try:
            check(args, Path(work), report)
        except OSError as e:
            print(f"harness: {e}", file=sys.stderr)
            return 2
    print(report.summary())
    return 0 if report.ok() else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
