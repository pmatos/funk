"""Runs generated programs on `fir-ref` and as native code (#165,
ADR-2026-11-08-2115).

Usage: programs.py --fir-ref FIR_REF [--funk FUNK] [--programs DIR]
                   [--texts DIR]...

`--programs DIR` holds what the `fir_programs` example wrote: for each seed,
`program-SEED.fir` and the runs to make of it, `program-SEED.toml`. Both
tools must accept each program and `funk build` must build it. A run with
`expect` must end that way on `fir-ref`. Any other run is judged as a
differential test, unless it is interpreter-only: `fir-ref`'s report on it
holds UB or a run out of fuel, or it chooses past the budget.

Every file of each `--texts DIR` goes through `fir-ref fmt`, which must
print its canonical form or report a parse error at a position (#165).

It exits with 0 when every check passed, 1 when one failed or too few runs
reached native code, and 2 on a usage error or a tool it cannot run.
"""

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

import corpus
import differential
import tools
from checks import Harness, show
from execution import ProcessRuns
from refine import FAILED, INVALID, PASSED, Judgement, expected
from report import Report

# The most bits that one path of a generated run may choose. Each path
# costs a run of the interpreter, so this bounds a run's cost.
CHOICE_BITS = 10
# The share of the runs without `expect` that must reach native code, so
# that a change to the generator cannot leave the check empty.
MIN_COMPARED = 0.5
# Below this many runs, the share says nothing: a replay of one seed is one.
MIN_RUNS_FOR_SHARE = 200

PARSE_ERROR_LINE = re.compile(r".*:\d+:\d+: parse error: ")
SEED = re.compile(r"program-(\d+)\.fir")


def arguments(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(prog="programs", description=__doc__.split("\n")[0])
    p.add_argument("--fir-ref", required=True, help="the fir-ref executable")
    p.add_argument("--funk", help="the funk executable, needed with --programs")
    p.add_argument("--programs", type=Path, help="what fir_programs wrote")
    p.add_argument(
        "--texts", type=Path, action="append", default=[], help="texts for fir-ref fmt"
    )
    args = p.parse_args(argv)
    if args.programs is not None and args.funk is None:
        p.error("--programs needs --funk")
    if args.programs is None and not args.texts:
        p.error("give --programs or --texts")
    return args


@dataclass
class Tally:
    """What became of the runs of generated programs."""

    compared: int = 0
    defined: int = 0
    planted: int = 0
    interpreter_only: dict[str, int] = field(default_factory=dict)
    failed_seeds: set[str] = field(default_factory=set)

    def differential(self) -> int:
        return self.compared + sum(self.interpreter_only.values())

    def show(self) -> str:
        reasons = ", ".join(
            f"{n}: {why}" for why, n in sorted(self.interpreter_only.items())
        )
        return (
            f"{self.compared} of {self.differential()} runs compared with native"
            f" code ({self.defined} built to stay defined), {self.planted} planted"
            " runs ended as planted"
            + (f"; interpreter-only {reasons}" if reasons else "")
        )

    def too_few_compared(self) -> str | None:
        """Why the share of runs compared with native code is too low."""
        runs = self.differential()
        if runs < MIN_RUNS_FOR_SHARE or self.compared / runs >= MIN_COMPARED:
            return None
        return (
            f"only {self.compared} of {runs} runs reached native code, and at"
            f" least {MIN_COMPARED:.0%} must"
        )


def run_generated(
    h: Harness, path: Path, t: corpus.Test, types, params, exe
) -> differential.Evaluation:
    """Runs one test of a program, and adds it to the report."""
    runs = ProcessRuns(h.fir_ref, path, t, exe, CHOICE_BITS)
    result = differential.evaluate_generated(t, types.get(t.func), params, runs)
    h.report.add(result.judgement.status, t.show(), result.detail, quiet=True)
    return result


def run_planted(h: Harness, path: Path, t: corpus.Test) -> str:
    """Runs a test planted to end one way, and adds it to the report."""
    ref = ProcessRuns(h.fir_ref, path, t, "is not built").scripted(t.args, t.choices)
    j = Judgement(FAILED) if isinstance(ref, str) else expected(ref.outcome, t.expect)
    detail = f"fir-ref {show(ref)}" + (f": {j.why}" if j.why else "")
    h.report.add(j.status, t.show(), detail, quiet=True)
    return j.status


def check_program(h: Harness, fir: Path, tally: Tally, errors: list[str]):
    """Runs every test of the program `fir`."""
    name = fir.name
    failed_before = h.report.counts[FAILED] + h.report.counts[INVALID]
    tests = corpus.read_tests(fir.with_suffix(".toml"), name, errors, generated=True)
    if h.accepted(name, fir, quiet=True):
        text = fir.read_text(encoding="utf-8")
        types, params = corpus.result_types(text), corpus.param_types(text)
        exe = h.build(corpus.Module(name, fir, tests))
        for t in tests:
            if t.expect is not None:
                if run_planted(h, fir, t) == PASSED:
                    tally.planted += 1
                continue
            r = run_generated(h, fir, t, types, params.get(t.func), exe)
            if r.judgement.status == PASSED:
                if r.interpreter_only is None:
                    tally.compared += 1
                    tally.defined += t.defined
                else:
                    why = r.interpreter_only
                    tally.interpreter_only[why] = tally.interpreter_only.get(why, 0) + 1
    if h.report.counts[FAILED] + h.report.counts[INVALID] != failed_before:
        tally.failed_seeds.add(SEED.fullmatch(name).group(1))


def check_programs(args, work: Path, report: Report):
    programs = sorted(args.programs.glob("program-*.fir"))
    if not programs:
        report.add(FAILED, "generated programs", f"{args.programs} holds none")
    h = Harness(args.funk, args.fir_ref, work, report)
    tally, errors = Tally(), []
    for fir in programs:
        check_program(h, fir, tally, errors)
    for e in errors:
        report.add(FAILED, "generated programs", e)
    report.note(tally.show())
    why = tally.too_few_compared()
    if why:
        report.add(FAILED, "generated programs", why)
    if tally.failed_seeds:
        seeds = " ".join(sorted(tally.failed_seeds, key=int))
        report.note(f"replay with: scripts/check-random-programs.sh {seeds}")


def fmt_problem(ran: tools.Ran) -> str | None:
    """Why `fir-ref fmt` did not end cleanly on a text, if it did not: it
    prints the canonical form, or a parse error at a position."""
    if ran.status == 0:
        return None
    first = ran.stderr.partition("\n")[0]
    if ran.status == 1 and PARSE_ERROR_LINE.match(first):
        return None
    return tools.failure(ran)


def check_texts(fir_ref: str, directory: Path, report: Report):
    texts = sorted(p for p in directory.iterdir() if p.is_file())
    if not texts:
        report.note(f"{directory} holds no text for fir-ref fmt")
    for p in texts:
        why = fmt_problem(tools.run([fir_ref, "fmt", str(p)]))
        report.add(
            FAILED if why else PASSED, f"fir-ref fmt {p.name}", why or "", quiet=True
        )


def main(argv: list[str]) -> int:
    args = arguments(argv)
    sys.set_int_max_str_digits(0)
    report = Report(sys.stdout)
    with tempfile.TemporaryDirectory(prefix="fir-programs.") as work:
        try:
            if args.programs is not None:
                check_programs(args, Path(work), report)
            for directory in args.texts:
                check_texts(args.fir_ref, directory, report)
        except OSError as e:
            print(f"programs: {e}", file=sys.stderr)
            return 2
    print(report.summary())
    return 0 if report.ok() else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
