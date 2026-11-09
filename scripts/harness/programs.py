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
from checks import Harness
from execution import ProcessRuns
from refine import FAILED, INVALID, PASSED
from report import Report

# The most bits that one path of a generated run may choose. Each path
# costs a run of the interpreter, so this bounds a run's cost.
CHOICE_BITS = 10
# The share of the runs without `expect` that must reach native code, so
# that a change to the generator cannot leave the check empty.
MIN_COMPARED = 0.5
# Below this many runs, the share says nothing: a replay of one seed is one.
MIN_RUNS_FOR_SHARE = 200

PROGRAMS_CHECK = "generated programs"
PARSE_ERROR_LINE = re.compile(r".*:\d+:\d+: parse error: ")
SEED = re.compile(r"program-(\d+)\.fir")
SOUP_SEED = re.compile(r"soup-(\d+)\.fir")


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

    def differential_runs(self) -> int:
        return self.compared + sum(self.interpreter_only.values())

    def record(self, result: differential.Evaluation, defined: bool):
        """Counts a differential run, if it passed."""
        if result.judgement.status != PASSED:
            return
        why = result.interpreter_only
        if why is None:
            self.compared += 1
            self.defined += defined
        else:
            self.interpreter_only[why] = self.interpreter_only.get(why, 0) + 1

    def show(self) -> str:
        reasons = ", ".join(
            f"{n}: {why}" for why, n in sorted(self.interpreter_only.items())
        )
        return (
            f"{self.compared} of {self.differential_runs()} runs compared with native"
            f" code ({self.defined} built to stay defined), {self.planted} planted"
            " runs ended as planted"
            + (f"; interpreter-only {reasons}" if reasons else "")
        )

    def too_few_compared(self) -> str | None:
        """Why the share of runs compared with native code is too low."""
        runs = self.differential_runs()
        if runs < MIN_RUNS_FOR_SHARE or self.compared / runs >= MIN_COMPARED:
            return None
        return (
            f"only {self.compared} of {runs} runs reached native code, and at"
            f" least {MIN_COMPARED:.0%} must"
        )


class QuietReport(Report):
    """A report that leaves out every check that passed."""

    def add(self, status: str, what: str, detail: str, quiet: bool = True):
        super().add(status, what, detail, True)


def parse_runs(
    data: dict, module: str
) -> tuple[list[tuple[corpus.Test, bool]], list[str]]:
    """The runs of a program's sidecar, each with whether it is built to stay
    defined, a key that only a generated program's sidecar has."""
    flags, problems = [], []
    items = data.get("tests")
    for i, t in enumerate(items if isinstance(items, list) else [], 1):
        defined = t.pop("defined", False) if isinstance(t, dict) else False
        if not isinstance(defined, bool):
            problems.append(f"test {i}: defined is true or false")
        elif defined and t.get("expect") is not None:
            problems.append(f"test {i}: defined goes with no expect")
        flags.append(defined)
    tests, more = corpus.parse_tests(data, module)
    problems += more
    return ([] if problems else list(zip(tests, flags))), problems


def read_runs(path: Path, module: str, errors: list[str]):
    """The runs of the sidecar at `path`; its problems join `errors`."""
    data = corpus.read_toml(path, errors)
    if data is None:
        return []
    runs, problems = parse_runs(data, module)
    errors += [f"{path}: {p}" for p in problems]
    return runs


def run_generated(
    h: Harness, path: Path, t: corpus.Test, types, params, exe, defined: bool
) -> differential.Evaluation:
    """Runs one test of a program, and adds it to the report."""
    runs = ProcessRuns(h.fir_ref, path, t, exe, CHOICE_BITS)
    result = differential.evaluate_generated(
        t, types.get(t.func), params, runs, defined
    )
    h.report.add(result.judgement.status, t.show(), result.detail)
    return result


def check_program(h: Harness, fir: Path, tally: Tally, errors: list[str]):
    """Runs every test of the program `fir`."""
    name = fir.name
    failed_before = h.report.counts[FAILED] + h.report.counts[INVALID]
    runs = read_runs(fir.with_suffix(".toml"), name, errors)
    if h.accepted(name, fir):
        text = fir.read_text(encoding="utf-8")
        types, params = corpus.result_types(text), corpus.param_types(text)
        exe = h.build(corpus.Module(name, fir, [t for t, _ in runs]))
        for t, defined in runs:
            if t.expect is not None:
                if h.interpreter_only(fir, t) == PASSED:
                    tally.planted += 1
                continue
            r = run_generated(h, fir, t, types, params.get(t.func), exe, defined)
            tally.record(r, defined)
    if h.report.counts[FAILED] + h.report.counts[INVALID] != failed_before:
        tally.failed_seeds.add(SEED.fullmatch(name).group(1))


def check_programs(args, work: Path, report: Report):
    programs = sorted(args.programs.glob("program-*.fir"))
    if not programs:
        report.add(FAILED, PROGRAMS_CHECK, f"{args.programs} holds none")
    h = Harness(args.funk, args.fir_ref, work, report)
    tally, errors = Tally(), []
    for fir in programs:
        check_program(h, fir, tally, errors)
    for e in errors:
        report.add(FAILED, PROGRAMS_CHECK, e)
    report.note(tally.show())
    why = tally.too_few_compared()
    if why:
        report.add(FAILED, PROGRAMS_CHECK, why)
    note_replay(report, tally.failed_seeds)


def note_replay(report: Report, seeds: set[str]):
    """Says how to run again the seeds that failed, if any did."""
    if seeds:
        shown = " ".join(sorted(seeds, key=int))
        report.note(f"replay with: scripts/check-random-programs.sh {shown}")


def fmt_problem(ran: tools.Ran) -> str | None:
    """Why `fir-ref fmt` did not end cleanly on a text, if it did not: it
    prints the canonical form, or a parse error at a position."""
    if ran.status == 0:
        return None if ran.stdout else "exits with 0 and prints nothing"
    first = ran.stderr.partition("\n")[0]
    if ran.status == 1 and PARSE_ERROR_LINE.match(first):
        return None
    return tools.failure(ran)


def check_texts(fir_ref: str, directory: Path, report: Report):
    texts = sorted(p for p in directory.iterdir() if p.is_file())
    if not texts:
        report.note(f"{directory} holds no text for fir-ref fmt")
    failed_seeds = set()
    for p in texts:
        why = fmt_problem(tools.run([fir_ref, "fmt", str(p)]))
        report.add(FAILED if why else PASSED, f"fir-ref fmt {p.name}", why or "")
        soup = SOUP_SEED.fullmatch(p.name)
        if why and soup:
            failed_seeds.add(soup.group(1))
    note_replay(report, failed_seeds)


def main(argv: list[str]) -> int:
    args = arguments(argv)
    sys.set_int_max_str_digits(0)
    report = QuietReport(sys.stdout)
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
