"""Runs a Python test hook's tests as its old `python ...` entry did, and
in CI writes their counts to the job summary (#150, ADR-2026-11-05-1633).

Usage: python scripts/run_unittests.py HOOK FILE [ARG...]
       python scripts/run_unittests.py HOOK -m unittest [ARG...]

The arguments after HOOK are those that the hook's entry gave `python`
before: a test file, run as `__main__`, or `-m unittest` and its arguments,
such as `discover -s DIR -p PATTERN`. The tests run in this process with
the sys.argv, sys.path[0] and `__main__` module that `python` would give
them, and the exit status is the one that their `unittest.main()` chose.

When GITHUB_STEP_SUMMARY is set, as in a step of a GitHub Actions job, the
tests run without it, so that a script they run cannot write to the job
summary, and then this script writes one row of counts there through
scripts/suite_summary.py and prints it to the log. Without it, the hook
prints and exits as it did before.
"""

import importlib.util
import os
import runpy
import sys
import traceback
import unittest
import unittest.runner
from typing import ClassVar

HERE = os.path.dirname(os.path.abspath(__file__))
USAGE = __doc__.split("\n\n")[1]


class CountingResult(unittest.TextTestResult):
    """unittest's text result, which also counts the tests that passed."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.passed = 0

    def addSuccess(self, test):
        super().addSuccess(test)
        self.passed += 1


class RecordingRunner(unittest.runner.TextTestRunner):
    """unittest's text runner, which keeps the result of the outermost run,
    not of a run that a test starts inside it."""

    resultclass = CountingResult
    results: ClassVar[list] = []
    depth = 0

    def run(self, test):
        RecordingRunner.depth += 1
        try:
            result = super().run(test)
        finally:
            RecordingRunner.depth -= 1
        if RecordingRunner.depth == 0:
            RecordingRunner.results.append(result)
        return result


def run_file(path: str, args: list[str]) -> None:
    """Runs the test file `path` as `python path args` runs it."""
    full = os.path.abspath(path)
    spec = importlib.util.spec_from_file_location("__main__", full)
    module = importlib.util.module_from_spec(spec)
    # A script run by `python FILE` has no spec and no package.
    module.__spec__ = module.__package__ = None
    sys.argv = [path, *args]
    sys.path[0] = os.path.dirname(full)
    main = sys.modules["__main__"]
    sys.modules["__main__"] = module
    try:
        spec.loader.exec_module(module)
    finally:
        sys.modules["__main__"] = main


def run_unittest(args: list[str]) -> None:
    """Runs `python -m unittest args`."""
    sys.argv = [sys.argv[0], *args]
    sys.path[0] = os.getcwd()
    runpy.run_module("unittest", run_name="__main__", alter_sys=True)


def counts(result) -> tuple[list[str], list[int]]:
    """The header and the values of the summary's row for `result`."""
    header = ["tests run", "passed", "failed", "errors", "skipped"]
    values = [
        result.testsRun,
        result.passed,
        len(result.failures),
        len(result.errors),
        len(result.skipped),
    ]
    for name, found in (
        ("expected failures", result.expectedFailures),
        ("unexpected successes", result.unexpectedSuccesses),
    ):
        if found:
            header.append(name)
            values.append(len(found))
    return header, values


def summarise(summary: str, hook: str, status, error: str) -> None:
    """Writes the row of counts to the job summary and the log."""
    spec = importlib.util.spec_from_file_location(
        "_suite_summary", os.path.join(HERE, "suite_summary.py")
    )
    writer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(writer)
    os.environ["GITHUB_STEP_SUMMARY"] = summary
    title = f"Python tests ({hook})"
    if not RecordingRunner.results:
        note = error or "No test ran."
        writer.write(title, ["tests run"], [[0]], note)
        return
    header, values = counts(RecordingRunner.results[0])
    note = writer.exited("unittest", str(exit_code(status)))
    if not values[0] and not values[4]:
        note = " ".join(filter(None, ["No test ran.", note]))
    writer.write(title, header, [values], note)


def exit_code(status) -> int:
    """The exit status that `sys.exit(status)` gives."""
    if status is None or status is False:
        return 0
    if status is True:
        return 1
    return status if isinstance(status, int) else 1


def print_from(error: BaseException, path: str) -> None:
    """Prints the traceback of `error` from the first frame in `path` on,
    as `python path` prints it."""
    tb = error.__traceback__
    while tb is not None and tb.tb_frame.f_code.co_filename != path:
        tb = tb.tb_next
    traceback.print_exception(type(error), error, tb or error.__traceback__)


def main(argv: list[str]) -> int:
    if len(argv) < 2 or (argv[1] == "-m" and argv[2:3] != ["unittest"]):
        print(USAGE, file=sys.stderr)
        return 2
    hook, args = argv[0], argv[1:]
    summary = os.environ.pop("GITHUB_STEP_SUMMARY", "")
    unittest.runner.TextTestRunner = RecordingRunner
    status, error = 0, ""
    try:
        if args[0] == "-m":
            run_unittest(args[2:])
        else:
            run_file(args[0], args[1:])
    except SystemExit as done:
        status = done.code
    except Exception as e:
        if args[0] == "-m":
            raise
        print_from(e, os.path.abspath(args[0]))
        status, error = 1, f"The tests did not run: {type(e).__name__}: {e}"
    if summary:
        sys.stdout.flush()
        sys.stderr.flush()
        summarise(summary, hook, status, error)
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
