"""The harness's checks: the verdicts of both tools on every text, and the
tests of the corpus's modules."""

from functools import partial
from pathlib import Path

import corpus
import sets
import standins
import tools
from refine import FAILED, INVALID, PASSED, POISON, Judgement, expected, show_values
from report import Report
from sets import BudgetExceeded
from tools import ACCEPTED, Verdict


def show(result) -> str:
    return result if isinstance(result, str) else result.show()


class Harness:
    def __init__(self, funk: str, fir_ref: str, work: Path, report: Report):
        self.funk = funk
        self.fir_ref = fir_ref
        self.work = work
        self.report = report
        self.builds = 0

    def verdicts(self, path: Path):
        """What `funk verify --json` and `fir-ref validate` say of `path`."""
        a = tools.verdict(tools.run([self.funk, "verify", "--json", str(path)]))
        b = tools.verdict(tools.run([self.fir_ref, "validate", str(path)]))
        return a, b

    def accepted(self, name: str, path: Path, quiet: bool = False) -> bool:
        """Checks that both tools accept a module of the corpus or of the
        generator."""
        a, b = self.verdicts(path)
        ok = all(isinstance(v, Verdict) and v.verdict == ACCEPTED for v in (a, b))
        detail = f"funk verify: {show(a)}; fir-ref validate: {show(b)}"
        if not ok:
            detail += messages(a, b)
        self.report.add(PASSED if ok else FAILED, name, detail, quiet)
        return ok

    def rejected(self, reject: corpus.Reject, index: int):
        """Checks that both tools reject a must-reject text at the stage it
        names, and a parse error at the same position."""
        path = self.work / f"reject-{index}.fir"
        path.write_bytes(reject.text)
        a, b = self.verdicts(path)
        ok = (
            isinstance(a, Verdict)
            and isinstance(b, Verdict)
            and a.verdict == b.verdict == reject.verdict
            and a.position == b.position
        )
        detail = f"funk verify: {show(a)}; fir-ref validate: {show(b)}"
        if ok:
            detail += f" ({reject.rule})"
        else:
            detail += f"; both must give {reject.verdict}, since the text"
            detail += f" breaks a rule: {reject.rule}" + messages(a, b)
        self.report.add(PASSED if ok else FAILED, reject.name, detail)

    def tests(self, module: corpus.Module, accepted: bool):
        """Runs a module's tests."""
        if not module.tests:
            return
        if not accepted:
            for t in module.tests:
                self.report.add(
                    FAILED,
                    t.show(),
                    "not run: funk verify and fir-ref validate must both"
                    " accept the module first",
                )
            return
        text = module.path.read_text(encoding="utf-8")
        types = corpus.result_types(text)
        params = corpus.param_types(text)
        exe = "is not built: the module has no differential test"
        if any(t.expect is None for t in module.tests):
            exe = self.build(module)
        for t in module.tests:
            self.test(module.path, t, types, exe, params.get(t.func))

    def build(self, module: corpus.Module) -> Path | str:
        """The executable that `funk build` makes of a module, or why it
        made none."""
        self.builds += 1
        out = self.work / f"build-{self.builds}"
        out.mkdir()
        exe = out / "exe"
        cmd = [self.funk, "build", "--json", "-o", str(exe), str(module.path)]
        why = tools.build_failure(tools.run(cmd))
        return exe if why is None else f"is not built: funk build gives {why}"

    def run_ref(self, path: Path, t: corpus.Test, *options: str) -> tools.Ran:
        """Runs `fir-ref run` on a test, with more options."""
        fuel = ["--fuel", str(t.fuel), *options, "--"]
        return tools.run([self.fir_ref, "run", *fuel, str(path), t.func, *t.args])

    def test(
        self, path: Path, t: corpus.Test, types: dict, exe: Path | str, params=None
    ):
        """Runs one test. `exe` is the module's executable, or why there is
        none, and `params` the parameter types of the test's function."""
        if t.expect is not None:
            choices = [] if t.choices is None else ["--choices", ",".join(t.choices)]
            ref = tools.path(self.run_ref(path, t, *choices))
            j = (
                Judgement(FAILED)
                if isinstance(ref, str)
                else expected(ref.outcome, t.expect)
            )
            self.report.add(j.status, t.show(), f"fir-ref {show(ref)}" + why(j))
            return
        ref = tools.outcomes(self.run_ref(path, t, "--exhaustive"))
        detail = f"fir-ref {show(ref)}"
        if t.results:
            n = len(t.results)
            detail += f", and the test declares {n} result{'s' if n != 1 else ''}"
        checked = "the set is the declared results"
        # `pre` judges the test whatever native code returns; otherwise
        # `judge` judges each native result.
        pre, judge = None, None
        if isinstance(ref, str):
            pre = Judgement(FAILED)
        elif t.func not in types:
            pre = Judgement(FAILED, f"cannot read the result types of {t.func}")
        elif isinstance(ref, BudgetExceeded):
            if not t.results:
                pre = Judgement(
                    INVALID,
                    "with no set to judge by, the test proves nothing unless it"
                    " declares its results, each with a witness",
                )
            else:
                pre = self.declared(path, t, None)
                judge = partial(sets.judge_declared, t.results, types=types[t.func])
                checked = f"{len(sets.SEEDS)} seeded runs give declared results"
        else:
            if t.results:
                pre = sets.problem(ref.outcomes) or self.declared(path, t, ref)
            judge = partial(sets.judge_set, ref, types=types[t.func])
        shown, j = self.native(t, exe, params, partial(either, pre, judge))
        detail += f"; native code {shown}"
        if t.results and j.status == PASSED:
            j = Judgement(PASSED, f"each witness gives its result, and {checked}")
        self.report.add(j.status, t.show(), detail + why(j))

    def native(self, t: corpus.Test, exe: Path | str, params, judge):
        """Runs native code on a differential test and judges its result
        with `judge`: what to show of it, and the judgement. A test whose
        arguments hold poison runs native code on each vector of stand-ins
        (`standins.py`), and passes when each result passes."""
        if not isinstance(exe, Path):
            return exe, judge(exe)
        if POISON not in t.args:
            native = self.run_native(exe, t.func, t.args)
            return returned(native), judge(native)
        vectors = standins.vectors(t.args, params)
        if isinstance(vectors, str):
            return f"is not run: {vectors}", judge(f"is not run: {vectors}")
        each = f"{len(vectors)} argument vectors with stand-ins for poison"
        shown = None
        for args in vectors:
            native = self.run_native(exe, t.func, args)
            j = judge(native)
            on = f"{returned(native)} on {' '.join(args)}"
            if j.status != PASSED:
                return f"{on}, one of {each}", j
            shown = shown or f"{on}, and passes on all {each}"
        return shown, j

    def run_native(self, exe: Path, func: str, args) -> tuple[str, ...] | str:
        """What a built executable returns on a function and its arguments,
        or how it fails."""
        return tools.native_values(tools.run_native([str(exe), func, *args]))

    def declared(self, path: Path, t: corpus.Test, ref) -> Judgement | None:
        """Checks a test's declared results: each witness gives its result,
        and the run's set, `ref` when exhaustive mode lists it, or else each
        seeded run, holds only declared results."""
        for i, r in enumerate(t.results, 1):
            got = tools.path(self.run_ref(path, t, "--choices", ",".join(r.witness)))
            j = sets.witness(i, r, got)
            if j is not None:
                return j
        if ref is not None:
            return sets.undeclared(ref, t.results)
        for seed in sets.SEEDS:
            got = tools.path(self.run_ref(path, t, "--seed", str(seed)))
            j = sets.sample(seed, got, t.results)
            if j is not None:
                return j
        return None


def either(pre: Judgement | None, judge, native) -> Judgement:
    """`pre` when it judges the test by itself, and otherwise `judge` on
    the native result."""
    return pre or judge(native)


def returned(native) -> str:
    """What native code did: the values it returned, or how it failed."""
    return native if isinstance(native, str) else "returns " + show_values(native)


def why(j: Judgement) -> str:
    return f": {j.why}" if j.why else ""


def messages(a, b) -> str:
    """The first message of each tool, for a failed check."""
    out = ""
    for tool, v in (("funk", a), ("fir-ref", b)):
        if isinstance(v, Verdict) and v.message:
            out += f"\n{'':<10}{tool}: {v.message}"
    return out
