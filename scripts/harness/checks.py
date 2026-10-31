"""The harness's checks: the verdicts of both tools on every text, and the
tests of the corpus's modules."""

from pathlib import Path

import corpus
import sets
import tools
from refine import FAILED, INVALID, PASSED, Judgement, expected, show_values
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
        types = corpus.result_types(module.path.read_text(encoding="utf-8"))
        exe = "is not built: the module has no differential test"
        if any(t.expect is None for t in module.tests):
            exe = self.build(module)
        for t in module.tests:
            self.test(module.path, t, types, exe)

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

    def test(self, path: Path, t: corpus.Test, types: dict, exe: Path | str):
        """Runs one test. `exe` is the module's executable, or why there is
        none."""
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
        native = exe
        if isinstance(exe, Path):
            native = tools.native_values(tools.run([str(exe), t.func, *t.args]))
        shown = native if isinstance(native, str) else "returns " + show_values(native)
        detail = f"fir-ref {show(ref)}"
        if t.results:
            n = len(t.results)
            detail += f", and the test declares {n} result{'s' if n != 1 else ''}"
        detail += f"; native code {shown}"
        checked = "the set is the declared results"
        if isinstance(ref, str):
            j = Judgement(FAILED)
        elif t.func not in types:
            j = Judgement(FAILED, f"cannot read the result types of {t.func}")
        elif isinstance(ref, BudgetExceeded):
            if not t.results:
                j = Judgement(
                    INVALID,
                    "with no set to judge by, the test proves nothing unless it"
                    " declares its results, each with a witness",
                )
            else:
                j = self.declared(path, t, None) or sets.judge_declared(
                    t.results, native, types[t.func]
                )
                checked = f"{len(sets.SEEDS)} seeded runs give declared results"
        else:
            j = None
            if t.results:
                j = sets.problem(ref.outcomes) or self.declared(path, t, ref)
            j = j or sets.judge_set(ref, native, types[t.func])
        if t.results and j.status == PASSED:
            j = Judgement(PASSED, f"each witness gives its result, and {checked}")
        if t.invalid is not None:
            j = sets.declared_invalid(j, ref, isinstance(exe, Path))
        self.report.add(j.status, t.show(), detail + why(j))

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


def why(j: Judgement) -> str:
    return f": {j.why}" if j.why else ""


def messages(a, b) -> str:
    """The first message of each tool, for a failed check."""
    out = ""
    for tool, v in (("funk", a), ("fir-ref", b)):
        if isinstance(v, Verdict) and v.message:
            out += f"\n{'':<10}{tool}: {v.message}"
    return out
