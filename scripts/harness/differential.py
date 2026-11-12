"""One differential test's judgement and explanation.

The corpus runner supplies function types and an adapter for tool runs; it
does not coordinate witnesses, samples, poison stand-ins or rechecks.
The rules remain those of ADR-2026-10-30-2135 and
docs/decisions/testing-and-harness.md#poison-arguments, and for a generated run
ADR-2026-11-08-2115. Process mechanics belong to `execution.py`.
"""

from dataclasses import dataclass
from typing import Protocol

import native_floats
import sets
import standins
from corpus import Test
from refine import (
    FAILED,
    FUEL_EXHAUSTED,
    INVALID,
    PASSED,
    POISON,
    STUCK,
    UB,
    Judgement,
    OutOfStack,
    show_values,
)
from sets import BudgetExceeded, Outcomes, Path


class Runs(Protocol):
    """Decoded tool runs for one function, file and fuel budget.

    `unavailable` is the build failure to show, or None for an executable.
    Errors starting a process propagate to the corpus runner. Argument
    vectors are explicit so only rechecks replace the reference's poison.
    """

    unavailable: str | None

    def exhaustive(self, args: tuple[str, ...]) -> Outcomes | BudgetExceeded | str: ...

    def scripted(
        self, args: tuple[str, ...], choices: tuple[str, ...] | None
    ) -> Path | str: ...

    def sampled(self, args: tuple[str, ...], seed: int) -> Path | str: ...

    def native(self, args: tuple[str, ...]) -> tuple[str, ...] | OutOfStack | str: ...


@dataclass(frozen=True)
class Evaluation:
    judgement: Judgement
    detail: str
    # Why fir-ref gave no result for the test, when it did not.
    reference_failure: str | None = None
    # Why a generated run is not compared with native code, when it is not.
    interpreter_only: str | None = None


def evaluate(test: Test, result_types, param_types, runs: Runs) -> Evaluation:
    """Judge one differential test, including all runs needed to explain it.

    Types are those read from the function's canonical text, or None when
    they could not be read. The returned detail is ready for the report;
    the caller owns the test's name, report counts and final exit status.
    """
    return _Run(test, result_types, param_types, runs).compare(
        runs.exhaustive(test.args)
    )


def evaluate_generated(
    test: Test, result_types, param_types, runs: Runs, defined: bool = False
) -> Evaluation:
    """Judge a run of a generated program, which cannot declare its results.

    A run that may hit UB or run out of fuel, or that chooses past the
    budget, is interpreter-only: it passes with fir-ref's report and native
    code does not run. A run built to stay `defined` fails instead, since
    the generator is a second opinion on it. Any other run is judged as a
    differential test.
    """
    ref = runs.exhaustive(test.args)
    detail = f"fir-ref {_show(ref)}"
    why = _interpreter_only(ref)
    wrong = (why or _not_defined(ref)) if defined else None
    if wrong is not None:
        failure = f"the run is built to stay defined, but {wrong}"
        return Evaluation(Judgement(FAILED, failure), f"{detail}: {failure}")
    if why is not None:
        shown = f"{detail}; native code is not run: {why}"
        return Evaluation(Judgement(PASSED), shown, interpreter_only=why)
    return _Run(test, result_types, param_types, runs).compare(ref)


class _Run:
    def __init__(self, test: Test, result_types, param_types, runs: Runs):
        self.test = test
        self.types = result_types
        self.params = param_types
        self.runs = runs

    def compare(self, ref) -> Evaluation:
        """Judge the test on fir-ref's report `ref` on its arguments."""
        t = self.test
        self.ref = ref
        detail = f"fir-ref {_show(self.ref)}"
        if t.results:
            n = len(t.results)
            detail += f", and the test declares {n} result{'s' if n != 1 else ''}"
        decided = self._reference()
        shown, j = self._native(decided)
        detail += f"; native code {shown}"
        if t.results and j.status == PASSED:
            checked = (
                f"{len(sets.SEEDS)} seeded runs give declared results"
                if isinstance(self.ref, BudgetExceeded)
                else "the set is the declared results"
            )
            j = Judgement(PASSED, f"each witness gives its result, and {checked}")
        failure = self.ref if isinstance(self.ref, str) else None
        return Evaluation(j, detail + (f": {j.why}" if j.why else ""), failure)

    def _reference(self) -> Judgement | None:
        """Checks that decide the test before looking at any native result."""
        if isinstance(self.ref, str):
            return Judgement(FAILED)
        if self.types is None:
            return Judgement(
                FAILED, f"cannot read the result types of {self.test.func}"
            )
        if isinstance(self.ref, BudgetExceeded):
            if not self.test.results:
                return Judgement(
                    INVALID,
                    "with no set to judge by, the test proves nothing unless it"
                    " declares its results, each with a witness",
                )
            return self._declared()
        if self.test.results:
            return sets.problem(self.ref.outcomes) or self._declared()
        return None

    def _judge(self, native, decided: Judgement | None) -> Judgement:
        # Preserve a reference-side verdict even if native execution failed.
        if decided is not None:
            return decided
        if isinstance(self.ref, BudgetExceeded):
            return sets.judge_declared(self.test.results, native, self.types)
        return sets.judge_set(self.ref, native, self.types)

    def _native(self, decided: Judgement | None) -> tuple[str, Judgement]:
        t = self.test
        if self.runs.unavailable is not None:
            return self.runs.unavailable, self._judge(self.runs.unavailable, decided)
        if POISON not in t.args:
            native = self._run_native(t.args)
            return _returned(native), self._judge(native, decided)
        vectors = standins.vectors(t.args, self.params)
        if isinstance(vectors, str):
            shown = f"is not run: {vectors}"
            return shown, self._judge(shown, decided)
        if decided is not None:
            # Even a decided test runs once for diagnostic evidence.
            native = self._run_native(vectors[0])
            return f"{_returned(native)} on {' '.join(vectors[0])}", decided
        each = f"{len(vectors)} argument vectors with stand-ins for poison"
        shown = None
        for args in vectors:
            native = self._run_native(args)
            j = self._judge(native, None)
            on = f"{_returned(native)} on {' '.join(args)}"
            if j.status == INVALID:
                return on, j
            if j.status != PASSED:
                if isinstance(self.ref, BudgetExceeded):
                    j = self._recheck(args, j)
                return f"{on}, one of {each}", j
            shown = shown or f"{on}, and passes on all {each}"
        return shown, j

    def _run_native(self, args: tuple[str, ...]):
        """Native code's result on `args`, with each float passed and read
        back as its bits (`native_floats`)."""
        native = self.runs.native(native_floats.to_native(args, self.params))
        return native_floats.from_native(native, self.types)

    def _declared(self) -> Judgement | None:
        t = self.test
        for i, r in enumerate(t.results, 1):
            got = self.runs.scripted(t.args, r.witness)
            j = sets.witness(i, r, got)
            if j is not None:
                return j
        if isinstance(self.ref, Outcomes):
            return sets.undeclared(self.ref, t.results)
        for seed in sets.SEEDS:
            got = self.runs.sampled(t.args, seed)
            j = sets.sample(seed, got, t.results)
            if j is not None:
                return j
        return None

    def _recheck(self, args: tuple[str, ...], j: Judgement) -> Judgement:
        """Find UB or fuel exhaustion on a failing vector past the budget.

        This is diagnostic evidence for an already failed native result,
        not a new comparison against that vector's reference result.
        Preserve the existing collection and precedence: collect every
        seed, ignore seed tool errors, then prefer UB to fuel exhaustion.
        Stuck leaves the original failure standing. `sets.problem` has
        different precedence and must not replace this classification.
        """
        on = " ".join(args)
        ref = self.runs.exhaustive(args)
        found = []
        if isinstance(ref, Outcomes):
            found = [("fir-ref", o) for o in ref.outcomes]
        elif isinstance(ref, BudgetExceeded):
            for seed in sets.SEEDS:
                got = self.runs.sampled(args, seed)
                if not isinstance(got, str):
                    found.append((f"fir-ref --seed {seed}", got.outcome))
        for who, o in found:
            if o.kind == UB:
                return Judgement(
                    INVALID,
                    f"on {on}, {who} {o.show()}, so the run on poison hits UB"
                    " too, or runs out of fuel, on a path that the seeded runs"
                    " miss: UB allows any result, so the test proves nothing",
                )
        for who, o in found:
            if o.kind == FUEL_EXHAUSTED:
                return Judgement(
                    INVALID,
                    f"on {on}, {who} runs out of fuel, so the result depends on"
                    " the fuel budget: raise the test's budget",
                )
        return Judgement(j.status, f"{j.why}; on {on}, fir-ref {_show(ref)}")


def _interpreter_only(ref) -> str | None:
    """Why fir-ref's report on a generated run leaves native code nothing to
    be compared with, if it does. A stuck path never makes a run
    interpreter-only: it fails, as in the corpus."""
    if isinstance(ref, BudgetExceeded):
        return "it chooses past the budget"
    if not isinstance(ref, Outcomes) or any(o.kind == STUCK for o in ref.outcomes):
        return None
    if any(o.kind == UB for o in ref.outcomes):
        return "its set of outcomes holds UB"
    if any(o.kind == FUEL_EXHAUSTED for o in ref.outcomes):
        return "a path runs out of fuel"
    return None


def _not_defined(ref) -> str | None:
    """How fir-ref's report contradicts a run built to stay defined, if it
    does: such a run makes no choice and returns defined values."""
    if not isinstance(ref, Outcomes) or any(o.kind == STUCK for o in ref.outcomes):
        return None
    if ref.choices != 0:
        return "it makes a choice"
    if any(POISON in o.values for o in ref.outcomes):
        return "it returns poison"
    return None


def _show(result) -> str:
    return result if isinstance(result, str) else result.show()


def _returned(native) -> str:
    if isinstance(native, OutOfStack):
        return native.show()
    return native if isinstance(native, str) else "returns " + show_values(native)
