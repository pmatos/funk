"""How the harness judges a run that makes choices (ADR-2026-10-31-0003).

`fir-ref run --exhaustive` lists every outcome of a run, within a budget
on the bits that one path chooses. A run that makes no choice has one
outcome, and native code is judged against it exactly, by refinement. Any
other set is judged as a whole: a stuck path fails the test, UB or fuel
exhausted in it makes the test invalid, and otherwise native code passes
when its result refines one outcome of the set.

A test may declare its results, each a list of values with a witness: the
choices, as `--choices` takes them, on which `fir-ref` gives it. The
harness checks each witness. When exhaustive mode lists the set, the set
must be exactly the declared results. When the run chooses more than the
budget, seeded runs, `fir-ref run --seed S` for each S of SEEDS, sample the
set instead, and each must give a declared result. Native code then passes
when its result refines one declared result.
"""

from dataclasses import dataclass

from refine import (
    FAILED,
    FUEL_EXHAUSTED,
    INVALID,
    PASSED,
    RETURN,
    STUCK,
    UB,
    Judgement,
    Outcome,
    refines,
    show_values,
)

# The seeds of the sampled runs of a test that declares its results and
# chooses more than the budget. Fixed, so that a run of the harness can be
# repeated.
SEEDS = tuple(range(32))


@dataclass(frozen=True)
class Path:
    """What scripted or sampled mode reports: the outcome of one path, the
    number of choices it made, and in sampled mode the values it drew."""

    outcome: Outcome
    choices: int
    sequence: tuple[str, ...] | None = None

    def show(self) -> str:
        return self.outcome.show()


@dataclass(frozen=True)
class Outcomes:
    """What exhaustive mode reports: every outcome of the run, each once,
    and the most choices that one path made."""

    choices: int
    outcomes: tuple[Outcome, ...]

    def show(self) -> str:
        if self.choices == 0 and len(self.outcomes) == 1:
            return self.outcomes[0].show()
        n, c = len(self.outcomes), self.choices
        return (
            f"makes {c} choice{'s' if c != 1 else ''} and gives"
            f" {n} outcome{'s' if n != 1 else ''}"
        )


@dataclass(frozen=True)
class BudgetExceeded:
    """What exhaustive mode reports when a path would choose more bits than
    its budget."""

    budget: int

    def show(self) -> str:
        return f"chooses more than its budget of {self.budget} bits"


@dataclass(frozen=True)
class Declared:
    """A result that a test declares: the values, and the witness, the
    choices on which `fir-ref` gives them."""

    values: tuple[str, ...]
    witness: tuple[str, ...]


def problem(outcomes) -> Judgement | None:
    """Why a set of outcomes judges the test by itself: a stuck path fails
    it, even beside UB, and UB or fuel exhausted in it makes it invalid."""
    if any(o.kind == STUCK for o in outcomes):
        return Judgement(FAILED, "no run of a valid module is stuck")
    for o in outcomes:
        if o.kind == UB:
            return Judgement(
                INVALID,
                f"the set holds UB ({o.reason}), which allows any result,"
                " so the test proves nothing",
            )
    for o in outcomes:
        if o.kind == FUEL_EXHAUSTED:
            return Judgement(
                INVALID,
                "a path runs out of fuel, so the result depends on the fuel"
                " budget: raise the test's budget",
            )
    return None


def member(outcomes, native, types, what: str = "outcomes") -> Judgement:
    """Native code's result refines one of `outcomes`."""
    if isinstance(native, str):
        return Judgement(FAILED, "native code fails where fir-ref returns")
    for o in outcomes:
        if refines(o, native, types).status == PASSED:
            return Judgement(PASSED)
    some = ", ".join(show_values(o.values) for o in outcomes[:3])
    more = ", ..." if len(outcomes) > 3 else ""
    return Judgement(
        FAILED,
        f"the native result refines none of the {len(outcomes)} {what}: {some}{more}",
    )


def judge_set(ref: Outcomes, native, types) -> Judgement:
    """Judges a differential test on the set that exhaustive mode lists."""
    if ref.choices == 0:
        if len(ref.outcomes) != 1:
            return Judgement(
                FAILED,
                f"fir-ref lists {len(ref.outcomes)} outcomes of a run that"
                " makes no choice",
            )
        return refines(ref.outcomes[0], native, types)
    return problem(ref.outcomes) or member(ref.outcomes, native, types)


def judge_declared(results, native, types) -> Judgement:
    """Judges a differential test on its declared results, once they are
    checked."""
    outcomes = tuple(Outcome(RETURN, r.values) for r in results)
    return member(outcomes, native, types, "declared results")


def witness(i: int, r: Declared, got) -> Judgement | None:
    """Checks that the witness of the declared result `i`, `r`, gives it:
    `got` is what `fir-ref run --choices` reports, or why it reports
    nothing, such as a witness that no longer fits the run."""
    name = f"the witness {show_values(r.witness)} of result {i}"
    if isinstance(got, str):
        return Judgement(FAILED, f"{name} does not give it: fir-ref {got}")
    j = problem([got.outcome])
    if j is not None:
        return Judgement(j.status, f"{name} {got.show()}: {j.why}")
    if got.outcome.values != r.values:
        return Judgement(
            FAILED,
            f"{name} gives {show_values(got.outcome.values)},"
            f" not {show_values(r.values)}",
        )
    if got.choices != len(r.witness):
        return Judgement(
            FAILED,
            f"fir-ref makes {got.choices} choices on {name},"
            f" which has {len(r.witness)}",
        )
    return None


def undeclared(ref: Outcomes, results) -> Judgement | None:
    """Checks that the declared results are exactly the set's outcomes."""
    declared = {r.values for r in results}
    missing = [o for o in ref.outcomes if o.values not in declared]
    if not missing:
        held = {o.values for o in ref.outcomes}
        extra = [r for r in results if r.values not in held]
        if extra:
            return Judgement(
                FAILED,
                f"the test declares {show_values(extra[0].values)},"
                " which the set does not hold",
            )
        return None
    first = show_values(missing[0].values)
    if len(missing) == 1:
        return Judgement(
            FAILED, f"the test does not declare {first}, which the set holds"
        )
    return Judgement(
        FAILED,
        f"the test does not declare {len(missing)} outcomes of the set,"
        f" such as {first}",
    )


def sample(seed: int, got, results) -> Judgement | None:
    """Checks what `fir-ref run --seed SEED` reports: a declared result."""
    if isinstance(got, str):
        return Judgement(FAILED, f"seed {seed}: fir-ref {got}")
    if got.sequence is None or len(got.sequence) != got.choices:
        return Judgement(FAILED, f"seed {seed}: fir-ref does not say what it drew")
    drew = f"seed {seed} draws {show_values(got.sequence)} and"
    j = problem([got.outcome])
    if j is not None:
        return Judgement(j.status, f"{drew} {got.show()}: {j.why}")
    if got.outcome.values not in {r.values for r in results}:
        return Judgement(
            FAILED,
            f"{drew} returns {show_values(got.outcome.values)}, which the test"
            " does not declare",
        )
    return None
