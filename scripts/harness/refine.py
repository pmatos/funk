"""How the harness judges a test (ADR-2026-10-30-2135, ADR-2026-10-29-2008).

A differential test passes when the native result refines fir-ref's: the
same number of values, each equal to fir-ref's, or anything of its type
where fir-ref returns poison. A test whose fir-ref result is UB or fuel
exhausted proves nothing, so it is invalid, never a pass. A stuck run of a
valid module is a failure (NeverStuck). An interpreter-only test passes
when fir-ref gives the result it expects; an expected UB matches any reason.
`sets.py` judges a run that makes choices by its set of outcomes. A native
run that outgrows its stack proves nothing either, so it makes its test
invalid, as a run out of fuel does on the other side (ADR-2026-11-09-1602).
"""

import re
from dataclasses import dataclass

import float_text

POISON = "poison"
UB = "ub"
FUEL_EXHAUSTED = "fuel-exhausted"
STUCK = "stuck"
RETURN = "return"

PASSED = "passed"
FAILED = "failed"
INVALID = "invalid"

DECIMAL = re.compile(r"-?(0|[1-9][0-9]*)")
INT_TYPE = re.compile(r"i([1-9][0-9]*)")
FLOAT_TYPE = re.compile(r"float\(([0-9]+), ([0-9]+)\)")
# The float formats with an alias, as `(e, m)` (ADR-2026-11-11-0951).
FLOAT_ALIASES = {
    "f16": (5, 10),
    "bf16": (8, 7),
    "f32": (8, 23),
    "f64": (11, 52),
    "f128": (15, 112),
}


def float_format(ty: str) -> tuple[int, int] | None:
    """`(e, m)` for the float type `float<e,m>`, by its alias or as
    `float(e, m)`, and None for any other type."""
    fmt = FLOAT_ALIASES.get(ty)
    if fmt is None:
        f = FLOAT_TYPE.fullmatch(ty)
        if f is None:
            return None
        fmt = int(f.group(1)), int(f.group(2))
    return fmt


def bits_of(ty: str) -> tuple[int, bool] | None:
    """The bits of a value of `ty`, and whether it is an integer type: `N`
    for `iN`, and `1 + e + m` for `float<e,m>`. None for any other type,
    such as `ptr`, whose values are pointers, not bits."""
    m = INT_TYPE.fullmatch(ty)
    if m is not None:
        return int(m.group(1)), True
    fmt = float_format(ty)
    if fmt is None:
        return None
    return 1 + fmt[0] + fmt[1], False


@dataclass(frozen=True)
class Outcome:
    """What `fir-ref run` reports for one run."""

    kind: str
    values: tuple[str, ...] = ()
    reason: str = ""

    def show(self) -> str:
        if self.kind == RETURN:
            return "returns " + show_values(self.values)
        if self.kind == FUEL_EXHAUSTED:
            return "runs out of fuel"
        what = "is stuck" if self.kind == STUCK else "hits UB"
        return f"{what} ({self.reason})" if self.reason else what


@dataclass(frozen=True)
class Judgement:
    status: str
    why: str = ""


@dataclass(frozen=True)
class OutOfStack:
    """A native run that reported that it outgrew the bytes of stack it
    reserved. That is a limit of the run, not a wrong result."""

    size: int

    def show(self) -> str:
        return f"runs out of its {self.size} bytes of stack"

    def judgement(self) -> Judgement:
        return Judgement(
            INVALID,
            f"native code outgrew its {self.size} bytes of stack, so the test"
            " proves nothing: recurse less deep, or raise ulimit -s",
        )


def show_values(values) -> str:
    return "[" + ", ".join(f'"{v}"' for v in values) + "]"


def is_value(spelling: str, ty: str) -> bool:
    """Whether `spelling` is a value of type `ty`, spelled as a constant."""
    b = bits_of(ty)
    if b is None:
        return False
    width, is_int = b
    if not is_int:
        # A float is the one float literal of its bits (ADR-2026-11-11-1438).
        e, m = float_format(ty)
        return float_text.decode(e, m, spelling) is not None
    if width == 1:
        return spelling in ("true", "false")
    if DECIMAL.fullmatch(spelling) is None or spelling == "-0":
        return False
    digits = len(spelling.lstrip("-"))
    if digits > width:
        return False
    bound = 1 << (width - 1)
    return -bound <= int(spelling) < bound


def refines(ref: Outcome, native, types) -> Judgement:
    """Judges a differential test.

    `native` is the list of values that native code returns, or a string
    saying how it failed. `types` are the function's result types.
    """
    if ref.kind == UB:
        return Judgement(INVALID, "UB allows any result, so the test proves nothing")
    if ref.kind == FUEL_EXHAUSTED:
        return Judgement(
            INVALID,
            "the result depends on the fuel budget: raise the test's budget, or"
            " make it an interpreter-only test that expects fuel-exhausted",
        )
    if ref.kind == STUCK:
        return Judgement(FAILED, "no run of a valid module is stuck")
    if isinstance(native, OutOfStack):
        return native.judgement()
    if isinstance(native, str):
        return Judgement(FAILED, "native code fails where fir-ref returns")
    if len(native) != len(ref.values):
        return Judgement(
            FAILED,
            f"fir-ref returns {len(ref.values)} values and native code {len(native)}",
        )
    if len(types) != len(ref.values):
        return Judgement(
            FAILED, f"the function returns {len(types)} values, not {len(ref.values)}"
        )
    for i, (want, got, ty) in enumerate(zip(ref.values, native, types), 1):
        if want == POISON:
            if not is_value(got, ty):
                return Judgement(FAILED, f"value {i}, {got}, is not a value of {ty}")
        elif got != want:
            return Judgement(FAILED, f"value {i} is {got}, not {want}")
    return Judgement(PASSED)


def expected(ref: Outcome, expect) -> Judgement:
    """Judges an interpreter-only test that expects `expect`: a tuple of
    values, each a value or poison, or UB or fuel exhausted."""
    if ref.kind == STUCK:
        return Judgement(FAILED, "no run of a valid module is stuck")
    if isinstance(expect, tuple):
        if ref.kind == RETURN and ref.values == expect:
            return Judgement(PASSED)
        return Judgement(FAILED, "the test expects " + show_values(expect))
    if ref.kind == expect:
        return Judgement(PASSED)
    return Judgement(FAILED, f"the test expects {expect}")
