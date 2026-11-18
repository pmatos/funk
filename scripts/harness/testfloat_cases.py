"""Berkeley TestFloat's vectors as checks of `fir-ref`
(docs/decisions/testing-and-harness-float-references.md#the-testfloat-check).

`testfloat.py` runs this module's checks. Here are the parts that need no
TestFloat: which function of `testfloat_gen` backs which op of fir, how a
line of its output reads, the module that runs a batch of vectors on
`fir-ref`, and how each result is judged.

A line of `testfloat_gen` is the operands, the result and the exception
flags, each in hexadecimal. The flags are ignored: M1 has no floating-point
exceptions. A NaN result is SoftFloat's default NaN, and fir's op gives any
NaN (ADR-2026-11-09-1549), so a NaN that TestFloat expects passes on any NaN
of the format; every other result passes only on its exact bits.

The module passes each operand as an integer constant and `bitcast`s it to
the float type, and each float result back to the integer, so the check
reads and compares bits, and leaves the float literal to its own tests.

TestFloat has `eq`, `le` and `lt`, and no other comparison. Each backs four
predicates of `fcmp` by IEEE 754 section 5.11: `ole a, b` is `le`, `ugt a, b`
its negation, `oge b, a` the same order read the other way, and `ult b, a`
its negation; likewise `lt` gives `olt`, `uge`, `ogt` and `ule`, and `eq`
gives `oeq` and `une`. TestFloat has no negation or absolute value, so it
backs no `fneg` and no `fabs`. Its `rem` is IEEE 754's remainder, fir's
`frem`, which has no rounding attribute; it has no `fmod`.

`bf16` is not one of TestFloat's formats. Its vectors come from TestFloat's
`f32` vectors whose operands are all `bf16` values, which are the `f32`
values whose low 16 bits are zero, and the same in both formats. The
arithmetic is generated rounding to odd, `-rodd`, and its result is rounded
once more, to nearest even at `bf16`. Rounding to odd at a precision of at
least two more bits, then to nearest, gives the correctly rounded result
(Boldo and Melquiond, "Emulation of FMA and correctly rounded sums: proved
algorithms using rounding to odd", IEEE Trans. Computers 57(4), 2008). `f32`
has 16 more mantissa bits than `bf16` at every exponent, the subnormal ones
included, since both have 8 exponent bits; and SoftFloat's round to odd
gives the largest finite `f32` for a result past it, which rounds on to the
infinity, as the exact result does. A comparison needs no rounding, and
neither does `rem`, whose vectors are generated to nearest even and whose
result is read as it is: a remainder is exact, and `bf16` has `f32`'s
exponents, so the remainder of two `bf16` values is a `bf16` value, and an
`f32` result that is not one is an error.
"""

from dataclasses import dataclass

from float_bitcast_cases import signed
from float_ref import Format

# Each format TestFloat generates.
FORMATS = {
    "f16": Format(5, 10),
    "f32": Format(8, 23),
    "f64": Format(11, 52),
    "f128": Format(15, 112),
}
F32 = FORMATS["f32"]
BF16 = Format(8, 7)
# Every format the check runs at: TestFloat's, and `bf16` from `f32`'s.
CHECKED = {**FORMATS, "bf16": BF16}

# Each arithmetic function of `testfloat_gen`: its fir op and operand count.
ARITHMETIC = {
    "add": ("fadd round(rne)", 2),
    "sub": ("fsub round(rne)", 2),
    "mul": ("fmul round(rne)", 2),
    "div": ("fdiv round(rne)", 2),
    "sqrt": ("sqrt round(rne)", 1),
    "mulAdd": ("fma round(rne)", 3),
    "rem": ("frem", 2),
}
# The arithmetic whose result is exact, so a `bf16` vector needs no rounding.
EXACT = {"rem"}

# Each comparison of `testfloat_gen`: the predicates it backs, each with
# whether it swaps the operands and whether it negates TestFloat's answer.
COMPARISONS = {
    "eq": (("oeq", False, False), ("une", False, True)),
    "le": (
        ("ole", False, False),
        ("ugt", False, True),
        ("oge", True, False),
        ("ult", True, True),
    ),
    "lt": (
        ("olt", False, False),
        ("uge", False, True),
        ("ogt", True, False),
        ("ule", True, True),
    ),
}

# Level 1 of `mulAdd` has 6,133,248 vectors at every format; the check takes
# every 131st, 46,819 of them. 131 is prime: a stride of 132, which divides
# the count, would keep only 6 values of the third operand.
MULADD_STRIDE = 131


@dataclass(frozen=True)
class Vector:
    """One line of `testfloat_gen`: operand bits, and the result's bits, or
    0 or 1 for a comparison."""

    operands: tuple[int, ...]
    result: int


def functions() -> list[str]:
    """The functions of `testfloat_gen` the check runs at each format."""
    return list(ARITHMETIC) + list(COMPARISONS)


def arity(function: str) -> int:
    return ARITHMETIC[function][1] if function in ARITHMETIC else 2


def parse(function: str, line: str) -> Vector:
    """Reads one line of `testfloat_gen FORMAT_FUNCTION`, flags ignored."""
    fields = line.split()
    n = arity(function)
    if len(fields) != n + 2:
        raise ValueError(f"{function}: not a vector: {line!r}")
    values = [int(f, 16) for f in fields[: n + 1]]
    return Vector(tuple(values[:n]), values[n])


def is_nan(f: Format, bits: int) -> bool:
    # Bit tests, not `Format.decode`, which builds a fraction for every
    # finite value: this runs on each of about 1.7 million results.
    return (bits >> f.m) & f.top == f.top and bits & ((1 << f.m) - 1) != 0


def is_bf16(bits: int) -> bool:
    """Whether an `f32` is also a `bf16`: its low 16 bits are zero."""
    return bits & 0xFFFF == 0


def round_to_bf16(bits: int) -> int:
    """Rounds an `f32` to `bf16`, to nearest even. A NaN stays a NaN: its
    top 16 bits keep the all-ones exponent, and a quiet bit is set."""
    if is_nan(F32, bits):
        return (bits >> 16) | 0x40
    upper, lower = bits >> 16, bits & 0xFFFF
    if lower > 0x8000 or (lower == 0x8000 and upper & 1):
        upper += 1
    return upper


def rounds(function: str) -> bool:
    """Whether a `bf16` vector of `function` must come from `-rodd`."""
    return function in ARITHMETIC and function not in EXACT


def to_bf16(function: str, v: Vector) -> Vector | None:
    """The `bf16` vector of an `f32` one, or None when an operand is not a
    `bf16`. A vector of a function that `rounds` must come from `-rodd`;
    an exact result that is not a `bf16` raises ValueError."""
    if not all(is_bf16(a) for a in v.operands):
        return None
    if function in COMPARISONS:
        result = v.result
    elif function in EXACT:
        if not is_bf16(v.result):
            raise ValueError(f"{function}: {v.result:08X} is not a bf16")
        result = v.result >> 16
    else:
        result = round_to_bf16(v.result)
    return Vector(tuple(a >> 16 for a in v.operands), result)


@dataclass(frozen=True)
class Check:
    """One result of a batch: the vector, the predicate for a comparison,
    and the value it must be."""

    vector: Vector
    predicate: str | None
    expected: int | bool


def checks(function: str, vectors: list[Vector]) -> list[Check]:
    if function in ARITHMETIC:
        return [Check(v, None, v.result) for v in vectors]
    return [
        Check(v, p, bool(v.result) != negate)
        for v in vectors
        for p, _, negate in COMPARISONS[function]
    ]


def module(fmt: str, function: str, vectors: list[Vector]) -> str:
    """A module whose `@v` returns one value per check of `checks`, in order:
    the bits of each arithmetic result as an integer, or each comparison's
    `i1`."""
    f = CHECKED[fmt]
    width = f.nbits
    body: list[str] = []
    results: list[str] = []
    for i, v in enumerate(vectors):
        names = []
        for j, a in enumerate(v.operands):
            body.append(f"  %x{i}_{j}: i{width} = const {signed(f, a)} @0")
            body.append(f"  %a{i}_{j}: {fmt} = bitcast %x{i}_{j} @0")
            names.append(f"%a{i}_{j}")
        if function in ARITHMETIC:
            op = ARITHMETIC[function][0]
            body.append(f"  %r{i}: {fmt} = {op} {', '.join(names)} @0")
            body.append(f"  %s{i}: i{width} = bitcast %r{i} @0")
            results.append(f"%s{i}")
            continue
        for p, swap, _ in COMPARISONS[function]:
            a, b = reversed(names) if swap else names
            body.append(f"  %{p}{i}: i1 = fcmp {p} {a}, {b} @0")
            results.append(f"%{p}{i}")
    result_type = "i1" if function in COMPARISONS else f"i{width}"
    return "\n".join(
        [
            f"func @v() -> {', '.join([result_type] * len(results))} {{",
            "^entry:",
            *body,
            f"  ret {', '.join(results)} @0",
            "}",
            "",
            "locs {",
            "  @0 = unknown",
            "}",
            "",
        ]
    )


def passes(f: Format, check: Check, value: str) -> bool:
    """Whether `fir-ref`'s value for one check is what TestFloat gives."""
    if check.predicate is not None:
        return value == ("true" if check.expected else "false")
    try:
        bits = int(value) % (1 << f.nbits)
    except ValueError:
        return False
    if is_nan(f, int(check.expected)):
        return is_nan(f, bits)
    return bits == check.expected
