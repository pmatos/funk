"""Writes the corpus of #241's conversions between float formats
(docs/decisions/testing-and-harness-floats.md#the-format-conversion-corpus).

Usage: python scripts/harness/float_convert_cases.py
       python scripts/harness/float_convert_cases.py --write

It prints, or with `--write` writes, the modules and tests of
`tests/fir/canonical/` named in `FILES`. Each ordered pair of two aliased
formats takes one op: `fpext` when the target has at least as many
exponent bits and as many mantissa bits as the source, and `fptrunc`,
with `round(rne)`, otherwise (the human's ruling of 2026-11-12 on #354),
`bf16` to `f16` and `f16` to `bf16` included. Each pair `S` to `T` has one
module, `float-OP-S-T`, whose one function `@S_T` converts a value of `S`
to `T` with the pair's op: nine take `fpext` and eleven `fptrunc`. The
backend lowers two of them, `f32` to `f64` and `f64` to `f32`.

`test_float_convert_cases.py` checks that the committed files hold exactly
what it writes, and checks each expected result against `float_ref.py`
again.

The cases are the source's own edges: both zeros and infinities, `1`, its
smallest and largest subnormals, its smallest normal and its largest
finite value; and, where the source holds them, the target's edges: its
largest finite value, the value halfway past it, which rounds to an
infinity, and the source's values next to it; its smallest subnormal,
half of it, which rounds to zero, and the source's values next to it, and
the subnormals halfway between two; and the values halfway between `1` and
the target's next value, and three halves of the way, which round to the
even neighbour, with the source's values next to them. Each finite case
comes with its negation. Each expected result is what `float_ref.py`
computes, apart from Lean.

- A result that is not a NaN is one bit pattern, so from `f32` to `f64`
  and from `f64` to `f32` its case is a differential test, and an interpreter-only test
  too, which checks `fir-ref` against the reference. Every other case is
  interpreter-only.
- A NaN operand gives any NaN of the target, so each such case is
  interpreter-only, with a choice that names the NaN, as in the arithmetic
  corpus. Native code is not compared on a NaN result until #219 decides
  how a NaN result is judged.
- A poison operand gives poison, in each conversion.
"""

import sys
from fractions import Fraction

import float_ref as ref
from float_arith_cases import CANONICAL, DIFFERENTIAL, FORMATS, NAN_CHOICES, nan_bits
from float_ref import TWO, Format
from float_text import spell


def holds_every_value(s: str, t: str) -> bool:
    """Whether the format `t` holds every value of `s`: it has at least as
    many exponent bits and as many mantissa bits."""
    (e, m), (e2, m2) = FORMATS[s], FORMATS[t]
    return e <= e2 and m <= m2


def op_of(s: str, t: str) -> str:
    """The op that converts from `s` to `t`."""
    return "fpext" if holds_every_value(s, t) else "fptrunc"


# Every ordered pair of two aliased formats, and the module of each.
PAIRS = [(s, t) for s in FORMATS for t in FORMATS if s != t]
FILES = [f"float-{op_of(s, t)}-{s}-{t}" for s, t in PAIRS]


def pair(module: str) -> tuple[str, str]:
    """The formats that `module` converts from and to."""
    _, _, s, t = module.split("-")
    return s, t


def is_native(module: str) -> bool:
    """Whether the backend lowers `module`'s conversion."""
    return all(t in DIFFERENTIAL for t in pair(module))


def largest(f: Format) -> Fraction:
    """The largest finite value of `f`."""
    return (2 ** (f.m + 1) - 1) * TWO ** (f.emax - f.m)


def tiniest(f: Format) -> Fraction:
    """The smallest subnormal of `f`."""
    return TWO ** (f.emin - f.m)


def exact_bits(f: Format, x: Fraction) -> int | None:
    """The bits of `x` in `f`, if `f` holds it."""
    b = f.round(x)
    return b if f.decode(b) == ("fin", x) else None


def edges(f: Format, g: Format) -> list[int]:
    """The bits of `f` whose conversion to `g` is an edge, positive."""
    out = [f.zero(), f.inf(), f.exact(Fraction(1)), 1, 2**f.m - 1, 2**f.m]
    out.append(f.round(largest(f)))
    big, tiny = largest(g), tiniest(g)
    ulp = TWO**-g.m
    halfway = [
        big + TWO ** (g.emax - g.m - 1),
        tiny / 2,
        3 * tiny / 2,
        5 * tiny / 2,
        1 + ulp / 2,
        1 + 3 * ulp / 2,
    ]
    for x in [big, TWO**g.emin, tiny, *halfway]:
        b = exact_bits(f, x)
        if b is None:
            continue
        out.append(b)
        if x in halfway:
            # The source's values next to a halfway value, which round
            # away from the tie.
            out += [b - 1, b + 1]
    return sorted(set(out))


def values(f: Format, g: Format) -> list[int]:
    """The cases of `f` converted to `g`, as bits: the edges, their
    negations, and NaNs."""
    pos = edges(f, g)
    nans = [f.nan(), f.inf() | 1, f.sign_bit | f.inf() | (2**f.m - 1)]
    return pos + [b | f.sign_bit for b in pos] + nans


def func_text(s: str, t: str) -> str:
    op = op_of(s, t)
    attr = " round(rne)" if op == "fptrunc" else ""
    return (
        f"func @{s}_{t}(%a: {s}) -> {t} {{\n^entry:\n"
        f"  %r: {t} = {op}{attr} %a @0\n  ret %r @0\n}}\n"
    )


def module_text(module: str) -> str:
    return func_text(*pair(module)) + "\nlocs {\n  @0 = unknown\n}\n"


def tests_text(module: str) -> str:
    native = is_native(module)
    s, t = pair(module)
    head = [
        f"# Tests of {module}.fir: {op_of(s, t)} from {s} to {t}",
        "# (ADR-2026-11-09-1549) on the edges of the source and of the target:",
        "# zeros, subnormals, the largest finite values, the values halfway",
        "# between two values of the target and next to them, overflow to",
        "# infinity, underflow to zero, infinities and NaNs. Written by",
        "# scripts/harness/float_convert_cases.py, which computes each expected",
        "# result with scripts/harness/float_ref.py, apart from Lean.",
    ]
    if native:
        head += [
            "# A test without expect is differential: fir-ref and native code",
            "# run it, and the native result must equal fir-ref's. Each",
            "# result that is not a NaN is also checked by an interpreter-only",
            "# test with expect.",
        ]
    else:
        head += [
            "# Each test is interpreter-only: the backend does not lower",
            f"# {s} and {t} both, so fir-ref alone runs it and must give what it",
            "# expects.",
        ]
    head += [
        "# A NaN operand gives any NaN of the target: its test is",
        "# interpreter-only and names the NaN by a choice of the sign and the",
        "# mantissa. Native code is not compared on a NaN result yet (#219).",
    ]
    lines = []
    f, g = Format(*FORMATS[s]), Format(*FORMATS[t])
    name = f"@{s}_{t}"
    nans = 0
    for b in values(f, g):
        arg = spell(f.e, f.m, b)
        r = ref.convert(f, g, b)
        if g.decode(r) == ("nan",):
            c = NAN_CHOICES[nans % len(NAN_CHOICES)]
            nans += 1
            want = spell(g.e, g.m, nan_bits(g, c))
            lines.append(
                f'  {{ func = "{name}", args = ["{arg}"], choices = ["{c}"], '
                f'expect = ["{want}"] }},'
            )
            continue
        if native:
            lines.append(f'  {{ func = "{name}", args = ["{arg}"] }},')
        lines.append(
            f'  {{ func = "{name}", args = ["{arg}"], '
            f'expect = ["{spell(g.e, g.m, r)}"] }},'
        )
    if native:
        lines.append(f'  {{ func = "{name}", args = ["poison"] }},')
    lines.append(f'  {{ func = "{name}", args = ["poison"], expect = ["poison"] }},')
    return "\n".join(head) + "\ntests = [\n" + "\n".join(lines) + "\n]\n"


def files() -> dict[str, str]:
    """Every file this writes, by its path below `tests/fir/canonical/`."""
    out = {}
    for module in FILES:
        out[f"{module}.fir"] = module_text(module)
        out[f"{module}.toml"] = tests_text(module)
    return out


def main(argv: list[str]) -> int:
    if argv not in ([], ["--write"]):
        print(__doc__.split("\n\n")[1], file=sys.stderr)
        return 2
    for path, text in files().items():
        if argv:
            (CANONICAL / path).write_text(text, encoding="utf-8")
        else:
            sys.stdout.write(f"==> {path}\n{text}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
