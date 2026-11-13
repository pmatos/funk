"""Writes the corpus of #241's conversions from floats to integers
(docs/decisions/testing-and-harness-floats.md#the-float-to-integer-corpus).

Usage: python scripts/harness/float_fptoi_cases.py
       python scripts/harness/float_fptoi_cases.py --write

It prints, or with `--write` writes, the modules and tests of
`tests/fir/canonical/` named in `FILES`:

- at each of `f16`, `bf16`, `f32`, `f64` and `f128`, one module
  `float-fptosi-FORMAT` with `@s_iW`, which converts the format to `iW`
  with `fptosi`, and one `float-fptoui-FORMAT` with `@u_iW`, which does
  with `fptoui`, at each width that the backend lowers: `i1`, `i8`, `i16`,
  `i32`, `i64` and `i128`;
- one module `float-fptosi-odd` and one `float-fptoui-odd`, with the same
  conversions from each format to `i7` and `i33`, which the backend does
  not lower: `@s_f16_i7`, `@u_f16_i7` and so on.

`test_float_fptoi_cases.py` checks that the committed files hold exactly
what it writes, and checks each expected result against `float_ref.py`
again.

Both ops truncate toward zero (the human's ruling of 2026-11-12 on #354),
and an integer that `iW` does not hold, an infinity or a NaN gives poison.
The cases are both zeros, the smallest subnormal, `0.5`, `1`, `1.5`,
`2.7` and `3`, the largest finite value, the infinities, and a NaN with
and without a payload, each of either sign; and at each end of the
width's range, the two floats on either side of where the truncated
integer leaves it: the largest below `hi + 1` and the smallest from it on,
and the same below `lo - 1`, as well as `lo` itself when `fptosi`'s
minimum is a float. Each expected result is what `float_ref.py` decodes,
truncated toward zero by Python's `int`, apart from Lean.

- A conversion gives one integer or poison, never a choice, so at `f32`
  and `f64`, which the backend lowers, each case of a width it lowers is
  a differential test, where native code refines `fir-ref`'s poison with
  any value, and an interpreter-only test too, which checks `fir-ref`
  against the reference. Every other case is interpreter-only.
- A poison operand gives poison, in each conversion.
"""

import sys
from fractions import Fraction

from float_arith_cases import DIFFERENTIAL, FORMATS, write_corpus
from float_itofp_cases import ODD_WIDTHS, WIDTHS, int_text, span
from float_ref import Format
from float_text import spell

OPS = (("s", "fptosi", True), ("u", "fptoui", False))
FILES = [f"float-{op}-{t}" for _, op, _ in OPS for t in (*FORMATS, "odd")]


def value(f: Format, b: int) -> Fraction | None:
    """The number that the bits `b` of `f` encode, or None for an infinity
    or a NaN."""
    d = f.decode(b)
    if d[0] == "zero":
        return Fraction(0)
    return d[1] if d[0] == "fin" else None


def largest(f: Format) -> int:
    """The bits of the largest finite value of `f`."""
    return f.inf() - 1


def below(f: Format, v: Fraction) -> int:
    """The bits of the largest float of `f` below the positive `v`."""
    b = min(f.round(v), largest(f))
    while value(f, b) >= v:
        b -= 1
    return b


def from_on(f: Format, v: Fraction) -> int:
    """The bits of the smallest float of `f` from the positive `v` on, an
    infinity past the largest finite value."""
    b = f.round(v)
    if b != f.inf() and value(f, b) < v:
        b += 1
    return b


def floats(f: Format, w: int, signed: bool) -> list[int]:
    """The cases of `f` converted to `iW`, as bits, in order."""
    lo, hi = span(w, signed)
    pos = [f.zero(), 1, largest(f), f.inf()]
    pos += [f.round(Fraction(x)) for x in ("1/2", "1", "3/2", "27/10", "3")]
    pos += [below(f, Fraction(hi + 1)), from_on(f, Fraction(hi + 1))]
    neg = [below(f, Fraction(1 - lo)), from_on(f, Fraction(1 - lo))]
    if signed:
        neg.append(from_on(f, Fraction(-lo)))
    out = pos + [b | f.sign_bit for b in pos + neg]
    out += [f.nan(), f.nan() | 1 | f.sign_bit]
    return sorted(set(out))


def expected(f: Format, w: int, signed: bool, b: int) -> str:
    """What the conversion of the bits `b` of `f` to `iW` gives: the number
    truncated toward zero when `iW` holds it, and poison otherwise."""
    x = value(f, b)
    lo, hi = span(w, signed)
    if x is None or not lo <= int(x) <= hi:
        return "poison"
    return int_text(w, int(x))


def func_text(name: str, op: str, t: str, w: int) -> str:
    return f"func @{name}(%a: {t}) -> i{w} {{\n^entry:\n  %r: i{w} = {op} %a @0\n  ret %r @0\n}}\n"


def functions(module: str) -> list[tuple[str, str, str, int, bool]]:
    """The functions of `module`: each name, op, format, width and whether
    it gives a signed integer."""
    _, op, t = module.split("-")
    [(p, s)] = [(p, s) for p, o, s in OPS if o == op]
    if t == "odd":
        return [(f"{p}_{f}_i{w}", op, f, w, s) for f in FORMATS for w in ODD_WIDTHS]
    return [(f"{p}_i{w}", op, t, w, s) for w in WIDTHS]


def module_text(module: str) -> str:
    funcs = [func_text(n, op, t, w) for n, op, t, w, _ in functions(module)]
    return "\n".join(funcs) + "\nlocs {\n  @0 = unknown\n}\n"


def tests_text(module: str) -> str:
    native = module.split("-")[-1] in DIFFERENTIAL
    head = [
        f"# Tests of {module}.fir: conversions to integers, truncated toward zero",
        "# (ADR-2026-11-09-1549; the human's ruling of 2026-11-12 on #354), on",
        "# the zeros, the smallest subnormal, small fractions, the largest",
        "# finite values, infinities and NaNs, and the floats on either side of",
        "# each end of the width's range. Written by",
        "# scripts/harness/float_fptoi_cases.py, which decodes each case with",
        "# scripts/harness/float_ref.py, apart from Lean.",
    ]
    if native:
        head += [
            "# A test without expect is differential: fir-ref and native code",
            "# run it, and the native result must refine fir-ref's, any value",
            "# where it is poison. Each case is also checked by an",
            "# interpreter-only test with expect.",
        ]
    else:
        head += [
            "# Each test is interpreter-only: the backend does not lower this",
            "# module's formats or widths, so fir-ref alone runs it and must",
            "# give what it expects.",
        ]
    lines = []
    for name, _, t, w, signed in functions(module):
        e, m = FORMATS[t]
        f = Format(e, m)
        cases = [
            (spell(e, m, b), expected(f, w, signed, b)) for b in floats(f, w, signed)
        ]
        cases.append(("poison", "poison"))
        for arg, want in cases:
            if native:
                lines.append(f'  {{ func = "@{name}", args = ["{arg}"] }},')
            lines.append(
                f'  {{ func = "@{name}", args = ["{arg}"], expect = ["{want}"] }},'
            )
    return "\n".join(head) + "\ntests = [\n" + "\n".join(lines) + "\n]\n"


def files() -> dict[str, str]:
    """Every file this writes, by its path below `tests/fir/canonical/`."""
    out = {}
    for module in FILES:
        out[f"{module}.fir"] = module_text(module)
        out[f"{module}.toml"] = tests_text(module)
    return out


def main(argv: list[str]) -> int:
    return write_corpus(argv, __doc__.split("\n\n")[1], files())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
