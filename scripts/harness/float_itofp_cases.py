"""Writes the corpus of #241's conversions from integers to floats
(docs/decisions/testing-and-harness-floats.md#the-integer-to-float-corpus).

Usage: python scripts/harness/float_itofp_cases.py
       python scripts/harness/float_itofp_cases.py --write

It prints, or with `--write` writes, the modules and tests of
`tests/fir/canonical/` named in `FILES`:

- at each of `f16`, `bf16`, `f32`, `f64` and `f128`, one module
  `float-sitofp-FORMAT` with `@si_iW`, which converts an `iW` to the format
  with `sitofp`, and one `float-uitofp-FORMAT` with `@ui_iW`, which does
  with `uitofp`, at each width that the backend lowers: `i1`, `i8`, `i16`,
  `i32`, `i64` and `i128`;
- one module `float-itofp-odd`, with the same conversions from `i7` and
  `i33`, which the backend does not lower, to each format: `@si_i7_f16`
  and so on.

`test_float_itofp_cases.py` checks that the committed files hold exactly
what it writes, and checks each expected result against `float_ref.py`
again.

The cases are the boundary integers of each width, read as signed or as
unsigned: zero, one, minus one, the smallest and largest, and their
neighbours; the integers next to `2^p`, where `p` is the format's
precision, the largest power of two below which every integer is exact;
the integers halfway between two floats there and at the top of the
width's range, which go to the even one, and those one above them; and the
integers on either side of the format's overflow, where one rounds to the
largest finite value and the next to infinity. Each expected result is
what `float_ref.py` computes, apart from Lean: `+0` for zero, and the
integer rounded to nearest even otherwise.

- A conversion gives one bit pattern, never a NaN, so at `f32` and `f64`,
  which the backend lowers, each case of a width it lowers is a
  differential test, and an interpreter-only test too, which checks
  `fir-ref` against the reference. Every other case is interpreter-only.
- A poison operand gives poison, in each conversion.
"""

import sys
from fractions import Fraction

from float_arith_cases import CANONICAL, DIFFERENTIAL, FORMATS
from float_ref import Format
from float_text import spell

# The widths of the operand that the backend lowers, and two that it does
# not, for the interpreter only.
WIDTHS = (1, 8, 16, 32, 64, 128)
ODD_WIDTHS = (7, 33)
OPS = (("si", "sitofp", True), ("ui", "uitofp", False))
FILES = [f"float-{op}-{t}" for _, op, _ in OPS for t in FORMATS] + ["float-itofp-odd"]


def span(w: int, signed: bool) -> tuple[int, int]:
    """The smallest and largest integer that an `iW` holds."""
    return (-(2 ** (w - 1)), 2 ** (w - 1) - 1) if signed else (0, 2**w - 1)


def ties(k: int, p: int) -> list[int]:
    """At `2^k`, with `p` bits of precision: the integer halfway to the next
    float, which goes down to the even `2^k`, the one above it, the one
    below it, and the next halfway one, which goes up."""
    if k < p:
        return []
    half = 2 ** (k - p)
    base = 2**k
    return [base + half, base + half + 1, base + half - 1, base + 3 * half]


def integers(w: int, signed: bool, f: Format) -> list[int]:
    """The cases of `iW` converted to `f`, in order."""
    lo, hi = span(w, signed)
    p = f.m + 1
    out = [0, 1, -1, 2, lo, lo + 1, hi, hi - 1, 2**p - 1, 2**p, 2**p + 1]
    out += ties(p, p) + ties(hi.bit_length() - 1, p)
    # Around the largest finite value `big`: below `big + half` an integer
    # rounds to it, and from there on to infinity.
    half = 2 ** (f.emax - p)
    if half >= 1:
        big = (2**p - 1) * 2 ** (f.emax - f.m)
        out += [big, big + half - 1, big + half]
    if signed:
        out += [-x for x in out]
    return sorted({x for x in out if lo <= x <= hi})


def int_text(w: int, x: int) -> str:
    """The spelling of `x` as an argument of `iW`: its bits read as a signed
    integer, and `true` or `false` at `i1`."""
    b = x % 2**w
    if w == 1:
        return "true" if b else "false"
    return str(b - 2**w if b >= 2 ** (w - 1) else b)


def reference(f: Format, x: int) -> int:
    """The bits of the reference's result of converting `x` to `f`: `+0`
    for zero, and `x` rounded to nearest even otherwise."""
    return f.zero() if x == 0 else f.round(Fraction(x))


def expected(f: Format, x: int) -> str:
    """The spelling of the reference's result of converting `x` to `f`."""
    return spell(f.e, f.m, reference(f, x))


def func_text(name: str, op: str, w: int, t: str) -> str:
    return (
        f"func @{name}(%a: i{w}) -> {t} {{\n^entry:\n"
        f"  %r: {t} = {op} round(rne) %a @0\n  ret %r @0\n}}\n"
    )


def functions(module: str) -> list[tuple[str, str, int, str, bool]]:
    """The functions of `module`: each name, op, width, type and whether it
    reads its operand as signed."""
    if module == "float-itofp-odd":
        return [
            (f"{p}_i{w}_{t}", op, w, t, s)
            for w in ODD_WIDTHS
            for t in FORMATS
            for p, op, s in OPS
        ]
    _, op, t = module.split("-")
    return [(f"{p}_i{w}", o, w, t, s) for w in WIDTHS for p, o, s in OPS if o == op]


def module_text(module: str) -> str:
    funcs = [func_text(n, op, w, t) for n, op, w, t, _ in functions(module)]
    return "\n".join(funcs) + "\nlocs {\n  @0 = unknown\n}\n"


def tests_text(module: str) -> str:
    native = module.split("-")[-1] in DIFFERENTIAL
    head = [
        f"# Tests of {module}.fir: conversions from integers (ADR-2026-11-09-1549) on",
        "# the boundary integers of each width, the integers next to the",
        "# format's precision, the ones halfway between two floats, and the",
        "# ones on either side of overflow. Written by",
        "# scripts/harness/float_itofp_cases.py, which computes each expected",
        "# result with scripts/harness/float_ref.py, apart from Lean.",
    ]
    if native:
        head += [
            "# A test without expect is differential: fir-ref and native code",
            "# run it, and the native result must equal fir-ref's. Each case",
            "# is also checked by an interpreter-only test with expect.",
        ]
    else:
        head += [
            "# Each test is interpreter-only: the backend does not lower this",
            "# module's formats or widths, so fir-ref alone runs it and must",
            "# give what it expects.",
        ]
    lines = []
    for name, _, w, t, signed in functions(module):
        f = Format(*FORMATS[t])
        cases = [(int_text(w, x), expected(f, x)) for x in integers(w, signed, f)]
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
