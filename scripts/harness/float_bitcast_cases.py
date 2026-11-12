"""Writes the corpus of #241's bit casts
(docs/decisions/testing-and-harness-floats.md#the-bit-cast-corpus).

Usage: python scripts/harness/float_bitcast_cases.py
       python scripts/harness/float_bitcast_cases.py --write

It prints, or with `--write` writes, the modules and tests of
`tests/fir/canonical/` named in `FILES`: at each of `f16`, `bf16`, `f32`,
`f64` and `f128`, one module `float-bitcast-FORMAT` with `@to_bits`, which
casts a float to the integer of its width, and `@of_bits`, which casts that
integer to the float. `test_float_bitcast_cases.py` checks that the
committed files hold exactly what it writes, and checks each expected
result against `float_ref.py`'s reading of the bits.

The cases are the bit patterns that each kind of float has at its edges:
zeros of both signs, the smallest and largest subnormals, the smallest
normal, one, the largest finite values, infinities, and NaNs, quiet and
signalling, with payloads and either sign. A bit cast gives its operand's
bits, so each expected result is the case's own bits, spelled as the other
type: a float as its shortest decimal or its hexadecimal bits
(ADR-2026-11-11-1438), and an integer as its bits read as a signed integer.

- At `f32` and `f64`, which the backend lowers, each case is a
  differential test, and an interpreter-only test too, which checks
  `fir-ref` against the expected bits; at the other formats it is
  interpreter-only. A NaN is an operand or a result like any other value
  here, since no op chooses it, so its cases are differential too.
- A poison operand gives poison, in each direction.
"""

import sys
from pathlib import Path

from float_ref import Format
from float_text import spell

ROOT = Path(__file__).resolve().parents[2]
CANONICAL = ROOT / "tests" / "fir" / "canonical"

FORMATS = {
    "f16": (5, 10),
    "bf16": (8, 7),
    "f32": (8, 23),
    "f64": (11, 52),
    "f128": (15, 112),
}
DIFFERENTIAL = ("f32", "f64")
FILES = [f"float-bitcast-{t}" for t in FORMATS]


def edges(f: Format) -> list[int]:
    """The bit patterns of `f` at the edges of each kind of float."""
    quiet = 1 << (f.m - 1)
    largest = (f.top - 1) << f.m | (2**f.m - 1)
    out = [
        f.zero(),
        f.zero(neg=True),
        1,
        f.sign_bit | 1,
        2**f.m - 1,
        1 << f.m,
        f.exact(1),
        f.exact(-1),
        largest,
        f.sign_bit | largest,
        f.inf(),
        f.inf(neg=True),
        f.nan(),
        f.sign_bit | f.top << f.m | quiet | 1,
        f.top << f.m | 1,
        2**f.nbits - 1,
    ]
    return list(dict.fromkeys(out))


def signed(f: Format, b: int) -> str:
    """The bits `b` of `iN`, with `N` the width of `f`, read as a signed
    integer."""
    return str(b - 2**f.nbits if b & f.sign_bit else b)


def module_text(t: str) -> str:
    """The module of `@to_bits` and `@of_bits` at the float type `t`."""
    e, m = FORMATS[t]
    i = f"i{1 + e + m}"
    return (
        f"func @to_bits(%a: {t}) -> {i} {{\n^entry:\n"
        f"  %r: {i} = bitcast %a @0\n  ret %r @0\n}}\n\n"
        f"func @of_bits(%a: {i}) -> {t} {{\n^entry:\n"
        f"  %r: {t} = bitcast %a @0\n  ret %r @0\n}}\n\n"
        "locs {\n  @0 = unknown\n}\n"
    )


def tests_text(t: str) -> str:
    """The tests of `float-bitcast-t`."""
    e, m = FORMATS[t]
    f = Format(e, m)
    native = t in DIFFERENTIAL
    head = [
        f"# Tests of float-bitcast-{t}.fir: bitcast from {t} to i{f.nbits} and",
        "# back (ADR-2026-11-09-1549), on zeros of both signs, subnormals, the",
        "# smallest normal, one, the largest finite values, infinities and",
        "# NaNs with payloads and either sign. Each result is its operand's",
        "# bits. Written by scripts/harness/float_bitcast_cases.py.",
    ]
    if native:
        head += [
            "# A test without expect is differential: fir-ref and native code",
            "# run it, and the native result must equal fir-ref's. Each case",
            "# is also checked by an interpreter-only test with expect.",
        ]
    else:
        head += [
            "# Each test is interpreter-only: the backend does not lower",
            f"# {t}, so fir-ref alone runs it and must give what it expects.",
        ]
    lines = []
    for b in edges(f):
        for func, arg, want in (
            ("@to_bits", spell(e, m, b), signed(f, b)),
            ("@of_bits", signed(f, b), spell(e, m, b)),
        ):
            if native:
                lines.append(f'  {{ func = "{func}", args = ["{arg}"] }},')
            lines.append(
                f'  {{ func = "{func}", args = ["{arg}"], expect = ["{want}"] }},'
            )
    for func in ("@to_bits", "@of_bits"):
        if native:
            lines.append(f'  {{ func = "{func}", args = ["poison"] }},')
        else:
            lines.append(
                f'  {{ func = "{func}", args = ["poison"], expect = ["poison"] }},'
            )
    return "\n".join(head) + "\ntests = [\n" + "\n".join(lines) + "\n]\n"


def files() -> dict[str, str]:
    """Every file this writes, by its path below `tests/fir/canonical/`."""
    out = {}
    for t in FORMATS:
        out[f"float-bitcast-{t}.fir"] = module_text(t)
        out[f"float-bitcast-{t}.toml"] = tests_text(t)
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
