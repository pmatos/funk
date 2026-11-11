"""Writes the corpus of #229's float arithmetic (ADR-2026-11-11-1803).

Usage: python scripts/harness/float_arith_cases.py
       python scripts/harness/float_arith_cases.py --write

It prints, or with `--write` writes, the modules and tests of
`tests/fir/canonical/` named in `FILES`: at each of `f16`, `bf16`, `f32`,
`f64` and `f128`, one module of `fadd`, `fsub`, `fmul` and `fdiv`
(`float-binary-FORMAT`) and one of `fneg`, `fabs`, `sqrt` and `fma`
(`float-unary-fma-FORMAT`). `test_float_arith_cases.py` checks that the
committed files hold exactly what it writes, and checks each expected
result against `float_ref.py` again.

The cases are the hard inputs of `float_cases.hard_cases`: results halfway
between two floats, subnormals, `-0`, overflow to infinity and NaN
operands, with each case of `fsub` and `fdiv` in both operand orders, and a
poison operand for each op. Each expected result is what `float_ref.py`
computes, apart from Lean, rounding to nearest even.

- A result that is not a NaN is one bit pattern. At `f32` and `f64`, which
  the backend lowers, its case is a differential test, and an
  interpreter-only test too, which checks `fir-ref` against the reference;
  at the other formats it is interpreter-only.
- A NaN result is any NaN of the format, and `fir-ref` chooses its sign and
  mantissa, so each such case is interpreter-only, with a choice that
  names the NaN: the quiet NaN, every bit set, or the signalling NaN with
  the lowest mantissa bit, in turn. Native code is not compared on a NaN
  result until #219 decides how a NaN result is judged.
- A poison operand gives poison: differential at `f32` and `f64`, and
  interpreter-only elsewhere.
"""

import sys
from pathlib import Path

import float_cases
import float_ref as ref
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

# Each module: its name before the format, and its ops with their number
# of operands and the name of their cases in `float_cases.hard_cases`.
MODULES = {
    "float-binary": [
        ("fadd", 2, "fadd"),
        ("fsub", 2, "fsub"),
        ("fmul", 2, "fmul"),
        ("fdiv", 2, "fdiv"),
    ],
    "float-unary-fma": [
        ("fneg", 1, "fneg"),
        ("fabs", 1, "fabs"),
        ("sqrt", 1, "fsqrt"),
        ("fma", 3, "ffma"),
    ],
}
FILES = [f"{m}-{t}" for m in MODULES for t in FORMATS]

# The choices of a NaN result, in turn: `m + 1` bits, the top one the
# sign, read as a signed integer.
NAN_CHOICES = (0, -1, 1)


def result(f: Format, op: str, bits: list[int]) -> int:
    """The reference's result of `op` on `bits`."""
    return {
        "fadd": lambda a, b: ref.add(f, a, b),
        "fsub": lambda a, b: ref.sub(f, a, b),
        "fmul": lambda a, b: ref.mul(f, a, b),
        "fdiv": lambda a, b: ref.div(f, a, b),
        "fneg": lambda a: ref.negate(f, a),
        "fabs": lambda a: ref.fabs(f, a),
        "sqrt": lambda a: ref.sqrt(f, a),
        "fma": lambda a, b, c: ref.fma(f, a, b, c),
    }[op](*bits)


def is_nan(f: Format, b: int) -> bool:
    return f.decode(b) == ("nan",)


def nan_bits(f: Format, c: int) -> int:
    """The NaN that the choice `c` of `m + 1` bits names (`nanBits` in
    `lean/Fir/Core/FloatArith.lean`): sign `c`'s top bit, the exponent all
    ones, and `c`'s low `m` bits as the mantissa, or the quiet bit alone
    when they are zero."""
    c %= 2 ** (f.m + 1)
    payload = c % 2**f.m
    mantissa = payload or 2 ** (f.m - 1)
    return (c >> f.m) * f.sign_bit | f.top << f.m | mantissa


def cases(f: Format, ops: list[tuple[str, int, str]]) -> list[tuple[str, list[int]]]:
    """The cases of each op: its operands' bits."""
    hard, _ = float_cases.hard_cases(f)
    out = []
    for op, _, name in ops:
        for case_op, args, _, _ in hard:
            if case_op != name:
                continue
            bits = [float_cases.bits_of(f, a) for a in args]
            out.append((op, bits))
            if op in ("fsub", "fdiv") and bits[0] != bits[1]:
                out.append((op, bits[::-1]))
    return out


def module_text(t: str, ops: list[tuple[str, int, str]]) -> str:
    """The module of one function for each op, at the type `t`."""
    out = []
    for op, n, _ in ops:
        params = ", ".join(f"%{x}: {t}" for x in "abc"[:n])
        attr = "" if op in ("fneg", "fabs") else " round(rne)"
        operands = ", ".join(f"%{x}" for x in "abc"[:n])
        out.append(
            f"func @{op}({params}) -> {t} {{\n^entry:\n"
            f"  %r: {t} = {op}{attr} {operands} @0\n  ret %r @0\n}}\n"
        )
    return "\n".join(out) + "\nlocs {\n  @0 = unknown\n}\n"


def tests_text(name: str, t: str, ops: list[tuple[str, int, str]]) -> str:
    """The tests of the module `name` at the type `t`."""
    e, m = FORMATS[t]
    f = Format(e, m)
    names = ", ".join(op for op, _, _ in ops)
    native = t in DIFFERENTIAL
    head = [
        f"# Tests of {name}.fir: {names} at {t}",
        "# (ADR-2026-11-11-1800), on the hard inputs: results halfway between",
        "# two floats, subnormals, -0, overflow to infinity and NaN operands.",
        "# Written by scripts/harness/float_arith_cases.py, which computes each",
        "# expected result with scripts/harness/float_ref.py, apart from Lean.",
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
            f"# {t}, so fir-ref alone runs it and must give what it expects.",
        ]
    head += [
        "# A NaN result is any NaN: its test is interpreter-only and names",
        "# the NaN by a choice of the sign and the mantissa, as signed",
        f"# i{m + 1}. Native code is not compared on a NaN result yet (#219).",
    ]
    lines = []
    turn = 0
    for op, bits in cases(f, ops):
        args = ", ".join(f'"{spell(e, m, b)}"' for b in bits)
        r = result(f, op, bits)
        if is_nan(f, r):
            c = NAN_CHOICES[turn % len(NAN_CHOICES)]
            turn += 1
            want = spell(e, m, nan_bits(f, c))
            lines.append(
                f'  {{ func = "@{op}", args = [{args}], choices = ["{c}"], '
                f'expect = ["{want}"] }},'
            )
            continue
        if native:
            lines.append(f'  {{ func = "@{op}", args = [{args}] }},')
        lines.append(
            f'  {{ func = "@{op}", args = [{args}], expect = ["{spell(e, m, r)}"] }},'
        )
    for op, n, _ in ops:
        args = ", ".join(['"poison"'] + [f'"{spell(e, m, f.zero())}"'] * (n - 1))
        if native:
            lines.append(f'  {{ func = "@{op}", args = [{args}] }},')
        else:
            lines.append(
                f'  {{ func = "@{op}", args = [{args}], expect = ["poison"] }},'
            )
    return "\n".join(head) + "\ntests = [\n" + "\n".join(lines) + "\n]\n"


def files() -> dict[str, str]:
    """Every file this writes, by its path below `tests/fir/canonical/`."""
    out = {}
    for name, ops in MODULES.items():
        for t in FORMATS:
            out[f"{name}-{t}.fir"] = module_text(t, ops)
            out[f"{name}-{t}.toml"] = tests_text(f"{name}-{t}", t, ops)
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
