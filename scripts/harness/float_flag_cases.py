"""Writes the corpus of #242's fast-math flags
(docs/decisions/testing-and-harness-floats.md#the-fast-math-flag-corpus).

Usage: python scripts/harness/float_flag_cases.py
       python scripts/harness/float_flag_cases.py --write

It prints, or with `--write` writes, the modules and tests of
`tests/fir/canonical/` named in `FILES`: at each of `f16`, `bf16`, `f32`,
`f64` and `f128`, one module, `float-flags-FORMAT`, with a function for each
float op and each flag, `nnan`, `ninf` and `nsz`, such as `@fadd_nnan`.
`test_float_flag_cases.py` checks that the committed files hold exactly what
it writes, and checks each expected result again.

Each flag's cases are ones whose outcome depends on it (ADR-2026-11-03-0557,
the human's ruling of 2026-11-13 on #355), beside one where it does not:

- `nnan`: a NaN operand, and operands whose result is a NaN, give poison.
- `ninf`: an infinite operand, and a result that rounds to an infinity,
  give poison.
- `nsz`: a zero result is either zero, a choice of one bit.
- `fcmp nsz` is the exception: its result is not a float, so the flag has
  no effect, and its cases pin that.

Each expected result is what `float_ref.py` computes, apart from Lean, with
the flags' rules applied to it. At `f32` and `f64`, which the backend
lowers, each case is a differential test too: native code ignores the
flags, which refines poison and either zero.
"""

import sys
from fractions import Fraction

import float_arith_cases as arith
import float_ref as ref
from float_ref import Format
from float_text import spell

FORMATS = arith.FORMATS
DIFFERENTIAL = arith.DIFFERENTIAL
FLAGS = ("nnan", "ninf", "nsz")
# The float ops, each with its number of operands, in the order of `Op`.
OPS = (
    ("fcmp", 2),
    ("fadd", 2),
    ("fsub", 2),
    ("fmul", 2),
    ("fdiv", 2),
    ("frem", 2),
    ("fmod", 2),
    ("fneg", 1),
    ("fabs", 1),
    ("sqrt", 1),
    ("fma", 3),
)
# The predicate of `fcmp` under each flag: one that a NaN, an infinity or
# a zero's sign would decide.
PREDICATE = {"nnan": "uno", "ninf": "olt", "nsz": "oeq"}
FILES = [f"float-flags-{t}" for t in FORMATS]


def values(f: Format) -> dict[str, int]:
    """The operands of the cases: named specials, small numbers and the
    largest finite number `M`."""
    m = (2 ** (f.m + 1) - 1) * Fraction(2) ** (f.emax - f.m)
    out = {
        "0": f.zero(),
        "-0": f.zero(True),
        "inf": f.inf(),
        "-inf": f.inf(True),
        "nan": f.nan(),
        "M": f.exact(m),
        "-M": f.exact(-m),
    }
    for k in (1, 2, 3, 4, -1, -4):
        out[str(k)] = f.exact(Fraction(k))
    return out


# The cases of each op under each flag, by the names of `values`. The first
# cases decide the flag; the last does not.
CASES = {
    "nnan": {
        "fcmp": [["nan", "1"], ["1", "2"]],
        "fadd": [["nan", "1"], ["inf", "-inf"], ["1", "2"]],
        "fsub": [["1", "nan"], ["inf", "inf"], ["3", "1"]],
        "fmul": [["nan", "2"], ["0", "inf"], ["2", "2"]],
        "fdiv": [["nan", "1"], ["0", "0"], ["1", "2"]],
        "frem": [["nan", "1"], ["1", "0"], ["3", "2"]],
        "fmod": [["1", "nan"], ["inf", "1"], ["3", "2"]],
        "fneg": [["nan"], ["1"]],
        "fabs": [["nan"], ["-1"]],
        "sqrt": [["nan"], ["-1"], ["4"]],
        "fma": [["nan", "1", "1"], ["0", "inf", "1"], ["1", "2", "3"]],
    },
    "ninf": {
        "fcmp": [["1", "inf"], ["1", "2"]],
        "fadd": [["inf", "1"], ["M", "M"], ["1", "2"]],
        "fsub": [["1", "-inf"], ["M", "-M"], ["3", "1"]],
        "fmul": [["inf", "2"], ["M", "2"], ["2", "2"]],
        "fdiv": [["1", "inf"], ["1", "0"], ["1", "2"]],
        "frem": [["1", "inf"], ["3", "2"]],
        "fmod": [["-1", "-inf"], ["3", "2"]],
        "fneg": [["inf"], ["1"]],
        "fabs": [["-inf"], ["-1"]],
        "sqrt": [["inf"], ["4"]],
        "fma": [["inf", "1", "1"], ["M", "2", "0"], ["1", "2", "3"]],
    },
    "nsz": {
        "fcmp": [["-0", "0"], ["1", "2"]],
        "fadd": [["-0", "-0"], ["1", "-1"], ["1", "2"]],
        "fsub": [["1", "1"], ["3", "1"]],
        "fmul": [["-0", "1"], ["2", "2"]],
        "fdiv": [["0", "1"], ["1", "2"]],
        "frem": [["4", "2"], ["-4", "2"], ["3", "2"]],
        "fmod": [["-4", "2"], ["3", "2"]],
        "fneg": [["0"], ["1"]],
        "fabs": [["-0"], ["-1"]],
        "sqrt": [["-0"], ["4"]],
        "fma": [["1", "-1", "1"], ["1", "2", "3"]],
    },
}

POISON = "poison"


def plain(f: Format, op: str, flag: str, bits: list[int]):
    """What the op gives without flags: its bits, or for `fcmp` whether the
    predicate holds."""
    if op == "fcmp":
        order = ref.compare(f, *bits)
        p = PREDICATE[flag]
        return {"uno": order is None, "olt": order == "lt", "oeq": order == "eq"}[p]
    return arith.result(f, op, bits)


def flagged(f: Format, op: str, flag: str, bits: list[int]) -> list:
    """Every result the op may give with the flag `flag`, by the rules of
    `lean/Fir/Core/FloatFlags.lean`: poison when an operand or the result
    breaks `nnan` or `ninf`, either zero under `nsz`, and otherwise the
    result without flags."""
    kinds = [f.decode(b)[0] for b in bits]
    if flag == "nnan" and "nan" in kinds or flag == "ninf" and "inf" in kinds:
        return [POISON]
    r = plain(f, op, flag, bits)
    if op == "fcmp":
        return [r]
    kind = f.decode(r)[0]
    if kind == "nan":
        if flag != "nnan":
            raise ValueError(f"{op} {flag} on {bits} gives a NaN, which chooses")
        return [POISON]
    if flag == "ninf" and kind == "inf":
        return [POISON]
    if flag == "nsz" and kind == "zero":
        return [r, r ^ f.sign_bit]
    return [r]


def spelled(f: Format, op: str, r) -> str:
    if r == POISON:
        return POISON
    if op == "fcmp":
        return "true" if r else "false"
    return spell(f.e, f.m, r)


def attrs(op: str, flag: str) -> str:
    """The attributes of `op` with `flag`: the flag, then the op's own."""
    if op == "fcmp":
        return f"{flag} {PREDICATE[flag]}"
    return flag if op in arith.EXACT else f"{flag} round(rne)"


def module_text(t: str) -> str:
    """The module of one function for each op and flag, at the type `t`."""
    out = []
    for flag in FLAGS:
        for op, n in OPS:
            params = ", ".join(f"%{x}: {t}" for x in "abc"[:n])
            result = "i1" if op == "fcmp" else t
            operands = ", ".join(f"%{x}" for x in "abc"[:n])
            out.append(
                f"func @{op}_{flag}({params}) -> {result} {{\n^entry:\n"
                f"  %r: {result} = {op} {attrs(op, flag)} {operands} @0\n"
                f"  ret %r @0\n}}\n"
            )
    return "\n".join(out) + "\nlocs {\n  @0 = unknown\n}\n"


def tests_text(t: str) -> str:
    """The tests of `float-flags-T` at the type `t`."""
    e, m = FORMATS[t]
    f = Format(e, m)
    native = t in DIFFERENTIAL
    head = [
        f"# Tests of float-flags-{t}.fir: each float op with each fast-math flag",
        f"# at {t} (#242, ADR-2026-11-09-1549): a NaN operand or result gives",
        "# poison under nnan, an infinite operand or result under ninf, and a",
        "# zero result is either zero under nsz, which the choice true flips;",
        "# fcmp nsz is the op without the flag. The last case of each op is",
        "# one the flag does not decide.",
        "# Written by scripts/harness/float_flag_cases.py, which computes each",
        "# expected result with scripts/harness/float_ref.py, apart from Lean.",
    ]
    if native:
        head += [
            "# A test without expect is differential: native code ignores the",
            "# flags, and its result must be one that fir-ref gives, where any",
            "# value refines poison.",
        ]
    else:
        head += [
            "# Each test is interpreter-only: the backend does not lower",
            f"# {t}, so fir-ref alone runs it and must give what it expects.",
        ]
    named = values(f)
    lines = []
    for flag in FLAGS:
        for op, _ in OPS:
            func = f"@{op}_{flag}"
            for case in CASES[flag][op]:
                bits = [named[a] for a in case]
                args = ", ".join(f'"{spell(e, m, b)}"' for b in bits)
                got = flagged(f, op, flag, bits)
                if native:
                    lines.append(f'  {{ func = "{func}", args = [{args}] }},')
                for c, r in (
                    zip(("false", "true"), got) if len(got) > 1 else [(None, got[0])]
                ):
                    choice = "" if c is None else f'choices = ["{c}"], '
                    lines.append(
                        f'  {{ func = "{func}", args = [{args}], {choice}'
                        f'expect = ["{spelled(f, op, r)}"] }},'
                    )
    return "\n".join(head) + "\ntests = [\n" + "\n".join(lines) + "\n]\n"


def files() -> dict[str, str]:
    """Every file this writes, by its path below `tests/fir/canonical/`."""
    return arith.corpus_files(
        FILES,
        lambda name: module_text(name.removeprefix("float-flags-")),
        lambda name: tests_text(name.removeprefix("float-flags-")),
    )


def main(argv: list[str]) -> int:
    return arith.write_corpus(argv, __doc__.split("\n\n")[1], files())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
