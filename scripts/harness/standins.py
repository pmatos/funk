"""The values that native code gets in place of a poison argument (#123,
ADR-2026-11-03-1847).

A test's arguments may hold `poison`, which `fir-ref run` takes as it is.
Native code holds no poison (ADR-2026-10-30-2248), and a built executable
reads each argument as a constant, so a differential test runs native code
on stand-ins: defined values in place of each poison. The stand-ins of
`iN`, and of a float type of `N` bits, are its boundary bit patterns, the
ones that `fir-ref run --seed` favours (ADR-2026-10-31-0002): 0, 1, all
ones, the signed minimum and the signed maximum, each once, so `false` and
`true` at `i1`. At a float type they are `+0`, the smallest subnormal, a
NaN with its sign set, `-0` and a NaN, each spelled as its one float
literal (ADR-2026-11-11-1438). Native code runs on every combination: with
`k` poison arguments, up to `5 ** k` runs.

Each native result must refine an outcome of `fir-ref`'s run on the poison
itself. A run with a value in place of poison refines the run with poison,
calls included (`Core.args_isRefinedBy`), so correct native code passes
on every stand-in.
"""

import itertools

import float_text
from refine import POISON, bits_of, float_format


def count(n: int, thing: str) -> str:
    return f"{n} {thing}" if n == 1 else f"{n} {thing}s"


def spell(bits: int, width: int) -> str:
    """The bit pattern `bits` of `iN` spelled as a constant of its type."""
    if width == 1:
        return "true" if bits else "false"
    signed = bits - (1 << width) if bits >> (width - 1) else bits
    return str(signed)


def standins(ty: str) -> tuple[str, ...] | None:
    """The stand-ins of the type `ty` in order, or None when it has none,
    as `ptr` has none: its values are pointers, not bits, and native code
    takes no pointer argument until the backend lowers pointers (#231)."""
    b = bits_of(ty)
    if b is None:
        return None
    width, is_int = b
    top = 1 << (width - 1)
    found = []
    for bits in (0, 1, (1 << width) - 1, top, top - 1):
        s = spell(bits, width) if is_int else float_text.spell(*float_format(ty), bits)
        if s not in found:
            found.append(s)
    return tuple(found)


def vectors(args: tuple[str, ...], params) -> list[tuple[str, ...]] | str:
    """The argument vectors that native code runs on: `args`, with each
    poison replaced by each stand-in of its parameter's type, in every
    combination, the first poison changing slowest; or why there are none.
    `params` are the function's parameter types, or None when they cannot
    be read."""
    if params is None:
        return "cannot read the parameter types"
    if len(args) != len(params):
        given, wanted = count(len(args), "argument"), count(len(params), "parameter")
        return f"the test gives {given} for {wanted}"
    each = []
    for i, (a, ty) in enumerate(zip(args, params), 1):
        if a != POISON:
            each.append((a,))
            continue
        s = standins(ty)
        if s is None:
            return f"argument {i} is poison, and {ty} has no stand-in for it"
        each.append(s)
    return list(itertools.product(*each))
