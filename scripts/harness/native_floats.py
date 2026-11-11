"""How the harness passes floats to native code and reads them back
(ADR-2026-11-11-1438).

The corpus and `fir-ref run` spell a float as the one float literal of its
bits, such as `1.0` or `0x7fc00000`. A built executable reads and writes a
float as its bits read as a two's-complement signed integer of the
format's width, as it reads and writes an integer of that width, so its
runtime needs no reader of decimals. The harness converts at that boundary:
each float argument to its bits before a native run, and each float that
native code returns back to its spelling. Both are exact on bits, so
comparing spellings compares bits.
"""

import float_text
import standins
from refine import DECIMAL, POISON, float_format


def to_native(args: tuple[str, ...], params) -> tuple[str, ...]:
    """`args` as native code reads them, with `params` their types. An
    argument that is no float literal of its type is passed as it is."""
    if params is None or len(params) != len(args):
        return args
    out = []
    for a, ty in zip(args, params):
        fmt = float_format(ty)
        b = None if fmt is None or a == POISON else float_text.decode(*fmt, a)
        if b is None:
            out.append(a)
            continue
        out.append(standins.spell(b, 1 + fmt[0] + fmt[1]))
    return tuple(out)


def from_native(values, types):
    """The values that native code returned, each float spelled as its
    float literal; anything else, such as a failure, as it is."""
    if not isinstance(values, tuple) or types is None or len(types) != len(values):
        return values
    out = []
    for v, ty in zip(values, types):
        fmt = float_format(ty)
        if fmt is None or DECIMAL.fullmatch(v) is None:
            out.append(v)
            continue
        width = 1 + fmt[0] + fmt[1]
        out.append(float_text.spell(*fmt, int(v) & ((1 << width) - 1)))
    return tuple(out)
