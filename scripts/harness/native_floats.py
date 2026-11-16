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

`nans` reads which of native code's results are NaNs, for `fir-ref run
--exhaustive --nans` (ADR-2026-11-16-1630).
"""

import float_text
import standins
from refine import DECIMAL, FLOAT_ALIASES, INT_TYPE, POISON, float_format


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


def is_nan(e: int, m: int, b: int) -> bool:
    """Whether `b` is the bits of a NaN of `float<e,m>`."""
    return b >> m & (1 << e) - 1 == (1 << e) - 1 and b & (1 << m) - 1 != 0


def nans(values, types) -> tuple[str, ...]:
    """The bits of each value that native code returned that is a NaN,
    once each and in order, as `--nans` takes them: a float of its format
    that is a NaN, or an integer whose bits are a NaN of a float format of
    its width, as a NaN that went through `bitcast` or memory is."""
    if not isinstance(values, tuple) or types is None or len(types) != len(values):
        return ()
    out = []
    for v, ty in zip(values, types):
        fmt = float_format(ty)
        if fmt is not None:
            b = float_text.decode(*fmt, v)
            formats = [fmt]
        elif (n := INT_TYPE.fullmatch(ty)) and DECIMAL.fullmatch(v):
            width = int(n.group(1))
            b = int(v) & ((1 << width) - 1)
            formats = [f for f in FLOAT_ALIASES.values() if 1 + sum(f) == width]
        else:
            continue
        nan = f"0x{b:x}" if b is not None else None
        if nan and nan not in out and any(is_nan(*f, b) for f in formats):
            out.append(nan)
    return tuple(out)
