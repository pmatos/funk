"""The cells of the conversions of the coverage matrix (#241,
ADR-2026-11-03-0557).

A conversion is a cell for each pair of types it converts between at the
side's float formats, in the table `conversions`: `bitcast` from each format
to the integer of its width and back, `sitofp` and `uitofp` from each width
to each format, `fpext` and `fptrunc` from each format to each other that
the op takes, and `fptosi` and `fptoui` from each format to each width.
`cells.py` lays the table out; this module reads a conversion's cell from
its text.
"""

from cell_types import Cell, CellError
from firtext import Op
from refine import bits_of, float_format

# The attribute of a float op that rounds in a valid module (`roundAttr`):
# every other mode decodes and fails validation, so it is not a cell.
ROUND = ("round(rne)",)
# The conversions between a float and another type, which have no
# attributes: a cell for each pair of types, at the side's float formats.
CONVERSIONS = ("bitcast",)
# The conversions from an integer to a float, which carry `round(rne)`: a
# cell for each width and float format of the side.
INT_TO_FLOAT = ("sitofp", "uitofp")
# The conversions between float formats: `fpext`, which has no attribute,
# and `fptrunc`, which carries `round(rne)`. A cell for each ordered pair of
# two float formats of the side that the op takes.
FLOAT_CONVERSIONS = {"fpext": ("",), "fptrunc": ROUND}
# The conversions from a float to an integer, which have no attributes: a
# cell for each float format and width of the side.
FLOAT_TO_INT = ("fptosi", "fptoui")


def is_float(t: str) -> bool:
    """Whether `t` is a float type: an alias or `float(e, m)`."""
    b = bits_of(t)
    return b is not None and not b[1]


def conversion(a: str, b: str) -> str:
    """The op that converts from the float format `a` to another, `b`:
    `fpext` when `b` holds every value of `a`, with at least as many
    exponent bits and as many mantissa bits, and `fptrunc` otherwise."""
    (e, m), (e2, m2) = float_format(a), float_format(b)
    return "fpext" if e <= e2 and m <= m2 else "fptrunc"


def bitcast(op: Op) -> Cell:
    """The cell of a `bitcast`: from a float to the integer of its width, or
    back. Any other text of it does not decode, so it is not a cell."""
    if not op.attrs and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        for f, i in ((a, b), (b, a)):
            if is_float(f) and bits_of(i) == (bits_of(f)[0], True):
                return Cell("conversions", "bitcast", a, b)
    raise CellError(f"bitcast from {op.operands} to {op.results} is not a cell")


def int_to_float(op: Op) -> Cell:
    """The cell of a `sitofp` or `uitofp`: from an integer to a float, with
    `round(rne)`. Any other text of it does not decode or does not
    validate, so it is not a cell."""
    if op.attrs == ROUND and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        operand = bits_of(a)
        if operand is not None and operand[1] and is_float(b):
            return Cell("conversions", op.name, a, b)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} from {op.operands} to {op.results} is not a cell"
    )


def float_conversion(op: Op) -> Cell:
    """The cell of an `fpext` or `fptrunc`: from a float format to another
    that the op takes, with its attribute. Any other text of it does not
    decode or validate, so it is not a cell."""
    attr = " ".join(op.attrs)
    if attr in FLOAT_CONVERSIONS[op.name] and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        if is_float(a) and is_float(b) and a != b and conversion(a, b) == op.name:
            return Cell("conversions", op.name, a, b)
    raise CellError(
        f"{op.name} {attr} from {op.operands} to {op.results} is not a cell"
    )


def float_to_int(op: Op) -> Cell:
    """The cell of an `fptosi` or `fptoui`: from a float to an integer, with
    no attribute. Any other text of it does not decode, so it is not a
    cell."""
    if not op.attrs and len(op.operands) == len(op.results) == 1:
        [a], [b] = op.operands, op.results
        result = bits_of(b)
        if is_float(a) and result is not None and result[1]:
            return Cell("conversions", op.name, a, b)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} from {op.operands} to {op.results} is not a cell"
    )
