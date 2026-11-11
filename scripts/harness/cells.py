"""The cells of the coverage matrix (ADR-2026-11-03-0557).

The cell set follows the core dialect's op instances, `Op` in
`lean/Fir/Core/Ops.lean`, as `lean/Fir/Core/Text.lean` writes them: an op,
its flag set or predicate, and its width. `add`, `sub` and `mul` take the
flag sets of `decodeWrap`, `sdiv` and `udiv` those of `decodeExact`, and
`icmp` each predicate of `Pred.all`. A constant's value and a callee are
attributes but not cells, and the other ops have no attributes. A flag or
predicate that the spec does not give an op is not a cell. `poison`, which
has neither operands nor attributes, is a cell at each width of its result
(ADR-2026-11-03-1618).

- An op at a width is a cell for each width of the matrix's side.
- A width change, `zext`, `sext` or `trunc`, is a cell for each pair of
  widths from `iM` to `iN` that the spec allows: `M < N`, or `N < M` for
  `trunc`.
- A float constant, and `fcmp` with each predicate of `FPred.all`, is a
  cell at each float format of the matrix's side: `f32` and `f64` for
  differential tests, which the backend lowers, and `f16`, `bf16`, `f32`,
  `f64` and `f128` for interpreter-only tests (#229).
- `br`, and each successor of `cond_br`, passes nothing, or values of a
  width. `ret` returns no value, one, or several; a `call` gives no result,
  one, or several; and so does the function that a test runs, `func`. One
  value or several are cells at each width that a value has. `unreachable`
  passes nothing, so it is one cell.
"""

from typing import NamedTuple

from firtext import Op
from refine import bits_of

DIFFERENTIAL = (1, 8, 16, 32, 64, 128)
INTERPRETER = (1, 7, 8, 16, 32, 33, 64, 128)
FLOAT_DIFFERENTIAL = ("f32", "f64")
FLOAT_INTERPRETER = ("f16", "bf16", "f32", "f64", "f128")

WRAP = ("", "nuw", "nsw", "nuw nsw")
EXACT = ("", "exact")
PREDS = ("eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge")
FPREDS = (
    "oeq",
    "one",
    "olt",
    "ole",
    "ogt",
    "oge",
    "ord",
    "ueq",
    "une",
    "ult",
    "ule",
    "ugt",
    "uge",
    "uno",
)

# The ops at a width, in the order of `Op`, with the attributes that are
# cells: a flag set or a predicate.
AT_WIDTH = {
    "const": ("",),
    "add": WRAP,
    "sub": WRAP,
    "mul": WRAP,
    "sdiv": EXACT,
    "udiv": EXACT,
    "srem": ("",),
    "urem": ("",),
    "and": ("",),
    "or": ("",),
    "xor": ("",),
    "shl": ("",),
    "lshr": ("",),
    "ashr": ("",),
    "icmp": PREDS,
    "select": ("",),
    "freeze": ("",),
    "poison": ("",),
}
# The float ops at a format, with the attributes that are cells.
AT_FORMAT = {"const": ("",), "fcmp": FPREDS}
CASTS = ("zext", "sext", "trunc")
NOTHING, PASSED, ONE, SEVERAL = "nothing", "values", "one", "several"
# The rows of passed and returned values: an op, and what it passes,
# returns or gives.
VALUES = (
    ("br", (NOTHING, PASSED)),
    ("cond_br", (NOTHING, PASSED)),
    ("ret", (NOTHING, ONE, SEVERAL)),
    ("unreachable", (NOTHING,)),
    ("call", (NOTHING, ONE, SEVERAL)),
    ("func", (NOTHING, ONE, SEVERAL)),
)
OPS = (*AT_WIDTH, "fcmp", *CASTS, *(op for op, _ in VALUES if op != "func"))


class Cell(NamedTuple):
    """`table` is `ops`, `floats`, `casts` or `values`. `row` is a flag set
    or predicate, the source width of a width change, or what a value row
    passes; `width` is a width or a float format, or empty where nothing is
    passed."""

    table: str
    op: str
    row: str
    width: str


class CellError(Exception):
    pass


def ty(w: int) -> str:
    return f"i{w}"


def cells(widths: tuple[int, ...], formats: tuple[str, ...] = ()) -> list[Cell]:
    """Every cell of one side of the matrix, at these widths and float
    formats."""
    out = []
    for op, attrs in AT_WIDTH.items():
        out += [Cell("ops", op, a, ty(w)) for a in attrs for w in widths]
    for op, attrs in AT_FORMAT.items():
        out += [Cell("floats", op, a, f) for a in attrs for f in formats]
    for op in CASTS:
        for m in widths:
            out += [
                Cell("casts", op, ty(m), ty(n)) for n in widths if allowed(op, m, n)
            ]
    for op, rows in VALUES:
        for row in rows:
            if row == NOTHING:
                out.append(Cell("values", op, row, ""))
            else:
                types = (*map(ty, widths), *formats)
                out += [Cell("values", op, row, t) for t in types]
    return out


def is_float(t: str) -> bool:
    """Whether `t` is a float type: an alias or `float(e, m)`."""
    b = bits_of(t)
    return b is not None and not b[1]


def allowed(op: str, m: int, n: int) -> bool:
    """Whether the spec has the width change `op` from `iM` to `iN`."""
    return n < m if op == "trunc" else m < n


def results(op: str, types: tuple[str, ...]) -> set[Cell]:
    """The cells of values that `op` passes, returns or gives."""
    if not types:
        return {Cell("values", op, NOTHING, "")}
    if op in ("br", "cond_br"):
        row = PASSED
    else:
        row = ONE if len(types) == 1 else SEVERAL
    return {Cell("values", op, row, t) for t in types}


def of_op(op: Op) -> set[Cell]:
    """The cells that an op exercises, at any width. An op that the core
    dialect does not have, or an attribute that is not a cell, is an
    error."""
    if op.name == "fcmp" or (op.name == "const" and is_float(op.results[0])):
        attr = "" if op.name == "const" else " ".join(op.attrs)
        if attr not in AT_FORMAT[op.name]:
            raise CellError(f"{op.name} {attr} is not a cell")
        typed = op.operands if op.name == "fcmp" else op.results
        return {Cell("floats", op.name, attr, typed[0])}
    if op.name in AT_WIDTH:
        attr = "" if op.name == "const" else " ".join(op.attrs)
        if attr not in AT_WIDTH[op.name]:
            raise CellError(f"{op.name} {attr} is not a cell")
        typed = op.operands if op.name == "icmp" else op.results
        return {Cell("ops", op.name, attr, typed[0])}
    if op.attrs and op.name != "call":
        raise CellError(f"{op.name} {' '.join(op.attrs)} is not a cell")
    if op.name in CASTS:
        return {Cell("casts", op.name, op.operands[0], op.results[0])}
    if op.name in ("br", "cond_br"):
        return set().union(*(results(op.name, s) for s in op.successors))
    if op.name in ("ret", "unreachable"):
        return results(op.name, op.operands)
    if op.name == "call":
        return results("call", op.results)
    raise CellError(f"{op.name} is not an op of the core dialect")
