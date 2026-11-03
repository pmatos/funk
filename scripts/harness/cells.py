"""The cells of the coverage matrix (ADR-2026-11-03-0557).

The cell set follows the core dialect's op instances, `Op` in
`lean/Fir/Core/Ops.lean`, as `lean/Fir/Core/Text.lean` writes them: an op,
its flag set or predicate, and its width. `add`, `sub` and `mul` take the
flag sets of `decodeWrap`, `sdiv` and `udiv` those of `decodeExact`, and
`icmp` each predicate of `Pred.all`; every other op has no attribute but a
constant's value or a callee. A flag or predicate that the spec does not
give an op is not a cell.

- An op at a width is a cell for each width of the matrix's side.
- A width change, `zext`, `sext` or `trunc`, is a cell for each pair of
  widths from `iM` to `iN` that the spec allows: `M < N`, or `N < M` for
  `trunc`.
- `br`, and each successor of `cond_br`, passes nothing, or values of a
  width. `ret` returns no value, one, or several; a `call` gives no result,
  one, or several; and so does the function that a test runs, `func`. One
  value or several are cells at each width that a value has.
"""

from typing import NamedTuple

from firtext import Op

DIFFERENTIAL = (1, 8, 16, 32, 64, 128)
INTERPRETER = (1, 7, 8, 16, 32, 33, 64, 128)

WRAP = ("", "nuw", "nsw", "nuw nsw")
EXACT = ("", "exact")
PREDS = ("eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge")

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
}
CASTS = ("zext", "sext", "trunc")
NOTHING, PASSED, ONE, SEVERAL = "nothing", "values", "one", "several"
# The rows of passed and returned values: an op, and what it passes,
# returns or gives.
VALUES = (
    ("br", (NOTHING, PASSED)),
    ("cond_br", (NOTHING, PASSED)),
    ("ret", (NOTHING, ONE, SEVERAL)),
    ("call", (NOTHING, ONE, SEVERAL)),
    ("func", (NOTHING, ONE, SEVERAL)),
)
OPS = (*AT_WIDTH, *CASTS, *(op for op, _ in VALUES if op != "func"))


class Cell(NamedTuple):
    """`table` is `ops`, `casts` or `values`. `row` is a flag set or
    predicate, the source width of a width change, or what a value row
    passes; `width` is a width, or empty where nothing is passed."""

    table: str
    op: str
    row: str
    width: str


class CellError(Exception):
    pass


def ty(w: int) -> str:
    return f"i{w}"


def cells(widths: tuple[int, ...]) -> list[Cell]:
    """Every cell of one side of the matrix, at these widths."""
    out = []
    for op, attrs in AT_WIDTH.items():
        out += [Cell("ops", op, a, ty(w)) for a in attrs for w in widths]
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
                out += [Cell("values", op, row, ty(w)) for w in widths]
    return out


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
    if op.name in AT_WIDTH:
        attr = "" if op.name == "const" else " ".join(op.attrs)
        if attr not in AT_WIDTH[op.name]:
            raise CellError(f"{op.name} {attr} is not a cell")
        typed = op.operands if op.name == "icmp" else op.results
        return {Cell("ops", op.name, attr, typed[0])}
    if op.name in CASTS:
        return {Cell("casts", op.name, op.operands[0], op.results[0])}
    if op.name in ("br", "cond_br"):
        return set().union(*(results(op.name, s) for s in op.successors))
    if op.name == "ret":
        return results("ret", op.operands)
    if op.name == "call":
        return results("call", op.results)
    raise CellError(f"{op.name} is not an op of the core dialect")
