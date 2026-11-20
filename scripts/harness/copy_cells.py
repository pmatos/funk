"""The cells of the copies, moves and fills of the coverage matrix (#234,
ADR-2026-11-03-0557).

`memcpy`, `memmove` and `memset` are each a cell for each width of their
length's integer, whatever their memory, at the side's pointer widths, in a
table of their own, `copies`. A fill's value is as wide as a unit of its
memory, which the data layout fixes, so its width is not part of a cell.
The ordering is not part of a cell: validation accepts only `nonatomic`,
so another ordering is not a cell, as a rounding mode other than `rne` is
not.

The cells are on both sides, since the backend lowers the three ops to
funk's own runtime routines (stage 4 of #234).
"""

from cell_types import Cell, CellError, Row, Table, is_pointer
from firtext import Op

COPIES = "copies"
COPY_OPS = ("memcpy", "memmove")
SET_OPS = ("memset",)
MEM_OPS = COPY_OPS + SET_OPS


def copies_table(columns: tuple[str, ...]) -> Table:
    """The table `copies`: each op, with its cell at each width of the
    columns."""
    rows = tuple(
        Row(op, "", tuple(Cell(COPIES, op, "", t) for t in columns)) for op in MEM_OPS
    )
    return Table(COPIES, columns, rows)


def copy_cell(op: Op) -> Cell:
    """The cell of a `memcpy` or a `memmove`: at the width of its length,
    with the ordering `nonatomic`, two pointers and an integer, and no
    result; or of a `memset`: at the width of its length, with the ordering
    `nonatomic`, a pointer and two integers, and no result. Any other text
    of it does not decode or validate, so it is not a cell."""
    if op.attrs == ("nonatomic",) and len(op.operands) == 3 and not op.results:
        dst, src, length = op.operands
        second = src.startswith("i") if op.name in SET_OPS else dst == src
        if is_pointer(dst) and second and length.startswith("i"):
            return Cell(COPIES, op.name, "", length)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} of {op.operands} to {op.results} is not a cell"
    )
