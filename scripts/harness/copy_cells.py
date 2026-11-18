"""The cells of the copies and moves of the coverage matrix (#234,
ADR-2026-11-03-0557).

`memcpy` and `memmove` are each a cell for each width of their length's
integer, whatever their memory, at the side's pointer widths, in a table of
their own, `copies`. The ordering is not part of a cell: validation accepts
only `nonatomic`, so another ordering is not a cell, as a rounding mode
other than `rne` is not.

The cells are on the interpreter-only side alone, until the backend lowers
the two ops to funk's own runtime routines (stage 4 of #234).
"""

from cell_types import Cell, CellError, is_pointer
from firtext import Op

COPIES = "copies"
COPY_OPS = ("memcpy", "memmove")


def copy_cells(columns: tuple[str, ...]) -> tuple[tuple[str, tuple[Cell, ...]], ...]:
    """Each op, with its cell at each width of the columns."""
    return tuple(
        (op, tuple(Cell(COPIES, op, "", t) for t in columns)) for op in COPY_OPS
    )


def copy_cell(op: Op) -> Cell:
    """The cell of a `memcpy` or a `memmove`: at the width of its length,
    with the ordering `nonatomic`, two pointers and an integer, and no
    result. Any other text of it does not decode or validate, so it is not
    a cell."""
    if op.attrs == ("nonatomic",) and len(op.operands) == 3 and not op.results:
        dst, src, length = op.operands
        if is_pointer(dst) and dst == src and length.startswith("i"):
            return Cell(COPIES, op.name, "", length)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} of {op.operands} to {op.results} is not a cell"
    )
