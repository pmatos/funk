"""The cells of the ops that turn pointers into integers and back, of the
coverage matrix (#232, ADR-2026-11-03-0557).

`ptr_expose` and `ptr_from_int` are each a cell for each width of their
integer, whatever their memory, in a table of their own, `addresses`. The
data layout asks that the integer be as wide as the memory's pointers, so
the columns are the pointer widths of the memories that the corpus
declares: `i64`, the default memory's, and `i32`.

The cells are on the interpreter side only: the backend lowers the two ops
in stage 5 of #232. A test that returns an exposed address depends on the
canonical layout that `fir-ref` follows, so the corpus returns what the
address reaches, or the difference of two addresses, never the address.
"""

from cell_types import Cell, CellError, Row, Table, is_pointer
from firtext import Op

ADDRESSES = "addresses"
ADDRESS_OPS = ("ptr_expose", "ptr_from_int")
ADDRESS_INTERPRETER = (32, 64)


def addresses_table(columns: tuple[str, ...]) -> Table:
    """The table `addresses`: each op, with its cell at each width of the
    columns."""
    rows = tuple(
        Row(op, "", tuple(Cell(ADDRESSES, op, "", t) for t in columns))
        for op in ADDRESS_OPS
    )
    return Table(ADDRESSES, columns, rows)


def address_cell(op: Op) -> Cell:
    """The cell of a `ptr_expose`: at the width of its result, with no
    attributes and a pointer operand; or of a `ptr_from_int`: at the width
    of its operand, with no attributes and a pointer result. Any other text
    of it does not decode, so it is not a cell."""
    if not op.attrs and len(op.operands) == len(op.results) == 1:
        [a], [r] = op.operands, op.results
        pointer, integer = (a, r) if op.name == "ptr_expose" else (r, a)
        if is_pointer(pointer) and integer.startswith("i"):
            return Cell(ADDRESSES, op.name, "", integer)
    raise CellError(f"{op.name} of {op.operands} to {op.results} is not a cell")
