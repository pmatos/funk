"""The cells of the pointer ops of the coverage matrix (#231,
ADR-2026-11-03-0557).

- `ptradd`, which has no attributes, is a cell for each width of its
  integer.
- `alloca` is a cell for each width of the integer type it allocates,
  whatever its kind, count and alignment, one, `ptr`, for a pointer
  type of any memory (stage 4d-2b of #231), and one for each float format
  it allocates (#264).
- `load` is a cell for each width of the integer it loads, whatever its
  ordering and alignment, one, `ptr`, for a pointer of any memory, and one
  for each float format it loads.
- `store` is a cell for each width of the integer it stores, whatever its
  ordering and alignment, one, `ptr`, for a pointer of any memory, and one
  for each float format it stores.

Each is a cell at the side's pointer widths, `cells.POINTER_DIFFERENTIAL`
and `cells.POINTER_INTERPRETER`, the pointer cells with them, and at the
side's float formats in memory, `MEMORY_FLOAT_DIFFERENTIAL` and
`MEMORY_FLOAT_INTERPRETER`: the differential side has `f32` and `f64`,
which the backend loads and stores with SSE moves (stage 2 of #264).

The field address `fieldaddr` (#236) is a cell for each width of its
index, read as signed, and one, with no index, for the address of a field
or of a repeated field's first element, whatever its layout and field, as
a call's callee is not part of its cell. Its cells are at the side's field
widths, `cells.FIELD_DIFFERENTIAL` and `cells.FIELD_INTERPRETER`: the
backend does not lower it yet, so the differential side has none (stage 4
of #236).
"""

from cell_types import Cell, CellError, Row, Table, is_pointer
from firtext import Op
from refine import FLOAT_ALIASES, bits_of

POINTER_OPS = ("ptradd", "alloca", "load", "store")
# The field address, and its table of cells (#236).
FIELD_ADDR = "fieldaddr"
FIELDS = "fields"
# The column of the pointer cells of `alloca`, `load` and `store`.
POINTER = "ptr"
# The float formats of `alloca`, `load` and `store` on each side (#264).
MEMORY_FLOAT_DIFFERENTIAL = ("f32", "f64")
MEMORY_FLOAT_INTERPRETER = tuple(FLOAT_ALIASES)


def is_int(t: str) -> bool:
    """Whether `t` is an integer type `iN`."""
    bits = bits_of(t)
    return bits is not None and bits[1]


def element(t: str) -> str | None:
    """The column of a type that memory holds: an integer or a float type's
    own, and `ptr` for a pointer type of any memory; none for any other
    type."""
    if bits_of(t) is not None:
        return t
    return POINTER if is_pointer(t) else None


def pointer_offset(op: Op) -> Cell:
    """The cell of a `ptradd`: at the width of its integer. Any other text
    of it does not decode, so it is not a cell."""
    if not op.attrs and len(op.operands) == 2 and op.results == op.operands[:1]:
        pointer, offset = op.operands
        if is_pointer(pointer) and is_int(offset):
            return Cell("pointers", op.name, "", offset)
    raise CellError(f"{op.name} of {op.operands} to {op.results} is not a cell")


def stack_allocation(op: Op) -> Cell:
    """The cell of an `alloca`: at the integer or float type it allocates,
    its second attribute after its kind, or at `ptr`. Its count and alignment
    are not part of its cell, as a constant's value is not. The matrix
    reads canonical modules, which both tools decode, so the rest of its
    attributes needs no check here."""
    if len(op.attrs) >= 2 and not op.operands and len(op.results) == 1:
        column = element(op.attrs[1])
        if is_pointer(op.results[0]) and column:
            return Cell("pointers", op.name, "", column)
    raise CellError(f"{op.name} {' '.join(op.attrs)} to {op.results} is not a cell")


def memory_load(op: Op) -> Cell:
    """The cell of a `load`: at the integer or float type it loads, or at
    `ptr`. Its ordering and alignment are not part of its cell, as an
    allocation's count is not. The matrix reads canonical modules, which
    both tools decode, so the rest of its attributes needs no check here."""
    if op.attrs and len(op.operands) == len(op.results) == 1:
        [pointer], [result] = op.operands, op.results
        column = element(result)
        if is_pointer(pointer) and column:
            return Cell("pointers", op.name, "", column)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} of {op.operands} to {op.results} is not a cell"
    )


def memory_store(op: Op) -> Cell:
    """The cell of a `store`: at the integer or float type it stores, its
    first operand, or at `ptr`. Its ordering and alignment are not part of its cell, as
    a load's are not. The matrix reads canonical modules, which both tools
    decode, so the rest of its attributes needs no check here."""
    if op.attrs and len(op.operands) == 2 and not op.results:
        value, pointer = op.operands
        column = element(value)
        if column and is_pointer(pointer):
            return Cell("pointers", op.name, "", column)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} of {op.operands} to {op.results} is not a cell"
    )


def pointer_cell(op: Op) -> Cell:
    """The cell of a pointer op."""
    if op.name == "alloca":
        return stack_allocation(op)
    if op.name == "load":
        return memory_load(op)
    if op.name == "store":
        return memory_store(op)
    return pointer_offset(op)


def field_address(op: Op) -> Cell:
    """The cell of a `fieldaddr`: at the width of its index, or with no
    index. Its layout's symbol and its field's number are not part of its
    cell. Any other text of it does not decode, so it is not a cell."""
    attrs_decode = (
        len(op.attrs) == 2 and op.attrs[0].startswith("@") and op.attrs[1].isdigit()
    )
    if attrs_decode and op.operands and op.results == op.operands[:1]:
        pointer, *index = op.operands
        if is_pointer(pointer) and len(index) <= 1 and all(map(is_int, index)):
            return Cell(FIELDS, op.name, "", index[0] if index else "")
    raise CellError(f"{op.name} of {op.operands} to {op.results} is not a cell")


def field_table(widths: tuple[str, ...]) -> Table:
    """The table of `fieldaddr`'s cells: with no index, then at each width
    of its index."""
    columns = ("", *widths)
    row = Row(FIELD_ADDR, "", tuple(Cell(FIELDS, FIELD_ADDR, "", t) for t in columns))
    return Table(FIELDS, columns, (row,))
