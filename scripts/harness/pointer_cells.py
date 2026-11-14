"""The cells of the pointer ops of the coverage matrix (#231,
ADR-2026-11-03-0557).

- `ptradd`, which has no attributes, is a cell for each width of its
  integer.
- `alloca` is a cell for each width of the integer type it allocates,
  whatever its kind, count and alignment.
- `load` is a cell for each width of the integer it loads, whatever its
  ordering and alignment.

Each is a cell at the side's pointer widths, `cells.POINTER_DIFFERENTIAL`
and `cells.POINTER_INTERPRETER`.
"""

from cell_types import Cell, CellError, is_pointer
from firtext import Op
from refine import bits_of

POINTER_OPS = ("ptradd", "alloca", "load")


def pointer_offset(op: Op) -> Cell:
    """The cell of a `ptradd`: at the width of its integer. Any other text
    of it does not decode, so it is not a cell."""
    if not op.attrs and len(op.operands) == 2 and op.results == op.operands[:1]:
        pointer, offset = op.operands
        bits = bits_of(offset)
        if is_pointer(pointer) and bits is not None and bits[1]:
            return Cell("pointers", op.name, "", offset)
    raise CellError(f"{op.name} of {op.operands} to {op.results} is not a cell")


def stack_allocation(op: Op) -> Cell:
    """The cell of an `alloca`: at the width of the integer type it
    allocates, its second attribute after its kind. Its count and alignment
    are not part of its cell, as a constant's value is not. The matrix
    reads canonical modules, which both tools decode, so the rest of its
    attributes needs no check here."""
    if len(op.attrs) >= 2 and not op.operands and len(op.results) == 1:
        element = op.attrs[1]
        bits = bits_of(element)
        if is_pointer(op.results[0]) and bits is not None and bits[1]:
            return Cell("pointers", op.name, "", element)
    raise CellError(f"{op.name} {' '.join(op.attrs)} to {op.results} is not a cell")


def memory_load(op: Op) -> Cell:
    """The cell of a `load`: at the width of the integer it loads. Its
    ordering and alignment are not part of its cell, as an allocation's
    count is not. The matrix reads canonical modules, which both tools
    decode, so the rest of its attributes needs no check here."""
    if op.attrs and len(op.operands) == len(op.results) == 1:
        [pointer], [result] = op.operands, op.results
        bits = bits_of(result)
        if is_pointer(pointer) and bits is not None and bits[1]:
            return Cell("pointers", op.name, "", result)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} of {op.operands} to {op.results} is not a cell"
    )


def pointer_cell(op: Op) -> Cell:
    """The cell of a pointer op."""
    if op.name == "alloca":
        return stack_allocation(op)
    if op.name == "load":
        return memory_load(op)
    return pointer_offset(op)
