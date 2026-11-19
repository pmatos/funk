"""The cell of the coverage matrix and the type tests that every module of
cells shares (ADR-2026-11-03-0557). `cells.py` gives the cell set,
`pointer_cells.py` the cells of the pointer ops, and `gpu_cells.py` those of
the `gpu` dialect."""

from typing import NamedTuple


class Cell(NamedTuple):
    """`table` is `ops`, `floats`, `casts`, `conversions`, `pointers`,
    `fields`, `values` or `gpu`.
    `row` is a flag set or predicate, the source type of a width change or a
    conversion, or what a value row passes, and empty for a pointer op;
    `width` is a width, a float format, the result type of a width change
    or a conversion, the width of a pointer offset's integer, of the
    integer an `alloca` allocates, of the integer a `load` loads or of the
    integer a `store` stores, `ptr` for a pointer that an `alloca`
    allocates, a `load` loads or a `store` stores, or empty where nothing
    is passed. A `fieldaddr`'s `width` is the type of its index, empty
    with none. A `gpu` op's `row` is its dimension and its `width` the
    `i32` it gives."""

    table: str
    op: str
    row: str
    width: str


class Row(NamedTuple):
    """A labelled row; `None` entries are not cells, even at a zero count."""

    op: str
    key: str
    entries: tuple[Cell | None, ...]


class Table(NamedTuple):
    """An ordered matrix section, with one entry per column in every row.

    `kind` distinguishes display sections, including the four conversion
    sections whose cells all have table `conversions`. Columns are type
    names; the empty name is the scalar or no-value column.
    """

    kind: str
    columns: tuple[str, ...]
    rows: tuple[Row, ...]


class CellError(Exception):
    pass


def is_pointer(t: str) -> bool:
    """Whether `t` is a pointer type: `ptr` or `ptr(N)`."""
    return t == "ptr" or (t.startswith("ptr(") and t.endswith(")"))
