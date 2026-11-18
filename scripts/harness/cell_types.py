"""The cell of the coverage matrix and the type tests that every module of
cells shares (ADR-2026-11-03-0557). `cells.py` gives the cell set,
`pointer_cells.py` the cells of the pointer ops, `gpu_cells.py` those of
the `gpu` dialect, and `copy_cells.py` those of `memcpy` and `memmove`."""

from typing import NamedTuple


class Cell(NamedTuple):
    """`table` is `ops`, `floats`, `casts`, `conversions`, `pointers`,
    `values`, `gpu` or `copies`.
    `row` is a flag set or predicate, the source type of a width change or a
    conversion, or what a value row passes, and empty for a pointer op;
    `width` is a width, a float format, the result type of a width change
    or a conversion, the width of a pointer offset's integer, of the
    integer an `alloca` allocates, of the integer a `load` loads or of the
    integer a `store` stores, `ptr` for a pointer that an `alloca`
    allocates, a `load` loads or a `store` stores, or empty where nothing
    is passed. A `gpu` op's `row` is its dimension and its `width` the
    `i32` it gives; a copy's `width` is the width of its length."""

    table: str
    op: str
    row: str
    width: str


class CellError(Exception):
    pass


def is_pointer(t: str) -> bool:
    """Whether `t` is a pointer type: `ptr` or `ptr(N)`."""
    return t == "ptr" or (t.startswith("ptr(") and t.endswith(")"))
