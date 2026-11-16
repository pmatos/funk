"""The cells of the `gpu` dialect's ops in the coverage matrix (#406,
ADR-2026-11-03-0557).

The cell set follows the dialect's op instances, `Op` in
`lean/Fir/Gpu/Ops.lean`, as `lean/Fir/Gpu/Text.lean` writes them: an op
asks one question, `Query`, in one dimension, `Dim`, and gives an integer.
Each op is a cell for each dimension, `gpu.x`, `gpu.y` and `gpu.z`, at the
one width that validation lets it give, `i32` (`lean/Fir/Gpu/Validation.lean`):
an op at another width decodes and fails validation, so it is not a cell, as
a rounding mode other than `rne` is not.

`gpu.work_group_alloca` allocates in work-group memory as `alloca` does
(stage 3 of #212). It is a cell for each width of the integer type it
allocates, whatever its count and alignment, and one, `ptr`, for a pointer
type of any memory, as `alloca`'s cells are (`pointer_cells.py`), at the
side's pointer widths.

The cells are on the interpreter-only side alone: a kernel is a function of
a nested module, which `funk build` does not build, so every test of one is
interpreter-only (#212).
"""

from cell_types import Cell, CellError, is_pointer
from firtext import Op
from pointer_cells import element

GPU = "gpu"
# The ops, in the order of `Query`, and the dimensions, in that of `Dim`.
GPU_OPS = (
    "gpu.work_item_id",
    "gpu.work_group_id",
    "gpu.work_group_size",
    "gpu.num_work_groups",
)
DIMS = ("gpu.x", "gpu.y", "gpu.z")
# The width that every op of `gpu` gives in a valid module.
GPU_WIDTH = "i32"
# The op that allocates in work-group memory, and its table of cells.
WORK_GROUP_ALLOCA = "gpu.work_group_alloca"
GPU_MEMORY = "gpu_memory"


def gpu_cells() -> tuple[tuple[str, str, Cell], ...]:
    """Each op and dimension, with its cell, in the order of `Op`."""
    return tuple((op, d, Cell(GPU, op, d, GPU_WIDTH)) for op in GPU_OPS for d in DIMS)


def gpu_cell(op: Op) -> Cell:
    """The cell of an op of `gpu`: its dimension, with no operand and one
    `i32` result. Any other text of it does not decode or validate, so it is
    not a cell."""
    if (
        len(op.attrs) == 1
        and op.attrs[0] in DIMS
        and not op.operands
        and op.results == (GPU_WIDTH,)
    ):
        return Cell(GPU, op.name, op.attrs[0], GPU_WIDTH)
    raise CellError(
        f"{op.name} {' '.join(op.attrs)} of {op.operands} to {op.results} is not a cell"
    )


def work_group_cell(op: Op) -> Cell:
    """The cell of a `gpu.work_group_alloca`: at the width of the integer
    type it allocates, its first attribute, or at `ptr`. Its count and
    alignment are not part of its cell, as `alloca`'s are not."""
    if op.attrs and not op.operands and len(op.results) == 1:
        column = element(op.attrs[0])
        if column and is_pointer(op.results[0]):
            return Cell(GPU_MEMORY, op.name, "", column)
    raise CellError(f"{op.name} {' '.join(op.attrs)} to {op.results} is not a cell")
