"""The coverage matrix of the corpus of `tests/fir/` (#23,
ADR-2026-11-03-0557).

Usage: coverage.py [--write]

It reads every test of the corpus and counts, for differential and for
interpreter-only tests apart, the tests that exercise each cell of
`cells.py`. A test exercises the cells of every op of the function it runs
and of every function that one calls, directly or through others, as the
module's text writes them; and the `func` cell of the results of the
function it runs. It checks that the committed matrix,
`docs/coverage/README.md`, is the one it makes, and that every cell has a
test. With `--write` it writes the matrix first. It exits with 0 when both
hold, 1 when either does not, and 2 when it cannot read the corpus.
"""

import argparse
import sys
from collections import Counter
from pathlib import Path
from typing import NamedTuple

import cells
import corpus
import firtext
from cells import Cell

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "tests" / "fir"
MATRIX = ROOT / "docs" / "coverage" / "README.md"


class Side(NamedTuple):
    """One side of the matrix: its key, its title, and the widths, float
    formats and widths of a pointer offset's integer that it has cells at."""

    name: str
    title: str
    widths: tuple[int, ...]
    formats: tuple[str, ...]
    offsets: tuple[int, ...]

    def cells(self) -> list[Cell]:
        return cells.cells(self.widths, self.formats, self.offsets)


SIDES = (
    Side(
        "differential",
        "Differential tests",
        cells.DIFFERENTIAL,
        cells.FLOAT_DIFFERENTIAL,
        cells.POINTER_DIFFERENTIAL,
    ),
    Side(
        "interpreter",
        "Interpreter-only tests",
        cells.INTERPRETER,
        cells.FLOAT_INTERPRETER,
        cells.POINTER_INTERPRETER,
    ),
)


class CoverageError(Exception):
    pass


def reachable(functions: dict[str, firtext.Function], start: str) -> list[str]:
    """`start` and every function that it calls, directly or through
    others."""
    seen, todo = [], [start]
    while todo:
        f = todo.pop()
        if f in seen:
            continue
        if f not in functions:
            raise CoverageError(f"there is no function {f}")
        seen.append(f)
        todo += sorted(functions[f].callees())
    return seen


def exercised(functions: dict[str, firtext.Function], func: str) -> set[Cell]:
    """The cells that a run of `func` exercises."""
    found = cells.results("func", functions[func].results)
    for f in reachable(functions, func):
        for op in functions[f].ops:
            found |= cells.of_op(op)
    return found


def count(root: Path) -> dict[str, Counter]:
    """How many tests of each side exercise each cell."""
    c = corpus.load(root)
    if c.errors:
        raise CoverageError("; ".join(c.errors))
    counts = {"differential": Counter(), "interpreter": Counter()}
    for m in c.modules:
        if not m.tests:
            continue
        try:
            functions = firtext.read(m.path.read_text(encoding="utf-8"))
            for t in m.tests:
                side = "differential" if t.expect is None else "interpreter"
                if t.func not in functions:
                    raise CoverageError(f"there is no function {t.func}")
                counts[side].update(exercised(functions, t.func))
        except (firtext.TextError, cells.CellError, CoverageError) as e:
            raise CoverageError(f"{m.name}: {e}") from e
    return counts


def empty(counts: dict[str, Counter]) -> list[str]:
    """The cells that no test exercises, named as the matrix shows them."""
    return [
        f"{side.name}: {show(cell)}"
        for side in SIDES
        for cell in side.cells()
        if not counts[side.name][cell]
    ]


def show(cell: Cell) -> str:
    if cell.table in ("casts", "conversions"):
        return f"{cell.op} from {cell.row} to {cell.width}"
    if cell.table == "pointers":
        return f"{cell.op} by {cell.width}"
    words = [cell.op, cell.row]
    if cell.table == "values" and cell.row != cells.NOTHING:
        words.append("at")
    return " ".join(w for w in [*words, cell.width] if w)


def number(n: int) -> str:
    return f"{n}" if n else "**0**"


def table(head: list[str], rows: list[list[str]]) -> list[str]:
    out = ["| " + " | ".join(head) + " |", "|" + " --- |" * len(head)]
    return out + ["| " + " | ".join(r) + " |" for r in rows]


def ops_table(counts: Counter, widths: tuple[int, ...]) -> list[str]:
    rows = []
    for op, attrs in cells.AT_WIDTH.items():
        for a in attrs:
            row = [f"`{op}`", f"`{a}`" if a else ""]
            rows.append(
                row + [number(counts[Cell("ops", op, a, cells.ty(w))]) for w in widths]
            )
    return table(["op", "flags or predicate", *(f"`i{w}`" for w in widths)], rows)


def floats_table(counts: Counter, formats: tuple[str, ...]) -> list[str]:
    rows = []
    for op, attrs in cells.AT_FORMAT.items():
        for a in attrs:
            row = [f"`{op}`", f"`{a}`" if a else ""]
            rows.append(
                row + [number(counts[Cell("floats", op, a, f)]) for f in formats]
            )
    return table(["op", "predicate", *(f"`{f}`" for f in formats)], rows)


def casts_table(counts: Counter, widths: tuple[int, ...]) -> list[str]:
    rows = []
    for op in cells.CASTS:
        for m in widths:
            row = [f"`{op}`", f"`i{m}`"]
            for n in widths:
                cell = Cell("casts", op, cells.ty(m), cells.ty(n))
                row.append(number(counts[cell]) if cells.allowed(op, m, n) else "")
            rows.append(row)
    return table(["op", "from", *(f"to `i{w}`" for w in widths)], rows)


def conversions_table(counts: Counter, formats: tuple[str, ...]) -> list[str]:
    rows = []
    for f in formats:
        i = cells.bits_type(f)
        for a, b in ((f, i), (i, f)):
            cell = Cell("conversions", "bitcast", a, b)
            rows.append(["`bitcast`", f"`{a}`", f"`{b}`", number(counts[cell])])
    return table(["op", "from", "to", "tests"], rows)


def int_to_float_table(
    counts: Counter, widths: tuple[int, ...], formats: tuple[str, ...]
) -> list[str]:
    rows = []
    for op in cells.INT_TO_FLOAT:
        for w in widths:
            row = [f"`{op}`", f"`i{w}`"]
            for f in formats:
                row.append(number(counts[Cell("conversions", op, cells.ty(w), f)]))
            rows.append(row)
    return table(["op", "from", *(f"to `{f}`" for f in formats)], rows)


def pointers_table(counts: Counter, offsets: tuple[int, ...]) -> list[str]:
    rows = [
        [f"`{op}`"]
        + [number(counts[Cell("pointers", op, "", cells.ty(w))]) for w in offsets]
        for op in cells.POINTER_OPS
    ]
    return table(["op", *(f"by `i{w}`" for w in offsets)], rows)


WHAT = {
    "br": {cells.NOTHING: "passes nothing", cells.PASSED: "passes values"},
    "cond_br": {
        cells.NOTHING: "a successor passes nothing",
        cells.PASSED: "a successor passes values",
    },
    "ret": {
        cells.NOTHING: "returns no value",
        cells.ONE: "returns one value",
        cells.SEVERAL: "returns several values",
    },
    "unreachable": {cells.NOTHING: "ends a block"},
    "call": {
        cells.NOTHING: "gives no result",
        cells.ONE: "gives one result",
        cells.SEVERAL: "gives several results",
    },
    "func": {
        cells.NOTHING: "returns no value",
        cells.ONE: "returns one value",
        cells.SEVERAL: "returns several values",
    },
}


def values_table(
    counts: Counter, widths: tuple[int, ...], formats: tuple[str, ...]
) -> list[str]:
    types = (*map(cells.ty, widths), *formats)
    rows = []
    for op, kinds in cells.VALUES:
        for k in kinds:
            row = [f"`{op}`", WHAT[op][k]]
            if k == cells.NOTHING:
                row += [number(counts[Cell("values", op, k, "")])] + [""] * len(types)
            else:
                row += [""] + [number(counts[Cell("values", op, k, t)]) for t in types]
            rows.append(row)
    return table(["op", "what", "no value", *(f"`{t}`" for t in types)], rows)


def render(counts: dict[str, Counter]) -> str:
    """The matrix as Markdown."""
    total = sum(len(side.cells()) for side in SIDES)
    gaps = empty(counts)
    lines = [
        "# Coverage matrix of the fir corpus",
        "",
        "Generated by `scripts/harness/coverage.py` from the tests of",
        "[`tests/fir/`](../../tests/fir/README.md); do not edit it by hand.",
        "Run `python3 scripts/harness/coverage.py --write` after changing the",
        "corpus. The `coverage-matrix` hook fails when this file is stale or a",
        "cell has no test. What a cell is, which widths each side covers and",
        "what a test exercises are decided in",
        "[ADR-2026-11-03-0557](../adrs/2026-11-03-0557-a-generated-matrix-counts-the-tests-of-each-cell.md).",
        "",
        "Each number is how many tests of the side exercise the cell: the",
        "ops of the function a test runs and of every function it calls,",
        "and, in the `func` rows, the results of the function it runs. An",
        "empty entry is not a cell: a width change that the spec does not",
        "allow, or a width for a row that passes no value.",
        "",
        f"{total} cells, {total - len(gaps)} with a test.",
    ]
    for side in SIDES:
        c, title = counts[side.name], side.title.lower()
        lines += ["", f"## {side.title}", ""]
        lines += [f"### Ops at a width ({title})", ""]
        lines += ops_table(c, side.widths)
        lines += ["", f"### Float ops at a format ({title})", ""]
        lines += floats_table(c, side.formats)
        lines += ["", f"### Width changes ({title})", ""]
        lines += casts_table(c, side.widths)
        lines += ["", f"### Conversions ({title})", ""]
        lines += conversions_table(c, side.formats)
        lines += ["", f"### Conversions from integers ({title})", ""]
        lines += int_to_float_table(c, side.widths, side.formats)
        if side.offsets:
            lines += ["", f"### Pointer offsets ({title})", ""]
            lines += pointers_table(c, side.offsets)
        lines += ["", f"### Passed and returned values ({title})", ""]
        lines += values_table(c, side.widths, side.formats)
    return "\n".join(lines) + "\n"


def run(root: Path, matrix: Path, write: bool, err) -> int:
    """Checks the matrix of the corpus at `root` against the file `matrix`,
    after writing it there if `write`, and reports to `err`."""
    try:
        counts = count(root)
    except CoverageError as e:
        print(f"coverage: {e}", file=err)
        return 2
    text = render(counts)
    if write:
        matrix.parent.mkdir(parents=True, exist_ok=True)
        matrix.write_text(text, encoding="utf-8")
    status = 0
    committed = matrix.read_text(encoding="utf-8") if matrix.exists() else None
    if committed != text:
        shown = matrix.relative_to(ROOT) if matrix.is_relative_to(ROOT) else matrix
        print(
            f"{shown} is stale: run python3 scripts/harness/coverage.py --write",
            file=err,
        )
        status = 1
    for gap in empty(counts):
        print(f"no test exercises the cell {gap}", file=err)
        status = 1
    return status


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(prog="coverage", description=__doc__.split("\n")[0])
    p.add_argument("--write", action="store_true", help="write the matrix first")
    args = p.parse_args(argv)
    return run(CORPUS, MATRIX, args.write, sys.stderr)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
