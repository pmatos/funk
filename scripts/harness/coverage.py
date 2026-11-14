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
        return f"{cell.op} {'of' if cell.op == 'alloca' else 'by'} {cell.width}"
    words = [cell.op, cell.row]
    if cell.table == "values" and cell.row != cells.NOTHING:
        words.append("at")
    return " ".join(w for w in [*words, cell.width] if w)


def number(n: int) -> str:
    return f"{n}" if n else "**0**"


def table(head: list[str], rows: list[list[str]]) -> list[str]:
    out = ["| " + " | ".join(head) + " |", "|" + " --- |" * len(head)]
    return out + ["| " + " | ".join(r) + " |" for r in rows]


# Presentation metadata only: taxonomy membership, row order and blanks
# come from cells.catalog, shared with the gap enumeration.
SECTIONS = {
    "ops": ("Ops at a width", ("op", "flags or predicate"), ""),
    "floats": ("Float ops at a format", ("op", "predicate, attribute or flag"), ""),
    "casts": ("Width changes", ("op", "from"), "to "),
    "bitcasts": ("Conversions", ("op", "from", "to"), ""),
    "int_to_float": ("Conversions from integers", ("op", "from"), "to "),
    "float_conversions": ("Conversions between formats", ("from",), "to "),
    "float_to_int": ("Conversions to integers", ("op", "from"), "to "),
    "pointers": ("Pointer ops: ptradd by an integer, alloca of one", ("op",), ""),
    "values": ("Passed and returned values", ("op", "what"), ""),
}


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


def code(text: str) -> str:
    return f"`{text}`" if text else ""


def catalog_table(counts: Counter, spec: cells.Table) -> list[str]:
    """Render already-expanded cells, without knowing which pairs exist."""
    _, labels, prefix = SECTIONS[spec.kind]
    head = [
        *labels,
        *(
            f"{prefix}{code(t)}"
            if t
            else "tests"
            if spec.kind == "bitcasts"
            else "no value"
            for t in spec.columns
        ),
    ]
    rows = [catalog_row(counts, spec.kind, row) for row in spec.rows]
    return table(head, rows)


def catalog_row(counts: Counter, kind: str, row: cells.Row) -> list[str]:
    """Format a row's labels and cell counts, retaining applicability blanks."""
    if kind == "float_conversions":
        shown = [code(row.key)]
    elif kind == "pointers":
        shown = [code(row.op)]
    elif kind == "values":
        shown = [code(row.op), WHAT[row.op][row.key]]
    else:
        shown = [code(row.op), code(row.key)]
    if kind == "bitcasts":
        cell = row.entries[0]
        assert cell is not None
        shown.append(code(cell.width))
    for cell in row.entries:
        if cell is None:
            shown.append("")
        else:
            n = number(counts[cell])
            shown.append(f"{code(cell.op)} {n}" if kind == "float_conversions" else n)
    return shown


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
        "allow, a conversion from a format to itself, or a width for a row",
        "that passes no value.",
        "",
        f"{total} cells, {total - len(gaps)} with a test.",
    ]
    for side in SIDES:
        c, title = counts[side.name], side.title.lower()
        lines += ["", f"## {side.title}"]
        for spec in cells.catalog(side.widths, side.formats, side.offsets):
            heading = SECTIONS[spec.kind][0]
            lines += ["", f"### {heading} ({title})", ""]
            lines += catalog_table(c, spec)
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
