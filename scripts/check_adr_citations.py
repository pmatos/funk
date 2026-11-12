"""Fail when an ADR citation in a tracked text file names no ADR.

A citation is `ADR-`, a date `YYYY-MM-DD-` and a run of digits, and ends with
the run's last digit, so `ADR-2026-10-30-1031` never matches the start of
`ADR-2026-10-30-103112`. The run must have four or six digits; any other
length is a malformed citation. Placeholders such as `ADR-YYYY-MM-DD-HHMM`
are not citations, and a citation in a code span or a fenced code block is
quoted, not cited. This is the grammar of the spec's checker,
docs/spec/FirSpecSite/Citation.lean
(docs/decisions/spec-site.md#the-adr-appendix-and-its-citations), ported line for
line, and both test suites read the cases of
docs/spec/FirSpecSite/citation-cases.json, so the two cannot drift
(ADR-2026-11-05-1709).

The check reads every text file that git tracks, not only the ones a commit
changes, since renaming or deleting an ADR breaks citations elsewhere. A
citation of a deleted ADR, one with a row in docs/adrs/removed.json, fails
with where its rule lives now. The
files of FIXTURES hold bad citations on purpose, as test data, and are not
checked; each must still hold one, or the list has gone stale.
"""

import re
import subprocess
import sys
from pathlib import Path

from check_adr_ids import RemovedError, adr_id, removed_adrs

FIXTURES = {
    "docs/spec/FirSpecSite/Tests.lean": "the spec checker's tests of linking and rendering",
    "docs/spec/FirSpecSite/citation-cases.json": "the grammar's cases, which both checkers read",
    "scripts/test_adr_index.py": "the adr-index tests, which invent ADRs",
    "scripts/test_check_adr_ids.py": "the adr-ids tests, which name clashing ids",
    "scripts/test_check_adr_citations.py": "this check's tests",
}

CITATION = re.compile(r"ADR-([0-9]{4}-[0-9]{2}-[0-9]{2}-([0-9]+))")


def run_length(line: str, i: int, c: str) -> int:
    n = 0
    while i + n < len(line) and line[i + n] == c:
        n += 1
    return n


def blank_code_spans(line: str) -> str:
    """Return `line` with each code span, from a run of backticks to the next
    run of the same length, blanked out."""
    out = list(line)
    i = 0
    while i < len(line):
        if line[i] != "`":
            i += 1
            continue
        n = run_length(line, i, "`")
        j = i + n
        close = None
        while j < len(line) and close is None:
            if line[j] == "`":
                m = run_length(line, j, "`")
                if m == n:
                    close = j + m
                j += m
            else:
                j += 1
        if close is None:
            i += n
        else:
            out[i:close] = " " * (close - i)
            i = close
    return "".join(out)


def is_fence(line: str) -> bool:
    rest = line.lstrip(" ")
    return rest.startswith(("```", "~~~"))


def blank_code(text: str) -> str:
    """Return `text` with its code spans and fenced code blocks, fences
    included, blanked out. Line breaks stay, so positions do not move."""
    out = []
    in_fence = False
    for line in text.split("\n"):
        if is_fence(line):
            in_fence = not in_fence
            out.append(" " * len(line))
        elif in_fence:
            out.append(" " * len(line))
        else:
            out.append(blank_code_spans(line))
    return "\n".join(out)


def line_column(text: str, pos: int) -> tuple[int, int]:
    """Return the 1-based line and column of the character at `pos`."""
    line_start = text.rfind("\n", 0, pos) + 1
    return text.count("\n", 0, pos) + 1, pos - line_start + 1


def citations(text: str) -> list[tuple[int, str, bool]]:
    """Return each citation outside code as (position, id, well formed)."""
    return [
        (m.start(), m[1], len(m[2]) in (4, 6))
        for m in CITATION.finditer(blank_code(text))
    ]


def check_text(known, path: str, text: str, removed=None) -> list[str]:
    """Return one message per citation in `text`, the contents of `path`,
    that names no ADR in `known`. `removed` maps the id of each removed ADR
    to where its rule lives now."""
    removed = removed or {}
    found = []
    for pos, ident, well_formed in citations(text):
        line, col = line_column(text, pos)
        if not well_formed:
            found.append(
                f"{path}:{line}:{col}: ADR-{ident} is not an ADR id,"
                " which ends in HHMM or HHMMSS"
            )
        elif ident in removed:
            found.append(
                f"{path}:{line}:{col}: ADR-{ident} was removed; its rule lives"
                f" in {removed[ident]} now (docs/adrs/INDEX.md, Removed)"
            )
        elif ident not in known:
            found.append(f"{path}:{line}:{col}: ADR-{ident} names no ADR in docs/adrs/")
    return found


def read_text(path: Path) -> str | None:
    """Return the contents of a text file, else None."""
    if path.is_symlink() or not path.is_file():
        return None
    data = path.read_bytes()
    if b"\0" in data:
        return None
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return None


def git_lines(root: Path, *args: str) -> list[str]:
    out = subprocess.run(
        ["git", *args], cwd=root, check=True, capture_output=True, text=True
    ).stdout
    return [path for path in out.split("\0") if path]


def problems(root: Path, fixtures) -> tuple[list[str], int]:
    """Return the messages for the repository at `root`, and the number of
    citations outside code in the files checked."""
    tracked = git_lines(root, "ls-files", "-z")
    known = set()
    for path in tracked:
        if path.startswith("docs/adrs/"):
            ident = adr_id(path.removeprefix("docs/adrs/"))
            if ident is not None:
                known.add(ident)
    found = []
    try:
        removed = {row.id: row.now for row in removed_adrs(root)}
    except RemovedError as e:
        found.append(str(e))
        removed = {}
    count = 0
    for path in tracked:
        text = read_text(root / path)
        if text is None or "ADR-" not in text:
            text = ""
        errors = check_text(known, path, text, removed)
        if path in fixtures:
            if not errors:
                found.append(
                    f"{path}: in FIXTURES of scripts/check_adr_citations.py but"
                    " cites no missing ADR; remove it from the list"
                )
            continue
        found.extend(errors)
        count += len(citations(text))
    missing = sorted(set(fixtures) - set(tracked))
    for path in missing:
        found.append(
            f"{path}: in FIXTURES of scripts/check_adr_citations.py but not"
            " tracked; remove it from the list"
        )
    return found, count


def main() -> int:
    root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    found, count = problems(Path(root), FIXTURES)
    for message in found:
        print(message, file=sys.stderr)
    if found:
        print(
            "\nCite an ADR as ADR- and the id at the start of its file name"
            " in docs/adrs/ (ADR-2026-11-05-1709).",
            file=sys.stderr,
        )
        return 1
    print(f"{count} ADR citations outside code name an ADR in docs/adrs/.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
