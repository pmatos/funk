"""Fail when an ADR is misnamed, two ADRs share a timestamp id, or an ADR
takes the id of a removed one.

An ADR is named `YYYY-MM-DD-HHMM-slug.md`, or `YYYY-MM-DD-HHMMSS-slug.md` when
its minute is already taken, and its id is the whole timestamp
(docs/adrs/README.md). The check reads the ADRs that git tracks, so it sees
every ADR, not only the ones a commit changes, and ignores untracked files.

A deleted ADR has a row in docs/adrs/removed.json, and its id is never used
again. `adr_index.py` renders the rows as the Removed table of INDEX.md, and
`check_adr_citations.py` points a citation of a removed id at the row.

With `--warn-added`, it checks nothing and instead prints a GitHub
`::warning::` when HEAD adds more than two ADRs to its first parent. In CI,
HEAD is a pull request's merge with its base. It always exits with 0 then:
the count asks a reviewer to look again, and never fails.
"""

import argparse
import json
import re
import subprocess
import sys
from collections.abc import Sequence
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

ADR_DIR = "docs/adrs/"
REMOVED = "removed.json"
NOT_ADRS = ("README.md", "INDEX.md", REMOVED)
MOST_ADDED = 2
NAME = re.compile(
    r"(?P<id>[0-9]{4}-[0-9]{2}-[0-9]{2}-[0-9]{4}(?P<seconds>[0-9]{2})?)"
    r"-[a-z0-9]+(?:-[a-z0-9]+)*\.md"
)
COMMIT = re.compile(r"[0-9a-f]{12,40}")
ROW_KEYS = {"file", "now", "commit"}


def adr_id(name: str) -> str | None:
    """Return the id of a well-formed ADR file name, else None."""
    match = NAME.fullmatch(name)
    if match is None:
        return None
    form = "%Y-%m-%d-%H%M%S" if match["seconds"] else "%Y-%m-%d-%H%M"
    try:
        datetime.strptime(match["id"], form)
    except ValueError:
        return None
    return match["id"]


class RemovedError(ValueError):
    """A removed.json that cannot be read."""


@dataclass(frozen=True)
class Removed:
    """One row of removed.json: a deleted ADR and where its rule lives now."""

    id: str
    file: str
    now: str
    commit: str


def parse_row(where: str, row) -> Removed:
    """Return the row of removed.json `row`, called `where` in messages."""
    if not isinstance(row, dict) or set(row) != ROW_KEYS:
        raise RemovedError(f"{where}: needs exactly the keys {sorted(ROW_KEYS)}")
    if not all(isinstance(row[key], str) for key in ROW_KEYS):
        raise RemovedError(f"{where}: every value is a string")
    ident = adr_id(row["file"])
    if ident is None:
        raise RemovedError(f"{where}: {row['file']!r} is not an ADR file name")
    if not row["now"].strip():
        raise RemovedError(f"{where}: now must say where the rule lives now")
    if COMMIT.fullmatch(row["commit"]) is None:
        raise RemovedError(
            f"{where}: commit must be 12 to 40 lower-case hex digits of the"
            " last commit on main that changed the file"
        )
    return Removed(ident, row["file"], row["now"], row["commit"])


def parse_removed(text: str) -> list[Removed]:
    """Return the rows of removed.json, whose contents are `text`, in order.
    Raises RemovedError naming the first thing that is wrong."""
    try:
        table = json.loads(text)
    except json.JSONDecodeError as e:
        raise RemovedError(f"is not JSON: {e}") from e
    rows = table.get("removed") if isinstance(table, dict) else None
    if not isinstance(rows, list):
        raise RemovedError('has no list "removed"')
    found: list[Removed] = []
    for i, row in enumerate(rows):
        removed = parse_row(f"row {i + 1}", row)
        if any(r.id == removed.id for r in found):
            raise RemovedError(f"row {i + 1}: ADR-{removed.id} has a row already")
        found.append(removed)
    return found


def removed_adrs(root: Path) -> list[Removed]:
    """Return the rows of removed.json at `root`, or none when git does not
    track it: like every ADR hook, this reads what a commit holds."""
    path = f"{ADR_DIR}{REMOVED}"
    if not git("ls-files", "--", path, cwd=root).strip():
        return []
    try:
        return parse_removed((root / path).read_text(encoding="utf-8"))
    except ValueError as e:
        raise RemovedError(f"{path}: {e}") from e


def problems(paths: list[str], removed: Sequence[Removed] = ()) -> list[str]:
    """Return one message per misnamed ADR, per id that two ADRs share and
    per ADR whose id is a removed one's."""
    found = []
    by_id: dict[str, list[str]] = {}
    gone = {row.id for row in removed}
    for path in sorted(paths):
        name = path.removeprefix(ADR_DIR)
        if name in NOT_ADRS:
            continue
        ident = adr_id(name)
        if ident is None:
            found.append(
                f"{path}: not named YYYY-MM-DD-HHMM-slug.md or"
                " YYYY-MM-DD-HHMMSS-slug.md with a real date and UTC time,"
                " and a slug of lower-case words joined by hyphens"
            )
            continue
        by_id.setdefault(ident, []).append(path)
        if ident in gone:
            found.append(
                f"{path}: ADR-{ident} was removed ({ADR_DIR}{REMOVED}), and a"
                " removed id is never used again. Name the ADR with the UTC"
                " time it is written"
            )
    for ident, clash in by_id.items():
        if len(clash) > 1:
            fix = (
                "Change the seconds of the newer one"
                if len(ident) > len("YYYY-MM-DD-HHMM")
                else "Add the seconds to the newer one"
            )
            found.append(
                f"ADR-{ident} names {len(clash)} files: {', '.join(clash)}."
                f" {fix}, YYYY-MM-DD-HHMMSS-slug.md, at a second no other ADR"
                " uses, and update every reference to it"
            )
    return found


def git(*args: str, cwd: Path | None = None) -> str:
    return subprocess.run(
        ["git", *args], cwd=cwd, check=True, capture_output=True, text=True
    ).stdout


def tracked_adrs() -> list[str]:
    out = git("ls-files", "-z", "--full-name", "--", f":/{ADR_DIR}")
    return [path for path in out.split("\0") if path]


def adrs_at(rev: str) -> dict[str, str]:
    """Map the id of each ADR in commit `rev` to its path."""
    out = git("ls-tree", "-r", "-z", "--name-only", "--full-tree", rev, "--", ADR_DIR)
    found = {}
    for path in out.split("\0"):
        ident = adr_id(path.removeprefix(ADR_DIR))
        if ident is not None:
            found[ident] = path
    return found


def added_adrs() -> list[str]:
    """Return the ADRs that HEAD adds to its first parent, by id: an ADR moved
    to a new id counts as added, and one that keeps its id does not."""
    base = adrs_at("HEAD^1")
    return sorted(path for ident, path in adrs_at("HEAD").items() if ident not in base)


def annotate(title: str, message: str) -> None:
    """Print a GitHub warning; a workflow command ends at a line break."""
    for raw, escaped in (("%", "%25"), ("\r", "%0D"), ("\n", "%0A")):
        message = message.replace(raw, escaped)
    print(f"::warning title={title}::{message}")


def warn_added() -> None:
    try:
        added = added_adrs()
    except subprocess.CalledProcessError as e:
        annotate("ADRs added", f"cannot read HEAD^1: {e.stderr.strip()}")
        return
    print(f"{len(added)} ADRs added to HEAD^1.")
    if len(added) > MOST_ADDED:
        annotate(
            f"More than {MOST_ADDED} ADRs",
            f"This pull request adds {len(added)} ADRs: {', '.join(added)}."
            " Write an ADR only for a direction decision that binds more than"
            " one module or a future dialect or target (docs/adrs/README.md)."
            " Look again at whether each one is an ADR, or belongs in a doc"
            " comment or an area page.",
        )


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(
        prog="check_adr_ids", description=__doc__.split("\n")[0]
    )
    p.add_argument(
        "--warn-added",
        action="store_true",
        help="warn when HEAD adds more than two ADRs to its first parent",
    )
    args = p.parse_args(argv)
    if args.warn_added:
        warn_added()
        return 0
    root = Path(git("rev-parse", "--show-toplevel").strip())
    try:
        found = problems(tracked_adrs(), removed_adrs(root))
    except ValueError as e:
        found = [str(e)]
    for message in found:
        print(message, file=sys.stderr)
    if found:
        print(
            "\nADR names and ids follow docs/adrs/README.md.",
            file=sys.stderr,
        )
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
