"""Fail when an ADR is misnamed or two ADRs share a timestamp id.

An ADR is named `YYYY-MM-DD-HHMM-slug.md`, or `YYYY-MM-DD-HHMMSS-slug.md` when
its minute is already taken, and its id is the whole timestamp
(docs/adrs/README.md). The check reads the ADRs that git tracks, so it sees
every ADR, not only the ones a commit changes, and ignores untracked files.
"""

import re
import subprocess
import sys
from datetime import datetime

ADR_DIR = "docs/adrs/"
NAME = re.compile(
    r"(?P<id>(\d{4})-(\d{2})-(\d{2})-(\d{2})(\d{2})(\d{2})?)"
    r"-[a-z0-9]+(?:-[a-z0-9]+)*\.md"
)


def adr_id(name: str) -> str | None:
    """Return the id of a well-formed ADR file name, else None."""
    match = NAME.fullmatch(name)
    if match is None:
        return None
    year, month, day, hour, minute, second = match.groups()[1:]
    try:
        datetime(
            int(year), int(month), int(day), int(hour), int(minute), int(second or 0)
        )
    except ValueError:
        return None
    return match["id"]


def problems(paths: list[str]) -> list[str]:
    """Return one message per misnamed ADR and per id that two ADRs share."""
    found = []
    by_id: dict[str, list[str]] = {}
    for path in sorted(paths):
        name = path.removeprefix(ADR_DIR)
        if name == "README.md":
            continue
        ident = adr_id(name)
        if ident is None:
            found.append(
                f"{path}: not named YYYY-MM-DD-HHMM-slug.md or"
                " YYYY-MM-DD-HHMMSS-slug.md with a real date and UTC time,"
                " and a slug of lower-case words joined by hyphens"
            )
        else:
            by_id.setdefault(ident, []).append(path)
    for ident, clash in by_id.items():
        if len(clash) > 1:
            found.append(
                f"ADR-{ident} names {len(clash)} files: {', '.join(clash)}."
                " Add the seconds to the newer one, YYYY-MM-DD-HHMMSS-slug.md,"
                " at a second no other ADR uses, and update every reference"
                " to it"
            )
    return found


def tracked_adrs() -> list[str]:
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", ADR_DIR],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return [path for path in out.split("\0") if path]


def main() -> int:
    found = problems(tracked_adrs())
    for message in found:
        print(message, file=sys.stderr)
    if found:
        print(
            "\nADR names and ids follow docs/adrs/README.md.",
            file=sys.stderr,
        )
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main())
