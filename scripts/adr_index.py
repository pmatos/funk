"""Generate docs/adrs/INDEX.md, and fail when it is stale or an ADR is unaccounted for.

Usage: adr_index.py [--write]

Each ADR ends its status paragraph with a line `Tier: TIER; area: AREA`
(ADR-2026-11-09-1610). The check reads the ADRs that git tracks, as the other
ADR hooks do, so stage a new ADR before running `--write`.

The index ends with the Removed table, one row per deleted ADR, from the
tables of docs/adrs/removed/, one per area. A row says where the rule lives now: an ADR, or a
page of docs/decisions/ and, after `#`, the anchor of one of its headings.
"""

import argparse
import re
import subprocess
import sys
from collections.abc import Sequence
from dataclasses import dataclass, field
from pathlib import Path

from check_adr_citations import citations
from check_adr_ids import REMOVED, Removed, RemovedError, adr_id, removed_adrs

ADR_DIR = "docs/adrs"
DECISIONS_DIR = "docs/decisions"
INDEX = "INDEX.md"
REPO_URL = "https://github.com/pmatos/funk"
TIERS = ("direction", "implementation")
AREAS = (
    "semantics",
    "text-format",
    "validation",
    "fir-ref",
    "rust-ir-and-tools",
    "x86-64-backend",
    "testing-and-harness",
    "spec-site",
    "process",
)

CITED = r"ADR-([0-9]{4}-[0-9]{2}-[0-9]{2}-(?:[0-9]{6}|[0-9]{4}))"
CITED_LIST = rf"{CITED}(?:(?:, | and ){CITED})*"
FOLLOWED = re.compile(rf"(?:refined|extended) by ({CITED_LIST})")
TIER_LINE = re.compile(r"Tier: (\S+); area: (\S+)")
PAGE_SECTION = re.compile(rf"{DECISIONS_DIR}/([^/#\s]+\.md)(?:#([a-z0-9_-]+))?")


class AdrError(Exception):
    """An ADR that the index cannot be built from."""


@dataclass
class Adr:
    id: str
    file: str
    title: str
    tier: str
    area: str
    followed_by: list[str] = field(default_factory=list)


def parse_status(file: str, status: str) -> list[str]:
    """Return the ADRs that refine or extend the ADR."""
    first, *clauses = status.split("; ")
    if first != "accepted":
        raise AdrError(
            f"{file}: Status must start with accepted. An ADR is edited in place"
            " when its decision changes, and a replaced one is deleted with a"
            f" row in {ADR_DIR}/{REMOVED}/AREA.json (docs/adrs/README.md)"
        )
    followed: list[str] = []
    for clause in clauses:
        match = FOLLOWED.fullmatch(clause)
        if match is None:
            raise AdrError(f"{file}: cannot read this part of Status: {clause!r}")
        followed += re.findall(CITED, match[1])
    return followed


def parse_adr(file: str, text: str) -> Adr:
    """Return the ADR of file name `file` whose Markdown is `text`."""
    ident = adr_id(file)
    if ident is None:
        raise AdrError(f"{file}: not named like an ADR")
    blocks = text.split("\n\n")
    if not blocks[0].startswith("# ") or "\n" in blocks[0]:
        raise AdrError(f"{file}: does not start with a one-line title")
    lines = blocks[1].splitlines() if len(blocks) > 1 else []
    if len(lines) < 2 or not lines[0].startswith("Status: "):
        raise AdrError(
            f"{file}: the title must be followed by a Status line and a last"
            " line `Tier: TIER; area: AREA`"
        )
    match = TIER_LINE.fullmatch(lines[-1])
    if match is None:
        raise AdrError(
            f"{file}: the last line of the status must be `Tier: TIER; area: AREA`"
        )
    tier, area = match[1], match[2]
    if tier not in TIERS:
        raise AdrError(
            f"{file}: the tier must be one of {', '.join(TIERS)}, not {tier}"
        )
    if area not in AREAS:
        raise AdrError(
            f"{file}: the area must be one of {', '.join(AREAS)}, not {area}"
        )
    status = " ".join(" ".join(lines[:-1]).removeprefix("Status: ").split())
    return Adr(ident, file, blocks[0][2:], tier, area, parse_status(file, status))


def holds(adrs: list[Adr]) -> dict[str, list[str]]:
    """Map each ADR's id to the ids that hold now: itself and every ADR its
    chain reaches."""
    by_id = {adr.id: adr for adr in adrs}
    done: dict[str, list[str]] = {}

    def held(ident: str, path: tuple[str, ...]) -> list[str]:
        if ident in path:
            raise AdrError(f"a cycle of Status lines runs through ADR-{ident}")
        if ident in done:
            return done[ident]
        adr = by_id.get(ident)
        if adr is None:
            raise AdrError(
                f"ADR-{path[-1]}: its Status names ADR-{ident}, which does not exist"
            )
        reached = {i for n in adr.followed_by for i in held(n, (*path, ident))}
        found = sorted(reached | {ident})
        done[ident] = found
        return found

    return {adr.id: held(adr.id, ()) for adr in adrs}


def removed_row(row: Removed, files: dict[str, str]) -> str:
    """Return the Removed table's row of `row`. `files` maps each ADR's id to
    its file. `removed_problems` says when the place it names does not exist."""
    if row.now.startswith("ADR-") and row.now[4:] in files:
        now = f"[{row.now}]({files[row.now[4:]]})"
    elif PAGE_SECTION.fullmatch(row.now):
        page = row.now.removeprefix(f"{DECISIONS_DIR}/")
        now = f"[{page}](../decisions/{page})"
    else:
        now = row.now.replace("|", "\\|")
    held = f"[`{row.commit}`]({REPO_URL}/blob/{row.commit}/{ADR_DIR}/{row.file})"
    return f"| `ADR-{row.id}` | {now} | {held} |"


def render(adrs: list[Adr], removed: Sequence[Removed] = ()) -> str:
    """Return the text of INDEX.md for `adrs` and the rows of the removed
    tables."""
    held = holds(adrs)
    lines = [
        "# Index of ADRs",
        "",
        "Generated by `scripts/adr_index.py` from the ADRs of this directory;",
        "do not edit it by hand. Stage a changed ADR, then run",
        "`python3 scripts/adr_index.py --write`. The `adr-index` hook fails when",
        "this file is stale, an ADR has no tier and area, or an accepted ADR is",
        "cited by no page of its area in `docs/decisions/`. ADR-2026-11-09-1610",
        "says what the tiers mean.",
        "",
        "The last column is what holds now: the ADR and every ADR that its",
        "`refined by` and `extended by` links reach, in order.",
    ]
    for tier in TIERS:
        rows = sorted((a for a in adrs if a.tier == tier), key=lambda a: a.id)
        lines += ["", f"## {tier.capitalize()}", ""]
        lines += ["| ADR | Area | Subject | Holds now |", "| --- | --- | --- | --- |"]
        for adr in rows:
            now = ", ".join(
                "this ADR" if i == adr.id else f"ADR-{i}" for i in held[adr.id]
            )
            title = adr.title.replace("|", "\\|")
            area = f"[{adr.area}](../decisions/{adr.area}.md)"
            lines.append(f"| [ADR-{adr.id}]({adr.file}) | {area} | {title} | {now} |")
    files = {adr.id: adr.file for adr in adrs}
    lines += [
        "",
        "## Removed",
        "",
        f"Each deleted ADR, from `{REMOVED}/`. Its id is never used again. The",
        "rule it held lives in the second column now, and the last column",
        "links the last commit on main that changed the file, which still holds it.",
        "",
        "| ADR | Its rule lives in | Last commit that held it |",
        "| --- | --- | --- |",
    ]
    lines += [removed_row(row, files) for row in sorted(removed, key=lambda r: r.id)]
    return "\n".join(lines) + "\n"


def tracked(root: Path, directory: str) -> list[str]:
    """Return the names of the files that git tracks directly in `directory`."""
    out = subprocess.run(
        ["git", "ls-files", "-z", "--", directory],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return [
        Path(path).name
        for path in out.split("\0")
        if path and Path(path).parent == Path(directory)
    ]


def tracked_adrs(root: Path) -> list[str]:
    return sorted(name for name in tracked(root, ADR_DIR) if adr_id(name) is not None)


def area_of_page(name: str) -> str | None:
    """Return the area of the page file `name`: AREA.md or AREA-TOPIC.md."""
    for area in AREAS:
        if name == f"{area}.md" or (
            name.startswith(f"{area}-") and name.endswith(".md")
        ):
            return area
    return None


def slugs(text: str) -> set[str]:
    """Return the anchors of the ATX headings in `text`, outside fenced code,
    as GitHub makes them: the text of a link or code span kept, lower case,
    without punctuation, spaces as hyphens, and `-1`, `-2` on repeats."""
    found: set[str] = set()
    in_fence = False
    for line in text.splitlines():
        if line.lstrip(" ").startswith(("```", "~~~")):
            in_fence = not in_fence
        heading = (
            None if in_fence else re.fullmatch(r" {0,3}#{1,6} +(.*?)(?: +#+)? *", line)
        )
        if heading:
            words = re.sub(r"\[([^]]*)\]\([^)]*\)", r"\1", heading[1]).lower()
            base = re.sub(r"[^\w\- ]", "", words).replace(" ", "-")
            slug, n = base, 0
            while slug in found:
                n += 1
                slug = f"{base}-{n}"
            found.add(slug)
    return found


def removed_problems(
    root: Path, removed: Sequence[Removed], adrs: list[Adr]
) -> list[str]:
    """Return one message per row of a removed table whose rule lives nowhere:
    in an ADR that does not exist, or a page or heading that does not."""
    found = []
    ids = {adr.id for adr in adrs}
    pages = set(tracked(root, DECISIONS_DIR))
    anchors: dict[str, set[str]] = {}
    for row in removed:
        table = row.table or f"{ADR_DIR}/{REMOVED}/"
        where = f"{table}: ADR-{row.id} lives in {row.now}"
        match = PAGE_SECTION.fullmatch(row.now)
        if row.now.startswith("ADR-"):
            if row.now[4:] not in ids:
                found.append(f"{where}, which is not an ADR of {ADR_DIR}/")
        elif match is None:
            found.append(
                f"{where}, which is neither ADR-ID nor {DECISIONS_DIR}/PAGE.md#ANCHOR"
            )
        elif match[1] not in pages:
            found.append(f"{where}, but {DECISIONS_DIR}/{match[1]} is not tracked")
        elif match[2]:
            if match[1] not in anchors:
                page = root / DECISIONS_DIR / match[1]
                anchors[match[1]] = slugs(page.read_text(encoding="utf-8"))
            if match[2] not in anchors[match[1]]:
                found.append(f"{where}, but that page has no heading #{match[2]}")
    return found


def page_problems(root: Path, adrs: list[Adr]) -> list[str]:
    """Return one message per page of no area, per area with no page, and per
    ADR that no page of its area cites outside code."""
    found = []
    names = sorted(tracked(root, DECISIONS_DIR))
    cited: dict[str, set[str]] = {area: set() for area in AREAS}
    for name in names:
        area = area_of_page(name)
        if area is None:
            found.append(f"{DECISIONS_DIR}/{name}: names no area of {', '.join(AREAS)}")
            continue
        text = (root / DECISIONS_DIR / name).read_text(encoding="utf-8")
        cited[area] |= {ident for _, ident, _ in citations(text)}
    for area in AREAS:
        if f"{area}.md" not in names:
            found.append(f"{DECISIONS_DIR}/{area}.md: the page of this area is missing")
    for adr in adrs:
        if adr.id not in cited[adr.area]:
            found.append(
                f"ADR-{adr.id}: no page of {DECISIONS_DIR}/ for its area"
                f" {adr.area} cites it"
            )
    return found


def load(root: Path, err) -> list[Adr] | None:
    """Return the tracked ADRs at `root`, or None after reporting to `err`."""
    adrs = []
    failed = False
    for name in tracked_adrs(root):
        try:
            adrs.append(
                parse_adr(name, (root / ADR_DIR / name).read_text(encoding="utf-8"))
            )
        except AdrError as e:
            print(f"{ADR_DIR}/{e}", file=err)
            failed = True
    return None if failed else adrs


def run(root: Path, write: bool, err) -> int:
    """Check INDEX.md of the repository at `root`, writing it first if `write`."""
    adrs = load(root, err)
    if adrs is None:
        return 1
    try:
        removed = removed_adrs(root)
        text = render(adrs, removed)
    except (AdrError, RemovedError) as e:
        print(e, file=err)
        return 1
    index = root / ADR_DIR / INDEX
    if write:
        index.write_text(text, encoding="utf-8")
    status = 0
    for problem in page_problems(root, adrs) + removed_problems(root, removed, adrs):
        print(problem, file=err)
        status = 1
    committed = index.read_text(encoding="utf-8") if index.exists() else None
    if committed != text:
        print(
            f"{ADR_DIR}/{INDEX} is stale: run python3 scripts/adr_index.py --write",
            file=err,
        )
        status = 1
    return status


def main(argv: list[str]) -> int:
    p = argparse.ArgumentParser(prog="adr_index", description=__doc__.split("\n")[0])
    p.add_argument("--write", action="store_true", help="write the index first")
    args = p.parse_args(argv)
    root = subprocess.run(
        ["git", "rev-parse", "--show-toplevel"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    return run(Path(root), args.write, sys.stderr)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
