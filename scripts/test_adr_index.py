"""Tests for scripts/adr_index.py. Run: python scripts/test_adr_index.py"""

import io
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from adr_index import AdrError, holds, parse_adr, render, run


def adr_text(
    title: str = "A decision",
    status: str = "accepted",
    tier_line: str = "Tier: direction; area: process",
) -> str:
    return f"# {title}\n\nStatus: {status}\n{tier_line}\n\n## Context\n\nWhy.\n"


def parsed(name: str, **kwargs):
    return parse_adr(f"{name}-a-slug.md", adr_text(**kwargs))


class Parsing(unittest.TestCase):
    def test_reads_title_tier_and_area(self):
        adr = parsed("2030-01-01-0001", title="We do `x`")
        self.assertEqual(adr.id, "2030-01-01-0001")
        self.assertEqual(adr.file, "2030-01-01-0001-a-slug.md")
        self.assertEqual(adr.title, "We do `x`")
        self.assertEqual(adr.tier, "direction")
        self.assertEqual(adr.area, "process")
        self.assertIsNone(adr.superseded_by)
        self.assertEqual(adr.followed_by, [])

    def test_status_may_wrap_over_lines(self):
        adr = parsed(
            "2030-01-01-0001",
            status=(
                "accepted; extended by ADR-2030-01-01-0002 and\n"
                "ADR-2030-01-01-0003; refined by ADR-2030-01-01-0004,\n"
                "ADR-2030-01-01-000500 and ADR-2030-01-01-0006"
            ),
        )
        self.assertEqual(
            adr.followed_by,
            [
                "2030-01-01-0002",
                "2030-01-01-0003",
                "2030-01-01-0004",
                "2030-01-01-000500",
                "2030-01-01-0006",
            ],
        )

    def test_superseded(self):
        adr = parsed("2030-01-01-0001", status="superseded by ADR-2030-01-01-0002")
        self.assertEqual(adr.superseded_by, "2030-01-01-0002")
        self.assertEqual(adr.followed_by, [])

    def test_rejects_a_missing_tier_line(self):
        text = "# A decision\n\nStatus: accepted\n\n## Context\n"
        with self.assertRaisesRegex(AdrError, "Tier: "):
            parse_adr("2030-01-01-0001-a.md", text)

    def test_rejects_an_unknown_tier(self):
        with self.assertRaisesRegex(AdrError, "tier"):
            parsed("2030-01-01-0001", tier_line="Tier: strategic; area: process")

    def test_rejects_an_unknown_area(self):
        with self.assertRaisesRegex(AdrError, "area"):
            parsed("2030-01-01-0001", tier_line="Tier: direction; area: nowhere")

    def test_rejects_a_status_it_cannot_read(self):
        with self.assertRaisesRegex(AdrError, "Status"):
            parsed("2030-01-01-0001", status="accepted; refined by someone")

    def test_rejects_text_that_does_not_start_with_a_title(self):
        with self.assertRaisesRegex(AdrError, "title"):
            parse_adr("2030-01-01-0001-a.md", "Status: accepted\n")


class Holds(unittest.TestCase):
    def test_an_adr_nothing_follows_holds_itself(self):
        one = parsed("2030-01-01-0001")
        self.assertEqual(holds([one]), {one.id: [one.id]})

    def test_a_chain_lists_every_adr_it_reaches(self):
        first = parsed(
            "2030-01-01-0001",
            status="accepted; refined by ADR-2030-01-01-0002 and ADR-2030-01-01-0003",
        )
        second = parsed(
            "2030-01-01-0002", status="accepted; extended by ADR-2030-01-01-0004"
        )
        third = parsed("2030-01-01-0003")
        fourth = parsed("2030-01-01-0004")
        found = holds([first, second, third, fourth])
        self.assertEqual(
            found[first.id],
            [first.id, second.id, third.id, fourth.id],
        )
        self.assertEqual(found[second.id], [second.id, fourth.id])

    def test_a_superseded_adr_gives_way_to_its_successor(self):
        old = parsed("2030-01-01-0001", status="superseded by ADR-2030-01-01-0002")
        new = parsed("2030-01-01-0002")
        self.assertEqual(holds([old, new])[old.id], [new.id])

    def test_a_superseded_refiner_gives_way_in_a_chain(self):
        first = parsed(
            "2030-01-01-0001", status="accepted; refined by ADR-2030-01-01-0002"
        )
        second = parsed("2030-01-01-0002", status="superseded by ADR-2030-01-01-0003")
        third = parsed("2030-01-01-0003")
        self.assertEqual(holds([first, second, third])[first.id], [first.id, third.id])

    def test_a_chain_to_an_unknown_adr_is_an_error(self):
        one = parsed(
            "2030-01-01-0001", status="accepted; refined by ADR-2030-01-01-0009"
        )
        with self.assertRaisesRegex(AdrError, "2030-01-01-0009"):
            holds([one])

    def test_a_cycle_is_an_error(self):
        one = parsed(
            "2030-01-01-0001", status="accepted; refined by ADR-2030-01-01-0002"
        )
        two = parsed(
            "2030-01-01-0002", status="accepted; refined by ADR-2030-01-01-0001"
        )
        with self.assertRaisesRegex(AdrError, "cycle"):
            holds([one, two])


class Rendering(unittest.TestCase):
    def test_direction_comes_first_with_one_row_each(self):
        impl = parsed(
            "2030-01-01-0001",
            title="How a tool works",
            tier_line="Tier: implementation; area: fir-ref",
            status="accepted; refined by ADR-2030-01-01-0002",
        )
        direc = parsed("2030-01-01-0002", title="What fir is")
        text = render([impl, direc])
        self.assertLess(text.index("## Direction"), text.index("## Implementation"))
        rows = [line for line in text.splitlines() if line.startswith("| [ADR-")]
        self.assertEqual(
            rows,
            [
                (
                    "| [ADR-2030-01-01-0002](2030-01-01-0002-a-slug.md) | process"
                    " | What fir is | this ADR |"
                ),
                (
                    "| [ADR-2030-01-01-0001](2030-01-01-0001-a-slug.md) | fir-ref"
                    " | How a tool works | this ADR, ADR-2030-01-01-0002 |"
                ),
            ],
        )

    def test_a_pipe_in_a_title_stays_in_its_cell(self):
        text = render([parsed("2030-01-01-0001", title="a | b")])
        self.assertIn("a \\| b", text)


def git(repo: Path, *args: str) -> None:
    subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", *args],
        cwd=repo,
        check=True,
        capture_output=True,
    )


class Running(unittest.TestCase):
    def setUp(self):
        # A commit hook in a linked worktree inherits GIT_DIR. Left set, git
        # here would act on the real repository, not the scratch one.
        outside = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        patcher = mock.patch.dict(os.environ, outside, clear=True)
        patcher.start()
        self.addCleanup(patcher.stop)
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name)
        self.adrs = self.repo / "docs" / "adrs"
        self.adrs.mkdir(parents=True)
        git(self.repo, "init", "-q")

    def add(self, name: str, text: str) -> None:
        (self.adrs / name).write_text(text, encoding="utf-8")
        git(self.repo, "add", f"docs/adrs/{name}")

    def run_it(self, write: bool = False) -> tuple[int, str]:
        err = io.StringIO()
        return run(self.repo, write, err), err.getvalue()

    def test_write_then_a_check_passes(self):
        self.add("README.md", "# ADRs\n")
        self.add("2030-01-01-0001-a.md", adr_text())
        self.assertEqual(self.run_it(write=True), (0, ""))
        self.assertEqual(self.run_it(), (0, ""))
        text = (self.adrs / "INDEX.md").read_text(encoding="utf-8")
        self.assertIn("ADR-2030-01-01-0001", text)
        self.assertNotIn("README", text.split("## Direction")[1])

    def test_a_stale_index_fails_and_says_how_to_fix_it(self):
        self.add("2030-01-01-0001-a.md", adr_text())
        (self.adrs / "INDEX.md").write_text("old\n", encoding="utf-8")
        status, message = self.run_it()
        self.assertEqual(status, 1)
        self.assertIn("python3 scripts/adr_index.py --write", message)

    def test_a_missing_index_fails(self):
        self.add("2030-01-01-0001-a.md", adr_text())
        self.assertEqual(self.run_it()[0], 1)

    def test_an_untracked_adr_is_ignored(self):
        self.add("2030-01-01-0001-a.md", adr_text())
        self.run_it(write=True)
        (self.adrs / "2030-01-01-0002-b.md").write_text("no tier\n", encoding="utf-8")
        self.assertEqual(self.run_it(), (0, ""))

    def test_an_adr_without_a_tier_fails_and_is_named(self):
        self.add("2030-01-01-0001-a.md", "# A\n\nStatus: accepted\n\n## Context\n")
        status, message = self.run_it()
        self.assertEqual(status, 1)
        self.assertIn("2030-01-01-0001-a.md", message)


if __name__ == "__main__":
    unittest.main()
