"""Tests for scripts/check_adr_citations.py. Run: python scripts/test_check_adr_citations.py"""

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from check_adr_citations import FIXTURES, check_text, citations, line_column, problems

SCRIPT = Path(__file__).with_name("check_adr_citations.py")
CASES = Path(__file__).parent.parent / "docs/spec/FirSpecSite/citation-cases.json"


class SharedCases(unittest.TestCase):
    """The cases that the spec's checker passes too (ADR-2026-11-05-1709)."""

    def test_every_case(self):
        table = json.loads(CASES.read_text(encoding="utf-8"))
        known = set(table["known"])
        self.assertGreater(len(table["cases"]), 0)
        for case in table["cases"]:
            text = case["text"]
            with self.subTest(about=case["about"]):
                found = []
                for pos, ident, _ in citations(text):
                    line, col = line_column(text, pos)
                    found.append(f"{line}:{col} ADR-{ident}")
                self.assertEqual(found, case["citations"])
                self.assertEqual(check_text(known, "a.md", text), case["errors"])


def outside_env() -> dict[str, str]:
    # A commit hook runs with GIT_INDEX_FILE and similar set for this
    # repository; drop them so git in a scratch repository uses its own.
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, env=outside_env(), check=True)


def write(repo: Path, path: str, text: str | bytes) -> None:
    target = repo / path
    target.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(text, bytes):
        target.write_bytes(text)
    else:
        target.write_text(text, encoding="utf-8")


def run_script(cwd: Path):
    return subprocess.run(
        [sys.executable, str(SCRIPT)],
        check=False,
        cwd=cwd,
        env=outside_env(),
        capture_output=True,
        text=True,
    )


class Repository(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name)
        git(self.repo, "init", "-q")
        write(self.repo, "docs/adrs/README.md", "Cite one as `ADR-YYYY-MM-DD-HHMM`.\n")
        write(self.repo, "docs/adrs/2026-10-30-1031-a.md", "# A\n\nStatus: accepted\n")
        write(
            self.repo,
            "docs/adrs/2026-10-30-103112-b.md",
            "# B\n\nSee ADR-2026-10-30-1031.\n",
        )
        self.add("docs/adrs")

    def tearDown(self):
        self.tmp.cleanup()

    def add(self, *paths: str) -> None:
        git(self.repo, "add", "--", *paths)

    def check(self, fixtures=None):
        return problems(self.repo, {} if fixtures is None else fixtures)

    def test_citations_of_tracked_adrs_pass(self):
        write(
            self.repo, "src/a.rs", "// ADR-2026-10-30-1031 and ADR-2026-10-30-103112\n"
        )
        self.add("src/a.rs")
        self.assertEqual(self.check(), ([], 3))

    def test_every_tracked_text_file_is_read(self):
        write(self.repo, "README.md", "ok\nsee ADR-2026-10-30-1032\n")
        write(self.repo, "a/b/c.yaml", "# ADR-2026-10-30-10311\n")
        self.add("README.md", "a/b/c.yaml")
        found, _ = self.check()
        self.assertEqual(
            found,
            [
                "README.md:2:5: ADR-2026-10-30-1032 names no ADR in docs/adrs/",
                (
                    "a/b/c.yaml:1:3: ADR-2026-10-30-10311 is not an ADR id,"
                    " which ends in HHMM or HHMMSS"
                ),
            ],
        )

    def test_untracked_binary_and_code_are_not_read(self):
        write(self.repo, "notes.md", "ADR-2026-10-30-1032\n")
        write(self.repo, "blob.bin", b"\0ADR-2026-10-30-1032\n")
        write(self.repo, "latin1.txt", b"\xe9 ADR-2026-10-30-1032\n")
        write(
            self.repo,
            "code.md",
            "`ADR-2026-10-30-1032`\n```\nADR-2026-10-30-1033\n```\n",
        )
        self.add("blob.bin", "latin1.txt", "code.md")
        self.assertEqual(self.check(), ([], 1))

    def test_an_adr_removed_breaks_its_citations(self):
        git(self.repo, "rm", "-q", "--cached", "docs/adrs/2026-10-30-1031-a.md")
        found, _ = self.check()
        self.assertEqual(
            found,
            [
                "docs/adrs/2026-10-30-103112-b.md:3:5: ADR-2026-10-30-1031 names no ADR in docs/adrs/"
            ],
        )

    def test_misnamed_adrs_name_nothing(self):
        write(self.repo, "docs/adrs/2026-02-30-1200-not-real.md", "# C\n")
        write(self.repo, "docs/adrs/old/2026-10-30-1200-nested.md", "# D\n")
        write(self.repo, "x.md", "ADR-2026-02-30-1200 ADR-2026-10-30-1200\n")
        self.add("docs/adrs", "x.md")
        found, _ = self.check()
        self.assertEqual(len(found), 2)

    def test_fixtures_are_skipped_but_must_be_needed(self):
        write(self.repo, "t.py", "ADR-2026-10-30-9999\n")
        write(self.repo, "u.py", "ADR-2026-10-30-1031\n")
        self.add("t.py", "u.py")
        self.assertEqual(self.check({"t.py": ""}), ([], 2))
        found, _ = self.check({"t.py": "", "u.py": "", "gone.py": ""})
        self.assertEqual(len(found), 2)
        self.assertTrue(found[0].startswith("u.py: in FIXTURES"))
        self.assertIn("remove it from the list", found[0])
        self.assertTrue(found[1].startswith("gone.py: in FIXTURES"))
        self.assertIn("not tracked", found[1])

    def test_script_reports_and_exits(self):
        for path in FIXTURES:
            write(self.repo, path, "ADR-2026-10-30-9999\n")
        self.add(*FIXTURES)
        ok = run_script(self.repo / "docs")
        self.assertEqual(ok.returncode, 0, ok.stderr)
        self.assertIn("1 ADR citations outside code name an ADR", ok.stdout)

        write(self.repo, "docs/x.md", "ADR-2026-10-30-1032\n")
        self.add("docs/x.md")
        bad = run_script(self.repo)
        self.assertEqual(bad.returncode, 1)
        self.assertIn("docs/x.md:1:1: ADR-2026-10-30-1032 names no ADR", bad.stderr)


if __name__ == "__main__":
    unittest.main()
