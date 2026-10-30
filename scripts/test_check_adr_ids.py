"""Tests for scripts/check_adr_ids.py. Run: python scripts/test_check_adr_ids.py"""

import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from check_adr_ids import problems

SCRIPT = Path(__file__).with_name("check_adr_ids.py")
ROOT = SCRIPT.parent.parent


def adrs(*names: str) -> list[str]:
    return [f"docs/adrs/{name}" for name in names]


class Names(unittest.TestCase):
    def test_both_forms_pass(self):
        self.assertEqual(
            problems(
                adrs(
                    "README.md",
                    "2026-10-30-1031-publish-spec.md",
                    "2026-10-30-103112-generic-ops.md",
                    "2024-02-29-2359-leap-day.md",
                    "2026-10-30-235959-last-second.md",
                )
            ),
            [],
        )

    def test_bad_names_fail(self):
        bad = [
            "notes.md",
            "2026-10-30-1031.md",
            "2026-10-30-1031-.md",
            "2026-10-30-1031-Upper-case.md",
            "2026-10-30-1031-two--hyphens.md",
            "2026-10-30-1031-slug.txt",
            "2026-10-30-10311-five-digits.md",
            "2026-10-30-1031123-seven-digits.md",
            "26-10-30-1031-short-year.md",
            "2026-10-30-1031-slug.md~",
            "old/2026-10-30-1031-nested.md",
        ]
        found = problems(adrs(*bad))
        self.assertEqual(len(found), len(bad))
        for name, message in zip(sorted(bad), found):
            self.assertTrue(message.startswith(f"docs/adrs/{name}: not named"))

    def test_impossible_dates_and_times_fail(self):
        bad = [
            "2026-02-29-1200-not-a-leap-year.md",
            "2026-13-01-1200-month.md",
            "2026-10-32-1200-day.md",
            "2026-10-30-2400-hour.md",
            "2026-10-30-1260-minute.md",
            "2026-10-30-123060-second.md",
        ]
        self.assertEqual(len(problems(adrs(*bad))), len(bad))


class Ids(unittest.TestCase):
    def test_same_minute_clashes(self):
        found = problems(
            adrs(
                "2026-10-30-1031-publish-spec.md",
                "2026-10-30-1031-generic-ops.md",
            )
        )
        self.assertEqual(len(found), 1)
        self.assertIn("ADR-2026-10-30-1031 names 2 files", found[0])
        self.assertIn("docs/adrs/2026-10-30-1031-generic-ops.md", found[0])
        self.assertIn("docs/adrs/2026-10-30-1031-publish-spec.md", found[0])
        self.assertIn("Add the seconds to the newer one", found[0])

    def test_same_second_clashes(self):
        found = problems(adrs("2026-10-30-103112-a.md", "2026-10-30-103112-b.md"))
        self.assertEqual(len(found), 1)
        self.assertIn("ADR-2026-10-30-103112 names 2 files", found[0])

    def test_seconds_resolve_a_clash(self):
        names = adrs(
            "2026-10-30-1031-a.md",
            "2026-10-30-103100-b.md",
            "2026-10-30-103112-c.md",
        )
        self.assertEqual(problems(names), [])

    def test_every_file_of_an_id_is_named(self):
        found = problems(
            adrs("2026-10-30-1031-a.md", "2026-10-30-1031-b.md", "2026-10-30-1031-c.md")
        )
        self.assertEqual(len(found), 1)
        self.assertIn("names 3 files", found[0])


def outside_env() -> dict[str, str]:
    # A commit hook runs with GIT_INDEX_FILE and similar set for this
    # repository; drop them so git in a scratch repository uses its own.
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, env=outside_env(), check=True)


def run_script(cwd: Path, env: dict[str, str] | None = None):
    return subprocess.run(
        [sys.executable, str(SCRIPT)],
        check=False,
        cwd=cwd,
        env=env,
        capture_output=True,
        text=True,
    )


class Repository(unittest.TestCase):
    def test_this_repository_passes(self):
        result = run_script(ROOT)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_planted_clash_fails_and_untracked_files_are_ignored(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            adr_dir = repo / "docs" / "adrs"
            adr_dir.mkdir(parents=True)
            for name in ("README.md", "2026-10-30-1031-a.md", "2026-10-30-1031-b.md"):
                (adr_dir / name).write_text("# ADR\n")
            (adr_dir / ".2026-10-30-1031-a.md.swp").write_text("untracked\n")
            git(repo, "init", "-q")
            git(repo, "add", "docs/adrs/README.md", "docs/adrs/2026-10-30-1031-a.md")
            self.assertEqual(run_script(repo, outside_env()).returncode, 0)

            git(repo, "add", "docs/adrs/2026-10-30-1031-b.md")
            result = run_script(repo, outside_env())
            self.assertEqual(result.returncode, 1)
            self.assertIn("docs/adrs/2026-10-30-1031-a.md", result.stderr)
            self.assertIn("docs/adrs/2026-10-30-1031-b.md", result.stderr)
            self.assertIn("Add the seconds to the newer one", result.stderr)


if __name__ == "__main__":
    unittest.main()
