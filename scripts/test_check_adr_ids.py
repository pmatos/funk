"""Tests for scripts/check_adr_ids.py. Run: python scripts/test_check_adr_ids.py"""

import contextlib
import io
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from check_adr_ids import Removed, annotate, parse_removed, problems

SCRIPT = Path(__file__).with_name("check_adr_ids.py")


def adrs(*names: str) -> list[str]:
    return [f"docs/adrs/{name}" for name in names]


class Names(unittest.TestCase):
    def test_both_forms_pass(self):
        self.assertEqual(
            problems(
                adrs(
                    "README.md",
                    "INDEX.md",
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
            "\uff12026-10-30-1031-fullwidth-digit.md",
            "2026-10-30-103\u0661-arabic-indic-digit.md",
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
        self.assertIn("Change the seconds of the newer one", found[0])

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


def row(
    file: str = "2026-10-30-1031-a.md",
    now: str = "ADR-2026-10-30-1046",
    commit: str = "0123456789ab",
) -> str:
    return f'{{"file": "{file}", "now": "{now}", "commit": "{commit}"}}'


def table(*rows: str) -> str:
    return '{"about": "x", "removed": [' + ", ".join(rows) + "]}"


class RemovedIds(unittest.TestCase):
    def test_rows_parse_in_order(self):
        rows = parse_removed(table(row(), row("2026-10-30-103112-b.md", "here")))
        self.assertEqual(
            rows,
            [
                Removed(
                    "2026-10-30-1031",
                    "2026-10-30-1031-a.md",
                    "ADR-2026-10-30-1046",
                    "0123456789ab",
                ),
                Removed(
                    "2026-10-30-103112",
                    "2026-10-30-103112-b.md",
                    "here",
                    "0123456789ab",
                ),
            ],
        )

    def test_bad_tables_fail(self):
        bad = {
            "not JSON": "{",
            'no list "removed"': '{"removed": {}}',
            "exactly the keys": table('{"file": "2026-10-30-1031-a.md"}'),
            "every value is a string": table(
                '{"file": "2026-10-30-1031-a.md", "now": 1, "commit": "0123456789ab"}'
            ),
            "not an ADR file name": table(row(file="notes.md")),
            "where the rule lives": table(row(now=" ")),
            "hex digits": table(row(commit="0123456")),
            "has a row already": table(row(), row(file="2026-10-30-1031-b.md")),
        }
        for message, text in bad.items():
            with (
                self.subTest(message=message),
                self.assertRaisesRegex(ValueError, message),
            ):
                parse_removed(text)

    def test_a_removed_id_is_never_used_again(self):
        removed = parse_removed(table(row()))
        found = problems(
            adrs(
                "2026-10-30-1031-new.md",
                "2026-10-30-1032-b.md",
                "removed/semantics.json",
            ),
            removed,
        )
        self.assertEqual(len(found), 1)
        self.assertTrue(
            found[0].startswith(
                "docs/adrs/2026-10-30-1031-new.md: ADR-2026-10-30-1031 was removed"
            )
        )
        self.assertEqual(problems(adrs("2026-10-30-103100-new.md"), removed), [])


def outside_env() -> dict[str, str]:
    # A commit hook runs with GIT_INDEX_FILE and similar set for this
    # repository; drop them so git in a scratch repository uses its own.
    return {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}


def git(repo: Path, *args: str) -> None:
    subprocess.run(["git", *args], cwd=repo, env=outside_env(), check=True)


def run_script(cwd: Path, *args: str):
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        check=False,
        cwd=cwd,
        env=outside_env(),
        capture_output=True,
        text=True,
    )


class Repository(unittest.TestCase):
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
            self.assertEqual(run_script(repo).returncode, 0)

            git(repo, "add", "docs/adrs/2026-10-30-1031-b.md")
            result = run_script(repo)
            self.assertEqual(result.returncode, 1)
            self.assertIn("docs/adrs/2026-10-30-1031-a.md", result.stderr)
            self.assertIn("docs/adrs/2026-10-30-1031-b.md", result.stderr)
            self.assertIn("Add the seconds to the newer one", result.stderr)

            nested = run_script(repo / "docs")
            self.assertEqual(nested.returncode, 1)
            self.assertIn("docs/adrs/2026-10-30-1031-b.md", nested.stderr)

    def test_a_removed_id_in_the_repository_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            tables = repo / "docs" / "adrs" / "removed"
            tables.mkdir(parents=True)
            (tables / "semantics.json").write_text(table(row()) + "\n")
            (repo / "docs" / "adrs" / "2026-10-30-1031-again.md").write_text("# ADR\n")
            git(repo, "init", "-q")
            git(repo, "add", "docs/adrs/removed/semantics.json")
            self.assertEqual(run_script(repo).returncode, 0)
            git(repo, "add", "docs/adrs/2026-10-30-1031-again.md")
            result = run_script(repo / "docs")
            self.assertEqual(result.returncode, 1)
            self.assertIn("ADR-2026-10-30-1031 was removed", result.stderr)
            (tables / "semantics.json").write_text("{}\n")
            self.assertIn("docs/adrs/removed/semantics.json: ", run_script(repo).stderr)

    def test_a_file_under_removed_that_is_not_a_table_fails(self):
        for name in ("semantics.jsn", "old/semantics.json"):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as tmp:
                repo = Path(tmp)
                stray = repo / "docs" / "adrs" / "removed" / name
                stray.parent.mkdir(parents=True)
                stray.write_text(table(row()) + "\n")
                git(repo, "init", "-q")
                git(repo, "add", "docs/adrs/removed")
                result = run_script(repo)
                self.assertEqual(result.returncode, 1)
                self.assertIn(
                    f"docs/adrs/removed/{name}: not a removed table", result.stderr
                )

    def test_an_id_with_rows_in_two_tables_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            tables = repo / "docs" / "adrs" / "removed"
            tables.mkdir(parents=True)
            (tables / "process.json").write_text(table(row()) + "\n")
            (tables / "semantics.json").write_text(table(row()) + "\n")
            git(repo, "init", "-q")
            git(repo, "add", "docs/adrs/removed")
            self.assertIn(
                "docs/adrs/removed/semantics.json: ADR-2026-10-30-1031 has a row"
                " already, in docs/adrs/removed/process.json",
                run_script(repo).stderr,
            )


class WarnAdded(unittest.TestCase):
    """--warn-added warns when HEAD adds more than two ADRs, and never fails."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name)
        self.adrs = self.repo / "docs" / "adrs"
        self.adrs.mkdir(parents=True)
        git(self.repo, "init", "-q")
        self.commit("2026-10-30-1031-old.md", "README.md")

    def commit(self, *names: str) -> None:
        for name in names:
            (self.adrs / name).write_text(f"# {name}\n")
        git(self.repo, "add", "docs")
        git(
            self.repo,
            "-c", "user.name=t", "-c", "user.email=t@t", "-c", "core.hooksPath=/dev/null",
            "commit", "-q", "-m", "x",
        )  # fmt: skip

    def warned(self):
        result = run_script(self.repo / "docs", "--warn-added")
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_two_new_adrs_warn_nothing(self):
        self.commit("2026-10-30-1032-a.md", "2026-10-30-1033-b.md", "INDEX.md")
        out = self.warned()
        self.assertIn("2 ADRs added to HEAD^1.", out)
        self.assertNotIn("::warning", out)

    def test_three_new_adrs_warn_on_one_line(self):
        names = ("2026-10-30-1032-a.md", "2026-10-30-1033-b.md", "2026-10-30-1034-c.md")
        self.commit(*names)
        warning = [line for line in self.warned().splitlines() if "::warning" in line]
        self.assertEqual(len(warning), 1)
        self.assertTrue(
            warning[0].startswith(
                "::warning title=More than 2 ADRs::This pull request adds 3 ADRs"
            )
        )
        for name in names:
            self.assertIn(f"docs/adrs/{name}", warning[0])

    def test_a_slug_renamed_or_changed_adr_is_not_added(self):
        git(
            self.repo,
            "mv",
            "docs/adrs/2026-10-30-1031-old.md",
            "docs/adrs/2026-10-30-1031-new.md",
        )
        self.commit("2026-10-30-1032-a.md", "2026-10-30-1033-b.md", "README.md")
        self.assertIn("2 ADRs added to HEAD^1.", self.warned())

    def test_an_adr_moved_to_a_new_id_is_added(self):
        for old, new in (("1040", "1140"), ("1041", "1141"), ("1042", "1142")):
            (self.adrs / f"2026-10-30-{old}-same.md").write_text("# The same text\n")
        self.commit()
        for old, new in (("1040", "1140"), ("1041", "1141"), ("1042", "1142")):
            git(
                self.repo,
                "mv",
                f"docs/adrs/2026-10-30-{old}-same.md",
                f"docs/adrs/2026-10-30-{new}-same.md",
            )
        self.commit()
        self.assertIn("::warning title=More than 2 ADRs::", self.warned())

    def test_no_first_parent_warns_on_one_line_and_passes(self):
        result = run_script(self.repo, "--warn-added")
        self.assertEqual(result.returncode, 0)
        lines = result.stdout.splitlines()
        self.assertEqual(len(lines), 1)
        self.assertTrue(lines[0].startswith("::warning title=ADRs added::cannot read"))

    def test_a_warning_escapes_its_line_breaks(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            annotate("T", "100% sure\r\nnext")
        self.assertEqual(out.getvalue(), "::warning title=T::100%25 sure%0D%0Anext\n")


if __name__ == "__main__":
    unittest.main()
