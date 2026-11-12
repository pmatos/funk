"""Tests for scripts/check_ci_hooks.py. Run: python scripts/test_check_ci_hooks.py"""

import io
import os
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

import yaml
from check_ci_hooks import commands, main, problems

REPO = Path(__file__).resolve().parent.parent
CONFIG = {
    "repos": [
        {
            "repo": "local",
            "hooks": [
                {"id": "lint", "entry": "lint", "language": "system"},
                {"id": "tests", "entry": "tests", "language": "system"},
            ],
        },
        {
            "repo": "https://example.com/msg",
            "rev": "v1",
            "hooks": [{"id": "msg", "stages": ["commit-msg"]}],
        },
    ]
}
RUN = "uvx pre-commit@4.6.2 run {} --all-files --verbose"


def job(*hooks: str, **fields) -> dict:
    steps = [{"uses": "actions/checkout@v7"}]
    steps += [{"run": RUN.format(h)} for h in hooks]
    return {"runs-on": "ubuntu-26.04", "steps": steps, **fields}


def gate(*needs: str) -> dict:
    return {"name": "pre-commit", "needs": list(needs), "if": "${{ always() }}"}


def ci(**jobs) -> dict:
    return {"name": "CI", "jobs": jobs}


TITLE = {
    "jobs": {
        "pr-title": {
            "steps": [
                {
                    "run": 'printf "%s" "$T" > t\n'
                    "uvx pre-commit@4.6.2 run msg \\\n"
                    '  --hook-stage commit-msg --commit-msg-filename "t"\n'
                }
            ]
        }
    }
}


class CheckCiHooks(unittest.TestCase):
    def setUp(self):
        self.repo = Path(self.enterContext(tempfile.TemporaryDirectory()))
        (self.repo / ".github" / "workflows").mkdir(parents=True)
        self.config(CONFIG)
        self.workflow("pr-title.yml", TITLE)
        env = {k: v for k, v in os.environ.items() if k != "GITHUB_STEP_SUMMARY"}
        self.enterContext(mock.patch.dict(os.environ, env, clear=True))

    def config(self, config: dict):
        (self.repo / ".pre-commit-config.yaml").write_text(yaml.safe_dump(config))

    def workflow(self, name: str, workflow: dict):
        path = self.repo / ".github" / "workflows" / name
        path.write_text(yaml.safe_dump(workflow, sort_keys=False))

    def found(self, workflow: dict) -> list[str]:
        self.workflow("ci.yml", workflow)
        return problems(self.repo)[0]

    def test_the_repository_passes(self):
        found, runs = problems(REPO)
        self.assertEqual(found, [])
        self.assertIn("conventional-pre-commit", runs)
        self.assertEqual(runs["rust-test"], [".github/workflows/ci.yml, job rust"])

    def test_every_hook_in_one_job_passes(self):
        good = ci(a=job("lint"), b=job("tests"), **{"pre-commit": gate("a", "b")})
        self.assertEqual(self.found(good), [])

    def test_a_hook_that_no_job_runs(self):
        found = self.found(ci(a=job("lint"), **{"pre-commit": gate("a")}))
        self.assertEqual(found, ["no CI job runs the hook tests"])

    def test_a_hook_that_two_jobs_run(self):
        found = self.found(
            ci(a=job("lint", "tests"), b=job("tests"), **{"pre-commit": gate("a", "b")})
        )
        self.assertEqual(len(found), 1)
        self.assertIn("the hook tests runs more than once", found[0])
        self.assertIn("job a; .github/workflows/ci.yml, job b", found[0])

    def test_a_hook_that_one_job_runs_twice(self):
        found = self.found(
            ci(a=job("lint", "tests", "lint"), **{"pre-commit": gate("a")})
        )
        self.assertEqual(len(found), 1)
        self.assertIn("the hook lint runs more than once", found[0])

    def test_a_hook_in_another_workflow_counts(self):
        self.workflow("other.yml", {"jobs": {"x": job("lint")}})
        found = self.found(ci(a=job("lint", "tests"), **{"pre-commit": gate("a")}))
        self.assertIn("the hook lint runs more than once", found[0])

    def test_a_hook_only_in_another_workflow_fails(self):
        self.workflow("other.yml", {"jobs": {"x": job("tests")}})
        found = self.found(ci(a=job("lint"), **{"pre-commit": gate("a")}))
        self.assertEqual(
            found,
            [
                (
                    "the hook tests runs in .github/workflows/other.yml, job x,"
                    " not in a job of ci.yml that the gate needs"
                )
            ],
        )

    def test_an_unknown_hook(self):
        found = self.found(
            ci(a=job("lint", "tests", "gone"), **{"pre-commit": gate("a")})
        )
        self.assertEqual(
            found, [".github/workflows/ci.yml, job a runs gone, which is not a hook"]
        )

    def test_every_hook_at_once_is_not_one_hook(self):
        steps = job("lint", "tests")
        steps["steps"].append({"run": "pre-commit run --all-files"})
        found = self.found(ci(a=steps, **{"pre-commit": gate("a")}))
        self.assertEqual(
            found,
            [
                ".github/workflows/ci.yml, job a runs pre-commit with no hook id after `run`"
            ],
        )

    def test_a_hook_without_all_files(self):
        steps = job("lint")
        steps["steps"].append({"run": "pre-commit run tests --files a.py"})
        found = self.found(ci(a=steps, **{"pre-commit": gate("a")}))
        self.assertEqual(
            found, [".github/workflows/ci.yml, job a runs tests without --all-files"]
        )

    def test_default_stages_with_pre_commit_keep_hooks_gated(self):
        self.config({**CONFIG, "default_stages": ["pre-commit", "pre-push"]})
        good = ci(a=job("lint", "tests"), **{"pre-commit": gate("a")})
        self.assertEqual(self.found(good), [])

    def test_default_stages_without_pre_commit_need_a_hook_stage(self):
        self.config({**CONFIG, "default_stages": ["pre-push"]})
        found = self.found(ci(a=job("lint", "tests"), **{"pre-commit": gate("a")}))
        self.assertEqual(
            found,
            [
                f".github/workflows/ci.yml, job a runs {hook} without"
                " --hook-stage and one of its stages, pre-push"
                for hook in ("lint", "tests")
            ],
        )

    def test_a_commit_msg_hook_needs_its_stage(self):
        title = {"jobs": {"pr-title": job("msg")}}
        self.workflow("pr-title.yml", title)
        found = self.found(ci(a=job("lint", "tests"), **{"pre-commit": gate("a")}))
        self.assertEqual(
            found,
            [
                (
                    ".github/workflows/pr-title.yml, job pr-title runs msg without"
                    " --hook-stage and one of its stages, commit-msg"
                )
            ],
        )

    def test_skip_anywhere_fails(self):
        base = ci(a=job("lint", "tests"), **{"pre-commit": gate("a")})
        for where in ("workflow", "job", "step"):
            workflow = yaml.safe_load(yaml.safe_dump(base))
            target = {
                "workflow": workflow,
                "job": workflow["jobs"]["a"],
                "step": workflow["jobs"]["a"]["steps"][1],
            }[where]
            target["env"] = {"SKIP": "tests"}
            with self.subTest(where=where):
                self.assertEqual(len(self.found(workflow)), 1)
        workflow = yaml.safe_load(yaml.safe_dump(base))
        workflow["jobs"]["a"]["steps"][1]["run"] = "SKIP=tests " + RUN.format("lint")
        self.assertEqual(
            self.found(workflow),
            [".github/workflows/ci.yml, job a sets SKIP in a command"],
        )

    def test_the_gate_needs_every_job(self):
        found = self.found(
            ci(a=job("lint"), b=job("tests"), **{"pre-commit": gate("a")})
        )
        self.assertEqual(found, ["ci.yml's job pre-commit does not need b"])

    def test_the_gate_runs_always(self):
        lax = {"name": "pre-commit", "needs": "a"}
        found = self.found(ci(a=job("lint", "tests"), **{"pre-commit": lax}))
        self.assertEqual(len(found), 1)
        self.assertIn("does not run always", found[0])

    def test_the_gate_keeps_its_name(self):
        renamed = {**gate("a"), "name": "Gate"}
        found = self.found(ci(a=job("lint", "tests"), **{"pre-commit": renamed}))
        self.assertEqual(
            found, ["ci.yml's job pre-commit is named 'Gate', not 'pre-commit'"]
        )
        found = self.found(ci(a=job("lint", "tests")))
        self.assertEqual(
            found, ["ci.yml has no job pre-commit, the required status check"]
        )

    def test_commands_join_continued_lines(self):
        script = (
            'echo "it\'s" # pre-commit run x\nuvx pre-commit run a \\\n  --all-files\n'
        )
        self.assertEqual(commands(script), [["run", "a", "--all-files"]])

    def test_main_writes_the_jobs_to_the_summary_in_ci(self):
        self.workflow("ci.yml", ci(a=job("lint", "tests"), **{"pre-commit": gate("a")}))
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(main([str(self.repo)]), 0)
        self.assertEqual(out.getvalue(), "")
        summary = self.repo / "summary.md"
        ci_env = {"GITHUB_STEP_SUMMARY": str(summary)}
        with mock.patch.dict(os.environ, ci_env), redirect_stdout(out):
            self.assertEqual(main([str(self.repo)]), 0)
        text = summary.read_text()
        self.assertIn("- .github/workflows/ci.yml, job a: `lint`, `tests`\n", text)
        self.assertIn("- .github/workflows/pr-title.yml, job pr-title: `msg`\n", text)
        self.assertEqual(out.getvalue(), text)

    def test_main_fails_with_each_problem(self):
        self.workflow("ci.yml", ci(a=job("lint"), **{"pre-commit": gate("a")}))
        err = io.StringIO()
        with redirect_stderr(err):
            self.assertEqual(main([str(self.repo)]), 1)
        self.assertEqual(err.getvalue(), "ci-hooks: no CI job runs the hook tests\n")


if __name__ == "__main__":
    unittest.main()
