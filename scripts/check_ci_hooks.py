"""Checks that CI runs every pre-commit hook in exactly one job (#148,
ADR-2026-11-05-1408).

Every check is a hook of .pre-commit-config.yaml, and the workflows of
.github/workflows/ run them by id, one hook per command, in one fixed form:
`pre-commit run ID` or `pre-commit@VERSION run ID`, with the id right after
`run`. It fails when:

- a hook is run by no step, or by more than one;
- a step runs a hook that the config does not have, or runs pre-commit
  without an id right after `run`;
- a hook of the `pre-commit` stage runs without `--all-files`, or a hook
  of other stages runs without `--hook-stage` and one of them;
- a workflow, job or step sets SKIP, or a step's command does;
- ci.yml's job `pre-commit`, the required status check, is missing, is
  named otherwise, does not need every other job of ci.yml, or does not
  run always, so that it fails when one of them failed, was cancelled or
  was skipped.

Usage: python scripts/check_ci_hooks.py [REPO]

When GITHUB_STEP_SUMMARY is set, it also lists each job's hooks there.
"""

import os
import re
import shlex
import sys
from pathlib import Path

import yaml

GATE = "pre-commit"
WORKFLOWS = Path(".github/workflows")


def hook_stages(config: dict) -> dict[str, list[str]]:
    """Each hook id of the config, with the stages it runs in ([] for all)."""
    default = config.get("default_stages", [])
    return {
        hook["id"]: hook.get("stages", default)
        for repo in config.get("repos", [])
        for hook in repo.get("hooks", [])
    }


def commands(script: str) -> list[list[str]]:
    """The words of each command in `script` that runs pre-commit."""
    found = []
    for line in script.replace("\\\n", " ").splitlines():
        try:
            words = shlex.split(line, comments=True)
        except ValueError:
            words = line.split()
        for i, word in enumerate(words):
            if re.fullmatch(r"pre-commit(@\S+)?", word.split("/")[-1]):
                found.append(words[i + 1 :])
    return found


def sets_skip(env) -> bool:
    return isinstance(env, dict) and "SKIP" in env


def workflow_problems(name: str, workflow: dict, stages: dict, runs: dict) -> list[str]:
    """What is wrong in one workflow; adds each hook it runs to `runs`, as
    hook id -> the jobs that run it."""
    found = []
    if sets_skip(workflow.get("env")):
        found.append(f"{name} sets SKIP")
    for job_id, job in (workflow.get("jobs") or {}).items():
        where = f"{name}, job {job_id}"
        if sets_skip(job.get("env")):
            found.append(f"{where} sets SKIP")
        for step in job.get("steps") or []:
            if sets_skip(step.get("env")):
                found.append(f"{where} sets SKIP in a step")
            script = step.get("run") or ""
            if re.search(r"\bSKIP=", script):
                found.append(f"{where} sets SKIP in a command")
            for words in commands(script):
                if not words or words[0] != "run":
                    continue
                if len(words) < 2 or words[1].startswith("-"):
                    found.append(f"{where} runs pre-commit with no hook id after `run`")
                    continue
                hook = words[1]
                if hook not in stages:
                    found.append(f"{where} runs {hook}, which is not a hook")
                    continue
                runs.setdefault(hook, []).append(where)
                hook_stages = stages[hook]
                if not hook_stages or "pre-commit" in hook_stages:
                    if "--all-files" not in words:
                        found.append(f"{where} runs {hook} without --all-files")
                else:
                    at = words.index("--hook-stage") if "--hook-stage" in words else -1
                    if at < 0 or words[at + 1 : at + 2] not in [
                        [s] for s in hook_stages
                    ]:
                        found.append(
                            f"{where} runs {hook} without --hook-stage and one of"
                            f" its stages, {', '.join(hook_stages)}"
                        )
    return found


def gate_problems(ci: dict) -> list[str]:
    jobs = ci.get("jobs") or {}
    gate = jobs.get(GATE)
    if gate is None:
        return [f"ci.yml has no job {GATE}, the required status check"]
    found = []
    if gate.get("name", GATE) != GATE:
        found.append(f"ci.yml's job {GATE} is named {gate['name']!r}, not {GATE!r}")
    needs = gate.get("needs") or []
    needs = [needs] if isinstance(needs, str) else needs
    missing = sorted(set(jobs) - {GATE} - set(needs))
    if missing:
        found.append(f"ci.yml's job {GATE} does not need {', '.join(missing)}")
    if "always()" not in str(gate.get("if", "")):
        found.append(
            f"ci.yml's job {GATE} does not run always: if: ${{{{ always() }}}}"
        )
    return found


def problems(repo: Path) -> tuple[list[str], dict[str, list[str]]]:
    config = yaml.safe_load((repo / ".pre-commit-config.yaml").read_text())
    stages = hook_stages(config)
    found, runs = [], {}
    paths = sorted((repo / WORKFLOWS).glob("*.y*ml"))
    for path in paths:
        workflow = yaml.safe_load(path.read_text()) or {}
        name = str(path.relative_to(repo))
        found += workflow_problems(name, workflow, stages, runs)
        if path.name == "ci.yml":
            found += gate_problems(workflow)
    if repo / WORKFLOWS / "ci.yml" not in paths:
        found.append(f"{WORKFLOWS}/ci.yml is missing")
    for hook in stages:
        where = runs.get(hook, [])
        if not where:
            found.append(f"no CI job runs the hook {hook}")
        elif len(where) > 1:
            found.append(f"the hook {hook} runs more than once: in {'; '.join(where)}")
    return found, runs


def summary(runs: dict[str, list[str]]) -> str:
    jobs: dict[str, list[str]] = {}
    for hook, where in runs.items():
        jobs.setdefault(where[0], []).append(hook)
    lines = ["### The hooks that each job runs", ""]
    lines += [
        f"- {job}: {', '.join(f'`{h}`' for h in hooks)}" for job, hooks in jobs.items()
    ]
    return "\n".join(lines) + "\n\n"


def main(argv: list[str]) -> int:
    repo = Path(argv[0]) if argv else Path(".")
    found, runs = problems(repo)
    for problem in found:
        print(f"ci-hooks: {problem}", file=sys.stderr)
    if found:
        return 1
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        text = summary(runs)
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as f:
            f.write(text)
        print(text, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
