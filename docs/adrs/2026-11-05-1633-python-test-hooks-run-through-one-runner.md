# The Python test hooks run their tests through one runner that writes their counts

Status: accepted

## Context

ADR-2026-11-05-1408 has each test suite write its counts to the GitHub job
summary and to the log. Seven hooks run Python tests with `unittest`
straight from their `entry`: `adr-ids-test`, `g0-test`, `ci-hooks-test`
and `suite-summary-test` run a test file with `python FILE`;
`verus-report-test`, `unsafe-code-test` and `fir-harness-test` run
`python -m unittest discover -s DIR -p PATTERN`. Their `Ran N tests` lines
reached the log through `--verbose`, but nothing reached the summary.

On 2026-11-05 the human chose, in
[#150](https://github.com/pmatos/funk/issues/150), one shared runner that
the seven entries call, with no change to any test file.

Facts:

- `python FILE` runs the file as `__main__` with `FILE`'s directory as
  `sys.path[0]`; every test file's `__main__` block calls `unittest.main()`.
  `python -m unittest` puts the working directory there, and `discover -s
  DIR` adds `DIR`.
- `unittest.main()` picks the exit status: 1 when a test failed or erred,
  and in discover mode also when a module did not import; 5 on Python 3.12
  and later when no test ran. A test file that does not import or compile
  never reaches it: `python FILE` exits 1, and 2 when the file is missing.
- Some tests run scripts while `GITHUB_STEP_SUMMARY` is set. On `main` at
  `be55ab3` each script that writes to the summary runs with the variable
  removed or pointed at a test's own file, so the seven hooks wrote no row:
  their entries, run with the variable set, leave its file empty.

## Decision

- **`scripts/run_unittests.py HOOK ARGS...`**, where `ARGS` are the
  arguments that the hook's entry gave `python`: a test file, or
  `-m unittest` and its arguments. Each of the seven entries puts
  `scripts/run_unittests.py HOOK` after `python` and keeps the rest.
- **The same tests, the same verdict.** The runner runs the tests in its
  own process with the `sys.argv`, `sys.path[0]` and `__main__` module that
  `python` would have given them, and exits with the status that their
  `unittest.main()` chose; when a test file does not import or does not
  exist, it exits 1 or 2, as `python FILE` does. It wraps unittest's text
  runner to keep the result, and changes nothing that the tests print.
  When the tests do not run at all, its row says why.
- **The summary.** When `GITHUB_STEP_SUMMARY` is set, the runner removes it
  while the tests run, so nothing they run writes to the summary, then
  writes one row through `scripts/suite_summary.py`, titled
  "Python tests (HOOK)": tests run, passed, failed, errors and skipped,
  expected failures and unexpected successes when there are any, and the
  exit status when it is not 0. It prints the same line to the log.
  Without the variable, a hook prints and exits as before.
- **Its tests** are `scripts/test_run_unittests.py`, in the hook
  `run-unittests-test` of the static job. They run each kind of test
  module both the old way and through the runner, and compare the exit
  status, the output and what the tests see.
- Each of the seven hooks also runs when `scripts/run_unittests.py`
  changes. Nothing else about them changes.

## Alternatives

- **Each test file writes its counts.** Every test file (22 on `be55ab3`)
  would repeat the same code, and the human ruled out test changes.
- **Steps in `ci.yml` read the log.** Logic would leave
  `.pre-commit-config.yaml`, which AGENTS.md keeps as the one list of
  checks.
- **Run the old entry in a child process and read its `Ran N tests`
  line.** That line holds no count of the tests that passed, and errors
  and skips only when there are some.

## Consequences

- The static, Rust and cross-language job summaries list each Python test
  hook's counts beside the other suites'.
- A new Python test hook should call the runner the same way, so that its
  counts reach the summary.
- A test that needs `GITHUB_STEP_SUMMARY` has to set it itself.
- This refines ADR-2026-11-05-1408, whose alternatives left these counts
  to #150.
