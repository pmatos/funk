# The frozen-divisor test lives in a fixture corpus outside `tests/fir/`, and `check-harness.sh` passes only when the harness reports it invalid for a zero divisor

Status: accepted

## Context

ADR-2026-10-31-0003 makes a differential test invalid when UB is in its
set of outcomes. ADR-2026-10-30-2135 says that an invalid test never
counts as a pass, as [#13](https://github.com/pmatos/funk/issues/13)
puts it: "An invalid test is reported as a failure, never as a pass."
The run then exits with 1 (ADR-2026-10-30-2049). Until now only unit
tests on hand-built sets, with stand-ins for the tools, checked that
rule.

[#18](https://github.com/pmatos/funk/issues/18) asks for a real test of
it: "A differential test with a frozen divisor that can be zero is
reported invalid". In `tests/fir/`, that test fails every run of the
harness, and CI stays red. The `fir-harness-test` hook runs the
harness's unit tests and builds neither tool; only the `fir-harness`
hook, `scripts/check-harness.sh`, builds `fir-ref` and `funk`.

## Decision

- **The fixture.** `scripts/harness/fixtures/invalid/` is a corpus in
  the format of ADR-2026-10-30-2050 that the main run over `tests/fir/`
  does not read. `canonical/div-frozen.fir` holds #18's test: `sdiv` at
  `i8` of 7 by `freeze` of `add nsw 127, 1`, which is poison, so the
  divisor may be 0 and the set holds `sdiv by zero`. Its sidecar states
  it as an ordinary differential test. `reject/div.toml` holds one
  must-reject text, since a corpus must hold one, and `README.md` says
  why the corpus exists.
- **The check.** `scripts/harness/check_invalid.py` runs `main.py` on
  the fixture with the real `funk` and `fir-ref`, as a process of its
  own. The fixture's module stands in for the modules that Rust printed,
  which the harness needs. The check passes only when the report has
  one line for the test, which starts
  `invalid canonical/div-frozen.fir @sdiv_frozen 7 127:`, names
  `the set holds UB (sdiv by zero)` and does not say that `funk build`
  failed, every other check passed, and the harness exits with 1.
  Anything else fails it: the test passed, failed or was invalid for
  another reason, a run with no choice that hits UB, a tool error
  (`funk build`, `fir-ref` or `funk verify`), another check that did not
  pass, or another exit status. A native crash is allowed: UB in the set
  allows any result.
- **The run.** `scripts/check-harness.sh` runs the check after the main
  run, with the same tools, and exits non-zero when either fails. The
  `fir-harness` hook already runs it when `scripts/harness/` changes.
- **The harness is unchanged.** It judges every test as before, and
  reports an invalid test as a failure, never as a pass.
  `test_check_invalid.py` tests the check's judgement on hand-written
  reports.

## Alternatives

- **A declared-invalid key, `invalid = "ub"`, in a sidecar of
  `tests/fir/`.** The test would pass when the harness judges it invalid
  for UB. Rejected: the harness would report a test that it judges
  invalid as passed, against #13's "never as a pass".
- **Run the fixture and expect exit status 1 alone.** The status says
  that something did not pass, not which test or why.
- **Count every invalid test as a pass.** It weakens the gate for every
  test: an invalid test that no one expected would pass unseen.

## Consequences

- The rule that UB in the set makes a test invalid is checked on the
  real tools in every run of `check-harness.sh`. If `fir-ref` stops
  listing the UB, or the harness stops reporting the test invalid, the
  hook fails.
- The check reads the report's lines and `fir-ref`'s UB reason, which
  the harness shows but never compares. A change to the report's layout,
  to the set rule's wording `the set holds UB` (`scripts/harness/sets.py`)
  or to the reason `sdiv by zero` (`lean/Fir/Core/Div.lean`) must update
  `check_invalid.py`.
- The round-trip hooks and `crates/funk-ir/tests/corpus.rs` read
  `tests/fir/` only, so they do not see the fixture's module. The
  harness's run on the fixture checks that both tools accept it.
- A change to the format of ADR-2026-10-30-2050 must keep the fixture
  valid: a format error there fails the check.
