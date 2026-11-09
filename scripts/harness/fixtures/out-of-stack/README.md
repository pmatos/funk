# A fixture corpus with a recursion deeper than native code's stack

A corpus in the format of `tests/fir/` (ADR-2026-10-30-2050) that the main
run of the harness does not read. Its one test, `canonical/down.toml`,
recurses 1,000,000 deep: `fir-ref` returns, and native code runs out of its
stack and says so in one line (ADR-2026-11-02-1132). The harness reports it
invalid and exits with 1. `scripts/check-harness.sh` runs
`scripts/harness/check_invalid.py` after the main run, which runs the harness
on this corpus with the real tools under an 8 MiB stack limit, and passes
only when that test, and nothing else, is reported invalid because `native
code outgrew its 8388608 bytes of stack` (ADR-2026-11-09-1602).
`reject/down.toml` holds one must-reject text, since a corpus must hold one.
