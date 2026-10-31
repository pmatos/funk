# A fixture corpus with one invalid test

A corpus in the format of `tests/fir/` (ADR-2026-10-30-2050) that the main
run of the harness does not read. Its one test, `canonical/div-frozen.toml`,
is #18's differential test with a frozen divisor that can be zero: its set
holds UB, so the harness reports it invalid and exits with 1.
`scripts/check-harness.sh` runs `scripts/harness/check_invalid.py` after the
main run, which runs the harness on this corpus with the real tools and
passes only when that test, and nothing else, is reported invalid because
`the set holds UB (sdiv by zero)` (ADR-2026-10-31-0208). `reject/div.toml`
holds one must-reject text, since a corpus must hold one.
