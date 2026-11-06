# One module owns the complete judgement of a differential test

Status: accepted

## Context

The harness runner coordinated exhaustive outcomes, declared witnesses,
seeded runs and poison stand-ins through optional `pre`, `judge` and
`recheck` callbacks. Understanding one test required following that protocol
across the runner and its rule functions. Tests covered individual rules and
the whole report, but could not exercise the sequence through one interface.

## Decision

`scripts/harness/differential.py` owns that sequence. Its `evaluate` operation
takes the test, its result and parameter types, and an adapter for decoded
tool runs. It returns the final judgement and the complete explanation.
Callers need no knowledge of witnesses, sampling or recheck ordering.

`execution.py` supplies the process adapter, using the existing command,
JSON, timeout and native resource-limit mechanics in `tools.py`. Focused
tests supply an in-memory adapter that records every run. The corpus runner
keeps validation, building once per module, interpreter-only tests, report
emission and counts. The existing refinement and outcome-set rules remain
in `refine.py` and `sets.py`.

This is a behavior-preserving refactor of the existing checks, under
ADR-2026-10-30-2135, ADR-2026-10-31-0003 and ADR-2026-11-03-1847. Report
text, tool-call order, stand-in order, seeds and judgement precedence stay as
they were. In particular, a reference-side judgement still wins over native
failure, and a decided test still runs native code once when possible for
evidence. A recheck collects all seeds, ignores seed tool errors, prefers UB
to fuel exhaustion and otherwise keeps the original failure, including on
stuck. It does not use the outcome-set rule, whose precedence differs.

## Consequences

Tests at the judgement interface cover complete decision paths without
subprocesses. Existing process and report tests still check their adapters
and integration. An implementation change does not expose a callback
protocol to the corpus runner. Correctness changes to the preserved rules
are separate work rather than hidden inside this refactor.
