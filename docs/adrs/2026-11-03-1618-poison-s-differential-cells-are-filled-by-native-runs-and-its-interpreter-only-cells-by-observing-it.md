# The differential cells of `poison` are filled by native runs, and its interpreter-only cells by tests that observe the poison

Status: accepted

## Context

ADR-2026-11-03-0557 makes each core op instance at each width a cell of
the coverage matrix, on each side, and asks of a test that fills a cell
that its path runs the op and that its outcome depends on what the op
computes. ADR-2026-11-03-1615 adds `poison`, whose result is poison.
Native code gives zero for it (ADR-2026-11-03-1616), and the harness
accepts any native value where `fir-ref` gives poison. So no differential
test can tell `poison` from `const 0`: on that side, the rule cannot be
met.

## Decision

- **Cells.** `poison` is a cell at each width of each side, as `const`
  is: it has no attributes (`scripts/harness/cells.py`).
- **Differential side.** A test fills a cell of `poison` when its path
  runs the op as native code: its module builds, the native run ends,
  and its result refines `fir-ref`'s, whether the poison reaches the
  result or not.
- **Interpreter-only side.** A test fills a cell of `poison` when its
  outcome observes the poison: `fir-ref` returns it, a result that it
  decides (such as `icmp eq %p, %p`, which is poison), a value that
  `freeze` chooses for it, or UB that it causes, such as a branch on it.
- The count stays static, as ADR-2026-11-03-0557 has it. Every other op
  keeps that ADR's rule. `tests/fir/canonical/poison-op-iN` fills the
  new cells, at the six widths of the backend and at `i7` and `i33`.

## Consequences

- The matrix has 14 more cells, 783 in all.
- On the differential side, a test of `poison` shows that it lowers and
  runs, not what it gives; its value is checked on the interpreter-only
  side.
