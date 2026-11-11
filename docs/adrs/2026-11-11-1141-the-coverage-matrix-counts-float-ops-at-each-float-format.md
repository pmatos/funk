# The coverage matrix counts the float ops at each float format

Status: accepted
Tier: implementation; area: testing-and-harness

## Context

The coverage matrix has a cell for each op instance at each width of a
side: `i1` to `i128` for differential tests, and `i7` and `i33` more for
interpreter-only tests (ADR-2026-11-03-0557). A new side or width changes
that ADR. #229 adds float constants and `fcmp` (ADR-2026-11-11-1138,
ADR-2026-11-11-1139). They work on float formats, not integer widths. The
backend lowers `f32` and `f64` only (ADR-2026-11-09-1549).

## Decision

- A float constant, and `fcmp` with each of its fourteen predicates, is a
  cell at each float format of a side, in a table of its own.
- The differential side has `f32` and `f64`. The interpreter-only side has
  `f16`, `bf16`, `f32`, `f64` and `f128`.
- Ops at other float formats count towards no cell, as ops at other widths
  do.

## Consequences

- The `coverage-matrix` hook fails until the corpus tests each float cell,
  so every predicate runs natively at `f32` and `f64`, and on `fir-ref` at
  every aliased format.
- A later float op, such as `fadd`, adds its row to `AT_FORMAT` in
  `scripts/harness/cells.py`.
