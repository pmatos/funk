# Functions are regions isolated from above

Status: accepted
Tier: direction; area: semantics

## Decision

- A function is a region **isolated from above**: nothing in one function
  references a value of another function.
- Functions reach each other only by symbol (H3, ADR-2026-10-29-2012).
- In Rust, ownership keeps functions apart: a pass that holds
  `&mut Function` cannot touch another function. The verifier checks
  isolation itself.
- Modules and symbol tables must be able to nest (G0, ADR-2026-10-29-2016).

This is H2 of the fir v0 decision record, agreed on 2026-10-29 (#5).
[semantics.md](../decisions/semantics.md) states what holds.

## Why

Passes, verifiers and backends work one function at a time. Isolated
functions can each be verified, transformed and compiled on their own, and
in parallel.

## Rejected alternatives

- **Values shared between functions.** No function could then be checked,
  changed or compiled without looking at the others.
