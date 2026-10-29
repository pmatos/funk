# Functions are regions isolated from above

Status: accepted

## Context

This is decision H2 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

Passes, verifiers and backends work one function at a time. If one function
could use a value defined in another, no function could be checked, changed
or compiled without looking at the others.

## Decision

- A function is a region **isolated from above**: nothing in one function
  references a value of another function.
- Functions reach each other only by symbol (H3, ADR-2026-10-29-2012).
- In Rust, ownership enforces it: a pass that holds `&mut Function` cannot
  reach another function.
- Modules and symbol tables must be able to nest, for example a device module
  inside a host module (G0, ADR-2026-10-29-2016). M0 does not use nesting, but
  its data structures must not rule it out.

## Consequences

- The verifier checks isolation.
- Each function can be verified, transformed and compiled on its own, and
  functions can be processed in parallel.
- Whatever a function needs from outside itself, it names by symbol.
