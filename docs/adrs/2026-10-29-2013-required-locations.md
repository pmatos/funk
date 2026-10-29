# Every op has a required source location

Status: accepted

## Context

This is decision H8 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

Funk's diagnostics point at IR locations, and frontends need to map compiled
code back to their sources. A location field that may be absent is easy to
drop by accident in a pass, and the loss shows up much later, if at all.

## Decision

- Every op has a location field. The field always exists; `unknown` is a valid
  value.
- A location is `unknown` or one of these kinds: a source range
  (`file:line:col-line:col`), a name, `callsite(callee at caller)`,
  `fused(a, b)` or `derived(op)`.
- Locations are erased before semantics: they never change what a program
  means.
- In text, each op carries a short `@N` reference, and a `locs { ... }` table
  ends the module, giving the location that each `@N` stands for.

The spec ([#8](https://github.com/pmatos/funk/issues/8)) gives the exact
spelling of each kind.

## Consequences

- An op cannot be built without a location. The `funk-ir` builder requires
  one, and the verifier checks that every op has one.
- Every pass must give each op it creates a location, so locations are
  propagated, not lost.
- Op lines stay short, because a location is a short reference into the table.
- The interpreter ignores locations, but both parsers and printers keep them,
  and round trips preserve them (P3, ADR-2026-10-29-2014).
