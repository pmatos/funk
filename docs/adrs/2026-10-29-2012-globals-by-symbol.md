# Globals are referenced by symbol only

Status: accepted
Tier: direction; area: semantics

## Decision

- An op refers to a function or other global by symbol only, for example
  `call @f`. The verifier resolves every symbol reference.
- Constants are ordinary ops inside the function (`const`), not
  module-level values.
- There are no module-wide use-lists: the IR does not keep, for each symbol,
  the list of ops that use it. Finding every user of a symbol takes a scan of
  the module, or an index that a pass builds for itself, and renaming a
  symbol rewrites every reference to it.
- Symbol tables must be able to nest (G0, ADR-2026-10-29-2016). Global items
  and function addresses build on this rule (ADR-2026-11-09-1546,
  ADR-2026-11-09-1548).

This is H3 of the fir v0 decision record, agreed on 2026-10-29 (#5).
[semantics.md](../decisions/semantics.md) states what holds.

## Why

Functions are isolated from above (H2, ADR-2026-10-29-2011), so a function
cannot hold an SSA value that another function defines. Referring by symbol
means functions share no mutable state through their references, so they
can be changed independently.

## Rejected alternatives

- **Globals and constants as values with use-lists,** as in LLVM. The
  use-lists are shared by every function that uses them, so changing one
  function touches state that other functions share.
