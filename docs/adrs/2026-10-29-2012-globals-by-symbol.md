# Globals are referenced by symbol only

Status: accepted

## Context

This is decision H3 of the fir v0 decision record, agreed on 2026-10-29 and
stated in the M0 epic ([#5](https://github.com/pmatos/funk/issues/5)).

Functions are isolated from above (H2, ADR-2026-10-29-2011), so a function
cannot hold an SSA value that another function defines. In LLVM, globals and
constants are values with use-lists shared by every function that uses them,
so changing one function touches state that other functions share.

## Decision

- An op refers to a function or other global by symbol only, for example
  `call @f`.
- Constants are ordinary ops inside the function (`const`), not module-level
  values.
- There are no module-wide use-lists: the IR does not keep, for each symbol,
  the list of ops that use it.
- Symbol tables must be able to nest (G0, ADR-2026-10-29-2016).

## Consequences

- The verifier resolves every symbol reference.
- Functions share no mutable state through their references, so they can be
  changed independently.
- Finding every user of a symbol takes a scan of the module, or an index that
  a pass builds for itself.
- Renaming a symbol means rewriting every reference to it.
