# No caller relies on an unmarked `i1` result being 0 or 1 in all of `%rax`

Status: accepted
Tier: direction; area: x86-64-backend

## Context

ADR-2026-10-30-1232 has a funk function return an `i1` result as 0 or 1 in
all of `%rax`, and ADR-2026-11-03-0109 says the same of an `i1` among several
results, in a register or in the result area. ADR-2026-11-09-1547 adds
optional `sext` and `zext` markers, and says that with no marker neither side
may rely on the upper bits. The two disagree on what a caller may rely on for
an unmarked `i1` result ([#251](https://github.com/pmatos/funk/issues/251)).
The human ruled on #251 on 2026-11-11.

## Decision

- **The backend may keep it.** The x86-64 backend may still return an
  unmarked `i1` result as 0 or 1 in all of `%rax`, and in all of its
  eightbyte among several results.
- **No caller relies on it.** No caller, funk's own code included, may rely
  on the bits above bit 0 of an unmarked `i1` result.
- **A C `_Bool`.** A caller that needs a C `_Bool` result relies on the
  `zext` marker (ADR-2026-11-09-1547).

This amends ADR-2026-10-30-1232's rule for `i1` results, and
ADR-2026-11-03-0109's restatement of it. Generated code does not change.

## Alternatives

- **Keep the guarantee.** Every unmarked `i1` result would be held to more
  than ADR-2026-11-09-1547 promises, and a later backend could not drop the
  extension.

## Consequences

- A later backend or pass may return an unmarked `i1` with any upper bits.
- The runtime already reads an `i1` result by bit 0, so nothing relies on
  the old guarantee.
