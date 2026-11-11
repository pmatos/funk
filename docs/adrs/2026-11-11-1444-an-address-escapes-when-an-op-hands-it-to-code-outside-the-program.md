# An address escapes when an op hands it to code outside the program

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-11-1016 makes an `internal` global observable once its address
escapes, and lets an observer see memory that escaped to an external call.
It names only the external call as a way to escape. Other ops also hand the
address of an `internal` global `@g` out: an observable inline assembly block
that takes `@g` as an operand, a volatile store that writes `@g` to memory,
and `ptr.expose @g`, which turns the address into a plain integer.

If only external calls counted, a pass could delete writes to `@g` after
assembly or a volatile store had already given its address out. The review
of PR #298 raised this ([#299](https://github.com/pmatos/funk/issues/299)).
The human ruled on #299 on 2026-11-11
([comment](https://github.com/pmatos/funk/issues/299#issuecomment-6798799252)).

## Decision

- **Escape.** An address escapes whenever an op hands it to code outside the
  program:
  - an external call that gets it as an argument;
  - an inline assembly block whose effect set says observable;
  - a volatile store whose stored value is the pointer;
  - `ptr.expose` (ADR-2026-11-09-1542).
- **Memory reachable from it.** Memory reachable from an escaped address has
  escaped too.
- **One meaning.** "Escaped" means this wherever the ADRs use it: the
  memory an observer sees at a return (ADR-2026-11-11-1016), the memory the
  world may write (ADR-2026-11-09-1540), and the memories an external call or
  inline assembly may touch (ADR-2026-11-09-1541). LLVM's capture tracking
  makes the same choice.

This refines ADR-2026-11-11-1016, which named only external calls.

## Alternatives

- **Only external calls.** Passes could delete writes to memory that
  assembly or a volatile store had already handed out, so the program would
  differ from what outside code sees.

## Consequences

- A pass that removes a store to an `internal` global first checks every
  way above, not only calls.
- An `internal` global whose address goes through `ptr.expose` is compared
  at a return.
- The harness's wrapper dumps memory that escaped by any of these ways.
- The `ptr.expose` ticket ([#232](https://github.com/pmatos/funk/issues/232)),
  the trace ticket ([#233](https://github.com/pmatos/funk/issues/233)) and
  the inline assembly ticket ([#240](https://github.com/pmatos/funk/issues/240))
  build this rule.
