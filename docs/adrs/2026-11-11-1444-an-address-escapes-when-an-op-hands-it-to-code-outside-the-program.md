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
  program, as in LLVM's capture tracking:
  - an external call that gets it as an argument;
  - an inline assembly block whose effect set says observable;
  - a volatile store whose stored value is the pointer;
  - `ptr.expose` (ADR-2026-11-09-1542).
- **What the observer sees.** At a return the observer sees the memory that
  escaped by any of these ways, and the memory reachable from it, as
  ADR-2026-11-11-1016 has it for external calls.
- **Internal globals.** An `internal` global is observable once its address
  escapes by any of these ways. After `ptr.expose` only an integer holds the
  address, yet the global is observable all the same.
- **Export globals.** Code outside the program sees an `export` global
  whether or not its address escapes (ADR-2026-11-09-1546). This ADR does
  not change that.

This refines ADR-2026-11-11-1016, which named only external calls and made
an `internal` global observable once it is reachable from what the observer
sees.

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
