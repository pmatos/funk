# An unobservable inline assembly block's answer depends on the contents of the memory it declares it reads

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-11-1015 keys the world's answer to an inline assembly block
without observable by the block and its operands. A block may also declare
that it reads a memory, but the key leaves out what that memory holds.

Take a loop whose body runs an unobservable block that declares it reads
memory and loads through a pointer `%p` it gets as an operand. A separate
store after the block writes the loaded value plus one through `%p`. With
that key the block gets the same answer on every iteration, since `%p`
does not change, so a pass may hoist it out of the loop. On real hardware it
reads a new value each time. The review of PR #298 raised this
([#299](https://github.com/pmatos/funk/issues/299)). The human ruled on #299
on 2026-11-11
([comment](https://github.com/pmatos/funk/issues/299#issuecomment-6798799252)).

## Decision

- **The key.** The world's answer to an inline assembly block without
  observable is keyed by the block, its operands and the contents of the
  memories it declares it reads.
- **Merging and moving.** A pass may merge such a block with an equal block,
  or move it, only when no write to those memories comes between. This is
  how LLVM treats a call that only reads memory. A block that also writes a
  memory it reads is such a write for the next block.
- **Unchanged.** A block with observable is still answered in trace order.
  Passes may still delete a block without observable, within its declared
  reads and writes (ADR-2026-11-11-1015).

This refines ADR-2026-11-11-1015's key.

## Alternatives

- **Keep the key as block and operands.** A block that reads memory that
  changes would then have to be marked observable. That is surprising, and
  it makes a common kind of block run worse.

## Consequences

- A block with no narrower declaration reads every memory that can have
  escaped to it (ADR-2026-11-09-1541), so its key covers all of them.
- A test's script answers an unobservable block by the block, its operands
  and the contents of the memories it declares it reads.
- The inline assembly ticket ([#240](https://github.com/pmatos/funk/issues/240))
  and the trace ticket ([#233](https://github.com/pmatos/funk/issues/233))
  build this rule.
