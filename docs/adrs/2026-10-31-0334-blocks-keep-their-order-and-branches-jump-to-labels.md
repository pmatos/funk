# Blocks keep the order of the function's body, and a branch jumps to its block's label unless that block comes next

Status: accepted

## Context

[#19](https://github.com/pmatos/funk/issues/19) brings `br` and `cond_br`
to the x86-64 backend. `br` goes to its one successor; `cond_br` goes to
its first when its `i1` condition is `true` and its second when it is
`false`. Each successor passes values to its block's arguments, which the
branch copies before it jumps (ADR-2026-10-31-0335). Every block of a
valid function is reachable (ADR-2026-10-30-0817), so the backend never
sees dead code. ADR-2026-10-30-1231 holds an `i1` in bit 0 of its slot,
with the bits above unspecified, and says that a branch tests bit 0. A
branch on poison is immediate UB (ADR-2026-10-30-0818), and native code
holds no poison (ADR-2026-10-30-2248). M0's backend is the baseline, meant
to be right by reading it (ADR-2026-10-30-1230).

## Decision

- **Layout.** A function's blocks are laid out in the order of its body,
  each at the label `.Lb` followed by the function's index in the module,
  `_` and the block's label, such as `.Lb0_loop`. A label is one or more
  letters, digits, `_` and `.`, so each is a valid GNU `as` symbol, and
  the index ends at the first `_`, so no two functions' labels collide.
- **`br`.** It copies its block arguments, then jumps with `jmp` to its
  block, unless that block comes next.
- **`cond_br`.** It loads its condition into `%rax` and tests bit 0 with
  `testb $1, %al`, before any copy. Then a conditional jump, `jnz` to the
  first successor or `jz` to the second, goes to one edge, and the code of
  the other edge follows it. An edge with nothing to copy has no code of
  its own, so the jump goes straight to its block. Otherwise the jumped-to
  edge's code goes after the other's, at a local label `.Lc` followed by
  the function's index, `_` and a count. An edge's code is its copies and
  a `jmp` to its block. Only the code that ends the branch may leave the
  `jmp` out, when its block comes next, so the edges are ordered to let
  that edge end it.
- **Poison.** A branch on poison goes one way or the other, which UB
  allows.

## Alternatives

- **Always jump.** One case fewer, but a `jmp` to the next instruction in
  every loop body and every fall-through.
- **Reorder blocks**, such as to put a loop's body after its header. It
  improves the code, not its correctness, so the baseline does without it.

## Consequences

- The order of a function's blocks in the text is the order of its code,
  so assembly reads alongside the fir text.
- A `cond_br` whose two edges both copy costs one local label and one
  extra jump.
- `%rax` and `%rcx` may be clobbered by a branch: `cond_br` loads its
  condition into `%rax`, a copy goes through `%rax`, and a cycle of copies
  through `%rcx`. Other ops clobber them too while values live in slots;
  a register allocator (M1) must treat them so.
- A later optimizer (M1) that makes poison real (ADR-2026-10-30-2248) may
  treat a `cond_br` on poison as UB, as the spec does
  (ADR-2026-10-30-0818). It must still read only bit 0 of the condition
  (ADR-2026-10-30-1231), and must not branch on a value that may be
  poison where the source does not, such as by turning a `select` into a
  `cond_br`, without freezing it first (ADR-2026-10-31-0215,
  `lean/Fir/Execution/PoisonUB.lean`).
