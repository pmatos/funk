# A branch copies the values it passes into its block's arguments as one parallel move, with one register to break cycles

Status: accepted

## Context

[#19](https://github.com/pmatos/funk/issues/19) brings block arguments to
the x86-64 backend. Every value has an 8-byte slot of its own
(ADR-2026-10-30-1230), a block's arguments included. A branch passes its
values to its successor's arguments all at once: in a loop
`^loop(%a, %b)`, `br ^loop(%b, %a)` swaps them, `br ^loop(%b, %c, %a)`
rotates three, and `br ^loop(%a, %a)` passes one value to two arguments. A
copy done one at a time, in order, can overwrite a slot that a later copy
still reads. The arguments of a block are distinct values, so no two
copies of one branch write the same slot.

## Decision

- **A parallel move, in sequence.** `moves.rs` turns the copies of one
  edge into steps. A copy from a slot to itself is dropped. Then, while
  copies remain, one whose destination no remaining copy reads is done.
  When none is left, every remaining destination is read by exactly one
  remaining copy: they form cycles, and nothing reads the register. The
  first remaining destination is saved in `%rcx`, and the copies that read
  that slot read `%rcx` instead, which opens its cycle into a chain.
- **Instructions.** A copy is `movq` from its slot into `%rax` and from
  `%rax` into its destination. Saving is `movq` from the slot into `%rcx`,
  and a copy from the register is one `movq` from `%rcx`. Every copy moves
  all 64 bits, so a value's low `N` bits arrive as they were, and so do
  the bits above them, which are unspecified (ADR-2026-10-30-1231).
- **Counts.** A branch makes one copy per argument whose slot is not its
  value's, and one save per cycle of copies, such as a swap or a rotation
  of any length.

## Alternatives

- **Push every value, then pop each into its argument.** Always right with
  no ordering, but two stack accesses per argument, and it moves `%rsp`
  in the middle of a function.
- **A temporary slot per argument.** Always right, but it doubles the
  copies and grows the frame by the largest number of arguments.

## Consequences

- A unit test runs random parallel moves on slots, with sources that
  repeat and destinations that are sources, and checks each sequence
  against the copies done at once. The native tests swap, rotate and fan
  out arguments round loops, and run a gcd whose loop must read `%y`
  before it writes it.
- `%rax` and `%rcx` are clobbered between a branch's test and its jump. A
  register allocator (M1) that keeps values in registers needs the same
  sequencing for registers, and a scratch register or an exchange for each
  cycle.
