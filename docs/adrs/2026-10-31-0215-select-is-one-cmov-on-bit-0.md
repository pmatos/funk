# select lowers to a test of its condition's bit 0 and one cmov, with no branch

Status: accepted

## Context

[#16](https://github.com/pmatos/funk/issues/16) brings `icmp` and `select`
to the x86-64 backend. `select %c, %a, %b` gives `%a` when `%c` is `true`
and `%b` when it is `false`. A poison condition gives poison; the value
not chosen does not matter, even when it is poison; the chosen one is
given as it is (ADR-2026-10-30-0818). ADR-2026-10-30-1231 holds an `i1` in
bit 0 of its slot, with the bits above unspecified, and says that a
`select` tests bit 0 of its condition and needs no extension of its
values. It does not say whether `select` branches. Native code holds no
poison (ADR-2026-10-30-2248).

## Decision

- **One `cmov`, no branch.** `select` loads its condition into `%rcx` and
  its first value into `%rax`, tests bit 0 with `testb $1, %cl`, and, when
  the bit is clear, moves its second value in from its slot with
  `cmovzq`. It stores `%rax` as the result.
- **Bit 0 only.** Nothing of the condition above bit 0 is read, so a
  condition whose slot holds other bits, such as `true + true` at `i1` or
  a `trunc` to `i1`, chooses by its value.
- **Values whole.** The chosen slot's 64 bits are copied, and its low `N`
  bits are the result, as ADR-2026-10-30-1231 says of an op that reads
  only its operands' low bits.
- **Poison.** Every case with a defined result is exact. Where the source
  gives poison, from its condition or from the value it chooses, the
  result is the bits of one of the two slots, which refines poison
  (ADR-2026-10-29-2008). A poison value that is not chosen is never
  seen.

## Alternatives

- **A branch on bit 0** to code that copies one value or the other. It
  needs two labels and a jump in every `select`, and a mispredicted jump
  costs more than a `cmov`.
- **Masks**: bit 0 spread to all ones or zero, then `and`, `andn` and
  `or` of the two values. It is longer, and `andn` needs BMI1.

## Consequences

- `select` reads both slots whatever its condition. Every slot is always
  readable, so this costs one load and never faults.
- Its tests run conditions with bits set above bit 0, which a test of the
  whole register, such as `testq %rcx, %rcx`, would misread.
