# Current decisions: semantics, M1 addresses

This page continues [semantics-m1-memory.md](semantics-m1-memory.md) with the
addresses of exposed allocations. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## What holds today

#232 is built in stages ([the stage plan on the issue](https://github.com/pmatos/funk/issues/232)).
Stage 1 gives the memory model its addresses. No op reaches them yet:
`ptr.expose` and `ptr.from_int`, the memory effect that they ask for, the
Rust tools and the backend come in the stages after it. The model is in
`lean/Fir/Memory/Address.lean`, its laws in `AddressLaws.lean`,
`CanonicalLaws.lean` and `ExposeLaws.lean`, and the spec's memory chapter
renders them.

## Which addresses an allocation may be given

Only exposed allocations have integer addresses (ADR-2026-11-09-1542). A
block records its address once it is exposed (`Block.addr`), and keeps the
first one it is given for the rest of the run, freed or not. Allocating
gives a block with no address, and allocating, freeing and storing keep
every address.

Each memory has its own addresses, from 0 to `2 ^ P`, where `P` is its
pointer width in the data layout (ADR-2026-11-12-1821). The address `x`
fits an allocation of `n` units, aligned to `A` (`Memory.fits`), when:

- `0 < x`;
- `A` divides `x`, as the human's ruling of 2026-11-14 on #388 asks of
  every address a block may be given;
- `x + n < 2 ^ P`;
- no other live allocation that has an address overlaps `x` to `x + n`.

The spec allows any address that fits. Only live allocations are compared,
so a freed allocation's addresses may be given again: the human ruled on
2026-11-10, on #232, that no law may assume fresh addresses, since native
stack slots are reused and `fir-ref`'s single layout cannot show it.
`addresses_not_fresh` proves that the model does not imply them, with a
witness in which a later allocation fits at the address of a freed one.
Rejected: comparing freed allocations too, which would make every address
fresh.

The first and third conditions are the strictest reading of a question
that is open for the human (stage plan, question 4): whether an
allocation may sit at the address 0 and whether it may end at `2 ^ P`.
Under them no allocation is at the null address, and the address one past
an allocation's end is an address of the memory and not 0. A looser ruling
changes `Memory.fits` alone, and the canonical layout's theorems hold
under either.

Exposure changes no access: a load, an aligned access and a store fault
or succeed as before, and every block keeps its shape and units
(`ExposeLaws.lean`). Refinement of blocks compares addresses, freed or
live, so memories that refine each other give every allocation the same
address, the same addresses fit, and the canonical layout gives the same.

## The canonical layout

`fir-ref` gives addresses from one canonical layout, in allocation order,
aligned and deterministic (ADR-2026-11-09-1542). `Memory.bump` lays a
memory's allocations out in the order they were made, from the address 1,
each at the first multiple of its alignment after the previous one ends,
with one unused address between them. An allocation's canonical address
depends only on the allocations made before it, so allocating moves none
(`Memory.bump_alloc`), and no two of them overlap (`Memory.bump_lt`). While
every exposed allocation has its canonical address, the canonical address
of another fits whenever it ends below `2 ^ P` (`Memory.fits_bump`).

`Memory.canonical` gives the canonical address when it fits, else the
first multiple of the alignment from 1 when that fits, else the first
fitting address just after a live allocation with an address. It gives an
address whenever any address fits, and the address it gives fits
(`Memory.exists_fits_iff`). So the canonical layout is one of the
assignments the spec allows, which #232 asks the spec to prove. Without
the fallbacks, a run that exhausts a small address space under the
canonical layout would have no address where another assignment had one.

The gap of one address keeps the address one past an allocation's end
apart from the next allocation's first address, whatever the open question
on which allocations `ptr.from_int` may pick (stage plan, question 3)
decides. It is `fir-ref`'s choice, not a rule of the spec.
