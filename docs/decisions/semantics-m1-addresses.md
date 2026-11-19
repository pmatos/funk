# Current decisions: semantics, M1 addresses

This page continues [semantics-m1-memory.md](semantics-m1-memory.md) with the
addresses of exposed allocations. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## What holds today

#232 is built in stages ([the stage plan on the issue](https://github.com/pmatos/funk/issues/232)).
Stage 1 gives the memory model its addresses, in
`lean/Fir/Memory/Address.lean`, with its laws in `AddressLaws.lean`,
`CanonicalLaws.lean` and `ExposeLaws.lean`. Stage 2 makes exposing a
pointer an operation of the memory effect, under an address policy
(`lean/Fir/Memory/Policy.lean`, `PolicyLaws.lean`,
`lean/Fir/Execution/MemoryExposeLaws.lean` and `MemoryPolicyRuns.lean`).
No op uses it yet: `ptr_expose` and `ptr_from_int` (the human's spelling of
2026-11-18, Q1), the operation that turns an integer back into a pointer,
the Rust tools and the backend come in the stages after it. The spec's
memory chapter renders all of them.

## Which addresses an allocation may be given

Only exposed allocations have integer addresses (ADR-2026-11-09-1542). A
block records its address once it is exposed (`Block.addr`), and keeps the
first one it is given for the rest of the run, freed or not. Allocating
gives a block with no address, and allocating, freeing and storing keep
every address.

Each memory has its own addresses, from 0 below `2 ^ P`, where `P` is its
pointer width in the data layout (ADR-2026-11-12-1821). The model takes the
range an allocation may take as two bounds, `lo` and `hi`. The address `x`
fits an allocation of `n` units, aligned to `A` (`Memory.fits`), when:

- `lo ≤ x` and `x + n ≤ hi`;
- `A` divides `x`, as the human's ruling of 2026-11-14 on #388 asks of
  every address a block may be given;
- no other live allocation that has an address overlaps `x` to `x + n`.

The spec allows any address that fits. Only live allocations are compared,
so a freed allocation's addresses may be given again: the human ruled on
2026-11-10, on #232, that no law may assume fresh addresses, since native
stack slots are reused and `fir-ref`'s single layout cannot show it.
`addresses_not_fresh` proves that the model does not imply them, with a
witness in which a later allocation fits at the address of a freed one.
Rejected: comparing freed allocations too, which would make every address
fresh.

A run exposes in a memory of `P`-bit pointers with `lo = 1` and
`hi = 2 ^ P - 1`: no allocation is at the null address, and the address
one past every allocation's end is an address of the memory and not 0. The
human ruled this on 2026-11-18, on #232 (Q4). The model's laws hold at
every bound, so only the effect fixes them (`addrHi`). Rejected: `lo = 0`
and `hi = 2 ^ P`, under which an allocation could sit at the null address
and one past its end could wrap to 0.

An allocation of no units takes no address, so it may share its address
with another, as zero-sized objects may in LLVM and Rust. No op of M1
makes one: `alloca` allocates at least one unit.

Exposure changes no access: a load, an aligned access and a store fault
or succeed as before, and every block keeps its shape and units
(`ExposeLaws.lean`). Refinement of blocks compares addresses, freed or
live, so memories that refine each other give every allocation the same
address, the same addresses fit, and the canonical layout gives the same.
`Block.shape`, which the effect obligations compare, leaves the address
out, so the obligations cannot tell an op that exposes from one that does
nothing. Stage 2 states what exposing changes as a property of its own,
_exposes nothing in `x`_ (`ExposesNot`): every allocation of `x` keeps its
address. Allocating, freeing, loading and storing expose nothing in any
memory, and exposing exposes nothing but in its own memory. Which declared
effect covers exposing is open for the human, and the op that exposes waits
for it. Rejected: adding the address to `Memory.allocs`, which would make
exposing an allocation effect but narrow _no read_ under the same
statement of `LawfulDialectEffects`.

## Exposing a pointer, and address policies

The memory effect's `expose` turns a pointer of the memory `x`, whose
pointers are `P` bits wide, into the integer of its allocation's address
plus its offset, wrapped at `P` bits, the width the human ruled on
2026-11-18 (Q2). An allocation with no address is given one first. A
pointer with no provenance gives its offset. Exposing an allocation again
gives the same address and changes nothing.

Which address an allocation gets is the run's _address policy_: for each
memory, by its number in the data layout, a function from the shape and
address of each of its blocks to a proposed address. It sees nothing that
refinement may change, so memories that refine each other get the same
address. The effect takes the proposal when it fits, and the canonical
address otherwise, so the address always fits whatever the policy, and
every address that fits is given by the policy that proposes it
(`Memories.expose_of_fits`). The canonical layout is the policy that
proposes nothing, `Policy.canonical`.

The policy travels in the record that a run gives each op (`RunItems`,
field `addrs`), beside the module's items. A run made from its module, as
`fir-ref` makes, gives the canonical policy. Every obligation and guarantee
over the semantics with memory holds for every such record, so for every
policy, with no new hypothesis. The spec's runs are those of every policy:
`Func.memBehaviour` is the union of the observable behaviours under each
policy, chosen once for the run, and a refinement that holds under each
policy holds of it. This extends the record of the human's ruling of
2026-11-16 on #236, which named the module's items. Rejected: a policy as
a type class argument of the state layer, which would give every statement
over a core run a new argument; and a policy that sees the units of a
memory, under which refinement would need a hypothesis on it.

No address fits when the memory has run out of addresses. The spec has no
outcome for that, as allocating has none, so exposing is then immediate UB,
with the reason "an exposure that no address fits" (the human's ruling of
2026-11-18, Q5). A pointer whose provenance names no allocation of the
memory has no address either, and is UB for the same reason.

## The canonical layout

`fir-ref` gives addresses from one canonical layout, in allocation order,
aligned and deterministic (ADR-2026-11-09-1542). `Memory.bump` lays a
memory's allocations out in the order they were made, from `lo`, each at
the first multiple of its alignment after the previous one ends, with one
unused address between them. An allocation's canonical address depends
only on the allocations made before it, so allocating moves none
(`Memory.bump_alloc`), and no two of them overlap (`Memory.bump_lt`). While
every exposed allocation has its canonical address, the canonical address
of another fits whenever it ends by `hi` (`Memory.fits_bump`).

`Memory.canonical` gives the canonical address when it fits, and else the
lowest address that fits (`Memory.lowestFit`, `Memory.canonical_lowest`),
which is the first multiple of the alignment from `lo` or the first from
where a live allocation with an address ends (`Memory.fits_candidate`). It
gives an address whenever any address fits, and the address it gives fits
(`Memory.exists_fits_iff`). So the canonical layout is one of the
assignments the spec allows, which #232 asks the spec to prove. Without the
fallback, a run that exhausts a small address space under the canonical
layout would have no address where another assignment had one.

The gap of one address keeps the address one past an allocation's end
apart from the next allocation's canonical address. The fallback does not
keep it: the lowest address that fits may start where a live allocation
ends. `ptr_from_int` takes an angelic choice among the live, exposed
allocations that contain the address, the end included (the human's ruling
of 2026-11-18, Q3), so at such an address it may pick either. How the spec
states that choice is open for the human, and the operation that turns an
integer back into a pointer waits for it. The gap is `fir-ref`'s choice,
not a rule of the spec.
