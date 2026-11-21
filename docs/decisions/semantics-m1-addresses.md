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
`lean/Fir/Execution/MemoryExposeLaws.lean` and `MemoryPolicyRuns.lean`),
and turning an integer back into a pointer one too, under an address
resolver (`lean/Fir/Memory/Resolver.lean`, `ResolverLaws.lean` and
`lean/Fir/Execution/MemoryFromAddrLaws.lean`). Stage 3 adds the core ops
that use them, `ptr_expose` and `ptr_from_int` (the human's spelling of
2026-11-18, Q1), to the spec, `fir-ref`, the Rust IR and verifier and
the corpus (see "The ops" below). The backend comes in the stage after it.
The spec's memory chapter renders all of them.

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

The spec allows any address that fits, and a freed allocation also any
aligned address in range (see "Exposing a pointer" below). Only live
allocations are compared,
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
memory, and exposing exposes nothing but in its own memory. Exposing counts
as allocating in its memory, as a declared effect: an op that exposes
declares that it allocates there (the human's ruling of 2026-11-20 on
#232, question B). `ptr_expose` declares it, and `LawfulDialectAddresses`
states it for every op (semantics-effects.md). Rejected: a new
declared effect, "exposes in memory m", which would add a field to every
effect set, the Rust effects, the verifier and the function summaries.
Also rejected: adding the address to `Memory.allocs`, which would make
exposing an allocation effect but narrow _no read_ under the same
statement of `LawfulDialectEffects`. The end of a return does not compare
the addresses of the allocations it observes: the human ruled this on
2026-11-20, on #233
([semantics-m1-trace.md](semantics-m1-trace.md#how-the-spec-states-the-end-of-a-return)).

## Exposing a pointer, and address policies

The memory effect's `expose` turns a pointer of the memory `x`, whose
pointers are `P` bits wide, into the integer of its allocation's address
plus its offset, wrapped at `P` bits, the width the human ruled on
2026-11-18 (Q2). An allocation with no address is given one first. A
pointer with no provenance gives its offset, and so does one whose
provenance names no allocation of `x`, which no run makes. Exposing an
allocation again gives the same address and changes nothing.

A live allocation may be given an address that fits. A freed one may also
be given any address in range that is a multiple of its alignment, a live
allocation's included (`Memory.admits`): no access reaches it, and the
stack slot that a dangling pointer names may hold a live allocation by the
time the pointer is exposed. The human ruled this on 2026-11-20, on #232
(question C): keep. Rejected: asking a freed allocation to fit, so that it
may not overlap a live one, under which exposing a dangling pointer after
its slot's new tenant could never give the address that native code gives.

Which address an allocation gets is the run's _address policy_: for each
memory, by its number in the data layout, a function from the shape and
address of each of its blocks to a proposed address. An op passes the
policy and the pointer width of the memory it exposes in, both from that
memory's layout entry, as it passes the unit width. The policy sees nothing
that refinement may change, so memories that refine each other get the
same address. The effect takes the proposal when it may be given, and else
the canonical address, or for a freed allocation the first aligned address
from `lo`. So the address may always be given whatever the policy, and at
each exposure every address that may be given is the one given under the
policy that proposes it (`Memories.expose_of_admits`). That the union over
policies holds every assignment along a path is an argument, not a
theorem: a policy sees the places, which each exposure that gives an
address changes. The canonical layout is the policy that proposes nothing,
`Policy.canonical`.

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

No address may be given when the memory has run out of addresses. The
spec has no outcome for that, as allocating has none, so exposing is then
immediate UB, with the reason "an exposure that no address fits" (the
human's ruling of 2026-11-18, Q5).

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
of 2026-11-18, Q3), so at such an address it may pick either (the next
section). The gap is `fir-ref`'s choice, not a rule of the spec.

## Turning an integer back into a pointer

The memory effect's `fromAddr` turns an integer of a memory's pointer width
back into a pointer of an allocation that holds its address: a live,
exposed allocation from its address to its end, the end included. A freed
allocation never counts (the human's ruling of 2026-11-18, Q3). The
pointer's offset is the address less the allocation's. When no allocation
holds it, the pointer has no provenance, and an access through it is
immediate UB, so a pointer rebuilt from an address that was never exposed
cannot access memory. `fromAddr` itself never fails.

Two allocations may hold one address, one ending where the next starts,
and the choice between them is angelic. It is stated by a _resolver per
call_ (`Memory.Resolver`), as the human ruled on 2026-11-20, on #232
(question A): the memories of a run count, for each memory, the integers
turned back into pointers of it (`Memories.rebuilds`), and the run's
resolver for each memory sees that memory's count, the places of the memory's blocks and the address, and
proposes an allocation. The effect takes the proposal when it holds the
address, and else the memory model's own pick (`Memory.pick`): the first
allocation whose units hold the address, and else the first whose end it
is. At each call every allocation that holds the address is the one picked
under the resolver that proposes it (`Memories.fromAddr_of_holds`).
Rejected: a resolver per memory state, under which two calls on the same
address in the same memories pick the same allocation, narrower than Q3;
wildcard provenance, as Miri has, which is broader; and the fixed rule that
the allocation that starts at the address wins, which is not angelic.

The resolver travels in the run's record (`RunItems`, field `resolvers`), as
the policy does, and a run made from its module gives the canonical
resolver, which proposes nothing, so `fir-ref` takes the memory model's
pick. The pick is `fir-ref`'s choice, not a rule of the spec. Every
obligation and guarantee over the semantics with memory holds for every
record, so for every resolver, with no new hypothesis.

Memories refine each other only when they have counted as many calls in
each memory (`Memories.IsRefinedBy`), so turning an integer back in memories that
refine each other gives the same pointer. The effect obligations do not
see the count: turning an integer back writes, allocates and exposes
nothing. Which declared effect covers the count is open for the human
(see "The ops" below). _Counts no rebuild in x_ (`RebuildsNot`) is its
own property: every other operation of the effect has it in every memory,
and turning an integer back into a pointer in every memory but its own, so
calls in different memories do not change each other's picks. Rejected:
one count shared by every memory, under which reordering calls in two
memories would change what each picks.

A step cannot look ahead at what the program does with the pointer, so the
angel chooses over whole runs. `Func.angelicBehaviour` is the spec's
behaviour with memory: under each policy, the resolvers whose runs never
end in UB, when there is one, and every resolver otherwise. Rejected: a
union over every resolver, as `Func.memBehaviour` is over policies, under
which one resolver that ends in UB would make the program UB. When the
runs of `fir-ref` never end in UB, on any path at any budget, their
outcomes are the spec's; when they do, another resolver may avoid the UB,
so from stage 3 `fir-ref` may report UB where the spec has none. A refinement
under each policy and resolver lifts to the spec's behaviour when the
target ends in UB under each resolver under which the source does
(`Func.angelicBehaviour_isRefinedBy_of_each`), and in general when each
resolver the target keeps is matched by one the source keeps.

## The ops

`ptr_expose` and `ptr_from_int` are core ops, `Core.Op.ptrExpose` and
`Core.Op.ptrFromInt` (`lean/Fir/Core/PtrInt.lean`), with no attributes:
`%a: i64 = ptr_expose %p` and `%q: ptr = ptr_from_int %a`. Each names its
memory by its pointer's type and carries the integer's width in the other
type, so an integer of any width reads back.

- **Width and integral memories.** The module's data layout asks that the
  integer be as wide as the memory's pointers (the human's ruling of
  2026-11-18, Q2) and that the memory not be `nonintegral` (the human's
  ruling of 2026-11-11 on #231). Each op lists its memory and width
  (`DialectValidation.opAddrs`), and `SymbolTable.MemoriesIn` checks both,
  as it checks the unit width of a `memset`. Rejected: an attribute that
  repeats the width, which the types already give.
- **Rules.** `ptr_expose` on a defined pointer is the memory effect's
  `expose` under the run's policy for its memory (`RunItems.addrs`), at the
  pointer width of the memory's entry; `ptr_from_int` on a defined integer
  is `fromAddr` under the run's resolver (`RunItems.resolvers`). `fir-ref`
  follows the canonical policy and resolver. `fir-ref run` does not
  validate, so each rule cuts or pads an integer of another width.
- **Poison.** A poison pointer makes `ptr_expose` immediate UB, so its
  poison class is `exception`: the rulings leave no other choice
  (semantics-poison.md). A poison integer makes `ptr_from_int` give a
  poison pointer, and it still counts the call, so memories that refine
  each other keep equal counts; it propagates poison.
- **Effects.** `ptr_expose` reads and allocates in its memory and may be
  UB. `ptr_from_int` reads and allocates in its memory and is never UB.
  Both read: their results depend on the addresses of the memory, which
  _no read_ lets differ.

The Rust IR registers both ops (`crates/funk-ir/src/dialects/core/ptr_int.rs`)
with the same effects, and `funk verify` checks the width and the integral
memory with the layout's rules. The corpus runs both ops on `fir-ref`
only, and `tests/fir/reject/ptr-int.toml` holds the texts that do not
decode and those that the layout rejects
([texts-addresses.md](../coverage/texts-addresses.md)). The backend comes
in the next stage.

Which declared effect covers the count of `ptr_from_int` has no ruling yet.
`ptr_from_int` declares an allocation, which over-approximates and so
licenses nothing unsound, and `LawfulDialectAddresses` states that an op
that does not declare one counts no rebuild. The options: count it as
allocating, as exposing is (recommended, and what the spec does now); no
declared effect beyond the read, so a pass may drop an unused
`ptr_from_int` or reorder two of them, which the union over resolvers
allows but a proof for each resolver does not; or a new effect. The answer
changes one line of `Core.Op.effects` and the second obligation.

## Addresses and the declared allocation

The effect obligations compare units and shapes, not addresses or the
count of integers turned back into pointers, so they cannot tell an op that
exposes from one that does nothing. Exposing counts as allocating in its
memory, as a declared effect (the human's ruling of 2026-11-20 on #232,
question B). `LawfulDialectAddresses`, in
`lean/Fir/Execution/AddressObligations.lean`, states it beside
`LawfulDialectEffects`, whose statement every guarantee asks for and which
stays as it is: an op that does not declare an allocation in a memory gives
no allocation of it an address (`ExposesNot`) and counts no rebuild there
(`RebuildsNot`). The core (`lean/Fir/Core/AddressLaws.lean`), `gpu` and the
sum `CoreGpu` (`lean/Fir/Gpu/AddressLaws.lean`, `lean/Fir/Sum/AddressLaws.lean`)
meet it. Rejected: adding both to `LawfulDialectEffects.allocatesNot`, which
would change the statement of a class that the #384 guarantees ask for.

Which declared effect covers the count is open: see "The ops" above.
