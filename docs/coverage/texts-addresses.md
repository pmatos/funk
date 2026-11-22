# What the corpus texts test: pointers as integers

This page continues [texts.md](texts.md): it lists the texts of the fir
test corpus that test `ptr_expose` and `ptr_from_int` (#232), in the order
their stages added them. Paths are relative to `tests/fir/`.

The texts of #232's third stage use both ops
([ADR-2026-11-09-1542](../adrs/2026-11-09-1542-memory-is-logical-blocks-in-typed-memories.md)).
`ptr-int.fir` exposes an allocation and turns its address back into a
pointer that loads what the allocation holds, poison included; turns the
address plus 4 into a pointer to the second `i32` of the allocation, and
the address plus 8, its end, or minus 4 into pointers through which a load
is UB; and takes the difference of two exposed addresses of one
allocation, 4. An address that no exposed allocation holds, 0 or 4096,
gives a pointer with no provenance, through which a load is UB, and
exposing such a pointer gives back its integer. A poison integer gives a
poison pointer, and exposing a poison pointer is UB.
`ptr-int-memories.fir` does the same in memory 1, of 32-bit pointers, with
`i32` addresses. No test returns an exposed address, which depends on the
canonical layout that `fir-ref` follows. When the third stage added them,
the backend lowered neither op, so every test of these texts was
interpreter-only.

`reject/ptr-int.toml` holds the texts that do not decode, an attribute, a
pointer where an integer is or the reverse, and those that the data layout
rejects: an integer that is not as wide as the memory's pointers, and
either op in a memory marked `nonintegral`.

#232's fifth stage lowers both ops as moves
([x86-64-backend-lowering-memory.md](../decisions/x86-64-backend-lowering-memory.md#pointers-as-integers)),
so each test of `ptr-int.fir` whose result does not depend on an address
runs as native code too and declares its result: the round trip, the
address plus 0 and plus 4, the difference of two addresses, and an integer
that no exposed allocation holds turned into a pointer and exposed again.
A test of poison or UB stays interpreter-only, and so does every test of
`ptr-int-memories.fir`, whose memory of 32-bit pointers the backend does
not realise. `ptr-int-programs.fir` runs round trips of an address on both:
stored in memory and loaded back, passed to a call that stores through it,
and stepped by 4 through an array in a loop; it also returns an address
modulo its allocation's alignment, 64, and whether it is 0, which every
address the spec may give agrees on. It makes the round trip in memory 1,
of 64-bit pointers too, and turns an address of memory 0 into a pointer of
memory 1, which has no exposed allocation, so a load through it is UB, an
interpreter-only test.
