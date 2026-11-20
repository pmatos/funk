# What the corpus texts test: copies, moves and sets

This page continues [texts.md](texts.md): it lists the texts of the fir
test corpus that test `memcpy`, `memmove` and `memset` (#234), in the order
their stages added them. Paths are relative to `tests/fir/`.

The texts of #234's second stage use `memcpy` and `memmove`
([ADR-2026-11-09-1551](../adrs/2026-11-09-1551-memory-intrinsics-are-ops.md),
[ADR-2026-11-18-2131](../adrs/2026-11-18-2131-memcpy-and-memmove-take-an-ordering-and-a-run-time-length.md)).
`memcpy.fir` copies and moves an `i32` and a stored pointer, which still
reaches its allocation, and copies part of a pointer, poison and fresh
units, which read back as poison. A move whose ranges overlap, up or down,
takes what the source held before it began; a `memcpy` whose ranges partly
overlap is UB, and one onto its own range or a disjoint one is not. A
length of 0 does nothing, even through poison and dangling pointers; any
other length through them, or past the allocation, is UB; a poison length
runs a length that `fir-ref` chooses; and a length may be an integer of any
width. `memcpy-memories` counts the length in the units of a memory of
16-bit units, and `gpu-memcpy` copies and moves in gpu work-group memory,
where half the work-items copy past their buffer, which is UB.
`reject/memcpy.toml` holds the texts that do not decode, such as one with
`align(A)` or with pointers of two memories, and those that validation
rejects, such as an ordering other than `nonatomic`.

The texts of the third stage use `memset`, which
[ADR-2026-11-18-2131](../adrs/2026-11-18-2131-memcpy-and-memmove-take-an-ordering-and-a-run-time-length.md)
spells too. `memset.fir` fills an `i32` with copies of an `i8`, whole and
in part, fills over a stored pointer, which then reads back as poison, and
writes a poison value. Its lengths are integers of any width, `i1`, `i7`,
`i33` and `i128` among them; a fill past the allocation, or starting
before it, is UB, and so is one of 2^63 bytes into an allocation of 4.
`memset-memories` fills with an `i16` in a memory of 16-bit units,
and `gpu-memset` fills in gpu work-group memory, where half the work-items
fill past their buffer. `reject/memset.toml` holds the texts that do not
decode, and those that validation rejects, such as a value that is not as
wide as a unit of its memory. Every test of these texts and of the second
stage's is interpreter-only. `funk build` builds a module all or nothing
([the corpus README](../../tests/fir/README.md)), and each of these texts
holds tests that native code cannot run: tests that return a pointer, pass
a poison one, reach UB or take a length of a width the backend does not
lower, or a memory of 16-bit units or a gpu kernel, which the backend does
not build. So even a test such as `@copy_int`, which native code could
run alone, is interpreter-only.

Since the fourth stage the backend lowers the three ops to calls of funk's
own runtime routines
([x86-64-backend-lowering-memory.md](../decisions/x86-64-backend-lowering-memory.md#copies-moves-and-sets)).
`memops-native` runs them on `fir-ref` and as native code: a copied
pointer, and one moved over a range that overlaps its own, still reach
their allocations; and at each width of the length that the backend
lowers, a copy, a copy onto its own range, moves 3 bytes up and down or
by none, a set of an `i8`, lengths of 0 and a poison value. Lengths cut by
`trunc` to `i1`, `i8`, `i16` and `i32` check that the call does not read
the bits above the width, and a move and a set take a poison length of
`i1`. Every test of it is differential. `fieldaddr-programs`, of
[texts-aggregates.md](texts-aggregates.md), also zeroes an array with
`memset` before it fills it.
