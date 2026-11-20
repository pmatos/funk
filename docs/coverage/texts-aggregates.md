# What the corpus texts test: aggregates and field addresses

This page continues [texts.md](texts.md): it lists the texts of the fir
test corpus that test aggregates' layouts and the field address
`fieldaddr` (#236), in the order their stages added them. Paths are
relative to `tests/fir/`.

The texts of #236's first stage hold aggregates' layouts, core items of
placed fields
([ADR-2026-11-16-1546](../adrs/2026-11-16-1546-an-aggregate-s-layout-is-a-core-item-of-placed-fields.md)).
`aggregates` places integer, pointer and float fields in the default
memory, a repeated `i24` field whose elements are rounded up to their
alignment, a flexible array member of no elements and an empty layout;
`aggregates-memories` places integer and pointer fields in a memory of
16-bit units, and in a nested module. Float fields in such a memory are
in `fieldaddr-programs-memories`, below. `reject/aggregate.toml` holds the layouts that do not
decode and those that validation rejects: overlapping fields, misaligned
ones, a field past the size, an alignment that is not a power of two, a
memory the module does not declare, and float fields that are misaligned,
overlap, end past the size or have an invalid format.

The texts of the second stage use `fieldaddr`
([ADR-2026-11-18-2041](../adrs/2026-11-18-2041-fieldaddr-moves-a-pointer-to-a-field-of-a-named-layout.md)).
`fieldaddr` reaches the fields of a pair and the elements of a repeated
`i24` field by an index of each width, and an element of a layout in a
memory of 16-bit units; an element past the field's last is an address,
and storing through it is UB only when it leaves the allocation.

The texts of the third stage run struct and array programs.
`fieldaddr-programs` stores an integer, two floats and a pointer to the
struct itself in a struct and reads them back by their offsets, fills and
sums an array in a loop, reads an element by an index, one past the end
and through a poison index included, steps back from the one-past-the-end
address, walks a linked list, appends to an array that follows its
length, writes past a flexible array member up to the end of its
allocation, and reaches the second element of an array of `float(15, 64)`,
16 units apart. `fieldaddr-programs-memories` runs such programs in a
memory of 16-bit units and 32-bit pointers, and keeps a pointer of the
default memory in a field of a layout of that memory.
`reject/fieldaddr.toml` holds the uses of `fieldaddr` that do not decode,
such as a negative field number, a result of another memory or a float
index, and those that validation rejects: a symbol that names no layout
of the op's own module, a field the layout does not have, an index on a
field that is not repeated, and a layout of another memory than the
pointer's. Every test runs on `fir-ref` alone until the backend lowers
`fieldaddr` (stage 4 of #236).
