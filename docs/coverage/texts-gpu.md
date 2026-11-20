# What the corpus texts test: the gpu dialect

This page continues [texts.md](texts.md): it lists the texts of the fir
test corpus that test `gpu`, the second dialect in tree (#212), in the
order their tickets added them. Paths are relative to `tests/fir/`.

The text of #212's first stage holds kernels
([ADR-2026-11-09-1545](../adrs/2026-11-09-1545-the-second-dialect-is-gpu-kernel-shaped.md),
[ADR-2026-11-10-1510](../adrs/2026-11-10-1510-a-module-item-nests-a-symbol-table-with-its-own-dialect-set.md)).
`gpu-kernel` is a host module with a function `@host` and a device module
`@dev`, whose dialect set names `gpu`. Its kernels ask the work-item its
id, its work-group's id, the size of a work-group and the number of
work-groups. `reject/gpu.toml` holds the texts that do not decode, such as
a dimension other than `gpu.x`, `gpu.y` and `gpu.z`, a gpu op with an
operand and one with a pointer result, and those that validation rejects:
a result other than an `i32`, a gpu op in a module whose dialect set does
not name `gpu`, a dialect set that names `gpu` twice, and a device
module whose pointers name a memory that the host's layout does not
declare
([ADR-2026-11-12-1821](../adrs/2026-11-12-1821-a-module-declares-its-memories-in-a-data-layout-line.md)).

The texts of the second stage run one work-item of a kernel, which a test
gives with `work_item`
([fir-ref-command-line.md](../decisions/fir-ref-command-line.md#kernels-and-the-work-item)).
`gpu-kernel` computes a global id, which wraps at `i32`, and multiplies the
numbers of work-groups in two dimensions; its `@scratch` allocates on the
stack in a memory of 32-bit pointers and stores at the work-item's id, in
units, where an id that is misaligned or past the allocation is UB. Its
`@host` doubles its argument, once where the `add` wraps at `i32` (#471).
`gpu-memories` runs kernels in the two memories of its host's layout, one
of 16-bit units and one of 16-bit pointers: each work-item stores its value
into its own slot of a buffer and keeps the slot's pointer in the other
memory, and the work-item past the buffer reaches UB. It also returns a
pointer, gives a kernel's two results, runs a kernel of a module nested in
the device module, and runs `@host`.

The text of #406 fills the coverage matrix's cells of the `gpu` ops
([testing-and-harness-corpus.md](../decisions/testing-and-harness-corpus.md#the-coverage-matrix)).
`gpu-dims` runs each op in each dimension, on a work-item whose ids and
sizes differ in every dimension, so that a read of another dimension
fails the test, and runs `gpu.num_work_groups` on the default work-item
too.

The texts of the third stage use `gpu.work_group_alloca`, which allocates
in a memory of the host's layout, as `alloca` does, for the whole run of
the kernel (the human's ruling of 2026-11-16 on #212). `gpu-work-group`
allocates a buffer in a callee, and each work-item stores into its own
slot of it after the call returns; the work-item past the buffer reaches
UB, and so does a store through an `alloca` of the callee's frame, which
the return freed. Two allocations are distinct, and one of each kind
returned from a call keeps the work-group one and frees the other. It
allocates an `i1`, `i7`, `i8`, `i16`, `i32`, `i33`, `i64`, `i128` and a
pointer, and a pointer stored into an allocation of `align(2)` is UB.
`gpu-work-group-floats` (#432) allocates floats, as the human ruled on
2026-11-18: each aliased format and `float(2, 1)` loads back as the
same float, a NaN's payload included, an `f32` takes two units of a
memory of 16-bit units, the second holding its top 16 bits, an `f64` at
offset 4 of a memory of bytes is UB, and a load from fresh memory gives
poison. `reject/gpu.toml` holds the
uses of `gpu.work_group_alloca` that do not decode, with a kind or a
written count of 1, and those that validation rejects: a count of 0, an
alignment that is not a power of two, an invalid float type and a memory
that the host's layout does not declare.

`gpu-memcpy` and `gpu-memset` (#234) copy, move and fill in work-group
memory; [texts-memops.md](texts-memops.md) lists them.

`funk build` builds none of a nested module's functions, so a kernel runs
on `fir-ref` alone
([testing-and-harness-corpus.md](../decisions/testing-and-harness-corpus.md#the-test-corpus)),
and every test of these texts is interpreter-only but those of `@host`.
The `@host` functions of `gpu-memories` (#467) and `gpu-kernel` (#471)
are host functions, which `funk build` builds, so their tests are
differential.
