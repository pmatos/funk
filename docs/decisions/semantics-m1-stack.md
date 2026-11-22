# Current decisions: semantics, M1 stack allocation

This page continues [semantics-m1-memory.md](semantics-m1-memory.md) with
stack allocation in M1's memory: the `alloca` op, its attributes and its
rule. It is the record: when this page and an ADR disagree, the page wins,
and the ADR is fixed or deleted (ADR-2026-11-09-1610).

## Stack allocation

`alloca` allocates room for a constant count of values of a type, written
`%p: ptr = alloca stack i32 4` and `%p: ptr(1) = alloca stack i8 12 align(4)`
(ADR-2026-11-14-0915; `lean/Fir/Core/Alloca.lean`). The human ruled on
2026-11-14, on #378, that the op takes a type and a constant count, that its
default alignment is the type's natural alignment, and that the natural
alignment of `iN` is the least power of two that is at least its units:
`i8` 1, `i24` 4, `i32` 4, `i64` 8 and `i128` 16 in memory 0
(`MemLayout.intAlign`). Rejected by that ruling: a count of units, with no
type to give a default alignment; a run-time count in M1 (#381); and
capping the natural alignment at the pointer's.

- The attributes are the kind, the type, the count when it is not 1 and
  `align(A)` when given, separated by spaces as every op's are. The human
  confirmed the spaces on 2026-11-14 (#382). Rejected: commas, as #378's
  examples wrote them, a second attribute grammar for one op.
- The op allocates the count times the units of the type in the memory of
  its result, with its kind and alignment. The pointer has provenance for
  the allocation at offset 0, and its units are poison. The frame of the
  call frees a stack allocation when the call returns.
- Validation accepts the kind `stack` alone, a count of at least 1, a power
  of two for `A` no larger than `MemLayout.limit` (`MemLayout.ValidAlign`,
  the layout's own rule) and a valid integer, pointer or float type.
  `global` and `heap` decode, as hooks in the format (ADR-2026-11-09-1542).
- The element is an integer, a pointer or a float type: the human ruled on
  2026-11-14 (#382) that pointer elements come with their loads and
  stores, which stage 4d-2b of #231 adds
  ([semantics-m1-memory-access.md](semantics-m1-memory-access.md#pointers-in-memory)),
  and on 2026-11-15 (#397) that float elements come with float loads and
  stores, which #264 adds
  ([semantics-m1-memory-access.md](semantics-m1-memory-access.md#floats-in-memory)).
  A float of `float<e,m>` takes the units of the integer of its
  `1 + e + m` bits, at the natural alignment of the float's size: in
  memory 0, `f16` and `bf16` 2, `f32` 4, `f64` 8 and `f128` 16 (#378 Q3).
  Rejected: float and pointer elements before any access could read or
  write them. `gpu.work_group_alloca` takes floats too, by the human's
  ruling of 2026-11-18 on #432
  ([semantics-m1-dialects.md](semantics-m1-dialects.md#work-group-memory)).
- `A` is at most `MemLayout.limit`, 2^24 - 1, the bound of the data layout's
  own alignments, so the largest `A` is 2^23; the count has no bound. An
  allocation larger than a machine holds is a resource error at run time, as
  a deep recursion is, and not a rule of the spec. The human ruled both on
  2026-11-14 (#382). Rejected: a bound on the count, which would not keep an
  allocation within a machine, since one `i16777215` takes 2 MiB. `fir-ref`
  has no resource error of its own: it holds each allocation's units, so a
  huge one exhausts its memory. Native code moves `%rsp` by the
  allocation, so a huge one ends the run as out of stack
  ([x86-64-backend-lowering-memory.md](x86-64-backend-lowering-memory.md#stack-allocation)).
  The bound covers a written `A` only. The natural alignment that an op
  without `align(A)` takes is not bounded: in a memory with 1-bit units, an
  element wider than 2^23 bits has the natural alignment 2^24, as a layout
  line's pointers of such a width do. The human ruled this on 2026-11-14
  (#385), as the orchestrator recorded. Rejected: rejecting an op whose
  natural alignment is above the bound, since the op rule would need the
  data layout and the proofs over op validity would change.
- The G0 check reads the words of `AllocaText.lean` and `TypeText.lean` as
  core words, but leaves out `align` by name (`SHARED_WORDS` in
  `scripts/check_g0.py`), since the data layout's generic grammar writes it
  too. The human ruled this on 2026-11-14 (#382). It leaves out `global`
  too, which a global's generic text writes, as the human ruled on
  2026-11-20 (#237 Q4; semantics-m1-design.md). Rejected: reading only
  `Text.lean` and `TypeText.lean`, which checks no `alloca` word.
- It is never UB, its result is never poison, and its effect set is
  "allocates in memory `N`". It has no rule in the set monad, so the core
  dialect no longer meets the lawful class there; its obligations with
  memory are proved op by op, and `alloca`'s by its own rule
  (`lean/Fir/Core/AllocaLaws.lean`). A core function that reaches no op
  that touches memory, no `alloca`, load, store, `memCopy`, `memSet`,
  `ptrExpose` or `ptrFromInt`, reaches no memory (`Core.reachesNoMemory`). The semantics with
  memory carries the core's guarantees
  ([semantics-m1-memory.md](semantics-m1-memory.md#the-cores-guarantees)).
