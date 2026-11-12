# In M1 aggregates are layouts over memory, not values

Status: accepted
Tier: direction; area: semantics

## Decision

- **Layouts.** A layout is a size, an alignment and a list of fields, each an
  offset and a scalar type: an integer, a float or a pointer. An array is a
  repeated field. Sizes and offsets count the units of the memory the layout
  describes.
- **Ops.** One op computes the address of a field or element from a pointer
  and a layout. Data moves through the scalar loads and stores. No op makes an
  aggregate value, or extracts from or inserts into one. Each unit in memory
  may be poison, so aggregates need nothing extra for poison.
- **Signatures.** A parameter may be `byval<layout>` and a result
  `sret<layout>`, in a function's own signature and in an external
  declaration (ADR-2026-11-09-1547). The x86-64 backend classifies them by the
  System V rules from the layout's fields. A variadic call may pass a `byval`
  aggregate.
- **Values stay open.** Dialects may add value types such as vectors and
  tensors (ADR-2026-11-09-1543). First-class aggregate values in the core may
  be added later if a frontend needs them.

[semantics-m1-design.md](../decisions/semantics-m1-design.md) states each
rule. The human ruled this on 2026-11-09, on #210.

## Why

M1 brings aggregates in as far as calling conventions and the frontends need
them. fir functions already return any number of values
(ADR-2026-10-29-2008), which covers tuples and multiple returns, and
frontends copy structs with memory intrinsics (ADR-2026-11-09-1551). System V
passes a small struct in registers, and classifying it needs each field's
offset and scalar kind, not only its size.

## Rejected alternatives

- **First-class aggregate values with extract and insert ops,** as in LLVM.
  Per-field poison rules and register lowering of large values would join M1,
  as a second way to do what memory and multiple results already do.
