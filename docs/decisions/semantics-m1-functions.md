# Current decisions: semantics, M1 function addresses

This page continues [semantics.md](semantics.md) with the address of a
function and, from #235's later stages, the call through a pointer. It is
the record: when this page and an ADR disagree, the page wins, and the ADR
is fixed or deleted (ADR-2026-11-09-1610).

## What holds today

#235 is built in stages
([the stage plan on the issue](https://github.com/pmatos/funk/issues/235)).
Stage 1 lets an op pick its callee when it runs
([semantics-interpreter.md](semantics-interpreter.md)). Stage 2 adds the
value of a function's address and the op that gives it, `funcaddr`, to
the spec, `fir-ref`, the Rust IR and verifier and the corpus. The call
through a pointer is stage 3, and native code stage 4.

## The value of a function's address

A function's address is a pointer to an allocation of the kind `function`
(`Memory.AllocKind.function`): one for each function of a table, in memory
0, with no units, made when a run starts and live for the whole run. A load
or a store through it, or through a pointer that `ptradd` moves from it,
is out of bounds, so UB when it runs. Pointer comparison and `ptr_expose`
work as for data. The human ruled this on 2026-11-19, on #235 (Q1).
Rejected: the kind `global`, under which every later rule about globals
must exclude functions by hand; a pointer with no provenance that carries
the code address, which every program would see without exposure; and a
provenance that names a symbol, which changes what a pointer is in every
memory law (ADR-2026-11-23-0906).

- **One address each.** An allocation of no units takes no address
  ([semantics-m1-addresses.md](semantics-m1-addresses.md)), so two of
  them may share one. A function's allocation is the exception: where the
  model asks which addresses a block takes (`Block.extent`), a block of
  the kind `function` with no units takes one. So exposing `@f` and `@g`
  gives two different integers, as the ruling asks, and the canonical
  layout puts the second two addresses after the first. Every law of
  `lean/Fir/Memory/AddressLaws.lean`, `CanonicalLaws.lean`,
  `ExposeLaws.lean` and `PolicyLaws.lean` is stated over the extent, and
  refinement keeps it (`Block.IsRefinedBy.extent`). This is the agent's
  design. Rejected: one unit in the block, which a load of one byte would
  read.
- **The run's start.** A run starts memory 0 with its table's globals of
  memory 0, in the table's order, then one allocation for each function of
  the table, in the table's order (`RunItems.ofTable`, `funcStart`). So
  every global keeps the id that #237 gave it, and an `addr(@g, K)`
  piece keeps its units. A run of a nested module's function holds that
  module's functions only, as it holds its globals (#237 Q3). Each block
  is constant and aligned to 1 unit. A run's own allocations in memory 0
  take the ids after the functions', so a module of nine functions and no
  global gives its first `alloca` the id 9; the corpus's expected pointers
  changed so when stage 2 landed. This is the agent's design. Rejected:
  functions before globals, which would move every global's id.
- **The guarantees.** Every #384 guarantee and its `CoreGpu` counterpart
  keeps its statement and gains no hypothesis: each holds for every record
  of the items a run gives (`RunItems`), so for every list of starting
  allocations. What they speak of changes: a module's runs
  (`Module.runItems`) now start with the functions' allocations in memory
  0, so a pointer result or an end that names a run's allocation names it
  by an id that counts them.

## The op

`%p: ptr = funcaddr @f` gives the address of the function `@f`
(`Core.Op.funcAddr`, `lean/Fir/Core/FuncAddr.lean`). It has one attribute,
the symbol, no operands and one pointer result. A result of another memory
decodes, and validation rejects it.

- **Validation.** `@f` names a function of the op's own table, the first
  with that symbol, as `call` names its callee: the op refers to its
  symbol (`Op.symbolRefs`), so the generic rule checks it. The result is
  `ptr`, memory 0 (`Op.Valid`). An external declaration is not a
  function, so `funcaddr` does not name one; whether an indirect call
  through a declaration's address is allowed is stage 3's question.
- **Rule.** It reads the run's items (`Op.readsItems`), as `globaladdr`
  does: `RunItems.func?` gives each function's allocation id, filled by
  `Func.startId?`. The pointer has that allocation as its provenance and
  offset 0. A record that gives no allocation for `@f`, or an op whose
  result is not of memory 0, gives the pointer with no provenance at
  offset 0, so the op is never UB and never gives poison for every
  record, and its laws hold with no hypothesis on the record. Validation
  and the run read a table's functions alike (`RunItems.ofTable_func`),
  and two symbols get different allocations (`RunItems.ofTable_func_ne`).
- **Effects.** Pure. Poison class: propagates, with no operand.

The Rust IR registers the op (`crates/funk-ir/src/dialects/core/func_addr.rs`)
with the same effects and checks, and its well-formed generator writes it.
The corpus runs it on `fir-ref` only (`tests/fir/canonical/funcaddr.fir`),
since the backend does not lower it yet: `funk build` rejects it with "the
x86-64 backend cannot lower the op funcaddr yet". The harness counts it as
one interpreter-only cell.
