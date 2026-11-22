# Current decisions: semantics, M1 globals

This page continues [semantics.md](semantics.md). It says what holds for M1's
globals: the item, its text and validation, and how a run starts with them.

## The item

A global is an item with (ADR-2026-11-09-1546):

- a symbol;
- the memory it lives in, the default memory when none is given;
- a size in that memory's units, and an alignment;
- an initializer of constant units, which may include the address of a symbol
  plus an offset, such as `@f` or `@g + 8`;
- a `const` flag, and writing a constant global is UB;
- a linkage, `internal` (the default) or `export`.

Each global is one allocation of kind global, live for the whole run. An op gets
its address by symbol. A frontend writes initial data as units and relocations,
as an assembler does. A global in a GPU memory names that memory
(ADR-2026-11-09-1546).

An `export` global is visible to code that funk did not compile, and an
observer sees it. Weak, common and visibility linkage wait for the C frontend,
M4 (ADR-2026-11-09-1546). An `internal` global is observable only once its
address escapes (ADR-2026-11-09-1540): an external call, an observable inline
assembly block, one that gets it as a pointer operand and may write escaped
memory (ADR-2026-11-09-1541), a volatile store of the pointer or `ptr.expose`
hands it out.

The human ruled globals on 2026-11-09, on #209. Rejected: typed globals that
hold a fir value, which would tie globals to the shape of aggregates while a C
frontend lays out bytes anyway. Rejected too: every global exported, which is
wrong for C's `static`.

A global is an item of the core's kind `global` (ADR-2026-11-19-0124):
`global @msg() size(8) align(1) const units(104, 105, 0) {` and `}`, with
`memory(N)` first when `N` is not 0, the words `const` and `export` in
that order, and the initializer's pieces `units(U, ...)`, `zeros(N)`,
`addr(@s)` and `addr(@s, K)`, which fill the units in order. An address
takes the units of one pointer of `@s`'s memory. A valid global names a
declared memory and a power-of-two alignment, gives units that fit its
memory's unit, takes addresses of globals of its own table only, and has
an initializer no larger than its size. The spec, `fir-ref fmt` and
`validate`, and `funk-ir` read, print and check globals, a run starts
with them, and the op `globaladdr` gives a global's address (below); the
backend places them in `.rodata`, `.data` or `.bss` and lowers the op
(#237 stage 3,
[x86-64-backend-lowering-memory.md](x86-64-backend-lowering-memory.md#globals)).
The words `global` and `const` are ADR-2026-11-09-1546's: the human ruled
on 2026-11-20 (#237 Q4) that a global keeps them, and that the G0 check, on
the Lean and the Rust side, lists both with `align` among the words generic
code shares with the core, since the core's text writes them too
(`alloca`'s kind `global`, the op `const`). Rejected: `data` and
`constant`, which stage 1 shipped so that no check changed, but which are
not what the ADR and its readers call a global. A global's allocation keeps
the kind `global`; a function's address is an allocation of kind `function`
(the human's ruling of 2026-11-19 on #235), so `addr(@f)` waits until runs
make those. Rejected:
units and relocations at explicit offsets, two parts that must agree.

## Globals in runs

A run starts with one allocation of kind `global` for each global of its
function's table, before anything it allocates, outside every call, so no
frame frees it (ADR-2026-11-09-1546). Each is the next allocation of the
memory of its number, so a memory's globals take its first ids in the
table's order, and an `addr(@g, K)` piece holds the pointer to `@g`'s
allocation plus `K`, in the fragments a store of that pointer writes. The
id an address names is the one the run places `@g` at when the run names
distinct memories by distinct numbers, as a module's own runs do. A
global's whole block is built at the start, so a run of a module with a
huge global, which validation accepts up to `2^64 - 1` units, builds all
its units, as `alloca` of a huge count does.

- A global's units past its initializer hold zeros when the run starts. The
  human ruled this on 2026-11-20 (#237 Q1). Rejected: poison, as fresh
  memory holds, which would make a frontend spell out C's zeros and let
  `fir-ref` and `.bss` disagree; and an initializer that must cover the whole
  size, which the issue does not ask.
- A write to a constant global is UB when it runs: its block is constant, and
  a store to a constant block faults, after the access's own faults and
  before a misaligned one. Copies, moves and fills reach it through the same
  store. The human ruled this on 2026-11-20 (#237 Q2). Rejected: the verifier
  rejecting a store whose pointer is a constant global's address, which
  catches only the writes it can see.
- A run holds the globals of its own function's table only: a host
  function's run holds the host's, and a kernel's run its device module's.
  The human ruled this on 2026-11-20 (#237 Q3). Rejected: every table's
  globals in every run, unused allocations that the run cannot name, which
  an observer of exposed or exported memory would still see.

The run's items list these starting allocations (`RunItems.starts`), filled
from the table (`RunItems.ofTable`), and every run of the spec starts from
them: the runs with memory, the runs that see the end of each return, the
traced runs and the modes that `fir-ref run` walks. A dialect says which of
its memories a data layout numbers (`DialectEffects.numbered`): the core's
memory `n` is memory `n`, and a sum's are its base's; a dialect that numbers
none starts from empty memories. So the guarantees over runs with memory,
the #384 ones and their `CoreGpu` counterparts included, keep their
statements: they hold for every record of the items. A function's address
will be another starting allocation, of the kind `function` (#235). This
is the agent's design for #237, not a ruling. Rejected: a start given to
each run as an argument, which would change the statements of the
guarantees.

## The address of a global

`%p: ptr(N) = globaladdr @g` gives a pointer to the first unit of the global
`@g` (ADR-2026-11-09-1546, spelled as ADR-2026-11-19-0124 says). It has one
attribute, the symbol, no operands and one pointer result. Validation
accepts it when `@g` names a global of the op's own table, the first global
with that symbol, whose memory is `N`: as `call` names its callee, a
function of a nested module names its own module's globals and not its
parent's, and the reverse. Effects: pure. Poison class: propagates, with no
operand, and it never gives poison.

Its rule reads the run's items (`Op.readsItems`), as `fieldaddr`'s does:
`RunItems.global?` gives each global's memory and allocation id, filled by
`RunItems.ofTable` from `Global.startId?`, the same function that gives an
`addr(@g, K)` piece its pointer, so the op and an initializer cannot name
different allocations. The pointer has the global's allocation as its
provenance and offset 0. A record that places no global `@g`, or places it
in a memory other than `N`, gives the pointer with no provenance at offset
0, through which every access is UB, so a `ptr(N)` never names another
memory's allocation, and so
the op is never UB and never gives poison for every record, and its laws,
and the #384 guarantees, hold with no hypothesis on the record. A store
through it to a constant global is UB when it runs (Q2 above). Validation
and the run read a table's globals alike (`RunItems.ofTable_globalMem`).
This is the agent's design for #237 stage 2b, not a ruling. Rejected: a
poison result for a symbol the record does not place, which would make the
op one that may give poison for some records, and so break the obligation
that a pure op makes none for every record.
