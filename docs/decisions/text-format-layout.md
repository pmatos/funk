# Current decisions: the data layout

This page continues [text-format.md](text-format.md). It says what holds
today for a module's data layout: its text, its default, what it means and
which layouts are valid. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted
(ADR-2026-11-09-1610).

## The layout line

A module declares its memories in its data layout (ADR-2026-11-09-1542). The
text writes it on one line after the dialect set: the word `layout`, then
one entry for each memory, separated by `, `, then an empty line, as in
`layout memory(1, unit(16), pointer(32), little, align(4), nonintegral)`.
An entry is `memory(N, unit(U), pointer(P), O)` with the memory's number
`N`, its unit's width `U` in bits, its pointers' width `P` in bits and its
byte order `O`, `little` or `big`, always written; then `align(A)` when the
entry gives its pointers an alignment of `A` units, and the word
`nonintegral` when the memory is non-integral, in that order. The grammar is
`module ::= ('dialects' word (',' word)*)? ('layout' type (',' type)*)? item* locs`,
and each entry is read as a type, so the lexer is unchanged
(ADR-2026-11-12-1821).

An entry decodes only in that exact shape, with each number from 0 to
16,777,215, the bound of an integer type's width and of a pointer type's
memory. Any other attribute is a parse error at the entry: a missing or
misplaced part, another word, `align(A)` after `nonintegral`, a negative
number or one above the bound. The entries keep the order the text gives
them, and nothing sorts or merges them. A nested module writes no layout:
`layout` in its body is no item's kind, so it does not parse
(ADR-2026-11-12-1821).

`lean/Fir/Syntax/Layout.lean` defines the layout, `lean/Fir/Text/Grammar.lean`
its text and `lean/Fir/Text/LayoutLaws.lean` proves that each entry reads
back. The round trip and the proof that every parsed module is well formed
cover it (`Module.WellFormed.layout`). In Rust it is
`crates/funk-ir/src/ir/layout.rs`, and `lean/FirTest/Layout.lean` and
`crates/funk-ir/tests/layout.rs` check the same texts on both sides.

Rejected: LLVM's layout string, `"e-p1:32:32-ni:1"`, which puts a second
grammar inside a string for both parsers and the proofs to read; positional
entries, `memory(1, 16, 32)`, where a reader cannot tell the unit from the
pointer width (ADR-2026-11-12-1821).

## What a layout means

A module with no layout line has the empty layout: memory 0 alone, with
8-bit units, 64-bit pointers of natural alignment, little endian and
integral, `MemLayout.default`. A layout that leaves memory 0 out gives it
that entry, so every module has memory 0, and every earlier text keeps its
meaning. A pointer of a memory takes `ceil(P / U)` units, and its natural
alignment is the least power of two at least that; `align(A)` replaces it.
`nonintegral` marks a memory as LLVM's `ni:` marks an address space: no
pointer of it becomes an integer, so #232 rejects `ptr.expose` and
`ptr.from_int` on it. The ops that read the widths, the byte order and the
alignment come with loads and stores, in stage 4 of #231
(ADR-2026-11-12-1821).

The layout is the top-level module's. A nested module has none of its own,
and the pointer types of its functions name the memories of the module that
holds it. Rejected: a layout per nested module, which no M1 dialect needs,
while memory numbers shared by a host and its device modules keep them
comparable (ADR-2026-11-12-1821).

## Valid layouts

A valid entry has a unit and pointers of 1 to 16,777,215 bits, an alignment,
if any, that is a power of two no larger than that, and the byte order
`little`. A valid layout declares each memory once. The human ruled on
2026-11-11 on #231, as the orchestrator recorded: M1 admits only `little`,
so a `big` memory decodes and validation rejects it, and no backend or
harness sees an untested big-endian path; a later milestone may allow `big`
with a backend that uses it. The same ruling added the per-memory
non-integral flag (ADR-2026-11-12-1821).

Every pointer type that a module states names a memory that the module has:
memory 0, or one that the layout declares. So `ptr(N)` is valid exactly
when the layout declares `N`. A dialect says which memory its pointer types
name through `DialectValidation.tyMemory` (in Rust, `TypeSpec::memory`); the
core's `ptr(N)` names `N`. The rule covers every type that a function
states, its results, parameters and the values its blocks define, and the
types of each item of a dialect's kind, at any depth of nesting. Both rules
are fields of `Module.Valid`, in `lean/Fir/Validation/Layout.lean`, and
`Module.problems` checks them after the symbol tables
(`lean/Fir/Validation/CheckLayout.lean`): first each entry's problems and
each memory declared twice, then, for each function or item whose types
name an undeclared memory, one problem that names the first such memory.
The Rust verifier does the same, in `crates/funk-ir/src/verify/layout.rs`.
`fir-ref validate` runs the check with a copy of `Func.types` compiled after
its walk of a function's blocks, so it takes no stack per level of nesting.

Rejected: checking the memory of `ptr(N)` in the core's rule of types,
which sees no module, so every dialect's type rule would need the layout as
a parameter; a rule beside `Module.Valid`, as the dialect set's is, which
would leave valid modules with pointers of memories they do not have.
