# Current decisions: semantics, sums of dialects

This page continues semantics.md. It says what holds today about how
dialects combine in the spec. It summarizes the ADRs it cites and does not
replace them. When this page and an ADR disagree, the page is wrong
(ADR-2026-11-09-1610).

## The sum in the spec

A module's dialects combine as a sum, routed by the `name.` prefix
(ADR-2026-11-09-1543). The spec builds the sum one dialect at a time, in
`lean/Fir/Sum/` (ADR-2026-11-09-2306).

An extension `e` has its own ops and its own types. It states each dialect
class for `base.over e`, whose types are the base's and its own. So its ops
can take and give the base's values. The base is the dialect it depends on.
A dialect with no types of its own takes `Empty` (ADR-2026-11-09-2306).

`base ⊞ e` has the ops of both and the types of both. Each class is lifted
side by side: signature, text, validation, poison classes and effects,
semantics, calls, and the meaning, poison and refinement of the summed types.
Any number of dialects is a nested sum, `core ⊞ a ⊞ b` (ADR-2026-11-09-2306).

The memories of `e` over the base are the base's and `e`'s own, as its types
are: `DialectMemOver base e` splits each of `e`'s memory names into one of the
base's or one of its own, and `ofBase` is `e`'s name for a base memory. The
sum's memories are `e`'s, and a base op's effects are renamed by `ofBase`, so
a memory has one name in the sum, whichever side names it
(ADR-2026-11-11-0452).

A word belongs to the dialect named before its first `.`. A bare word
belongs to the core. Reading an op or a type sends a word of `e`'s name to
`e`, and every other word to the base. A type goes by its head word
(ADR-2026-11-09-2306).

Each side's function rule sees the function through its own view
(ADR-2026-11-09-2257). A base op sees only the symbols whose types are all
the base's. It sees the function's result types only when they are all the
base's, and otherwise it is invalid (ADR-2026-11-09-2353).

An op's attributes go with the op, to the side that its name picks. The
sum does not route them on their own (ADR-2026-11-09-2306).

## Dialect sets and laws

`DialectSet d` lists the dialects whose names the words of `d` may use. The
core's set is empty. The set of `base ⊞ e` is the base's set and `e`'s name.
`LawfulDialectSet` says every op name, attribute word and valid type word
names a dialect of the set (ADR-2026-11-09-2306).

The sum's text is lawful exactly when every word goes to its own side. That
holds when the base's set is lawful, `e` writes its words under its name, and
`e`'s name is new to the base. Then the round trip and well-formedness hold
for the sum. The sum of lawful dialects is lawful when `e` accepts every type
the base accepts (ADR-2026-11-09-2306). The same condition makes the sum
lawful in its effects when both sides are (ADR-2026-11-09-1541).

## Lifting an extension

An extension is written over the dialects it depends on. It joins any sum
that holds them by a lift: `e.lift dep ι` is `e`, written over `dep`, with
an inclusion `ι` of `dep`'s types in those of a larger base `big`. An
inclusion maps types and their values each way. The base of a sum is
included by `TyIncl.inl`, and inclusions extend over an extension and
compose, so a dialect held anywhere in a nested sum is included
(ADR-2026-11-10-1310).

The lift has `e`'s ops and rules, `big`'s rules and text for `big`'s types,
and `e`'s semantics on values moved across the inclusion. A lifted op sees
only the symbols whose types `e` can write, and is valid only where it can
write the function's result types (ADR-2026-11-10-1310).

A lift also records a memory map `μ` from `dep`'s memories to `big`'s:
`e.lift dep ι μ`. Its memories are `big`'s and `e`'s own. `liftMem μ` renames
`e`'s name for a memory of `dep` to `μ` of it and keeps `e`'s own, so the sum
names each memory of `dep` once (`liftMem_ofBase`; ADR-2026-11-11-0452).

The sum of a larger base and the lift has lawful text when the base's text
and set are lawful, `e`'s name is new to the base, and the set of what `e`
depends on is in the base's set. The lift is lawful for poison when the base
and `e` are, the inclusion is lawful, and `e` accepts each type it depends on
whose inclusion the base accepts. Under the same conditions, the lift is
lawful in its effects when `e` is, with `e`'s effects renamed by the lift's
memory map (ADR-2026-11-09-1541, ADR-2026-11-11-0452). So two extensions of the core, written apart, combine
in one lawful sum (ADR-2026-11-10-1310).

## Region kinds in sums

A dialect registers region kinds, each with its rule. The sum registers the
base's kinds and then `e`'s, and a region obeys the rule of the side that
registers its kind, through that side's view. A lift registers `e`'s kinds
with `e`'s rule. The laws of names ask that a dialect register only words of
its own name, so no kind goes to the wrong side (ADR-2026-11-10-1941).

The interpreter runs only the core's kind, a function's body. An op that
owns regions of a dialect's kinds runs by its dialect's semantics, which
sees its op instance and operands, not the regions. An op that owns a
region of the core's kind is stuck, and no valid op does
(ADR-2026-11-10-1941).
## Kinds of item

A dialect registers kinds of item, each a word of the dialect such as
`toy.cell`, with its own rule, `validItem` (ADR-2026-11-10-2224). An item
of a dialect's kind is written by the one item production, with an empty
body, and every reader decodes it whichever dialects it holds. Validation
asks that a dialect register its kind, that it obey that dialect's rule,
and that its table's dialect set name the dialect of each of its words.
The sum registers both sides' kinds and sends each to the side that
registers it. The core registers none: `func` and `module` are its own
terms (ADR-2026-11-10-2224, ADR-2026-11-10-1510).

## Limits

Core ops carry core types only. A value of an extension's own type cannot
pass through a core `br`, `ret` or `call` (ADR-2026-11-09-2306). No core op
is valid in a function that returns such a value (ADR-2026-11-09-2353).

The Lean test dialects, toy, use-once and probe, are extensions of the core
named `toy` (ADR-2026-11-09-2306). The bit dialect, named `bit`, makes a sum
of three dialects with the core and the toy dialect (ADR-2026-11-10-1310).

## A module's dialect set

A module names its dialects other than the core on its first line,
`dialects toy`. Its words must name only the core or those dialects, and it
may name only dialects of the reader's set (ADR-2026-11-10-1306). A module
that names none uses the core alone (ADR-2026-11-09-1543).

A nested module, a `module` item, names its own set on the first line of its
body. Its set is its own, not its parent's, so a host module can hold a
device module whose dialects the host does not use (ADR-2026-11-10-1510).
