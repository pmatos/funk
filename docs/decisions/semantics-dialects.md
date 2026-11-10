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
side by side: signature, text, validation, poison classes, semantics, calls,
and the meaning, poison and refinement of the summed types. Any number of
dialects is a nested sum, `core ⊞ a ⊞ b` (ADR-2026-11-09-2306).

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
the base accepts (ADR-2026-11-09-2306).

## Lifting an extension

An extension is written over the dialects it depends on. It joins any sum
that holds them by a lift: `e.lift dep ι` is `e`, written over `dep`, with
an inclusion `ι` of `dep`'s types in a larger base's. An inclusion maps
types and their values each way. The base of a sum is included by
`TyIncl.inl`, and inclusions extend over an extension and compose, so a
dialect held anywhere in a nested sum is included (ADR-2026-11-10-1310).

The lift has `e`'s ops and rules, `big`'s rules and text for `big`'s types,
and `e`'s semantics on values moved across the inclusion. A lifted op sees
only the symbols whose types `e` can write, and is valid only where it can
write the function's result types (ADR-2026-11-10-1310).

The lift of a lawful extension is lawful, for its text and for poison, when
the inclusion is lawful and `e`'s name is new to the larger base. So two
extensions of the core, written apart, combine in one lawful sum
(ADR-2026-11-10-1310).

## Limits

Core ops carry core types only. A value of an extension's own type cannot
pass through a core `br`, `ret` or `call` (ADR-2026-11-09-2306). No core op
is valid in a function that returns such a value (ADR-2026-11-09-2353).

A module does not yet declare its dialect set in the text. That is a later
stage of #227 (ADR-2026-11-10-1310).

The Lean test dialects, toy, use-once and probe, are extensions of the core
named `toy` (ADR-2026-11-09-2306). The bit dialect, named `bit`, makes a sum
of three dialects with the core and the toy dialect (ADR-2026-11-10-1310).
