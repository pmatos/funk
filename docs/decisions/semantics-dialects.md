# Current decisions: semantics, sums of dialects

This page continues semantics.md. It says what holds today about how dialects
combine in the spec. It is the record: when this page and an ADR disagree, the
page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).
ADR-2026-11-09-1543 holds how dialects extend fir, and ADR-2026-11-09-2306 how
the spec sums them.

## Dialects extend fir

Every dialect other than the core writes its ops, types, attributes and kinds
of item as `name.word`. Core words stay bare. A module's dialects combine as a
sum, routed by the `name.` prefix, for ops, types and attributes alike. A
dialect declares the dialects it depends on, and may name their types, which
is how an extension op takes a core value. Effects and observations come from
the dialect too (ADR-2026-11-09-1543). The human ruled this on 2026-11-09, on
#202. Rejected: every extension must have a verified lowering to core, as the
decision record proposed. A quantum or photonic dialect cannot lower to a
CPU-shaped core, so it would fail G0 (ADR-2026-11-09-1544).

## The sum in the spec

The spec builds the sum one dialect at a time, in `lean/Fir/Sum/`
(ADR-2026-11-09-2306).

An extension `e` has its own ops and its own types. It states each dialect
class for `base.over e`, whose types are the base's and its own. So its ops
can take and give the base's values. The base is the dialect it depends on.
A dialect with no types of its own takes `Empty` (ADR-2026-11-09-2306).
Rejected: a plain sum of two dialects, with types `Ty₁ ⊕ Ty₂`. An extension's
op could not take a core value, and the core's `i8` would have two spellings.

`base ⊞ e` has the ops of both and the types of both. Each class is lifted
side by side: signature, text, validation, poison classes and effects,
semantics, calls, and the meaning, poison and refinement of the summed types.
A base op takes and gives the base's values as the sum's `.inl` values. Any
number of dialects is a nested sum, `core ⊞ a ⊞ b` (ADR-2026-11-09-2306).
Rejected: a list of dialects indexed by name. Typeclass search over a dependent
family is fragile in Lean, and nested sums already hold any number.

The memories of `e` over the base are the base's and `e`'s own, as its types
are: `DialectMemOver base e`, in `lean/Fir/Sum/Dialect.lean`, splits each of
`e`'s memory names into one of the base's or one of its own (`Own`), and back,
and `ofBase` is `e`'s name for a base memory. The sum's memories are `e`'s, and
a base op's effects are renamed by `ofBase`, so a memory has one name in the
sum, whichever side names it (ADR-2026-11-09-2306). Every extension that
declares effects gives a `DialectMemOver` instance. The test dialects have no
memory of their own: their memories are `Mem core ⊕ Empty`. Rejected: each
side's memories kept apart, which named a base memory twice, so a pass could
reorder the core's store with an extension's load of the same memory. Rejected
too: one global type of memory names, such as `ptr<N>`'s `N`. Each dialect
names its own memories, and two dialects could then claim one name.

A word belongs to the dialect named before its first `.`. A bare word
belongs to the core (`wordDialect`). Reading an op or a type sends a word of
`e`'s name to `e`, and every other word to the base. A type goes by its head
word (ADR-2026-11-09-2306). Rejected: each extension routes its own types. The
sum would trust the extension to send the base's types back to the base;
routing in the sum keeps the base's own rules on its types.

Each side's function rule sees the function through its own view
(ADR-2026-11-09-2257). A base op sees only the symbols whose types are all
the base's. It sees the function's result types only when they are all the
base's, and otherwise it is invalid (ADR-2026-11-09-2353). The human ruled on
2026-11-10, on #227, to merge this strict rule as is. It may be relaxed later,
for base ops and lifted ops together.

An op's attributes go with the op, to the side that its name picks. They are
generic terms, read by the op's own dialect, so the sum does not route them on
their own (ADR-2026-11-09-2306).

## Dialect sets and laws

`DialectSet d` lists the dialects whose names the words of `d` may use. The
core's set is empty. The set of `base ⊞ e` is the base's set and `e`'s name.
`LawfulDialectSet` says every op name, attribute word, valid type word and
kind of item names a dialect of the set. `LawfulDialectName base e` says that
`e` writes its own words under its name (ADR-2026-11-09-2306).

The sum's text is lawful exactly when every word goes to its own side
(`Dialect.sum.lawful_iff`). That holds when the base's set is lawful, `e`
writes its words under its name, and `e`'s name is new to the base
(`Dialect.sum.routes_of_names`). Then the round trip and well-formedness hold
for the sum with no new assumption. The sum of lawful dialects is lawful
(`Dialect.sum.lawfulPoison`) when `e` accepts every type the base accepts
(ADR-2026-11-09-2306). The same condition makes the sum lawful in its effects
when both sides are (ADR-2026-11-09-1541).

## Lifting an extension

An extension is written over the dialects it depends on. It joins any sum
that holds them by a lift: `e.lift dep ι μ`, in `lean/Fir/Sum/Lift.lean`, is
`e`, written over `dep`, with an inclusion `ι` of `dep`'s types in those of a
larger base `big` and a memory map `μ` from `dep`'s memories to `big`'s
(ADR-2026-11-09-2306).

An inclusion, `TyIncl A B` in `lean/Fir/Sum/Inclusion.lean`, says that the
types `A` are among the types `B`: a map `incl` of types, its projection
`proj`, and maps `up` and `down` of values that undo each other. The base of a
sum is included by `TyIncl.inl`, `TyIncl.over` includes the types of an
extension over a base in those of the same extension over a larger base, and
`TyIncl.comp` composes two inclusions. So a dialect held anywhere in a nested
sum is included. An inclusion is lawful when crossing it keeps poison and
refinement. Rejected: a type equation `⟦incl t⟧ = ⟦t⟧` in place of maps of
values. It would move values by casts, which every proof about poison would
have to undo.

The lift has `e`'s ops and rules, `big`'s rules and text for `big`'s types,
and `e`'s semantics on values moved across the inclusion. A lifted op sees
only the symbols whose types `e` can write, and is valid only where it can
write the function's result types. This is ADR-2026-11-09-2353 with `e` in
place of the base, within the human's ruling on it (ADR-2026-11-09-2306). So in
a function that returns a type of a dialect `e` does not depend on, no op of
`e` is valid. Rejected: a class saying which base an extension depends on, so
that instance search lifts it. The class would have to find `dep` from `big`
alone and would give a second instance beside `e`'s own over `dep`.

The lift's memories are `big`'s and `e`'s own. `liftMem μ` renames `e`'s name
for a memory of `dep` to `μ` of it and keeps `e`'s own, so `big ⊞ e.lift dep ι
μ` names each memory of `dep` once (`liftMem_ofBase`). Memory maps compose as
inclusions do: `ofBase` maps the base of a sum, composition reaches a base held
deeper, and `liftMem` maps an extension's memories over a smaller base into
the larger one. `lean/FirTest/Deps.lean` builds each. `μ` is the caller's
choice, as `ι` is, and nothing checks that it names each memory of `dep` as
`big` does; the right map for a base held in a sum is `ofBase`, composed
through each level. The type of a lift mentions `μ`, so every lift names its
memory map, even one whose extension declares no effects. Rejected: find the
memory map by instance search; it is recorded beside `ι` for the same reason
(ADR-2026-11-09-2306).

The sum of a larger base and the lift has lawful text when the base's text
and set are lawful, `e`'s name is new to the base, and the set of what `e`
depends on is in the base's set. The lift is lawful for poison when the base
and `e` are, the inclusion is lawful, and `e` accepts each type it depends on
whose inclusion the base accepts. Under the same conditions, the lift is
lawful in its effects when `e` is, with `e`'s effects renamed by the lift's
memory map (ADR-2026-11-09-1541). The round trip, well-formedness and the
poison obligations hold for the sum with no new assumption. So two extensions
of the core, written apart, combine in one lawful sum (ADR-2026-11-09-2306).

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

A dialect registers kinds of item through the one grammar, as it registers
ops, so a new kind needs no parser change (ADR-2026-11-09-1543). Rejected: a
fixed list of kinds of item in the core, which makes every new kind a core
change. The core registers none: `func` and `module` are its own terms
(ADR-2026-11-10-1510). Globals (#237) and external declarations (#239) are
to register their kinds through this hook.

- **The term.** `Item.dialect` holds a `DialectItem`: what the item
  production writes, its kind, symbol, parameters, results and attributes,
  with an empty body. Its attributes are the generic terms `Attr` of the
  abstract syntax. In `funk-ir` it is `Item::Dialect`.
- **Text.** `kind @sym(params) -> results attrs {` and, on the next line,
  `}` at the item's indentation. A kind is a word of a dialect, a word with a
  `.`, such as `toy.cell`. Every reader decodes such an item, whichever
  dialects it holds; a body that is not empty does not decode. Every other
  bare kind but `func` and `module` does not decode, so M0's texts and
  verdicts stay.
- **A rule per kind.** `DialectValidation` has `itemKindNames` and
  `validItem`, with defaults of none and `False`, and
  `DecidableDialectValidation` decides it. The rule sees the item through a
  `DialectView` and the symbols of its table, as `validFunc` does, so it is
  written once and holds in any sum. In Rust a dialect registers an
  `ItemKindSpec` with `Dialect::item_kind`; registration puts each kind under
  the dialect's prefix, as for ops, and rejects a kind of the core.
- **A valid item** (`DialectItem.Valid`): its kind is a word of a dialect that
  the dialect registers, its parameters have distinct names, its types are
  valid, its attributes can be written, and it obeys the rule. Its symbol is a
  symbol of its table. A kind that no dialect registers has no rule to break,
  so the check reports only that.
- **Sums and lifts.** The sum registers the base's kinds then `e`'s, and sends
  a kind that the base registers to the base's rule and any other to `e`'s,
  each through its own view (`Dialect.sum.validItem_ext`). The lift passes
  `e`'s kinds and rule through its view.
- **Dialect sets.** The kind's word, and each word of the item's types and
  attributes, join the words that the module's dialect set must name, so an
  item of a dialect outside its table's set is rejected on both sides.
- The round trip holds for every dialect with no new assumption. Nothing runs
  an item of a dialect's kind: `Module.funcs` and `funk build` read functions
  only. A reader keeps an item's attributes at any depth, so `fir-ref` walks
  them with loops, `writableLoop` and `dialectsLoop`, by the depth rule
  (ADR-2026-10-30-1450).

Rejected: a typed item instance per dialect, `d.Item` with a decoder and
round-trip laws, as for ops. It changes the `Dialect` structure that every
dialect builds, and nothing in M1 needs it: a global's data are attributes and
an external declaration is a signature.
Rejected: reject an unregistered kind when decoding, which needs a parser that
knows the dialects; validation rejects it, as it rejects an unregistered region
kind. An item with a body waits for a kind that needs one, with scoping rules
for its ops.

## Limits

Core ops carry core types only. A value of an extension's own type cannot
pass through a core `br`, `ret` or `call` (ADR-2026-11-09-2306). No core op
is valid in a function that returns such a value (ADR-2026-11-09-2353). Lifting
this needs the core's control ops to be generic in their types, which the
human's #227 ruling of 2026-11-10 leaves out for now.

The Lean test dialects, toy, use-once and probe, are extensions of the core
named `toy`. The bit dialect, named `bit`, makes a sum of three dialects with
the core and the toy dialect, each extension written over the core alone; it
has a name of its own, since two dialects of one name cannot share a sum
(ADR-2026-11-09-2306).

## A module's dialect set

A module names its dialects other than the core on its first line,
`dialects toy`. Its words must name only the core or those dialects, and it
may name only dialects of the reader's set (ADR-2026-11-10-1306). A module
that names none uses the core alone, so M0's texts stay valid
(ADR-2026-11-09-1543).

A nested module, a `module` item, names its own set on the first line of its
body. Its set is its own, not its parent's, so a host module can hold a
device module whose dialects the host does not use (ADR-2026-11-10-1510).
