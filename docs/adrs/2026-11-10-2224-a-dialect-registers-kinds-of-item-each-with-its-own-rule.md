# A dialect registers kinds of item, each with its own rule, written by the one item production

Status: accepted
Tier: direction; area: semantics

## Context

ADR-2026-11-09-1543 decides that a dialect registers kinds of item through
the one grammar, as it registers ops, so a new kind needs no parser change,
and that the verifier rejects a kind of item from a dialect outside the
module's set. The core's kinds are `func` and `module`
(ADR-2026-11-10-1510). Until now an item of any other kind did not decode.
Stage 4 of [#211](https://github.com/pmatos/funk/issues/211) builds the
hook, which globals (#237) and external declarations (#239) build on.
ADR-2026-11-10-1941 does the same for region kinds.

## Decision

- **The term.** `Item.dialect` holds a `DialectItem`: what the item
  production writes, its kind, symbol, parameters, results and attributes,
  with an empty body. Its attributes are the generic terms `Attr`, which
  move from the text chapter to the abstract syntax. In `funk-ir` it is
  `Item::Dialect`.
- **Text.** `kind @sym(params) -> results attrs {` and, on the next line,
  `}` at the item's indentation. A kind is a word of a dialect: a word with
  a `.`. Every reader decodes such an item, whichever dialects it holds; a
  body that is not empty does not decode. Every other bare kind but `func`
  and `module` still does not decode, so M0's texts and verdicts stay.
- **A dialect registers kinds, each with a rule.** `DialectValidation`
  gains `itemKindNames` and `validItem`, with defaults of none and `False`,
  and `DecidableDialectValidation` decides it. The rule sees the item
  through a `DialectView` and the symbols of its table, as `validFunc`
  does, so it is written once and holds in any sum. In Rust a dialect
  registers an `ItemKindSpec` with `Dialect::item_kind`; registration puts
  each kind under the dialect's prefix, as for ops (ADR-2026-11-10-0042),
  and rejects a kind of the core.
- **A valid item** (`DialectItem.Valid`): its kind is a word of a dialect
  that the dialect registers, its parameters have distinct names, its
  types are valid, its attributes can be written, and it obeys the rule.
  Its symbol is a symbol of its table. A kind that no dialect registers has
  no rule to break, so the check reports only that.
- **Sums and lifts.** The sum `base ⊞ e` registers the base's kinds then
  `e`'s, and sends a kind that the base registers to the base's rule and
  any other to `e`'s, each through its own view. The lift passes `e`'s
  kinds and rule through its view. `LawfulDialectSet` and
  `LawfulDialectName` ask that kinds be words of the dialect's name, with
  defaults for a dialect that registers none, so a kind goes to the dialect
  that registers it (`Dialect.sum.validItem_ext`).
- **Dialect sets.** The kind's word, each word of the item's types and of
  its attributes join the words of ADR-2026-11-10-1306, so an item of a
  dialect outside its table's set is rejected on both sides.
- **The round trip** holds for every dialect with no new assumption:
  validity gives each fact the text needs.
- **What runs.** Nothing: `Module.funcs` and `funk build` read functions
  only.
- **Depth.** A reader keeps an item's attributes at any depth, so
  `fir-ref` walks them with loops, `writableLoop` and `dialectsLoop`, by
  the depth rule (ADR-2026-11-09-1941).

## Alternatives

- **A typed item instance per dialect,** `d.Item` with a decoder and
  round-trip laws, as for ops. It changes the `Dialect` structure that
  every dialect builds, adds text laws, and nothing in M1 needs it: a
  global's data are attributes and an external declaration is a signature.
- **Reject an unregistered kind when decoding.** The decoder would need
  the registered kinds, a new law tying them to the rule, and a parser
  that knows the dialects. Validation already rejects it, as it rejects an
  unregistered region kind.
- **An item with a body.** Blocks in an item of a dialect's kind need
  scoping rules for their ops. No kind in M1 has one.

## Consequences

- #237 and #239 register their kinds through this hook.
- Running an item of a dialect's kind, and a kind with a body, wait for a
  dialect that needs them.
- ADR-2026-11-09-1543 and ADR-2026-11-10-1306 are refined.
