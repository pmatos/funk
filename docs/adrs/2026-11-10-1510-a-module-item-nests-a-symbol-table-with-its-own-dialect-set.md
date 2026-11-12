# A `module` item nests a symbol table with its own dialect set, written two spaces deeper

Status: accepted
Tier: direction; area: text-format

## Decision

- **The item.** A `module` item has a symbol, a dialect set and a list of
  items, in the order the text writes them: `Item.module name dialects items`
  in the spec, `Item::Module` in `funk-ir`.
- **Header.** It is written `module @dev()`: the parentheses that every item
  writes, and no parameters, results or attributes.
- **Body.** Its body is a module's text without the location table: the
  dialect set and an empty line when it names a dialect
  (ADR-2026-11-10-1306), then each item followed by an empty line. `{ }` is a
  module with no dialect and no items. The grammar is
  `body ::= '{' (('dialects' word (',' word)*)? item* | block*) '}'`. A
  `module` with a header or with blocks, and a `func` whose body holds a
  dialect set or items, do not decode.
- **Layout.** The body is printed two spaces deeper than the `module` line,
  and its `}` at that line's indentation. An empty line has no spaces. A
  function at indentation `n` writes its header, labels and `}` at `n` and its
  ops at `n + 2`, so a top-level module prints as in M0. One location table,
  at the end of the text, serves every item at any depth.
- **Its own table and set.** A nested module is a symbol table of its own,
  and an op refers by symbol only to an item of its own table. Its dialect set
  is its own: one that names no dialect uses the core alone, whatever its
  parent names.
- **What runs.** `Module.funcs` is the functions of the top-level table. A
  nested module's functions run only through what its own dialects define,
  such as a device's kernels (ADR-2026-11-09-1545).

## Why

ADR-2026-11-09-1543 makes `module` a kind of item that the core registers, so
that nested and device modules exist, each with its own dialect set. The
grammar already writes every item as `kind @sym(params) -> results attrs {
body }`, so the item needs only a body of items. Every M0 text parses, prints
and validates unchanged.

## Rejected alternatives

- **The set as the item's attributes,** `module @dev() gpu {`. It spells the
  same set two ways, which the one canonical text forbids
  (ADR-2026-10-29-2014).
- **Nested items at their module's indentation,** as a function's blocks
  are. Deep nests would be hard to read; labels are the only reason blocks
  stay at the function's indentation.
- **A set inherited from the parent.** A host module could not then hold a
  device module that does not use the host's dialects.
