# A `module` item nests a symbol table with its own dialect set, written two spaces deeper

Status: accepted
Tier: direction; area: text-format

## Context

ADR-2026-11-09-1543 makes `module` a kind of item that the core registers,
so that nested and device modules exist, and says that a nested module
declares its own dialect set. ADR-2026-11-10-1306 spells a module's set as a
first line, `dialects toy, gpu`, and notes that a nested module can write the
same line at the start of its body of items. The grammar already writes every
item as `kind @sym(params) -> results attrs { body }`, and a body may hold
items (ADR-2026-10-29-2014). M0 rejects every kind but `func` when it decodes.
[#211](https://github.com/pmatos/funk/issues/211) builds the `module` kind.

## Decision

- **The item.** A `module` item has a symbol, a dialect set and a list of
  items, in the order the text writes them. In the spec it is
  `Item.module name dialects items`; in `funk-ir` it is `Item::Module`.
- **Header.** It is written `module @dev()`: the parentheses, which every
  item writes, and no parameters, results or attributes. A `module` with any
  of them, or with blocks in its body, does not decode.
- **Body.** Its body is its dialect set and its items, as a module's text is
  without its location table: `dialects gpu` and an empty line when the set
  names a dialect, then each item followed by an empty line. An empty body,
  `{ }`, is a module with no dialect and no items. A body of items may start
  with the dialect set, so the grammar is
  `body ::= '{' (('dialects' word (',' word)*)? item* | block*) '}'`. A
  `func` whose body holds a dialect set or items does not decode.
- **Layout.** The body is printed two spaces deeper than the `module` line,
  and its `}` at that line's indentation. An empty line has no spaces. A
  function at indentation `n` writes its header, its labels and its `}` at
  `n` and its ops at `n + 2`, so a top-level module prints as in M0, byte
  for byte. One location table, at the end of the text, serves every item at
  any depth.
- **Its own table.** A nested module is a symbol table of its own. Its symbol
  is a symbol of the table that holds it, and each symbol is unique in its
  table. An op refers by symbol only to an item of its own table: in M1 no op
  refers into a nested module or out of one.
- **Its own dialect set.** A nested module's set is its own, not its
  parent's: one that names no dialect uses the core alone, whatever its
  parent names. Each table's words are checked against its own set.
- **What runs.** `Module.funcs`, which the interpreter and `funk build` read,
  is the functions of the top-level table. A nested module's functions run
  only through what its own dialects define, such as a device's kernels
  (ADR-2026-11-09-1545).

## Alternatives

- **The dialect set as the item's attributes,** `module @dev() gpu {`. It
  needs no grammar change, but it spells the same set two ways, which the
  one canonical text forbids (ADR-2026-10-29-2014).
- **Nested items at the indentation of their module,** as a function's
  blocks are. Deep nests would be hard to read, and labels are the only
  reason blocks stay at the function's indentation.
- **A nested module that inherits its parent's set.** Then a host module
  could not hold a device module that does not use the host's dialects.

## Consequences

- Every M0 text parses, prints and validates unchanged.
- A device module of the second dialect (ADR-2026-11-09-1545) is a `module`
  item whose set names that dialect.
- Each step of the round-trip proofs gains a case for the `module` item, and
  `fir-ref` follows the spec in the same change.
- ADR-2026-11-09-1543 is refined: it names the `module` kind, and this ADR
  says how it is written and scoped.
