# funk-ir's registry routes each word by its dialect prefix and checks names and dependencies at registration

Status: accepted
Tier: direction; area: rust-ir-and-tools

## Context

ADR-2026-11-09-1543 decides that every dialect but the core writes its ops,
types and attributes as `name.word`, that a module's dialects combine as a sum
routed by that prefix, and that a dialect declares the dialects it depends on.
`funk-ir`'s registry (ADR-2026-10-30-1146) knows none of this. It finds an op
by its whole name, asks every dialect's `TypeSpec` about every type, and lets
a dialect named `fine` register the op `toy.a`. Stage 3 of
[#227](https://github.com/pmatos/funk/issues/227) builds the Rust side. The
dialect set of a module, in the text and in the verifier, is stage 4.

## Decision

- **A word names a dialect.** `word_dialect` in `ir/names.rs` gives the part of
  a word before its first `.`, or none for a bare word. `toy.a.b` names `toy`.
  A bare word is the core's: the dialect named `dialects::core::NAME`.
- **A dialect's name is its prefix.** `Registry::register` rejects a name that
  is not a word or that holds a `.` (`DialectNameNotAPrefix`).
- **Ops are written under their dialect's name.** Registration rejects an op
  whose name does not name its dialect (`OpOutsideDialect`): a core op must be
  bare, and an op of `toy` must be `toy.` and a word. So the one map from op
  names to ops routes each op to its own dialect.
- **Types go to the dialect their head word names.** `Registry::check_type`
  asks only that dialect's `TypeSpec`s. A type of an unregistered dialect, or
  one its dialect does not claim, does not decode. A `TypeSpec` decodes a
  family, such as the core's `iN`, so registration cannot list a dialect's
  types; routing is what keeps a dialect from claiming a type outside its
  prefix.
- **Dependencies.** `Dialect::depends_on` names a dialect whose types this
  one's ops may take. Registration rejects a dependency that is not yet
  registered (`MissingDependency`), so dependencies form no cycle.
  `Registry::dependencies` gives them back. The core depends on nothing, and
  the test dialects named `toy` depend on the core.
- A failed registration changes nothing, as before.

## Alternatives

- **Each `TypeSpec` lists the head words it decodes**, so registration could
  reject a type outside the prefix by name. The core's `iN` is an infinite
  family, so the core would need an exception, and routing already gives the
  guarantee.
- **A map per dialect, looked up after the prefix.** Since registration puts
  every op under its prefix, the flat map gives the same answer with one hash
  per op, on funk's hot path.

## Consequences

- An op or type of a dialect cannot be confused with another's, and no
  dialect can register a core word.
- An extension in Rust registers after the dialects it depends on.
- Nothing yet checks that a dialect's ops take only types of the dialects it
  depends on. A module's dialect set (stage 4 of #227) will use the
  dependencies.
- ADR-2026-10-30-1146 is refined: registration also checks a dialect's name,
  its ops' prefix and its dependencies.
