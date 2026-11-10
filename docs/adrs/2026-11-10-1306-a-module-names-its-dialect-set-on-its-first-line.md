# A module names its dialect set on a first line that starts with the word dialects

Status: accepted
Tier: direction; area: text-format

## Context

ADR-2026-11-09-1543 decides that each module declares the dialects it uses,
that the verifier rejects any op, type, attribute or kind of item from a
dialect outside that set, and that a module that declares none uses the core
alone, so M0's texts stay valid. It leaves the spelling open. Stage 4 of
[#227](https://github.com/pmatos/funk/issues/227) builds it on both sides:
the spec's sum gives each dialect a set of names (ADR-2026-11-09-2306), and
funk-ir's registry knows its dialects by name (ADR-2026-11-10-0042).

## Decision

- **Spelling.** A module's text may start with the word `dialects` and the
  names of its dialects, separated by `, `, then an empty line:
  `dialects toy, gpu`. Each name is a word. The core is in every module's
  set and is never named. A module that names no dialect writes no line, so
  every M0 text is unchanged, byte for byte.
- **Grammar.** `module ::= ('dialects' word (',' word)*)? item* locs`. The
  word `dialects` is no item's kind, as `locs` is not. The line uses only
  existing tokens, so the lexer is unchanged.
- **Order.** The names are stored and printed in the order the text writes
  them. Nothing sorts or merges them.
- **Validity.** `Module.Valid` asks that each name be a word, named once. The
  rule of the set, `Module.InDialectSet` in
  [`lean/Fir/Validation/DialectSet.lean`](../../lean/Fir/Validation/DialectSet.lean),
  asks that each name be a dialect that the reader holds, other than the
  core (`names d` in Lean, a registered dialect in Rust), and that every word
  of the module name the core or a dialect of its set: each op's name, each
  word of its attributes, and each word of each type that a function states,
  at any depth.
- **Where the rule lives.** It reads words, which the dialect's text gives,
  so it sits beside `Module.Valid`, not in it. The theorems about valid
  modules need no text. `funk verify` and `fir-ref validate` report both:
  the problems of `Module.problems`, then those of `Module.setProblems`.
- **Reports.** A function that writes a word outside the set gets one
  problem, naming the first such dialect in the order of `Func.wordDialects`:
  the types the function states, then each op's name and attributes.
- **Shared cases.** `tests/dialects/dialect-set.cases` holds must-accept and
  must-reject cases that both validators read.

## Alternatives

- **A `module` item that holds the items, with the set as its attribute.**
  It would change every text, which the ruling forbids for M0's texts.
- **The set as a list in parentheses, `dialects(toy, gpu)`.** It reads as an
  applied attribute, and the plain list is shorter.
- **Reject the unknown word at parse time.** A builder or a pass can make a
  module that no text wrote, so the rule must be validation's.

## Consequences

- A nested module (#211) can write the same line at the start of its body
  of items.
- A dialect's dependencies (ADR-2026-11-10-0042) do not yet constrain the
  set: a module that names `toy` need not name what `toy` depends on beyond
  the core. That waits for dependencies in Lean (stage 2 of #227).
- A kind of item is not yet a word of a dialect: every item is a core
  `func`. When dialects register kinds of item, their kind words join the
  rule.
- ADR-2026-11-09-2306 is refined: a module now declares its dialect set in
  the text, and both validators check its words against it.
