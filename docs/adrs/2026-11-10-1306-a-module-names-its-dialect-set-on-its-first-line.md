# A module names its dialect set on a first line that starts with the word dialects

Status: accepted
Tier: direction; area: text-format

## Decision

- **Spelling.** A module's text may start with the word `dialects` and the
  names of its dialects, separated by `, `, then an empty line:
  `dialects toy, gpu`. Each name is a word. The core is in every module's set
  and is never named. A module that names no dialect writes no line, so every
  M0 text is unchanged. A nested module's body starts with its own set the
  same way (ADR-2026-11-10-1510).
- **Grammar.** `module ::= ('dialects' word (',' word)*)? item* locs`. The
  word `dialects` is no item's kind, as `locs` is not, and the lexer is
  unchanged.
- **Order.** The names are stored and printed in the order the text writes
  them. Nothing sorts or merges them.
- **Validity.** `Module.Valid` asks that each name be a word, named once. The
  rule of the set, `Module.InDialectSet`, asks that each name be a dialect
  that the reader holds, other than the core, and that every word of the
  module name the core or a dialect of its set: op names, attribute words,
  type words, region kinds (ADR-2026-11-10-1941) and item kinds
  (ADR-2026-11-09-1543), at any depth. The rule sits beside `Module.Valid`,
  not in it, since it reads words that the dialect's text gives. `funk verify`
  and `fir-ref validate` report both, and both read the shared cases of
  `tests/dialects/dialect-set.cases`.

## Why

ADR-2026-11-09-1543 decides that each module declares the dialects it uses and
that one declaring none uses the core alone, and leaves the spelling open. An
optional first line made of existing tokens keeps every M0 text byte for byte,
and needs no lexer change.

## Rejected alternatives

- **A `module` item that holds the items, with the set as its attribute.** It
  would change every text, and M0's texts must not change.
- **The set in parentheses, `dialects(toy, gpu)`.** It reads as an applied
  attribute, and the plain list is shorter.
- **Rejecting an unknown word at parse time.** A builder or a pass can make a
  module that no text wrote, so the rule must be validation's.
