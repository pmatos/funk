# A signature's markers are attributes after a type, which the type's dialect reads, and `...` ends the parameters

Status: accepted
Tier: direction; area: text-format

## Decision

- **Spelling.** A parameter or a result of a function carries attributes after
  its type, each after a space: `func @f(%c: i8 sext, %n: i32) -> i8 zext {`.
  The parameters may end in `...`, after a comma when a parameter comes
  before: `(%fmt: ptr, ...)`, or `(...)` alone. `...` is a token of its own.
- **Generic terms.** The grammar reads the attributes as generic terms, as it
  reads an op's. A `func` holds one list per parameter and per result
  (`Func.paramAttrs`, `Func.resultAttrs`), without the empty lists at the end,
  and whether it is variadic (`Func.variadic`).
- **The dialect decides.** Validation asks the dialect of each parameter's or
  result's type whether it allows the attributes: `validSigAttrs` in
  `DialectValidation`, which allows none by default, and
  `TypeSpec::sig_attrs` in `funk-ir`. The core allows one word, `sext` or
  `zext`, on an integer narrower than 32 bits (ADR-2026-11-09-1547). A
  `func` whose parameters end in `...` is not valid (ADR-2026-11-09-1548).
- **Only a func.** Another item whose parameter carries an attribute, whose
  parameters end in `...`, or whose result before a comma carries one does
  not decode. The attributes after the last result are that result's in a
  `func`, and the item's own in any other item, as before. A `func` with no
  results has no attributes.

## Why

The grammar has one production for every item, and G0 keeps the core's
words out of generic code (ADR-2026-11-03-0600). Markers as generic
attributes keep both: the parser, printer and round-trip proofs know no
marker, and only the core's rule names `sext` and `zext`. A dialect with its
own integer types can allow its own markers. External declarations reuse the
same signature (#239).

## Rejected alternatives

- **Markers as keywords of the grammar.** The generic parser would write core
  words, against G0, and every dialect would share the core's two markers.
- **Markers before the type, `%c: sext i8`.** An attribute after the type
  reads like an op's attributes after its name, and leaves the type where a
  reader of the text, such as the harness, expects it.
