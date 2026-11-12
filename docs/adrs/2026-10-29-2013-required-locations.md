# Every op has a required source location

Status: accepted
Tier: direction; area: text-format

## Decision

- Every op has a location field. The field always exists; `unknown` is a valid
  value. The `funk-ir` builder requires one, the verifier checks that every op
  has one, and every pass gives each op it creates a location.
- A location is `unknown` or one of these kinds: a source range, a name,
  `callsite(callee at caller)`, `fused(a, b)` or `derived(op)`.
- A source range is written as MLIR writes it, `"f":2:3 to 2:14`: the file as
  a string, the line and column of its start, the word `to`, then the line and
  column of its end. The end is exclusive, the position just after the range's
  last byte. Lines count from 1. Columns count UTF-8 bytes from 1, and column
  0 means that the column is unknown.
- Locations are erased before semantics: they never change what a program
  means. Parsers and printers keep them, and round trips preserve them.
- In text, each op carries a short `@N` reference, and a `locs { ... }` table
  ends the module, giving the location that each `@N` stands for.

## Why

Funk's diagnostics point at IR locations, and frontends map compiled code back
to their sources. A field that may be absent is easy to drop by accident in a
pass, and the loss shows up much later, if at all. The human chose this as H8
on 2026-10-29 (#5).

The M0 epic sketched a range as `file:line:col-line:col`. The decision memo on
#8 found three faults in it: the unit of a column was unstated, an inclusive
end cannot write an empty range, and the `-` separator makes the lexer depend
on context. The human ruled the spelling above on 2026-10-30 (choice 16 of the
rulings on #5). An exclusive end writes an empty range as end equal to start,
the word `to` lexes without context, and a byte column does not depend on how
a tool counts characters.

## Rejected alternatives

- **An optional location.** A pass drops it by accident, and nothing notices.
- **The sketch `file:line:col-line:col`**, with an inclusive end and a `-`
  separator. It cannot write an empty range, and the lexer would need context
  to read the `-`.
- **The location written in full on each op line.** Op lines would grow long;
  a short reference into one table keeps them short.
