# A source range is written `"f":2:3 to 2:14`, as MLIR writes it, with an exclusive end and columns in UTF-8 bytes

Status: accepted
Tier: direction; area: text-format

## Context

H8 (ADR-2026-10-29-2013) makes a source range one kind of location and
writes it `file:line:col-line:col`, the M0 epic's sketch. It leaves the
exact spelling to the spec (#8). The
[decision memo](https://github.com/pmatos/funk/issues/8#issuecomment-6510078680)
on #8 found three faults in the sketch, as its choice 16: the unit of a
column is unstated, an inclusive end cannot express an empty range, and
the `-` separator makes the lexer depend on context.

The human ruled on 2026-10-30: choice 16, in part 1 of the
[rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
on #5. The epic's
[comment on location ranges](https://github.com/pmatos/funk/issues/5#issuecomment-6520150283)
restates it. Lean and Rust follow that ruling, but no ADR recorded it, so
ADR-2026-10-29-2013 still shows the sketch.

## Decision

A source range follows choice 16:

- It is written as MLIR writes it: `"f":2:3 to 2:14`, the file as a
  string, the line and column of its start, the word `to`, then the line
  and column of its end.
- The end is exclusive: it is the position just after the range's last
  byte.
- Columns count UTF-8 bytes, from 1.
- Column 0 means that the column is unknown.

This replaces H8's sketch spelling only; the rest of H8 stands.

## Consequences

- A range whose end equals its start is empty, so an empty range can be
  written.
- The separator is the word `to`, not `-`, so the lexer reads a range
  without depending on context.
- A column does not depend on how a tool counts characters: it counts the
  bytes of the UTF-8 text.
- The spec states it in `lean/Fir/Syntax/Location.lean`, which also says
  that lines count from 1, and in `lean/Fir/Text/Grammar.lean`. The
  Lean printer (`lean/Fir/Text/Print.lean`) and `funk-ir`
  (`crates/funk-ir/src/text/print.rs`) both print it.
  `tests/fir/canonical/locations.fir` holds an empty range and a range
  with column 0.
- Lines and columns are below `2^32` (N3, ADR-2026-11-03-1000).
