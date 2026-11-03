# fir's numbers have MLIR's limits: widths up to 16,777,215, other numbers below 2^32

Status: accepted

## Context

S2 (ADR-2026-10-29-2007) says that the IR and the Lean interpreter accept
`iN` for any `N >= 1`. An implementation holds a width, a line or a
location reference in an integer of fixed width, so the decision memo on
#8 asked what bounds them. The human ruled on 2026-10-30: N3, in part 3
of the [rulings comment](https://github.com/pmatos/funk/issues/5#issuecomment-6506908304)
on #5. Lean and Rust follow that ruling, but no ADR recorded it, so
ADR-2026-10-29-2007 still reads as if every width were allowed.

## Decision

fir takes MLIR's limits (N3):

- An integer type `iN` has `1 <= N <= 16,777,215`, which is `2^24 - 1`:
  `maxWidth` in `lean/Fir/Core/Types.lean` and `MAX_WIDTH` in
  `crates/funk-ir/src/dialects/core/types.rs`. This narrows S2's "any
  `N >= 1`"; the rest of S2 stands.
- Every other number that gives the text its structure is below `2^32`: a
  location reference, a line and a column.
- An integer attribute has no bound of its own. The dialect that reads it
  bounds it, as a core constant must fit its type.
- A number out of its range is a parse error, located at the number.

## Consequences

- Every tool can hold a width in 24 bits, and a location reference, a line
  or a column in 32.
- `i16777216` and wider do not decode, in Lean and in Rust alike.
  `tests/fir/canonical/widths.fir` holds `i16777215`, and
  `tests/fir/reject/tokens.toml` rejects `i16777216` and a location
  reference, a line and a column of `2^32`.
- A frontend that needs a wider integer has to split it. MLIR has the same
  limit.
