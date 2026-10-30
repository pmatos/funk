# A constant near its width's limit is compared with 2^(w-1) in decimal, squared by funk-ir's own NTT

Status: accepted

## Context

A core `const` must fit its type: `-2^(w-1) <= v < 2^(w-1)`. A width goes
up to 16,777,215 bits, so a constant can have about 5 million digits, and
`funk-ir` holds it as its decimal spelling. `Int::fits_signed` decides most
digit counts from bounds on log2(10). Near a width's limit, about 48 digit
counts at `i16777215`, the digits must be read. Converting them to binary
digit by digit is quadratic: about two minutes per constant, paid by the
parser and again by the verifier
([#37](https://github.com/pmatos/funk/issues/37)).

ADR-2026-10-30-1030 keeps `funk-ir` free of third-party crates, so the big
integers that check constants are its own code. The check must stay fast in
a debug build, which `cargo test` runs.

## Decision

- **Compare in decimal.** When the digit count does not decide,
  `fits_signed` computes `2^(w-1)` in decimal and compares it with the
  magnitude: digit count first, then digit by digit. Below fits; equal
  fits only when negative; above does not. The digits are never converted
  to binary.
- **Square and double.** `2^k` is built along the bits of `k` by squaring
  and doubling, in base-10^5 limbs (`crates/funk-ir/src/ir/int/decimal.rs`).
  The last squaring dominates, so the whole costs about two squarings of
  the result's size.
- **Square by an NTT over `2^64 - 2^32 + 1`**
  (`crates/funk-ir/src/ir/int/ntt.rs`). One prime, one forward and one
  inverse transform per squaring, no `unsafe`. With base 10^5, every
  coefficient of a square is below the prime for any `2^k` with
  `k < 2^32`, so every `u32` width is exact; an `assert!` guards the bound.
- **Tested against the quadratic code.** The NTT square is checked against
  the schoolbook product, `2^k` against `Nat::pow2(k).to_decimal()`, and
  `fits_signed` against the old binary conversion on random widths and
  values near each limit. A timed test at `i16777215` checks `2^16777214 - 1`,
  `2^16777214`, `-2^16777214` and `-(2^16777214 + 1)`, with the power of
  two checked by digit count, leading and trailing digits and residues.

## Alternatives

- **Divide-and-conquer conversion of the digits to binary.** It needs about
  log n full-size products, against about two squarings here.
- **Karatsuba instead of an NTT.** At half a million limbs it does about 50
  times as many operations, too slow for a test in a debug build.
- **A big-integer crate.** It would be the first dependency, for one
  comparison that under 200 lines of code cover.

## Consequences

- A constant in the band costs about a second in a debug build and about
  0.2 s in a release build, against minutes before. `funk verify` still
  decodes each op twice, so it pays this twice.
- `funk-ir` carries its own NTT. Its correctness rests on the tests above
  and on the coefficient bound, which a change of base must recheck.
- `Nat::from_decimal` stays quadratic; nothing in the check uses it any
  more.
