# `fir-ref` writes an integer by splitting it at powers of ten, in a module that `FirRef.PrintAttr` imports

Status: accepted

## Context

A core constant of type `i16777215` has up to 5,050,445 decimal digits
(ADR-2026-11-03-1000). The spec writes an integer with
`Text.printInt i := toString i`, which calls core's `Int.repr`. That
divides the whole number by ten once per digit, so its time is quadratic
in the number of digits: `fir-ref fmt` took 2.5 seconds on a constant of
100,000 digits and did not finish one of five million in ten minutes
([#41](https://github.com/pmatos/funk/issues/41)). `fir-ref run` writes
the values it returns in the same way.

ADR-2026-10-30-1450 gives the way `fir-ref` runs a faster function: proved
equal to the spec's, and registered with `@[csimp]`. Its consequences note
that `printAttrs` inlines `printInt` and calls `Int.repr`, so a theorem on
`Nat.repr` or `toString` changes nothing, and a theorem on `printInt` must
be in scope where `printAttrs` is compiled. Every integer of a module or a
run result that `fir-ref` writes goes through `FirRef.printAttr`: `fmt`
through `FirRef.printModule`, `run` through `Attr.print` of the value's
constant.

## Decision

- **`FirRef.printDecimal` replaces `printInt`**
  ([`lean/FirRef/PrintInt.lean`](../../lean/FirRef/PrintInt.lean)). It
  splits a number at the largest of `10^18`, `10^36`, `10^72` and so on
  that is at most the number. It writes the quotient in the same way with
  the smaller powers. It then writes the remainder with its leading zeros,
  splitting a part of `2k` digits at `10^k`, down to parts of 18 digits.
  It computes each power once, as a square. Lean's `Nat` divides and
  multiplies with GMP, so the time is about `log2 (n / 18)` rounds of fast
  products for `n` digits.
- **It is proved equal and registered:** `@[csimp] theorem
  printInt_eq_printDecimal : @printInt = @printDecimal`. The proof shows
  that each step appends the digits that `Nat.toDigits 10` gives, by
  induction on the list of powers, and uses `propext`,
  `Classical.choice` and `Quot.sound` only.
- **`FirRef.PrintAttr` imports `FirRef.PrintInt`**, so `printAttrs` is
  compiled after the theorem and calls `printDecimal`.
  `FirRef.Fast` imports it too, as it imports every such module.
- **The text grows in one accumulator, appended to in place.** Each
  function takes it and passes it on, and an 18-digit part lists its
  digits with `digitsOnto`, from the last, and appends them with `++`.
  A first version pushed each digit with `String.push` onto the result of a
  recursive call that returned the accumulator itself at the end. Lean then
  passed the accumulator borrowed, so the first push of each part copied
  the whole text, which made the time quadratic again. The emitted C
  (`lean/.lake/build/ir/FirRef/PrintInt.c`) shows `lean_string_append`
  consuming the accumulator.
- **A check at the limit.** `scripts/check-fir-ref.sh test` has `fir-ref
  run` compute `2^16777214 - 1`, checks its digit count and last nine
  digits, then reprints a module with it and the type's minimum and runs
  it, each under a soft limit of 30 seconds of CPU time.

## Alternatives

- **A lemma on `Nat.repr` or `toString`.** Core's `Int.repr` is compiled
  already, so `printAttrs` would still call the slow code.
- **Keep each constant's spelling, as `funk-ir` does.** The spec's syntax
  holds an `Int`, and changing it is a change of the spec.
- **Leave it and document the limit**, option 2 of #41. A module that
  `funk fmt` prints in milliseconds would take `fir-ref` hours.

## Consequences

- `fir-ref fmt` reprints a module with the signed maximum and minimum of
  `i16777215` in about 4 seconds of CPU time, about 1.5 of them writing
  the digits, and `fir-ref run` returns both in about 5.
- Four spec functions that `fir-ref` runs still take time quadratic in an
  integer's digits. They meet a long integer only in a text that does not
  parse or decode, given to `fir-ref validate`, `fmt` or `run`:
  - `Tok.describe` (`lean/Fir/Text/Lex.lean:57`) names an integer in a
    parse error, through `fail` (`lean/Fir/Text/Read.lean:106`).
  - `lexAt` (`lean/Fir/Text/Lex.lean:219`) names a location reference
    that is out of range.
  - `readNat` (`lean/Fir/Text/ReadLocs.lean:17`) names a line or a column
    that is out of range.
  - `Ty.decode` (`lean/Fir/Core/Text.lean:158-159`) reads a type's whole
    width with `String.toNat?` and writes it back with `toString` before
    it compares it with the limit.

  They call `Int.repr`, `Nat.repr` or `String.toNat?` in code compiled in
  `lean/Fir/`, before any `FirRef` theorem, so `printInt_eq_printDecimal`
  reaches none of them.
- A new caller of `printInt` in `lean/FirRef/` reaches `printDecimal` only
  if its module imports `FirRef.PrintInt`, directly or through
  `FirRef.Fast`.
