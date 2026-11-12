# A float constant is its shortest decimal, or its bits in hexadecimal

Status: accepted
Tier: direction; area: text-format

## Decision

- **The token.** The lexer reads a float literal as one token, kept as it is
  written: a decimal such as `-1.5e-7`, or `0x` and lowercase hexadecimal
  digits. The generic attribute `Attr.float` holds one, so any dialect may use
  float literals.
- **Decimals.** A zero, or a finite value of a format no wider than `f128` in
  either field (`2 <= e <= 15`, `1 <= m <= 112`), is written as the shortest
  decimal that reads back to its bits: `const 1.0`, `0.1`, `-0.0`, `1.5e-7`.
  Of two shortest, the nearer wins, then the one with an even last digit.
- **Hexadecimal bits.** Every other value, NaNs and infinities among them,
  and every value of a wider format, zeros included, is `0x` and its bits in
  exactly `ceil((1 + e + m) / 4)` digits, as `0x7fc00000`.
- **Reading.** A decimal reads as its exact value rounded to the format, to
  nearest with ties to even, by Lean's float model.
- **One spelling.** A literal decodes only when it is the spelling of the bits
  it reads as, so `1.00`, `0x3f800000` and `1065353216` at `f32` do not
  decode.
- **Runs.** `fir-ref run` and the corpus spell float arguments and results the
  same way. A built executable keeps its bits read as a signed integer, which
  the harness converts exactly.

`docs/decisions/text-format.md` holds the layout of a decimal and the
reader's bounds.

## Why

A value of `float<e,m>` is its raw bit pattern, each NaN payload and sign
included (ADR-2026-11-11-0950). Each value keeps exactly one printed spelling,
so `print(parse(t)) == t` holds (ADR-2026-10-29-2014), and constants read as
numbers. The human ruled on 2026-11-11: "Decimal float, hex fallback", as
LLVM writes them; the orchestrator recorded the ruling on #229. The shortest
decimal, the tie rules and the bound on formats are the agent's choices that
implement the ruling.

## Rejected alternatives

- **The bits read as a signed integer**, `const 1065353216` for `f32` `1.0`.
  The first spelling, replaced by the human's ruling.
- **The shortest decimal of at most six digits, as LLVM writes `double`.** It
  sends most `f32` and `f128` values to hexadecimal, and a cap is no simpler
  to state.
- **Decimals at every format.** A wide exponent can need a decimal of
  millions of digits, and reading one a power of ten as large.
- **Hexadecimal for every value.** Exact, but not what the human ruled.
