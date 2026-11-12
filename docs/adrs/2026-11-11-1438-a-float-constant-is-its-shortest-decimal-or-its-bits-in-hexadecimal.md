# A float constant is its shortest decimal, or its bits in hexadecimal

Status: accepted
Tier: direction; area: text-format

## Context

An earlier ADR wrote a float constant as its bits read as a signed
integer, so `1.0` at `f32` was `const 1065353216`. The human ruled on #229
(2026-11-11) that float constants are written as LLVM writes them: a plain
decimal, such as `1.0` or `0.5`, when that decimal reads back to exactly
the same bits, and otherwise hexadecimal bits, such as `0x7fc00000` for
the quiet NaN of `f32`. Each value keeps exactly one printed spelling, and
`print(parse(t)) == t` holds (ADR-2026-10-29-2014).

A value of `float<e,m>` is its raw bit pattern (ADR-2026-11-11-0950), each
NaN payload and sign included. Formats run from `float<2,1>` to formats of
16,777,215 bits.

## Decision

- **Tokens.** The lexer reads a float literal as one token, kept as it is
  written. A decimal is an optional `-`, a whole part with no leading
  zeros, `.`, one or more digits, and an optional `e` and integer exponent
  with no leading zeros and never `-0`, as in `-1.5e-7`. Hexadecimal bits
  are `0x` and one or more lowercase hexadecimal digits. A whole number
  followed by `.` and a digit, or `0` followed by `x`, starts a float
  literal. The attribute `Attr.float` holds one, so any dialect may use
  float literals.
- **Formats with decimals.** A format has decimal spellings when
  `2 <= e <= 15` and `1 <= m <= 112`: no wider than `f128` in either field.
- **The canonical decimal.** A zero, or a finite value of a format with
  decimals, is written as the shortest decimal that reads back to its bits.
  Of two such decimals, the nearer to the value is taken; of two equally
  near, the one whose last digit is even. With `d.ddd · 10^E` its value,
  it is laid out plainly when `-4 <= E < 16`, as `1234.5`, `0.0001` or
  `-0.0`, and otherwise as one digit, `.`, the rest and `e` and `E`, as
  `1.5e-7` or `1.0e16`. There is always a digit after `.`, and no other
  trailing zero.
- **Hexadecimal bits.** Every other value, NaNs and infinities among them,
  and every value of a format without decimals, is written as `0x` and its
  bits in exactly `ceil((1 + e + m) / 4)` digits, leading zeros included:
  `0x7fc00000`, `0xff800000`, and `0x6` for the positive infinity of `float<2,1>`.
- **Reading.** A decimal reads as its exact value rounded to the format, to
  nearest with ties to even, by Lean's float model: its `round` when the
  value is an integer and its `div` of the digits by a power of ten
  otherwise, then `pack`. A negative decimal that rounds to zero reads as
  `-0`. Before reading, the reader rejects a decimal whose whole part or
  fraction has more than 64 digits, or whose exponent is more than 9999 in
  magnitude, so it never computes a huge power of ten.
- **One spelling.** A literal decodes as a constant only when it is the
  spelling of the bits it reads as. So `1.00`, `1.0e0`, `0x3f800000` and
  `1065353216` at `f32` do not decode, nor does `1.0e39`, which reads as an
  infinity, nor `0x7fc0000`, which has seven digits.
- **Runs.** `fir-ref run`'s arguments and results, and the corpus, spell a
  float the same way. A built executable reads and writes a float as its
  bits read as a signed integer, as before: that spelling is internal to
  the harness, which converts each float argument to it before a native
  run and each float result back, exactly (`scripts/harness/native_floats.py`).

It replaces that earlier ADR, now deleted (`INDEX.md`, Removed).

## Alternatives

- **The shortest decimal of at most six digits, as LLVM writes `double`.**
  It sends most `f32` and `f128` values to hexadecimal, and a cap of digits
  is no simpler to state than the shortest decimal.
- **Decimals at every format.** A value of a format with a wide exponent
  can need a decimal of millions of digits, and reading one a power of ten
  as large; the bound on formats keeps both small.
- **Hexadecimal for every value.** Exact, but not what the human ruled.

## Consequences

- Constants read as numbers: `const 1.0`, `const 0.1`, `const -0.0`.
- Both lexers, the generic attribute and its proofs gained a token, and
  the spec proves the laws of the core's text for float constants: the
  printer takes a decimal only when the reader reads it back, and the
  reader checks the spelling, so `print(parse(t)) == t` holds by
  construction.
- Lean's `ofScientific` is not used: it reads every value below a bound as
  zero, and at a format with many mantissa bits and few exponent bits, such
  as `float<2,30>`, that bound lies above the smallest subnormal.
- `scripts/harness/float_text.py` is the reference that the shared cases
  of `tests/dialects/float-text.cases` come from, for the Lean and Rust
  tests.
