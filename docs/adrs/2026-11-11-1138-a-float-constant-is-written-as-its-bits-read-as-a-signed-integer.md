# A float constant is written as its bits read as a signed integer

Status: accepted
Tier: direction; area: text-format

## Context

#229 adds constants of the float types `float<e,m>`
(ADR-2026-11-09-1549). A value of a float type is its raw bit pattern
(ADR-2026-11-11-0950), and when an op's IEEE result is a NaN, fir may
choose any NaN, so a NaN's payload and sign are part of the value. A
constant's spelling must therefore name every bit pattern of the format,
each NaN payload included, and each pattern must have one spelling
(ADR-2026-10-29-2014).

fir's lexer reads decimal integers only. It has no hexadecimal and no
float literal. `fir-ref run`, the corpus, the harness and the executables
that `funk build` writes spell arguments and results as constants of
their types.

## Decision

- A float constant is `const` with one attribute: the bits of the value,
  read as a two's-complement signed integer of `1 + e + m` bits, in
  decimal. This is how an integer constant of that width is written, `i1`
  aside: `%one: f32 = const 1065353216 @1` is `1.0`, and
  `%m: f32 = const -2147483648 @1` is `-0`.
- The number must lie in the signed range of `1 + e + m` bits, so each bit
  pattern has one spelling. `const 4294967295` at `f32` does not decode.
- A NaN is written like any other value: `2143289344` is the quiet NaN of
  `f32` with an empty payload, and `-4194304` the same NaN with its sign
  set.
- `fir-ref run`'s arguments and results, and the values of the built
  executables, use the same spelling. `poison` is an argument and a
  result of every float type, as of every integer type.

## Alternatives

- **Hexadecimal bits, as in LLVM's `0x3FF0000000000000`.** It reads better
  for a bit pattern, but needs a new token in both lexers and new lexer
  proofs, for one family of constants.
- **Decimal float literals, such as `1.5`.** Readable, but a literal names
  no NaN payload or sign, and a second spelling for the same bits would
  break `print(parse(t)) == t`.
- **The bits read as unsigned.** Equally exact, but a float of `N` bits
  would not be spelled as an `iN` of the same bits is, and the runtime of
  the built executables would need a parser of its own.

## Consequences

- No grammar change, and both parsers read a float constant as they read
  an integer one. The type of the result says which it is.
- The spelling is exact and round-trips every bit pattern. The sign of the
  number is the float's sign bit.
- The spelling does not show the number a float encodes. Tools and tests
  that want it decode the bits, as `scripts/harness/float_ref.py` does.
