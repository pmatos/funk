# A float type is written by its alias, or as float(e, m) when it has none

Status: accepted
Tier: direction; area: text-format

## Decision

- A format with an alias is written by it: `float<5,10>` is `f16`,
  `float<8,7>` is `bf16`, `float<8,23>` is `f32`, `float<11,52>` is `f64` and
  `float<15,112>` is `f128` (ADR-2026-11-09-1549).
- Every other format is written with the grammar's applied form,
  `float(e, m)`, with `e` and `m` in decimal, such as `float(5, 2)`.
- `float(e, m)` of a format with an alias does not decode, so `float(8, 23)`
  is a parse error and each format has one spelling. Neither does a negative
  number, any other argument list, an alias applied to arguments (`f16()`) or
  the bare word `float`.
- `float<e,m>` stays the notation of the spec's prose and the ADRs. It is not
  text.

## Why

fir has one canonical text, with one spelling for every construct
(ADR-2026-10-29-2014). The grammar writes a type as a word, or as a word
applied to attributes, `h(a, b)`, and has no angle brackets. So both parsers
read float types as they read any type, and only the core dialect's decoding
of types changes. The usual formats read as in LLVM and MLIR.

The human ruled on 2026-11-11: "Leave it as is. No need for angle brackets
then." The orchestrator recorded the ruling on #229.

## Rejected alternatives

- **`float<e,m>` in text.** It needs angle brackets in the grammar of both
  parsers and new round-trip proofs, for one type family.
- **Aliases as a second spelling of `float(e, m)`.** Two spellings break
  `print(parse(t)) == t` (ADR-2026-10-29-2014).
