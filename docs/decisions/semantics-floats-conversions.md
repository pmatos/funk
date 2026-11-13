# Current decisions: semantics, float conversions

This page continues [semantics-floats.md](semantics-floats.md). It says what
the ADRs and the human's rulings decide about the conversions of #241, between
a float and an integer and between two float formats, and what holds in the
spec and the tools today. It is the record: when this page and an ADR
disagree, the page wins, and the ADR is fixed or deleted (ADR-2026-11-09-1610).
ADR-2026-11-09-1549 holds the direction decision.

## The conversions

#241 adds the conversions of ADR-2026-11-09-1549 in four stages, as its stage
plan says: bit casts, then `fpext` and `fptrunc`, then integer to float, then
float to integer.

The human ruled both questions of #354 on 2026-11-12: float to integer
truncates toward zero, with no rounding attribute, and which op converts
between two formats. Each is recorded below, with its op.

`bitcast` reads the same bits as another type of the same width. From
`float<e,m>` it gives an `iN` with `N = 1 + e + m`, and from that `iN` it
gives a `float<e,m>`; the spec has one op instance for each direction,
`toBits e m` and `ofBits e m`, with one rule, `bitcastValue`, which keeps
every bit (`lean/Fir/Core/FloatBitcast.lean`).

- A value of a float type is its bit pattern, so the rule changes no bit. It
  reads no number: Lean's model takes no part, nothing rounds, and no NaN is
  chosen. A NaN's sign and payload come through as they are, both ways, and
  every bit pattern of `iN` is a float, a signalling NaN's included. This is
  IEEE 754's view of an encoding as its bits, and LLVM's `bitcast`.
- A poison operand gives poison, and a value gives a value. It is never UB,
  and it is pure.
- Its widths must match: an op whose integer has another width, or that
  casts between two floats or two integers, does not decode, so validation
  has no rule of its own for it. Rejected: bit casts between two float
  formats of one width, such as `f16` and `bf16`, which #241 does not ask
  for.

`sitofp` and `uitofp` convert an integer to a float (stage 3). Each takes one
value of `iN`, of any width, and gives one of `float<e,m>`, of any format; in
the spec they are `sitofp n e m` and `uitofp n e m`, with one rule,
`intToFloat` (`lean/Fir/Core/FloatOfInt.lean`).

- `sitofp` reads the operand's bits in two's complement and `uitofp` as
  unsigned, so the `i8` value with every bit set is `-1` to one and `255` to
  the other.
- The model's `UnpackedFloat.ofInt` takes the integer to a number, rounded to
  nearest, ties to even, and `UnpackedFloat.pack` writes its bits. So an
  integer the format holds is exact, a tie such as `2^24 + 1` at `f32` goes to
  the even neighbour, an integer at or past the largest finite value plus half an
  ulp is an infinity of its sign, as IEEE 754's overflow under rounding to
  nearest is, and zero is `+0`. This is IEEE 754's `convertFromInt` and LLVM's
  `sitofp` and `uitofp`.
- `ofInt` never gives a NaN, so at every valid format the result is one bit
  pattern and the rule chooses nothing (`intToFloat_valid`). Only at a format
  that validation rejects does it choose a NaN, as the arithmetic does, so
  that the rule is total.
- Each carries `round(rne)`, the one mode M1 has; #229's open question on
  rounding modes decides no other here. A poison operand gives poison. It is
  never UB, and it is pure.

Rejected: building the conversion from the arithmetic, such as the sum of the
integer's bits as powers of two, which rounds more than once; and a rule of
fir's own that rounds the integer itself, a second definition of rounding
beside the model's.

`fpext` and `fptrunc` convert a float to another format (stage 2). Each takes
one value of `float<e,m>` and gives one of `float<e',m'>`; in the spec they are
`fpext e m e' m'` and `fptrunc e m e' m'`, with one rule, `convertFloat`
(`lean/Fir/Core/FloatConvert.lean`).

- The human ruled on 2026-11-12 (#354): `fpext` applies only when the target
  has at least as many exponent bits and at least as many mantissa bits as the
  source, so it holds every value of the source and `fpext` never rounds.
  `fptrunc`, with `round(rne)`, rounds into a format that cannot hold every
  value of the source, and covers every other pair of two formats, `bf16` to
  `f16` and `f16` to `bf16` included. Every ordered pair of two formats takes
  exactly one of the two, a format to itself takes neither, and validation
  checks it, as it checks `zext` and `trunc`. Rejected: `fpext` wherever the
  target is wider, which would round from `f16` to `bf16`, and an op of its
  own for the pairs where neither format holds the other.
- Lean's model has no conversion, so the rule is built from its steps:
  `UnpackedFloat.unpack` reads the operand in the source format,
  `UnpackedFloat.round` rounds a finite number into the target, to nearest
  even, and `pack` writes it, an infinity of its sign past the largest finite
  value. A number below half the target's smallest subnormal is a zero of its
  sign, and a tie goes to the even neighbour, so `1 + 2^-24` from `f64` to
  `f32` is `1`. This is IEEE 754's `convertFormat`, and LLVM's `fpext` and
  `fptrunc` where LLVM has them: it has neither between `bf16` and `f16`,
  which have the same width. That `fpext` is exact at every pair it takes is
  tested, on the corpus and on `#guard`s, not proved.
- A zero and an infinity keep their sign. A NaN gives any NaN of the target
  (ADR-2026-11-09-1549), so its payload need not survive, as SSE's quieting
  and LLVM's rules allow. So the rule chooses only on a NaN, or at a format
  that validation rejects (`convertFloat_valid`). A poison operand gives
  poison. It is never UB, and it is pure.

Rejected: a rule of fir's own that rounds by shifting the mantissa, a second
definition of rounding beside the model's; and keeping a NaN's payload, which
the target may not hold and which no other float op keeps.

`fptosi` and `fptoui` convert a float to an integer (stage 4). Each takes one
value of `float<e,m>`, of any format, and gives one of `iN`, of any width; in
the spec they are `fptosi e m n` and `fptoui e m n`, with one rule,
`floatToInt` (`lean/Fir/Core/FloatToInt.lean`).

- The human ruled on 2026-11-12 (#354): both truncate toward zero, so `2.7`
  gives `2` and `-2.7` gives `-2`. This is IEEE 754's
  `convertToIntegerTowardZero` (§5.8), C's `(int)x`, Rust's `as` and LLVM's
  `fptosi` and `fptoui`. Truncation is what the ops mean, so neither carries
  a rounding attribute: `fptosi round(rne)` and `fptoui round(rtz)` do not
  decode. #229's question on rounding modes decides nothing here. Rejected:
  rounding to nearest even with `round(rne)`, as the conversions from
  integers do, which is not what C's and Rust's casts mean.
- `UnpackedFloat.unpack` reads the operand, and the model's
  `UnpackedFloat.roundToInt` cuts a finite number's fraction off toward zero.
  `fptosi` gives that integer when `iN` holds it read as signed, from
  `-2^(N-1)` to `2^(N-1) - 1`, as its bits in two's complement; `fptoui`
  when `iN` holds it read as unsigned, from `0` to `2^N - 1`. A zero of
  either sign gives `0`, and so does `-0.5`, which truncates to `0`, for both.
- An integer that `iN` does not hold, an infinity and a NaN give poison
  (#241), as LLVM's `fptosi` and `fptoui` do. So each may produce poison on a
  defined operand and declares `mayPoison`, as the shifts do. Rejected: a
  saturating conversion, as Rust's `as` and WebAssembly's `trunc_sat` are,
  which #241 does not ask for and which a later op can add.
- The rule chooses nothing, a NaN included, and is never UB. A poison
  operand gives poison, and so does a format that validation rejects, so
  that the rule is total.
