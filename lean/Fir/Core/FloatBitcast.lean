import Fir.Core.Values

/-!
# Bit casts

This section gives the bit casts their rule (ADR-2026-11-09-1549).
`bitcast` reads the bits of a value as another type of the same width:

* from `float<e,m>` to `iN`, with `N = 1 + e + m`, it gives the float's
  bits as an integer: its sign bit on top, then its `e` exponent bits,
  then its `m` mantissa bits. So `bitcast` of the `f32` value `1.0` to
  `i32` is `0x3f800000`, and of `-0.0` it is the signed minimum.
* from `iN` to `float<e,m>` it gives the float whose bits are the
  integer's. So `bitcast` of the `i32` value `0x7f800000` to `f32` is
  `+∞`.

A value of a float type is its bit pattern (ADR-2026-11-09-1549), so the
rule changes no bit. Lean's float model takes no part: the cast reads no
number, so it never rounds and never chooses a NaN, as the float
arithmetic does. A NaN's sign and payload come through as they are, both
ways, and every
bit pattern of `iN` is a float of the format, a signalling NaN's
included.

A bit cast is never UB. A poison operand gives poison
(ADR-2026-10-29-2006), and a value gives a value: no bit pattern makes
poison.

The text writes both directions `bitcast`, and the types say which one
it is: an op whose widths differ does not decode, so validation has no
rule of its own for it.
-/

namespace Fir.Core

/-- A bit cast: the operand's bits, unchanged, and poison for poison. -/
def bitcastValue : PoisonOr (BitVec w) → PoisonOr (BitVec w)
  | .value a => .value a
  | .poison => .poison

-- The bits come through both ways, a NaN's payload and sign among them.
#guard bitcastValue (.value (0x3f800000 : BitVec (floatWidth 8 23))) == .value 0x3f800000
#guard bitcastValue (.value (0xffc00001 : BitVec 32)) == .value 0xffc00001
#guard bitcastValue (.value (BitVec.intMin (floatWidth 11 52))) == .value (BitVec.intMin 64)
-- A poison operand gives poison.
#guard bitcastValue (.poison : PoisonOr (BitVec (floatWidth 5 10))) == .poison

end Fir.Core
