import Fir.Core.Types
import Fir.Text.Lex

/-!
# Float constants in text

A float constant is written as a float literal (ADR-2026-11-11-1438), and
each value of `float<e,m>` has exactly one spelling. A finite value of a
format with decimal spellings, one with `2 ≤ e ≤ 15` and `1 ≤ m ≤ 112`,
no wider than `f128` in either field, is written as a decimal: `1.0`,
`0.5`, `-0.0`, `1.5e-7`. Every other value, NaNs and infinities among
them, and every value of a wider format, is written as `0x` and its bits
in exactly `⌈(1 + e + m) / 4⌉` lowercase hexadecimal digits:
`0x7fc00000` is the quiet NaN of `f32`.

Reading a decimal is exact. A decimal `d.ddd` with exponent `k` is the
rational number `±d · 10^k`, and it reads as that number rounded to the
format, to nearest with ties to even, by Lean's float model: the model's
`round` when the number is an integer, and its `div` of the digits by a
power of ten otherwise, then `pack`. A negative decimal that rounds to zero
reads as `-0`. Lean's own `ofScientific` is not used: it treats every
number below a bound as zero, and at a format with many mantissa bits and
few exponent bits that bound lies above the smallest subnormal, so it
reads such a decimal as zero.

The decimal of a value is the shortest one that reads back to its bits.
It is found by trying one significant digit, then two, and so on: with
`n` digits, the two multiples of `10^j` nearest the value, `j` chosen so
that the multiples have `n` digits, are the only candidates, since the
decimals that read back to the value form an interval around it. Of two
that read back, the nearer to the value is taken, and of two equally near,
the one whose last digit is even. The search stops after `m + 4` digits,
more than any value needs.

A decimal is laid out plainly when its value is `d.ddd · 10^E` with
`-4 ≤ E < 16`, as `1234.5` or `0.0001`, and otherwise as one digit, `.`,
the others and `e` and `E`, as `1.5e-7` or `1.0e16`. There is always a
digit after the `.`, and no other trailing zero.

A literal reads as a value only when it is that value's spelling. The
reader first takes the literal apart and reads it, then checks that the
value it gives is spelled so: any other spelling of the value, such as
`1.50`, `0x3f800000` or `1065353216` for `1.0` at `f32`, does not
decode. Before reading a decimal, it rejects one whose whole part has more
than 64 digits, whose fraction has more than 64, or whose exponent is
more than 9999 in magnitude: no spelling has them, and so reading never
computes a huge power of ten.
-/

namespace Fir.Core

open Float.Model Text

/-- Whether the finite values of `float<e,m>` are spelled in decimal: no
wider than `f128` in either field, and a format of Lean's model. -/
def hasDecimals (e m : Nat) : Bool := 2 ≤ e && e ≤ 15 && 1 ≤ m && m ≤ 112

/-- The format of Lean's model with `e` exponent bits and `m` explicit
mantissa bits. -/
def modelFormat (e m : Nat) (h : 2 ≤ e ∧ 0 < m) : Format :=
  { exponentBits := e, mantissaBitsWithoutImplicit := m, he := h.1, hm := h.2 }

theorem modelFormat_cond {e m : Nat} (h : hasDecimals e m = true) : 2 ≤ e ∧ 0 < m := by
  simp only [hasDecimals, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

/-- The bits that `-1^neg · d · 10^k` reads as at the format `f`: rounded
to nearest, ties to even, by Lean's model. -/
def readDecimal (f : Format) (neg : Bool) (d : Nat) (k : Int) : BitVec f.numBits :=
  let s : UnpackedFloat.Sign := if neg then .negative else .positive
  if hd : d = 0 then UnpackedFloat.pack f (.zero s)
  else if 0 ≤ k then UnpackedFloat.pack f (UnpackedFloat.round f s (d * 10 ^ k.toNat) 0)
  else
    UnpackedFloat.pack f (UnpackedFloat.div f (.finite s d 0 (Nat.pos_of_ne_zero hd))
      (.finite .positive (10 ^ (-k).toNat) 0 (Nat.pow_pos (by decide))))

/-- `ds` with zeros before it, to make `k` digits. -/
def padDigits (k : Nat) (ds : List Char) : List Char := List.replicate (k - ds.length) '0' ++ ds

/-- The literal of the bits `b` of a format of `w` bits as hexadecimal:
`0x` and `⌈w / 4⌉` digits. -/
def hexLit (w : Nat) (b : BitVec w) : FloatLit := .hex (padDigits ((w + 3) / 4) (Nat.toDigits 16 b.toNat))

/-- The decimal literal of `-1^neg · c · 10^j`, with `c > 0` and no
trailing zero, laid out plainly or with an exponent. -/
def decimalLayout (neg : Bool) (c : Nat) (j : Int) : FloatLit :=
  let len := (Nat.toDigits 10 c).length
  let e := j + len - 1
  if e < -4 ∨ 16 ≤ e then
    let rest := c % 10 ^ (len - 1)
    .dec neg (c / 10 ^ (len - 1)) (if len = 1 then ['0'] else padDigits (len - 1) (Nat.toDigits 10 rest))
      (some e)
  else if 0 ≤ j then .dec neg (c * 10 ^ j.toNat) ['0'] none
  else .dec neg (c / 10 ^ (-j).toNat) (padDigits (-j).toNat (Nat.toDigits 10 (c % 10 ^ (-j).toNat))) none

/-- `c · 10^j` with the trailing zeros of `c` moved into `j`, for `c > 0`.
`fuel` bounds the zeros it drops. -/
def dropZeros : Nat → Nat → Int → Nat × Int
  | 0, c, j => (c, j)
  | fuel + 1, c, j => if c % 10 = 0 ∧ c ≠ 0 then dropZeros fuel (c / 10) (j + 1) else (c, j)

/-- The exponent `E` of a positive rational `num / den`: `10^E ≤ num / den <
10^(E+1)`. It scales the rational by `10^K`, with `K` the number of digits
of `den`, so that it is at least 1, and counts the digits of the whole
part. -/
def decExponent (num den : Nat) : Int :=
  let k := (Nat.toDigits 10 den).length
  ((Nat.toDigits 10 (num * 10 ^ k / den)).length : Int) - 1 - k

/-- The two multiples of `10^j` around `num / den`: below, and above when
`num / den` is not one. -/
def around (num den : Nat) (j : Int) : List Nat :=
  let (a, b) := if 0 ≤ j then (num, den * 10 ^ j.toNat) else (num * 10 ^ (-j).toNat, den)
  if a % b = 0 then [a / b] else [a / b, a / b + 1]

/-- Of the candidates `cs` that read back to `b`, the nearer to
`num / den · 10^-j`, and of two equally near, the even one. -/
def pickNearest (num den : Nat) (j : Int) (ok : List Nat) : Option Nat :=
  match ok with
  | [c] => some c
  | [lo, hi] =>
    let (a, b) := if 0 ≤ j then (num, den * 10 ^ j.toNat) else (num * 10 ^ (-j).toNat, den)
    let below := a - lo * b
    let above := hi * b - a
    some (if below < above ∨ (below = above ∧ lo % 2 = 0) then lo else hi)
  | _ => none

/-- The shortest decimal `c · 10^j` that reads back to `b` at `f`, for the
positive value `num / den` with sign `neg`: it tries `n` significant
digits for `n` from `n₀` up, `fuel` times. -/
def shortestFrom (f : Format) (b : BitVec f.numBits) (neg : Bool) (num den : Nat) (top : Int) :
    Nat → Nat → Option (Nat × Int)
  | 0, _ => none
  | fuel + 1, n =>
    let j := top - n + 1
    let ok := (around num den j).filter fun c => readDecimal f neg c j == b
    match pickNearest num den j ok with
    | some c => some (c, j)
    | none => shortestFrom f b neg num den top fuel (n + 1)

/-- The decimal literal of the bits `b` of `float<e,m>`, when the format
has decimals and `b` is a zero or a finite value. -/
def decimalLit (e m : Nat) (b : BitVec (floatWidth e m)) : Option FloatLit :=
  if h : hasDecimals e m = true then
    let f := modelFormat e m (modelFormat_cond h)
    match UnpackedFloat.unpack f b with
    | .zero s => some (.dec (s == .negative) 0 ['0'] none)
    | .finite s mant ex _ =>
      let neg := s == .negative
      let num := mant * 2 ^ ex.toNat
      let den := 2 ^ (-ex).toNat
      (shortestFrom f b neg num den (decExponent num den) (m + 4) 1).map fun (c, j) =>
        let (c, j) := dropZeros (m + 40) c j
        decimalLayout neg c j
    | _ => none
  else none

/-- The bits that the literal `l` reads as at `float<e,m>`, before the
check that `l` is their spelling: hexadecimal bits of the format's width,
or a decimal within the reader's bounds, rounded by `readDecimal`. -/
def readFloatLit (e m : Nat) : FloatLit → Option (BitVec (floatWidth e m))
  | .hex ds =>
    if ds.length = (floatWidth e m + 3) / 4 ∧ hexValue ds < 2 ^ floatWidth e m then
      some (.ofNat _ (hexValue ds))
    else none
  | .dec neg whole frac exp =>
    if h : hasDecimals e m = true then
      let x := exp.getD 0
      if whole < 10 ^ 64 ∧ frac.length ≤ 64 ∧ x.natAbs ≤ 9999 then
        some (readDecimal (modelFormat e m (modelFormat_cond h)) neg
          (whole * 10 ^ frac.length + digitsValue frac) (x - frac.length))
      else none
    else none

/-- The one spelling of the bits `b` of `float<e,m>`: its decimal, when it
has one and it reads back to `b`, and otherwise its hexadecimal bits. -/
def floatLit (e m : Nat) (b : BitVec (floatWidth e m)) : FloatLit :=
  match decimalLit e m b with
  | some l => if readFloatLit e m l = some b then l else hexLit _ b
  | none => hexLit _ b

/-- The bits that the literal `l` spells at `float<e,m>`: those it reads
as, when it is their spelling. -/
def decodeFloatLit (e m : Nat) (l : FloatLit) : Option (BitVec (floatWidth e m)) :=
  match readFloatLit e m l with
  | some b => if floatLit e m b = l then some b else none
  | none => none

/-!
# Tests

The spellings below were computed apart from Lean, by
`scripts/harness/float_text.py`. `FirTest.FloatText` checks many more.
-/

/-- The spelling of the bits of `float<e,m>` whose value is `b`, as text:
how the tests below and `FirTest.FloatText` write a case. -/
def spellBits (e m : Nat) (b : Nat) : String := (floatLit e m (.ofNat _ b)).print

#guard spellBits 8 23 0x3f800000 == "1.0" && spellBits 8 23 0x3f000000 == "0.5" &&
  spellBits 8 23 0x80000000 == "-0.0" && spellBits 8 23 0x7fc00000 == "0x7fc00000" &&
  spellBits 8 23 0x3dcccccd == "0.1" && spellBits 8 23 0xff800000 == "0xff800000"
#guard spellBits 11 52 0x3e8421f5f40d8376 == "1.5e-7" && spellBits 11 52 0x4341c37937e08000 == "1.0e16"
#guard spellBits 5 10 0x3c00 == "1.0" && spellBits 15 112 1 == "6.0e-4966"
#guard (List.range 16).map (spellBits 2 1) ==
  ["0.0", "0.5", "1.0", "1.5", "2.0", "3.0", "0x6", "0x7", "-0.0", "-0.5", "-1.0", "-1.5", "-2.0",
   "-3.0", "0xe", "0xf"]
#guard spellBits 1 1 0 == "0x0" && spellBits 16 3 0 == "0x00000"
#guard decodeFloatLit 8 23 (.dec false 1 ['0'] none) == some 0x3f800000#32
#guard decodeFloatLit 8 23 (.dec false 1 ['0', '0'] none) == none
#guard decodeFloatLit 8 23 (.hex ['3', 'f', '8', '0', '0', '0', '0', '0']) == none
#guard decodeFloatLit 8 23 (.hex ['7', 'f', 'c', '0', '0', '0', '0', '0']) == some 0x7fc00000#32

end Fir.Core
