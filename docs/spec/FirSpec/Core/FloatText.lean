import VersoManual
import Fir.Core.FloatText
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on float constants in text, which
renders `Fir.Core.FloatText` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float constants in text: readable blocks" =>

:::moduleDocs (fingerprint := "6332588082455822586")
:::

:::readable Fir.Core.hasDecimals Fir.Core.modelFormat Fir.Core.modelFormat_cond (fingerprint := "10244866007434555026")
*Definition: the formats with decimals.* The finite values of
$`\mathsf{float}\langle e,m \rangle` are spelled in decimal when
$`2 \le e \le 15` and $`1 \le m \le 112`: no wider than `f128` in either
field (ADR-2026-11-11-1438). Such a format is also a format of Lean's
float model, which needs $`e \ge 2` and $`m > 0`, and
$`\mathrm{model}(e, m)` names it.
:::

:::readable Fir.Core.readDecimal (fingerprint := "12190726528162592661")
*Definition: reading a decimal.* $`\mathrm{readdec}_f(s, d, k)` is the
bits of the rational number $`(-1)^s \cdot d \cdot 10^k` rounded to the
format $`f`, to nearest with ties to even, by Lean's float model. A zero
$`d` gives the zero of sign $`s`. When $`k \ge 0` the number is the
integer $`d \cdot 10^k`, which the model's `round` rounds; otherwise the
model's `div` divides $`d` by $`10^{-k}`, rounding once. The model's
`pack` then gives the bits, so a negative number that rounds to zero gives
$`-0`, and one that rounds past the largest finite value gives an
infinity.
:::

:::readable Fir.Core.padDigits Fir.Core.hexLit (fingerprint := "7791790352555494329")
*Definition: hexadecimal bits.* $`\mathrm{pad}_k(\mathit{ds})` puts zeros
before the digits $`\mathit{ds}` to make $`k` of them, and leaves longer
digits as they are. $`\mathrm{hexlit}_w(b)` is the literal `0x` followed
by the lowercase hexadecimal digits of the bits $`b`, padded to exactly
$`\lceil w / 4 \rceil` digits: `0x7fc00000` at `f32`, `0x6` at
$`\mathsf{float}\langle 2,1 \rangle`.
:::

:::readable Fir.Core.decimalLayout (fingerprint := "334248779964634121")
*Definition: laying out a decimal.* For a sign $`s`, a positive integer
$`c` with no trailing zero and an integer $`j`, $`\mathrm{layout}(s, c,
j)` writes $`(-1)^s \cdot c \cdot 10^j`. With $`n` the number of digits
of $`c`, its value is $`d.ddd \cdot 10^E` with $`E = j + n - 1`:

* when $`E < -4` or $`E \ge 16`, it is the first digit of $`c`, `.`, the
  other digits, or `0` when there are none, and `e` and $`E`: `1.5e-7`,
  `1.0e16`;
* otherwise, when $`j \ge 0`, it is the integer $`c \cdot 10^j` and `.0`:
  `1500.0`;
* otherwise it is the digits of $`c` with a point $`-j` digits from the
  right, and zeros after the point to fill: `12.5`, `0.0001`.
:::

:::readable Fir.Core.dropZeros (fingerprint := "10387781642429851192")
*Definition: dropping trailing zeros.* $`\mathrm{dropzeros}(c, j)` writes
the same number $`c \cdot 10^j` with every trailing zero of $`c` moved into
the exponent: $`(1500, 0)` becomes $`(15, 2)`. A count bounds the zeros it
drops, so that it is a structural recursion; the spelling gives a count
larger than the digits of any candidate.
:::

:::readable Fir.Core.decExponent (fingerprint := "7826447772874225649")
*Definition: the decimal exponent of a rational.* For positive integers
$`\mathit{num}` and $`\mathit{den}`, $`\mathrm{decexp}(\mathit{num},
\mathit{den})` is the integer $`E` with
$`10^E \le \mathit{num} / \mathit{den} < 10^{E+1}`. With $`K` the number of
digits of $`\mathit{den}`, the rational times $`10^K` is at least 1, and
$`E` is the number of digits of its whole part, less one, less $`K`.
:::

:::readable Fir.Core.around Fir.Core.pickNearest (fingerprint := "2791600958952345411")
*Definition: the candidates at one length.* $`\mathrm{around}(\mathit{num},
\mathit{den}, j)` is the multiples $`c` of $`10^j`, written by $`c`, next
to $`x = \mathit{num} / \mathit{den}`: $`\lfloor x / 10^j \rfloor` alone
when it is exact, and otherwise it and the one above. Of the candidates
that read back, $`\mathrm{nearest}` takes the only one, or of two the one
nearer to $`x / 10^j`, and of two equally near the even one.
:::

:::readable Fir.Core.shortestFrom (fingerprint := "3038407445575817679")
*Definition: the shortest decimal that reads back.* For bits $`b` of the
format $`f` whose value is $`(-1)^s \cdot \mathit{num} / \mathit{den}`,
with decimal exponent $`E`, $`\mathrm{shortest}` tries $`n = 1, 2,
\dots` significant digits. With $`n` digits the multiples of $`10^j`, for
$`j = E - n + 1`, have $`n` digits, and only the two around the value can
read back: the decimals that read back to $`b` form an interval around its
value. It keeps those that read back to $`b` by $`\mathrm{readdec}`, picks
one by $`\mathrm{nearest}`, and stops at the first $`n` that has one. A
count bounds the search.
:::

:::readable Fir.Core.decimalLit (fingerprint := "8272231106591551293")
*Definition: the decimal of a float.* $`\mathrm{declit}_{e,m}(b)` is the
decimal literal of the bits $`b` of $`\mathsf{float}\langle e,m \rangle`,
when the format has decimals and $`b` is a zero or finite. A zero is
`0.0` or `-0.0`. A finite value, with mantissa $`\mathit{mant}` and
exponent $`x`, is $`\mathit{mant} \cdot 2^x`; the search tries up to
$`m + 4` digits, and its decimal, with trailing zeros dropped, is laid out
by $`\mathrm{layout}`. Infinities and NaNs have no decimal.
:::

:::readable Fir.Core.readFloatLit (pin := Fir.Text.hexValue) (pin := Fir.Text.digitsValue) (fingerprint := "3724862749958047350")
*Definition: reading a float literal.* $`\mathrm{readlit}_{e,m}(l)` is the
bits of $`\mathsf{float}\langle e,m \rangle` that the literal $`l` reads
as, before the check that it is their spelling:

* hexadecimal digits $`\mathit{ds}` read as the bits of their value, when
  there are exactly $`\lceil (1+e+m)/4 \rceil` of them and the value fits
  in $`1+e+m` bits;
* a decimal with sign $`s`, whole part $`w`, fraction digits
  $`f_1 \dots f_n` and exponent $`x`, $`0` when it has none, reads as
  $`\mathrm{readdec}(s, w \cdot 10^n + f, x - n)`, with $`f` the value of
  the fraction's digits, when the format has decimals, $`w < 10^{64}`,
  $`n \le 64` and $`|x| \le 9999`.

Every other literal reads as no bits. The bounds come before any power of
ten is computed, so reading never computes a huge one.
:::

:::readable Fir.Core.floatLit Fir.Core.decodeFloatLit (fingerprint := "12079729617817994871")
*Definition: the spelling of a float, and reading it back.*
$`\mathrm{floatlit}_{e,m}(b)` is the one spelling of the bits $`b`: its
decimal, when it has one and that decimal reads back as $`b`, and
otherwise its hexadecimal bits. $`\mathrm{decodelit}_{e,m}(l)` is the bits
$`b` that $`l` reads as, when $`\mathrm{floatlit}_{e,m}(b) = l`, and
nothing otherwise. So `1.0` at `f32` decodes, and `1.00`, `0x3f800000` and
`1.0e39`, which reads as an infinity spelled `0x7f800000`, do not.
:::

:::readable Fir.Core.spellBits (pin := Fir.Core.floatLit) (fingerprint := "9799827423055158480")
*Definition: a spelling for tests.* $`\mathrm{spellbits}(e, m, b)` is the
text of $`\mathrm{floatlit}_{e,m}` of the bits whose value is the natural
number $`b`. The tests of this section, and the shared cases that
`scripts/harness/float_text.py` computes apart from Lean, write a spelling
so: `f32`'s bits `0x3f800000` are `1.0`, and `0x7fc00000` are
`0x7fc00000`.
:::
