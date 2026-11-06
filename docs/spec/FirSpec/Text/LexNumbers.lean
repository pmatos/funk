import VersoManual
import Fir.Text.LexNumbers
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on digits and their values, which
renders `Fir.Text.LexNumbers` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Digits and their values: readable blocks" =>

:::readable Fir.Text.digitsValue_eq_ofDigitChars (pin := Fir.Text.digitsValue) (pin := Nat.ofDigitChars) (fingerprint := "7578560943843579309")
*Theorem: reading digits in two halves gives their value read from left to
right.* For every list of characters $`d_1 \dots d_k`, the value that the
{ref "The-fir-specification--Text-format--The-parser"}[lexer] gives
decimal digits, $`\mathrm{val}_{10}(d_1 \dots d_k)`, is the value read from the
left, one digit at a time:

$$`\begin{aligned} & \mathrm{val}_{10}(d_1 \dots d_k) = n_k, \quad \text{where } n_0 = 0 \\ & \text{and } n_j = 10 \cdot n_{j-1} + v(d_j) \end{aligned}`

Here $`v(c)` is the code point of $`c` less that of `0`, or 0 when $`c`
comes before `0`, so $`v` gives each digit its value. The lexer reads up
to 64 digits this way, and a longer number as two halves, the first with
the extra digit when $`k` is odd, whose values it joins as
$`\mathrm{val}_{10}(\mathit{first}) \cdot 10^{h} + \mathrm{val}_{10}(\mathit{second})`
for a second half of $`h` digits. The halves keep a constant of millions
of digits fast to read; this theorem says that they change no value.
:::

:::readable Fir.Text.digitsValue_toDigits (pin := Nat.toDigits) (pin := Fir.Text.digitsValue) (fingerprint := "11066089495097601701")
*Theorem: the digits of a number read back as the number.* For every
natural number $`n`, with $`\mathrm{val}_{10}` the
{ref "The-fir-specification--Text-format--The-parser"}[lexer's] reading of
decimal digits, let $`\mathrm{digits}_{10}(n)` be its decimal digits,
most significant first, with no leading zero (one `0` for zero). Then

$$`\mathrm{val}_{10}(\mathrm{digits}_{10}(n)) = n`

The printer writes every integer, line, column and location reference
with these digits.
:::

:::readable Fir.Text.hexDigitValue Fir.Text.hexValue_append (pin := Fir.Text.hexValue) (fingerprint := "4000557157533766303")
*Definition and theorem: the value of a hexadecimal digit, and one digit
more.* The value $`h(c)` of a hexadecimal digit $`c` is the code point of
$`c` less that of `0` when $`c` is a decimal digit, and otherwise its code
point less that of `a`, or 0 when $`c` comes before `a`, plus 10. The value $`\mathrm{val}_{16}(l)` that the lexer gives the
hexadecimal digits $`l` of an escape reads them from the left in base 16.
For every list of characters $`l` and character $`c`:

$$`\mathrm{val}_{16}(l~c) = 16 \cdot \mathrm{val}_{16}(l) + h(c)`

The next proofs read a number's digits from its last.
:::

:::readable Fir.Text.digitChar_hex Fir.Text.digitChar_ne_zero (pin := Nat.digitChar) (pin := Fir.Text.isHexDigit) (fingerprint := "4554902301655242862")
*Theorems: each digit below 16 is a lowercase hexadecimal digit, and `0`
only for zero.* Let $`\mathrm{char}(k)` be the character of the digit
$`k`: `0` to `9` for 0 to 9, and `a` to `f` for 10 to 15. For every
$`k < 16`, $`\mathrm{char}(k)` is a decimal digit or one of `a` to `f`,
and $`h(\mathrm{char}(k)) = k`. For every $`k` with $`0 < k < 16`,
$`\mathrm{char}(k)` is not `0`. The proofs below rest on these two facts
for the last digit of a number.
:::

:::readable Fir.Text.hexValue_toDigits (pin := Nat.toDigits) (pin := Fir.Text.hexValue) (fingerprint := "13645665449076592793")
*Theorem: the hexadecimal digits of a number read back as the number.* For
every natural number $`n`, with $`\mathrm{digits}_{16}(n)` its lowercase
hexadecimal digits, most significant first, with no leading zero:

$$`\mathrm{val}_{16}(\mathrm{digits}_{16}(n)) = n`

The printer writes the code point of an escaped character in a string with
these digits, as `\u{h}`.
:::

:::readable Fir.Text.mem_toDigits Fir.Text.isHexDigit_of_mem_toDigits (pin := Nat.toDigits) (pin := Nat.digitChar) (pin := Fir.Text.isHexDigit) (fingerprint := "11634978082827501699")
*Theorems: the digits of a number are digits.* For every base $`b > 1` and
every natural number $`n`, each character of $`\mathrm{digits}_b(n)` is
$`\mathrm{char}(k)` for some $`k < b`. So, for every $`n`, each character
of $`\mathrm{digits}_{16}(n)` is a lowercase hexadecimal digit, and the
lexer, which reads an escape's digits up to the first other character,
reads them all.
:::

:::readable Fir.Text.head_toDigits_ne_zero (pin := Nat.toDigits) (fingerprint := "11236894394820365253")
*Theorem: a number above zero has no leading zero.* For every base $`b`
with $`1 < b \le 16` and every natural number $`n > 0`, the first
character of $`\mathrm{digits}_b(n)` is not `0`. The lexer rejects a
number, and a `\u{h}` escape, with a leading zero, so this is what lets it
accept the printer's digits.
:::
