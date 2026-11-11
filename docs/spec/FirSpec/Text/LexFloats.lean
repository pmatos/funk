import VersoManual
import Fir.Text.LexFloats
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on reading printed float literals, which
renders `Fir.Text.LexFloats` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Reading printed float literals: readable blocks" =>

:::moduleDocs (fingerprint := "5309215100885948372")
:::

:::readable Fir.Text.expChars (pin := Fir.Text.printInt) (fingerprint := "1203644042471034513")
*Definition: the characters of an exponent.* The exponent part of a
decimal float literal is `e` followed by the printed integer $`x`, when the
literal has the exponent $`x`, and nothing when it has none.
:::

:::readable Fir.Text.lexEnd_boundary Fir.Text.ne_of_boundary (pin := Fir.Text.lexEnd) (pin := Fir.Text.Boundary) (pin := Fir.Text.isHexDigit) (fingerprint := "3167677855465405217")
*Theorem: a literal may end at the end of a token.* When characters $`c`
are {ref "The-fir-specification--Text-format--Maximal-munch"}[at the end of a token],
the lexer's check that a number ends before $`c` passes.

*Theorem: what a token's end is not.* The first character of characters at
the end of a token is not `e`, `x`, `.`, a lowercase hexadecimal digit or
a decimal digit: each of those is a name character.
:::

:::readable Fir.Text.lexExponent_spells Fir.Text.notDigit_expChars (pin := Fir.Text.lexExponent) (pin := Fir.Text.expChars) (fingerprint := "6581133216072705537")
*Theorem: an exponent reads back.* For every exponent $`x`, or none, and
characters $`c` at the end of a token, the lexer reads the exponent part of
$`x` followed by $`c` as $`x`, and leaves $`c`. A negative exponent is
never $`-0` and its digits have no leading zero, as the printer writes it.

*Theorem: no digit follows a fraction.* The exponent part followed by
characters at the end of a token does not start with a decimal digit, so
the fraction before it ends where it starts.
:::

:::readable Fir.Text.takeWhile_digits' Fir.Text.lexFraction_spells (pin := Fir.Text.lexFraction) (pin := Fir.FloatLit.print) (fingerprint := "14056279493126812937")
*Theorem: digits are taken up to the first non-digit.* When the characters
$`\mathit{ds}` are all decimal digits and characters $`c` do not start
with one, the digits at the start of $`\mathit{ds}~c` are $`\mathit{ds}`,
and what follows them is $`c`.

*Theorem: a fraction reads back.* For a fraction of one or more decimal
digits $`f~\mathit{fs}`, an exponent $`x` or none, and characters $`c` at
the end of a token, the lexer reads $`f~\mathit{fs}`, the exponent part of
$`x` and $`c`, after the `.` of a literal with sign $`s` and whole part
$`w`, as the decimal literal with sign $`s`, whole part $`w`, fraction
$`f~\mathit{fs}` and exponent $`x`, and leaves $`c`.
:::

:::readable Fir.Text.whole_toDigits Fir.Text.lexFloat_dec (pin := Fir.Text.afterWhole) (pin := Fir.Text.wholeValue) (pin := Fir.Text.lexFloat) (fingerprint := "9972514557209548087")
*Theorem: the whole part of a printed number.* When the decimal digits of
the number $`n` are $`d~\mathit{ds}` and characters $`c` do not start with
a digit, the whole part of $`d~\mathit{ds}~c` is all of $`d~\mathit{ds}`:
$`c` follows it, and its value is $`n`. A whole part `0` is one digit,
since printed numbers have no leading zeros.

*Theorem: a decimal float literal reads back from its first digit.* With
the whole part $`n` printed as $`d~\mathit{ds}`, the lexer's reader of
float literals reads $`d~\mathit{ds}`, `.`, a fraction of one or more
digits, the exponent part of $`x` and characters $`c` at the end of a
token as the decimal literal of those parts, and leaves $`c`.
:::

:::readable Fir.Text.lexHex_spells Fir.Text.lexFloat_hex (pin := Fir.Text.lexHex) (pin := Fir.Text.lexFloat) (fingerprint := "2927607604069112200")
*Theorem: hexadecimal bits read back.* For one or more lowercase
hexadecimal digits $`\mathit{ds}` and characters $`c` at the end of a
token, the lexer reads $`\mathit{ds}~c` after `0x` as the literal of the
bits $`\mathit{ds}`, and leaves $`c`; and its reader of float literals
reads `0`, `x`, $`\mathit{ds}` and $`c` the same way.
:::

:::readable Fir.Text.readsToken_dec Fir.Text.readsToken_negDec Fir.Text.readsToken_hex (pin := Fir.Text.ReadsToken) (pin := Fir.Text.lexToken) (pin := Fir.Text.lexNumber) (fingerprint := "14244622392645874083")
*Theorems: each printed float literal is one token.* Followed by
characters $`c` at the end of a token, the lexer reads as one token, and
leaves $`c`:

* a decimal float literal with no `-`, from its first digit;
* a decimal float literal with `-`, from the `-`;
* hexadecimal bits, from the `0` of `0x`.

These are the cases of float literals in the proof that every printed token
reads back as itself.
:::
