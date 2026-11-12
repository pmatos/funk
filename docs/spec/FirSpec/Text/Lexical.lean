import VersoManual
import Fir.Text.Lexical
import Fir.Text.Lex
import Fir.Text.ReadLocs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on tokens, which renders
`Fir.Text.Lexical` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Tokens: readable blocks" =>

:::moduleDocs (fingerprint := "14499131429193190193")
:::

:::readable Fir.Text.hex Fir.Text.formatChars Fir.Text.isEscaped Fir.Text.allowedOutsideStrings (pin := Fir.Text.lexFrom) (pin := Fir.Text.lexToken) (fingerprint := "6181810885127377459")
*Definition: the characters that a string escapes, and the characters that
a text may hold outside strings.* A character $`c` is _escaped_ when it is
one of these:

* a control character, Unicode's category Cc: U+0000 to U+001F, and
  U+007F to U+009F;
* a format character, Unicode's category Cf, as Unicode 16.0 lists them:
  U+00AD, U+0600 to U+0605, U+061C, U+06DD, U+070F, U+0890 to U+0891,
  U+08E2, U+180E, U+200B to U+200F, U+202A to U+202E, U+2060 to U+2064,
  U+2066 to U+206F, U+FEFF, U+FFF9 to U+FFFB, U+110BD, U+110CD, U+13430
  to U+1343F, U+1BCA0 to U+1BCA3, U+1D173 to U+1D17A, U+E0001, and
  U+E0020 to U+E007F, both ends of each range included;
* the line separator U+2028, or the paragraph separator U+2029.

The format characters include the bidirectional controls, such as U+202E,
and the byte-order mark U+FEFF. A string writes each escaped character as
an escape, defined in the next block, using $`\mathrm{hex}(n)`, the digits
of the number $`n` in lowercase hexadecimal with no leading zeros.

Outside strings, comments included, a text may hold the character $`c`
only when

$$`\begin{aligned} & c \text{ is the tab, or} \\ & c \text{ is the line feed, or} \\ & c \text{ is not escaped} \end{aligned}`

So a text holds no carriage return, no byte-order mark and no bidirectional
control, not even in a comment. `"` and `\` are not escaped, so a comment
may hold them. The
{ref "The-fir-specification--Text-format--The-parser"}[parser] rejects a
text that holds any other character outside strings, at that character.

This gives a text one kind of line end, and it keeps a text from showing a
reader an order of characters other than the one a parser reads, as the
Trojan Source attack does with bidirectional controls in comments.
:::

:::readable Fir.Text.escapeChar Fir.Text.quote (pin := Fir.Text.unicodeEscape) (pin := Fir.Text.lexEscape) (pin := Fir.Text.hex) (fingerprint := "475873319601185174")
*Definition: the one spelling of a string.* A string is written between
double quotes, and holds any Unicode text:

$$`\begin{array}{rcl} \mathit{string} & ::= & \texttt{"}~\mathit{part}^*~\texttt{"} \\ \mathit{part} & ::= & \mathit{strchar} \mid \mathit{escape} \\ \mathit{escape} & ::= & \texttt{\textbackslash\textbackslash} \mid \texttt{\textbackslash"} \mid \texttt{\textbackslash n} \mid \texttt{\textbackslash t} \\ & \mid & \texttt{\textbackslash u\{}~\mathit{xdigit}~\mathit{xdigit}^*~\texttt{\}} \\ \mathit{xdigit} & ::= & \texttt{0} \mid \dots \mid \texttt{9} \\ & \mid & \texttt{a} \mid \dots \mid \texttt{f} \end{array}`

Characters in typewriter type, such as $`\texttt{"}`, stand for
themselves. A $`\mathit{strchar}` is any character but $`\texttt{"}`,
$`\texttt{\textbackslash}` and the escaped characters of the previous
block.

Each character $`c` of the string has one spelling,
$`\mathrm{esc}(c)`:

$$`\mathrm{esc}(c) = \begin{cases} \texttt{\textbackslash"} & \text{if } c = \texttt{"} \\ \texttt{\textbackslash\textbackslash} & \text{if } c = \texttt{\textbackslash} \\ \texttt{\textbackslash n} & \text{if } c = \mathrm{LF} \\ \texttt{\textbackslash t} & \text{if } c = \mathrm{TAB} \\ \texttt{\textbackslash u\{}\,h\,\texttt{\}} & \text{else if escaped} \\ c & \text{otherwise} \end{cases}`

where $`\mathrm{LF}` is the line feed, $`\mathrm{TAB}` the tab, and
$`h = \mathrm{hex}(\mathrm{cp}(c))`: $`\mathrm{cp}(c)` is the code point
of $`c`, and $`\mathrm{hex}` gives its lowercase hexadecimal digits, as in
the previous block. The string $`s = c_1 \dots c_n` is
written

$$`\mathrm{quote}(s) = \texttt{"}\,\mathrm{esc}(c_1) \dots \mathrm{esc}(c_n)\,\texttt{"}`

No other character is escaped. The
{ref "The-fir-specification--Text-format--The-parser"}[parser] accepts an
escape only in this spelling: $`\texttt{\textbackslash u\{}h\texttt{\}}`
only for an escaped character other than the line feed and the tab, with no
leading zeros. So `\u{41}` for `A`, `\u{9}` for a tab and `\u{001}` are
errors, and each string has exactly one spelling, as the canonical text
needs.
:::

:::readable Fir.Text.printInt Fir.Text.printSymbol (pin := Fir.isName) (pin := Fir.isWord) (pin := Fir.isNameChar) (pin := Fir.isWordStart) (pin := Fir.isLetter) (pin := Fir.Location.limit) (pin := Fir.Text.lexAt) (pin := Fir.Text.lexDigits) (pin := Fir.Text.readNat) (fingerprint := "10414318569984400172")
*Definition: the tokens, and the one spelling of an integer and of a
symbol.* The tokens of a text are these:

$$`\begin{array}{rcl} \mathit{token} & ::= & \mathit{value} \mid \mathit{label} \mid \mathit{symbol} \\ & \mid & \mathit{locref} \mid \mathit{word} \mid \mathit{int} \\ & \mid & \mathit{float} \mid \mathit{string} \mid \mathit{punct} \\ \mathit{value} & ::= & \texttt{\%}~\mathit{name} \\ \mathit{label} & ::= & \texttt{\textasciicircum}~\mathit{name} \\ \mathit{symbol} & ::= & \texttt{@}~\mathit{word} \mid \texttt{@}~\mathit{string} \\ \mathit{locref} & ::= & \texttt{@}~\mathit{nat} \\ \mathit{nat} & ::= & \texttt{0} \mid \mathit{nz}~\mathit{digit}^* \\ \mathit{int} & ::= & \mathit{nat} \mid \texttt{-}~\mathit{nz}~\mathit{digit}^* \\ \mathit{nz} & ::= & \texttt{1} \mid \dots \mid \texttt{9} \\ \mathit{digit} & ::= & \texttt{0} \mid \mathit{nz} \\ \mathit{punct} & ::= & \texttt{(} \mid \texttt{)} \mid \texttt{\{} \mid \texttt{\}} \\ & \mid & \texttt{,} \mid \texttt{:} \mid \texttt{=} \mid \texttt{->} \end{array}`

$`\mathit{name}` and $`\mathit{word}` are the
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[names and words]
of the abstract syntax: one or more ASCII letters, digits, `_` and `.`, and
for a word a first character that is a letter or `_`. $`\mathit{nz}` is a
digit other than 0.

* A value is `%` and a name, so `%0` and `%acc.1` are values. A block label
  is a name after `^`.
* A symbol names a function or another global. It is written $`\mathrm{printsym}(s)`:

  $$`\begin{aligned} & \mathrm{printsym}(s) = \\ & \quad \begin{cases} \texttt{@}\,s & s \text{ a word} \\ \texttt{@}\,\mathrm{quote}(s) & \text{otherwise} \end{cases} \end{aligned}`

  so `@sum`, but `@"1"` and `@"_ZN3foo$LT$E"`. A name that is a word is
  never quoted, so each symbol has one spelling, and the parser rejects
  `@"sum"`.
* A location reference is `@` and a number below $`2^{32}`. So `@1` is
  always a location reference, and the symbol named `1` is written `@"1"`.
* A word is an op name, a type, a word attribute such as a flag, an item
  kind or a keyword. A word may contain `.`, which is kept for writing a
  dialect's name before the names of its ops; no word of the core dialect
  contains one.
* An integer is written in decimal with no leading zeros and no `+`, and
  with `-` when it is negative: $`\mathrm{printint}(i)`. `-0` is not an
  integer, and the only other token with `-` is `->`.

Numbers have limits, so that every implementation can hold them in integers
of a fixed width, as MLIR does (ADR-2026-10-29-2007). The numbers that give
the text its structure, a location reference and a line and a column of a
source range, are below $`2^{32}`. An integer of an attribute has no limit
of its own: it is a value of its dialect, which bounds it, as a
{ref "The-fir-specification--Text-format--The-core-dialect-in-text"}[core constant]
must fit its type. The parser rejects a number out of its range at the
number, and a number that runs into a name character, such as `007`,
`1.5x` or `1.e5`.
:::

:::readable Fir.Text.expText Fir.FloatLit.print (pin := Fir.FloatLit) (fingerprint := "869767723309194699")
*Definition: the spelling of a float literal.* A float literal is a token
of its own (ADR-2026-11-11-1438):

$$`\begin{array}{rcl} \mathit{float} & ::= & \texttt{-}^?~\mathit{nat}~\texttt{.}~\mathit{digit}~\mathit{digit}^*~\mathit{exp}^? \\ & \mid & \texttt{0x}~\mathit{hex}~\mathit{hex}^* \\ \mathit{exp} & ::= & \texttt{e}~\mathit{int} \\ \mathit{hex} & ::= & \mathit{digit} \mid \texttt{a} \mid \dots \mid \texttt{f} \end{array}`

A decimal $`\mathsf{dec}~s~w~f~x` is written `-` when $`s` is set, then
$`\mathrm{printint}(w)`, `.`, the digits $`f`, and `e` and
$`\mathrm{printint}(x)` when it has an exponent $`x`: `1.0`, `-0.5`,
`1.5e-7`. Hexadecimal bits $`\mathsf{hex}~\mathit{ds}` are written `0x`
and the digits $`\mathit{ds}`: `0x7fc00000`. The exponent, like every
integer, has no leading zeros and is never `-0`. The literal is kept as it
is written, leading zeros of its fraction and of its hexadecimal digits
included; the
{ref "The-fir-specification--Text-format--Float-constants-in-text"}[core dialect]
says which literals spell a value of a float type. A whole number followed
by `.` and a digit, or `0` followed by `x`, starts a float literal, so `1.`
and `1.e5` are errors, as is `0X7F`, whose `X` runs into the `0`.
:::
