import VersoManual
import Fir.Text.LexStrings
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on escapes and quoted symbols, which
renders `Fir.Text.LexStrings` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Escapes and quoted symbols: readable blocks" =>

:::moduleDocs (fingerprint := "14293073654072783962")
:::

:::readable Fir.Text.unicodeEscape_toDigits (pin := Fir.Text.unicodeEscape) (pin := Nat.toDigits) (fingerprint := "15463218578782466095")
*Theorem: the printer's `\u{…}` escape reads back as its character.* Let
$`c` be a character that a string
{ref "The-fir-specification--Text-format--Tokens"}[escapes], other than the
line feed and the tab. At every position, the lexer's reader of a `\u{…}`
escape, given the lowercase hexadecimal digits of the code point of $`c`
with no leading zero, gives $`c`. It checks that the digits have no
leading zero and stand for a character that must be escaped this way; the
printer's digits pass both checks.
:::

:::readable Fir.Text.escapeChar_quote Fir.Text.escapeChar_backslash Fir.Text.escapeChar_lf Fir.Text.escapeChar_tab Fir.Text.escapeChar_unicode Fir.Text.escapeChar_self (pin := Fir.Text.escapeChar) (pin := Nat.toDigits) (fingerprint := "8288077872388925399")
*Theorems: how one character of a string is spelled.* Inside a string, the
printer spells:

* `"` as `\"`, `\` as `\\`, a line feed as `\n` and a tab as `\t`;
* any other character $`c` that a string escapes as `\u{`, then the
  lowercase hexadecimal digits of its code point, then `}`;
* any other character as itself.

The proofs below take the spelling of each character apart case by case
with these.
:::

:::readable Fir.Text.lexStringFrom_escapeChar (pin := Fir.Text.lexStringFrom) (pin := Fir.Text.lexEscape) (fingerprint := "914042878758268952")
*Theorem: the spelling of one character reads back as the character.* The
lexer reads the characters of a string in a loop that keeps the
characters read so far and works on what is left of the text after the
opening quote. For every character $`c` and characters $`r`, at every
position and with any characters read so far, reading the spelling of
$`c` followed by $`r` comes to the same as reading $`r` from some
position, with $`c` added to the characters read. The loop reads an escape
in one turn, from its backslash.
:::

:::readable Fir.Text.lexStringFrom_quote (pin := Fir.Text.lexStringFrom) (fingerprint := "11413120460232138874")
*Theorem: the spellings of the characters of a string, then a quote, read
back as the string.* For all characters $`s = s_1 \dots s_n` and $`c`, at
every position and with any characters $`a` read so far: when what is left
is the spellings of $`s_1, \dots, s_n`, then `"`, then $`c`, the loop gives
the string $`a~s` and leaves $`c`.
:::

:::readable Fir.Text.toList_quote (pin := Fir.Text.quote) (fingerprint := "15777555760131986541")
*Lemma: the characters of a quoted string.* A string quoted by the printer
is `"`, the spelling of each of its characters, and `"`. It unfolds the
printer's quoting for the proofs below.
:::

:::readable Fir.Text.lexString_quote (pin := Fir.Text.lexString) (fingerprint := "17476162493406468519")
*Theorem: a string reads back as itself, up to its closing quote.* For every
string $`s`, characters $`c` and positions: the lexer's reader of a string,
given the spellings of the characters of $`s`, then `"`, then $`c`, gives
$`s` and leaves $`c`.
:::

:::readable Fir.Text.readsToken_str (pin := Fir.Text.lexToken) (fingerprint := "18402106761232902883")
*Theorem: a string token is read.* For every
{ref "The-fir-specification--Text-format--Tokens"}[string] $`s` and characters
$`c`, the token that starts with `"`, followed by the spellings of the
characters of $`s`, `"` and $`c`, is read as $`\mathsf{str}~s`, leaving
$`c`. Unlike a name, a string ends at its closing quote, so $`c` may be
anything.
:::

:::readable Fir.Text.readsToken_quotedSym Fir.Text.readsToken_wordSym (pin := Fir.Text.lexToken) (pin := Fir.Text.lexAt) (fingerprint := "15992180265448534080")
*Theorems: a symbol is read, quoted or bare.* For every string $`s` that is
not a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[word],
and characters $`c`: `@`, then $`s` quoted, then $`c` is read as
$`\mathsf{sym}~s`, leaving $`c`. For every character $`a` that starts a
word, characters $`l` that are each a name character, and $`c`
{ref "The-fir-specification--Text-format--Maximal-munch"}[at the end of a token], $`\mathrm{boundary}(c)`: `@`, then $`a~l`, then $`c` is read as
$`\mathsf{sym}~(a~l)`, leaving $`c`.

The lexer rejects a quoted symbol whose name is a word, since a word is
written bare; the printer quotes a symbol only when its name is not one.
:::

:::readable Fir.Text.isWord_iff (fingerprint := "7543824082579312445")
*Lemma: what a word is, as a statement.* A string is a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[word] exactly when
it is a character that starts a word followed by characters that are each
a name character. It turns the word test into a statement the proofs can
take apart.
:::

:::readable Fir.Text.spells_of_reads (fingerprint := "10681497462333076005")
*Theorem: a token that is read whole spells itself.* Let $`a` be none of a
space, a tab, a line feed and `/`, $`s` characters and $`t` a token. If,
for all characters $`c` with $`\mathrm{boundary}(c)`, the token that starts
with $`a`, followed by $`s~c`, is read as $`t`, leaving $`c`, then $`a~s`
{ref "The-fir-specification--Text-format--Maximal-munch"}[spells] $`t`: $`\mathrm{spells}(a~s, t)`.
:::

:::readable Fir.Text.spells_nat (fingerprint := "2232630879042954436")
*Theorem: the digits of a natural number spell it.* For every natural
number $`n`, its decimal digits spell $`\mathsf{int}~n`.
:::

:::readable Fir.Text.spells_float (pin := Fir.FloatLit.print) (pin := Fir.FloatLit.valid) (pin := Fir.Text.expChars) (fingerprint := "3848005901455791572")
*Theorem: a float literal that can be written spells itself.* For every
float literal $`l` that can be written,
$`\mathrm{spells}(\mathrm{print}(l), \mathsf{float}~l)`: its spelling,
followed by any characters at the end of a token, is read back as it, by
the {ref "The-fir-specification--Text-format--Reading-printed-float-literals"}[theorems on float literals].
A decimal's whole part is a natural number printed with its digits, so its
first digit starts it; a negative decimal starts with `-`; and hexadecimal
bits start with `0`, then `x`.
:::

:::readable Fir.Text.Tok.spells (pin := Fir.Text.Tok.spell) (pin := Fir.Text.Tok.Writable) (fingerprint := "7954031007255374294")
*Theorem: every token that can be written spells itself.* For every token
$`t` that
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[can be written]:

$$`\mathrm{writable}(t) \implies \mathrm{spells}(\mathrm{spell}(t), t)`

So the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[spelling] of $`t`, followed by any characters at the end of a token
that lex to $`u`, lexes to $`t~u`. This is the fact about single tokens
that the next sections build on: a printed construct is its tokens'
spellings, with spaces and line feeds between them.
:::
