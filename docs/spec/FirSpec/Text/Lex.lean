import VersoManual
import Fir.Text.Lex
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the parser, which renders
`Fir.Text.Lex` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The parser: readable blocks" =>

:::moduleDocs (fingerprint := "5822860858962979440")
:::

:::readable Fir.Text.Tok (pin := Fir.Location.limit) (fingerprint := "10478793237488592436")
*Definition: a token.* The lexer reads a text into these tokens, from the
{ref "The-fir-specification--Text-format--Tokens"}[tokens section]:

```grammar Fir.Text.Tok
\mathit{tok}
value,label                 \mathsf{value}~x \mid \mathsf{label}~\ell
sym,locRef                  \mathsf{sym}~s \mid \mathsf{locref}~r
word,int,str                \mathsf{word}~w \mid \mathsf{int}~i \mid \mathsf{str}~s
lparen,rparen,lbrace,rbrace \texttt{(} \mid \texttt{)} \mid \texttt{\{} \mid \texttt{\}}
comma,colon,eq,arrow        \texttt{,} \mid \texttt{:} \mid \texttt{=} \mid \texttt{->}
eof                         \mathsf{eof}
```

$`\mathsf{value}~x` is the value `%x`, $`\mathsf{label}~\ell` the label
`^ℓ`, $`\mathsf{sym}~s` a symbol, quoted or not, $`\mathsf{locref}~r` the
location reference `@r` (`locRef` in the Lean), $`\mathsf{word}~w` a word,
$`\mathsf{int}~i` an integer and $`\mathsf{str}~s` a string, each with
what it holds: $`s` is the text of the string, with its escapes read. The
punctuation tokens are their characters (`lparen` to `arrow` in the Lean).
$`\mathsf{eof}` ends every list of tokens, at the end of the text. Numbers
are read whole: a location reference below $`2^{32}`, and an integer of
any size.
:::

:::readable Fir.Text.Tok.describe Fir.Text.Token Fir.TextPos.advance Fir.Text.utf8Len Fir.Text.codePoint Fir.Text.errorAt (pin := Fir.Text.printSymbol) (pin := Fir.Text.quote) (pin := Fir.Text.hex) (fingerprint := "6110927321418021566")
*Definition: a token at its position, and the parts of an error.* A token
of the lexer's output is a token with the
{ref "The-fir-specification--Text-format--Round-trips"}[position] where it
starts. Moving $`n` bytes along a line adds $`n` to the column, and the
size of some characters is the sum of their sizes in UTF-8.

An error is a position and a reason. A reason names a token as `value %x`,
`label ^ℓ`, `symbol` and the symbol, `location reference @r`, `word w`,
`integer i`, `string` and the string, a punctuation token as itself, and
$`\mathsf{eof}` as `the end of the text`. Strings and symbols are spelled
canonically, so a message never holds a character that a string escapes. A
reason names a character by its code point, such as `U+000D`: uppercase
hexadecimal with at least four digits.
:::

:::readable Fir.Text.length_dropWhile_le Fir.Text.Left (fingerprint := "6601872693856412026")
*Definition and theorem: what a reader leaves is never longer than what it
was given.* For every
test $`f` on characters and list of characters $`l`, dropping the
characters at the start of $`l` that pass $`f` leaves at most
$`|l|` characters. Each reader returns the characters after what it read
together with this bound, so that the lexer, which calls itself on them,
is seen to end.
:::

:::readable Fir.Text.isHexDigit Fir.Text.hexValue (fingerprint := "17084292184813307361")
*Definition: hexadecimal digits, and their value.* A hexadecimal digit is
a decimal digit or one of the lowercase letters `a` to `f`; uppercase
letters are not digits. The value of some digits $`h_1 \dots h_k` is
$`\sum_j h_j \cdot 16^{k-j}`, where `a` to `f` count 10 to 15.
:::

:::readable Fir.Text.unicodeEscape Fir.Text.lexEscape Fir.Text.lexStringFrom Fir.Text.lexString (pin := Fir.Text.isEscaped) (fingerprint := "9424781684911375709")
*Definition: reading a string.* After the opening `"`, the lexer reads the
characters of a string up to the closing `"`, and gives the string, the
characters after it and the position there. Each character $`c` is read
as follows:

* `"` closes the string.
* `\` starts an escape, read below.
* A character that a
  {ref "The-fir-specification--Text-format--Tokens"}[string escapes] is
  an error at it: it must be escaped.
* Any other character is itself, and moves the position by its size in
  UTF-8.

The text ending before the closing `"` is an error at the opening `"`.
After a `\`, the escapes `\\`, `\"`, `\n` and `\t` are a backslash, a
quote, a line feed and a tab. `\u{h}`, with $`h` one or more hexadecimal
digits, is the character with the code point $`h`, when all of these hold,
and each failure is an error at the `\`:

* $`h` is the code point of a character;
* $`h` has no leading zero;
* the character is not the line feed or the tab, which are written `\n`
  and `\t`;
* the character is one that a string escapes; any other is written as
  itself.

Any other escape, and `\u{` not followed by digits and `}`, is an error at
the `\`. So the lexer accepts a string only in the one spelling that the
printer writes. The loop keeps the characters read so far, and calls itself
as its last step, so that a string of any length takes no stack.
:::

:::readable Fir.Text.lexDigits Fir.Text.digitsValue (pin := Fir.isNameChar) (fingerprint := "5481629183998418021")
*Definition: reading the digits of a number.* A number that starts with
the digit 0 is the one digit 0. Any other number is its first digit and
every digit that follows it. When the character after the digits is a name
character, the number is an error at its start: numbers have no leading
zeros, and fir has no float literal. So `007`, `1abc` and `1.5` are errors.

The value of the digits is their decimal value. A number of more than 64
digits is split in two halves, whose values are joined by one product, so
that a constant of millions of digits, as wide types allow, is read in
about the time of a few products, not in time quadratic in its length.
:::

:::readable Fir.Text.lexAt Fir.Text.lexInt (pin := Fir.Location.limit) (pin := Fir.isWord) (pin := Fir.isWordStart) (pin := Fir.isNameChar) (fingerprint := "5941601449031920245")
*Definition: reading what follows `@`, and an integer.* After `@`, the
lexer reads:

* digits: a location reference, whose value must be below $`2^{32}`, or
  it is an error at the digits;
* a letter or `_`, then every name character after it: the symbol with
  that name, which is a word;
* a string: the symbol with that string as its name, which must not be a
  word, or it is an error at the `@`, since a word is written bare;
* anything else, or the end of the text: an error at the `@`.

An integer is its digits, read as above, and is negative when a `-` comes
before them. Its value has no limit: the dialect that reads it bounds it.
:::

:::readable Fir.Text.lexToken (pin := Fir.Text.allowedOutsideStrings) (pin := Fir.isNameChar) (pin := Fir.isWordStart) (fingerprint := "1931958670576985994")
*Definition: reading one token.* The lexer reads the token that starts with
the character $`c`, which is not whitespace and does not start a comment:

* when a text may not hold $`c` outside strings, it is an error at $`c`;
* `(`, `)`, `{`, `}`, `,`, `:` and `=` are their tokens;
* `%` and `^` start a value and a label: the token is every name character
  after them, and an error when there is none;
* `@` starts a symbol or a location reference, and `"` a string, read as
  above;
* `-` followed by `>` is `->`, and followed by a digit other than 0 a
  negative integer; `-0` is an error, and so is a `-` followed by anything
  else;
* a digit starts an integer;
* a letter or `_` starts a word: it and every name character after it;
* any other character is an error at it.

A value, a label, a symbol or a word takes every name character that
follows it, and a number that a name character follows is an error, so
each token is the longest one that the text starts with: maximal munch.
:::

:::readable Fir.Text.notLineFeed Fir.Text.firstDisallowed Fir.Text.lexFrom Fir.Text.lex (pin := Fir.Text.allowedOutsideStrings) (fingerprint := "16125086146743415106")
*Definition: the tokens of a text.* The lexer reads the characters of a
text from the first, at line 1 and column 1, and keeps the position:

* a space or a tab moves one column on, and a line feed starts the next
  line at column 1;
* `//` starts a comment, which runs to the next line feed, or to the end of
  the text. It is skipped, unless it holds a character that a text may not
  hold outside strings, which is an error at that character;
* any other character starts a token, which is read with its position.

At the end of the text, the tokens are those read, in order, followed by
$`\mathsf{eof}` at the end's position. The lexer stops at its first error.
:::
