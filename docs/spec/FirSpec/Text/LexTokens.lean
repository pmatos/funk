import VersoManual
import Fir.Text.LexTokens
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on maximal munch, which renders
`Fir.Text.LexTokens` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Maximal munch: readable blocks" =>

:::readable Fir.Text.Boundary (pin := Fir.isNameChar) (fingerprint := "8957515299771534444")
*Definition: the end of a token.* Characters $`c` are _at the end of a
token_, $`\mathrm{boundary}(c)`, when they are empty or their first
character is not a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[name character]:
a letter, a digit, `_` or `.`. A name, a word or a number that such
characters follow ends where they start, since the lexer reads every name
character that follows one as part of it.
:::

:::readable Fir.Text.Lexes (pin := Fir.Text.lexFrom) (fingerprint := "1537384208854420284")
*Definition: characters that lex to tokens.* Characters $`c` _lex to_ the
tokens $`u`, $`\mathrm{lexes}(c, u)`, when, from every position and after
any tokens already read, the
{ref "The-fir-specification--Text-format--The-parser"}[lexer] reads $`c`
without error, and gives the tokens already read, then tokens whose kinds,
positions aside, are $`u~\mathsf{eof}`.

Characters, like tokens, are written side by side: $`s~c` is the
characters $`s` followed by the characters $`c`. The lexer reads a text
from its first character and keeps the tokens read so far, so a statement
about the rest of a text must hold whatever came before it; that is why
the definition asks it of every position and whatever tokens were read
before.
:::

:::readable Fir.Text.Spells (pin := Fir.Text.Boundary) (pin := Fir.Text.Lexes) (fingerprint := "4906871973712591511")
*Definition: characters that spell tokens.* The characters $`s` _spell_
the tokens $`t`, $`\mathrm{spells}(s, t)`, when $`s`, followed by any
characters $`c` at the end of a token that lex to some tokens $`u`, lexes
to $`t~u`:

$$`\begin{aligned} & \mathrm{spells}(s, t) \iff \forall c, u. \\ & \quad \mathrm{boundary}(c) \wedge \mathrm{lexes}(c, u) \\ & \quad \implies \mathrm{lexes}(s~c, t~u) \end{aligned}`

This is maximal munch seen from the printer's side: the printer never
writes a name character directly after a value, a label, a symbol written
as a word, a location reference, a word or an integer, so each of them is
read back whole. The rest of this part proves $`\mathrm{spells}` for the
text of every token, then of every construct.
:::

:::readable Fir.Text.ok_bind Fir.Text.boundary_cons (fingerprint := "16699646170285060169")
*Lemmas: proof plumbing.* A step that succeeds with $`a`, followed by $`f`,
is $`f` applied to $`a`; and a character that is not a name character, then
any characters, is at the end of a token. The proofs below rewrite with
both.
:::

:::readable Fir.Text.Lexes.nil Fir.Text.Lexes.space Fir.Text.Lexes.lf Fir.Text.Lexes.spaces (pin := Fir.Text.lexFrom) (fingerprint := "3302270484701013097")
*Theorems: the empty text, and whitespace.* The empty text lexes to no
token, $`\mathrm{lexes}(\epsilon, \epsilon)`: the lexer gives only
$`\mathsf{eof}`. For all characters $`c` and tokens $`u` with
$`\mathrm{lexes}(c, u)`:

* a space then $`c` lexes to $`u`;
* a line feed then $`c` lexes to $`u`;
* for every $`n`, $`n` spaces then $`c` lex to $`u`.

The lexer drops whitespace, and these are how the proofs drop the
printer's spaces, line feeds and indentation.
:::

:::readable Fir.Text.ReadsToken Fir.Text.Lexes.token (pin := Fir.Text.lexToken) (pin := Fir.Text.lexFrom) (fingerprint := "10611525379012511674")
*Definition and theorem: reading one token.* The lexer reads each token
with a token reader, which is given the token's first character $`c`, the
characters $`\mathit{rest}` after it and a position.
$`\mathrm{reads}(c, \mathit{rest}, t, r)` holds when, at every position,
the token reader reads the token $`t` from $`c` and $`\mathit{rest}`
and leaves the characters $`r`, at some position.

*Theorem:* let $`c` be none of a space, a tab, a line feed and `/`. For all
characters $`\mathit{rest}` and $`r` and tokens $`t` and $`u`:

$$`\begin{aligned} & \mathrm{reads}(c, \mathit{rest}, t, r) \wedge \mathrm{lexes}(r, u) \\ & \implies \mathrm{lexes}(c~\mathit{rest}, t~u) \end{aligned}`

The lexer hands every other character, one that does not start whitespace
or a comment, to the token reader, so this is how each token below joins
the tokens that follow it.
:::

:::readable Fir.Text.Tok.IsPunct Fir.Text.Tok.lexes_punct (pin := Fir.Text.lexToken) (pin := Fir.Text.Tok.spell) (fingerprint := "8354599374140513397")
*Definition and theorem: punctuation is read before any characters.* The
punctuation tokens are $`\texttt{(}`, $`\texttt{)}`, $`\texttt{\{}`,
$`\texttt{\}}`, $`\texttt{,}`, $`\texttt{:}`, $`\texttt{=}` and
$`\texttt{->}`. For every punctuation token $`t`, and all characters $`c`
and tokens $`u` with $`\mathrm{lexes}(c, u)`:

$$`\mathrm{lexes}(\mathrm{spell}(t)~c,\ t~u)`

Unlike $`\mathrm{spells}`, this asks nothing of $`c`: punctuation ends
where it is, so the printer may write `(` and `:` directly before a word or
a number, as in `h(i32)` and `"f":2:3`.
:::

:::readable Fir.Text.takeWhile_name (fingerprint := "7096711574217819124")
*Theorem: name characters are read up to the end of a token.* For all
characters $`l` that are each a name character, and characters $`c` with
$`\mathrm{boundary}(c)`: taking the name characters at the start of
$`l~c` gives $`l`, and leaves $`c`. This is maximal munch for a name or a
word: the reader takes exactly the printed name.
:::

:::readable Fir.Text.isName_iff (fingerprint := "3433924943955704327")
*Lemma: what a name is, as a statement.* A string is a name exactly when it
has a character and each of its characters is a name character. This turns
the name test into a statement the proofs can use.
:::

:::readable Fir.Text.le_char_iff Fir.Text.eq_char_iff Fir.Text.isDigit_iff (fingerprint := "16307656197113693534")
*Lemmas: characters by code point.* Characters compare, and are equal,
exactly as their code points do, and a character is a decimal digit
exactly when its code point is from 48 to 57. They let the proofs below
decide questions about characters by arithmetic on code points.
:::

:::readable Fir.Text.isNameChar_iff Fir.Text.isWordStart_iff (pin := Fir.isNameChar) (pin := Fir.isWordStart) (pin := Fir.isLetter) (fingerprint := "13655858174497020320")
*Theorems: the name characters, and the characters that start a word, by
code point.* A character is a name character exactly when its code point
is from 65 to 90 (`A` to `Z`), from 97 to 122 (`a` to `z`), 95 (`_`),
from 48 to 57 (`0` to `9`) or 46 (`.`). It starts a word exactly when its
code point is from 65 to 90, from 97 to 122, or 95.
:::

:::readable Fir.Text.formatChars_ge Fir.Text.isEscaped_toNat Fir.Text.isEscaped_of_ascii Fir.Text.allowed_of_ascii Fir.Text.ascii_of_isNameChar (pin := Fir.Text.formatChars) (pin := Fir.Text.isEscaped) (pin := Fir.Text.allowedOutsideStrings) (fingerprint := "1590749765807917374")
*Theorems: names are printable ASCII, which the lexer allows.* Printable
ASCII is the characters with code points from 32 to 126.

* Every format character that a string
  {ref "The-fir-specification--Text-format--Tokens"}[escapes] has a code
  point of at least U+00AD.
* So every character that a string escapes is a control character, below
  32, or has a code point of 127 or more.
* So no printable ASCII character is escaped,
* and every printable ASCII character is allowed outside strings.
* Every name character is printable ASCII.

The lexer rejects a character that a text may not hold outside strings,
before it reads a token; these facts show that it never rejects the first
character of a name, a word or a number.
:::

:::readable Fir.Text.isDigit_of_isWordStart Fir.Text.ne_of_isNameChar (fingerprint := "17472075975194507019")
*Theorems: what a name character is not.* A character that starts a word
is not a decimal digit. A name character is none of `(`, `)`, `{`, `}`,
`,`, `:`, `=`, `%`, `^`, `@`, `"`, `-`, a space, a tab, a line feed and
`/`. So the token reader, which tries punctuation, `%`, `^`, `@`, `"`,
`-` and digits before words, reads a word that starts with such a
character as a word.
:::

:::readable Fir.Text.readsToken_name (pin := Fir.Text.lexToken) (fingerprint := "18409507457798329378")
*Theorem: a value or a label is read up to the end of its name.* Let
$`\sigma` be `%` or `^`, $`x` a name, and $`c` characters with
$`\mathrm{boundary}(c)`. Then $`\mathrm{reads}(\sigma, x~c, t, c)`, where
$`t` is $`\mathsf{value}~x` when $`\sigma` is `%`, and
$`\mathsf{label}~x` when it is `^`.
:::

:::readable Fir.Text.readsToken_word (pin := Fir.Text.lexToken) (fingerprint := "3064419926229029853")
*Theorem: a word is read up to the end of a token.* Let $`a` be a
character that starts a word, $`l` characters that are each a name
character, and $`c` characters with $`\mathrm{boundary}(c)`. Then
$`\mathrm{reads}(a, l~c, \mathsf{word}~(a~l), c)`: the word $`a~l` is
read, and $`c` is left.
:::

:::readable Fir.Text.isDigit_of_not_isNameChar Fir.Text.takeWhile_digits Fir.Text.isDigit_of_toDigits (fingerprint := "9095456358460756976")
*Theorems: digits up to the end of a token.* A character that is not a
name character is not a digit. So, for all characters $`d` that are each a
decimal digit, and $`c` with $`\mathrm{boundary}(c)`, taking the digits at
the start of $`d~c` gives $`d` and leaves $`c`. Every character of the
decimal digits of a number is a decimal digit.
:::

:::readable Fir.Text.lexDigits_toDigits (pin := Fir.Text.lexDigits) (pin := Nat.toDigits) (fingerprint := "753233971530860166")
*Theorem: the printer's digits of a number are read whole.* For every
natural number $`n` whose decimal digits are $`d~l`, a first digit $`d`
and the others $`l`, all characters $`c` with $`\mathrm{boundary}(c)`
and every position: the lexer's reader of digits, given $`d` and
$`l~c`, gives the digits $`d~l` and leaves $`c`. It rejects a leading
zero and a number that a name character follows; the printer writes
neither.
:::

:::readable Fir.Text.toDigits_cons Fir.Text.isNameChar_of_isDigit (fingerprint := "14245282254730609743")
*Lemmas: proof plumbing.* The decimal digits of every natural number are a
first digit and the others, and every digit is a name character.
:::

:::readable Fir.Text.readsToken_nat (pin := Fir.Text.lexToken) (pin := Fir.Text.lexInt) (fingerprint := "5459937746606524210")
*Theorem: a natural number is read as an integer token.* For every natural
number $`n` whose decimal digits are $`d~l`, and characters $`c` with
$`\mathrm{boundary}(c)`: $`\mathrm{reads}(d, l~c, \mathsf{int}~n, c)`.
:::

:::readable Fir.Text.readsToken_neg (pin := Fir.Text.lexToken) (pin := Fir.Text.lexInt) (fingerprint := "14051053255598936565")
*Theorem: a negative integer is read as an integer token.* For every
natural number $`m`, with $`d~l` the decimal digits of $`m + 1`, and
characters $`c` with $`\mathrm{boundary}(c)`:
$`\mathrm{reads}(\texttt{-}, d~l~c, \mathsf{int}~(-(m+1)), c)`. Every
negative integer is $`-(m+1)` for some $`m`, and is spelled `-` then the
digits of its magnitude, which do not start with `0`.
:::

:::readable Fir.Text.readsToken_locRef (pin := Fir.Text.lexToken) (pin := Fir.Text.lexAt) (fingerprint := "3336394283689462252")
*Theorem: a location reference below 2³² is read.* For every natural
number $`r < 2^{32}` whose decimal digits are $`d~l`, and characters $`c`
with $`\mathrm{boundary}(c)`: $`\mathrm{reads}(\texttt{@}, d~l~c, \mathsf{locref}~r, c)`.
The lexer rejects a larger reference, which is why it must be below the
limit to be written.
:::
