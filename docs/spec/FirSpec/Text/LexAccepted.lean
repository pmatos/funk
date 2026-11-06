import VersoManual
import Fir.Text.LexAccepted
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the lexer accepts, which renders
`Fir.Text.LexAccepted` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "What the lexer accepts: readable blocks" =>

:::readable Fir.Text.bind_eq_ok (fingerprint := "17647912058474426905")
*Lemma: proof plumbing.* For every computation $`x` that ends with a
result or an error, every $`f` that maps a result of $`x` to such a
computation, and every result $`b`: if running $`x`, then $`f` on its
result, ends with $`b`, then $`x` ends with some result $`a`, and $`f(a)`
ends with $`b`. A reader of the parser is a chain of such steps, and the
proofs of the parser's three steps take it apart one step at a time with
this lemma.
:::

:::readable Fir.Text.mem_takeWhile Fir.Text.isName_takeWhile Fir.Text.isWord_takeWhile (pin := Fir.isName) (pin := Fir.isWord) (pin := Fir.isWordStart) (fingerprint := "1045717097886148641")
*Lemmas: a run of name characters is a name.* For every test $`p` on
characters and every list of characters, each character of the longest
prefix of the list whose characters all pass $`p` passes $`p`. So, for
every list of characters:

* when the longest run of
  {ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[name characters]
  at its start is not empty, that run is a name;
* for every character that may start a word, that character followed by
  the longest run of name characters at the start of the list is a word.

A name is one or more name characters, and a word is a name whose first
character is a letter or `_`. The lexer reads a value, a label and a word
in exactly this way, so these lemmas are what make its tokens names and
words.
:::

:::readable Fir.Text.lexInt_writable Fir.Text.lexAt_writable Fir.Text.lexToken_writable (pin := Fir.Text.lexInt) (pin := Fir.Text.lexAt) (pin := Fir.Text.lexToken) (pin := Fir.Text.Tok.Writable) (pin := Fir.Location.limit) (pin := Fir.isWordStart) (fingerprint := "6050580012468359362")
*Theorems: every token that the lexer reads can be written.* For every
character $`c`, the characters after it, and position: every token that
the reader of one {ref "The-fir-specification--Text-format--The-parser"}[token]
reads from $`c` on
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[can be written].
So does every integer that it reads after a first digit, with or without a
`-` before it, and every token that it reads after `@`. Case by case:

* a value or a label is `%` or `^` and the longest run of name characters
  after it, and the reader rejects it when that run is empty, so its name
  is a name;
* a word starts with a letter or `_` and takes in every name character
  after it, so it is a word;
* after `@`, a number of $`2^{32}` or more is an error at the number, so a
  location reference $`\mathsf{locref}~r` has $`r < 2^{32}`;
* a symbol, an integer, a string and a punctuation token can always be
  written.

The reader gives no other token: whitespace and comments give no token at
all, and the end of the text, $`\mathsf{eof}`, is added by the loop that
calls it.
:::

:::readable Fir.Text.TokensWritable (fingerprint := "17403735823257984506")
*Definition: a list of tokens that can be written.* A list of tokens
$`\mathit{ts}` _can be written_, written $`\mathrm{writable}(\mathit{ts})`,
when each of its tokens is $`\mathsf{eof}` or can be written. The lexer
ends every list it gives with $`\mathsf{eof}`, which has no spelling, and
the readers of the grammar read it only to check that the text has ended;
so it is allowed here, and every other token must be one that the printer
could write.
:::

:::readable Fir.Text.lexFrom_writable Fir.Text.lex_writable (pin := Fir.Text.lexFrom) (pin := Fir.Text.lex) (fingerprint := "16547685817246884587")
*Theorems: the lexer's step.* The lexer's loop reads a text from a
position, keeping the tokens it has read so far. For every list of
characters, position, and list of tokens read so far each of which can be
written: if the loop ends with the tokens $`\mathit{ts}`, then
$`\mathrm{writable}(\mathit{ts})`. Each step of the loop drops a space, a
tab, a line feed or a comment, or adds the token that the reader of one
token reads, which can be written; at the end of the characters it adds
$`\mathsf{eof}`.

So, for every text $`t`, when the
{ref "The-fir-specification--Text-format--The-parser"}[lexer] reads $`t`
as the tokens $`\mathit{ts}`, from line 1, column 1, with no token read
before:

$$`\mathrm{lex}(t) = \mathsf{ok}(\mathit{ts}) \implies \mathrm{writable}(\mathit{ts})`

Here $`\mathrm{lex}(t) = \mathsf{ok}(\mathit{ts})` says that the lexer
reads $`t` without an error, and gives $`\mathit{ts}`. This is the first of the parser's three steps: the grammar step starts
from tokens that can be written.
:::
