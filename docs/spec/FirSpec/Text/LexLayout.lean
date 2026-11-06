import VersoManual
import Fir.Text.LexLayout
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on spaces, line feeds and lists, which
renders `Fir.Text.LexLayout` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Spaces, line feeds and lists: readable blocks" =>

:::readable Fir.Text.SpellsAny Fir.Text.Spells.nil (pin := Fir.Text.Lexes) (pin := Fir.Text.Spells) (fingerprint := "2470327400403327257")
*Definition and theorem: spelling tokens before any characters.* The
characters $`s` spell the tokens $`t` _before any characters_,
$`\mathrm{spells}_{\mathrm{any}}(s, t)`, when $`s` followed by any
characters that lex to $`u` lexes to $`t~u`:

$$`\begin{aligned} \mathrm{spells}_{\mathrm{any}}(s, t) \iff\ & \forall c, u.\ \mathrm{lexes}(c, u) \\ & \implies \mathrm{lexes}(s~c, t~u) \end{aligned}`

It is $`\mathrm{spells}` without the condition that $`c` be
{ref "The-fir-specification--Text-format--Maximal-munch"}[at the end of a token],
and holds for text that ends with punctuation or whitespace. Every line,
block, region, item and module that the printer writes ends with a line
feed or a `}`, so each is read whatever follows it.

*Theorem:* the empty text spells no tokens,
$`\mathrm{spells}(\epsilon, \epsilon)`.
:::

:::readable Fir.Text.StartsBoundary Fir.Text.startsBoundary_cons (pin := Fir.Text.Boundary) (fingerprint := "17302690920968997386")
*Definition and theorem: text that keeps a boundary.* The characters $`s`
_keep a boundary_, $`\mathrm{keeps}(s)`, when $`s` followed by any
characters at the end of a token is at the end of a token too:

$$`\begin{aligned} & \mathrm{keeps}(s) \iff \forall c.\ \mathrm{boundary}(c) \\ & \quad \implies \mathrm{boundary}(s~c) \end{aligned}`

So $`s` is empty or starts with a character that is not a name character.
*Theorem:* for every character $`a` that is not a name character and all
characters $`s`, $`\mathrm{keeps}(a~s)`.
:::

:::readable Fir.Text.Spells.append Fir.Text.SpellsAny.append_any Fir.Text.Spells.append_any (fingerprint := "9018314951637294630")
*Theorems: two texts side by side.* For all characters $`a` and $`b` and
tokens $`t_a` and $`t_b`:

* if $`\mathrm{spells}(a, t_a)`, $`\mathrm{spells}(b, t_b)` and
  $`\mathrm{keeps}(b)`, then $`\mathrm{spells}(a~b, t_a~t_b)`;
* if $`\mathrm{spells}_{\mathrm{any}}(a, t_a)` and
  $`\mathrm{spells}_{\mathrm{any}}(b, t_b)`, then
  $`\mathrm{spells}_{\mathrm{any}}(a~b, t_a~t_b)`;
* if $`\mathrm{spells}(a, t_a)`, $`\mathrm{spells}_{\mathrm{any}}(b, t_b)`,
  and $`b~c` is at the end of a token for all characters $`c`, then
  $`\mathrm{spells}_{\mathrm{any}}(a~b, t_a~t_b)`.

The condition on $`b` is where maximal munch shows: a text that may end in
the middle of a name must be followed by one that cannot continue it.
:::

:::readable Fir.Text.Spells.space Fir.Text.SpellsAny.space Fir.Text.SpellsAny.lf Fir.Text.SpellsAny.nil (fingerprint := "16966144791684330468")
*Theorems: whitespace in front of a text.* For all characters $`s` and
tokens $`t`:

* if $`\mathrm{spells}(s, t)`, a space then $`s` spells $`t`;
* if $`\mathrm{spells}_{\mathrm{any}}(s, t)`, a space then $`s` spells
  $`t` before any characters;
* if $`\mathrm{spells}_{\mathrm{any}}(s, t)`, a line feed then $`s`
  spells $`t` before any characters.

And the empty text spells no tokens before any characters,
$`\mathrm{spells}_{\mathrm{any}}(\epsilon, \epsilon)`.
:::

:::readable Fir.Text.toList_indent Fir.Text.SpellsAny.indent (pin := Fir.indent) (fingerprint := "14854796118338773501")
*Theorems: indentation is dropped.* The
{ref "The-fir-specification--Text-format--The-canonical-printer"}[printer's]
indentation by $`n` is $`n` spaces. So, for all characters $`s`, tokens
$`t` and every $`n`, if $`\mathrm{spells}_{\mathrm{any}}(s, t)`, the
indentation by $`n` then $`s` spells $`t` before any characters.
:::

:::readable Fir.Text.Spells.punct Fir.Text.SpellsAny.punct_any (fingerprint := "10509021152498437824")
*Theorems: punctuation in front of a text.* Let $`t` be a punctuation
token whose spelling is the character $`a` followed by the characters $`l`
($`l` is empty but for $`\texttt{->}`). For all characters $`s` and tokens
$`u`:

* if $`\mathrm{spells}(s, u)`, then $`\mathrm{spells}(a~l~s, t~u)`;
* if $`\mathrm{spells}_{\mathrm{any}}(s, u)`, then
  $`\mathrm{spells}_{\mathrm{any}}(a~l~s, t~u)`.
:::

:::readable Fir.Text.Spells.comma Fir.Text.SpellsAny.lbrace Fir.Text.SpellsAny.rbrace Fir.Text.SpellsAny.rparen Fir.Text.SpellsAny.colon Fir.Text.SpellsAny.lparen Fir.Text.SpellsAny.eq (fingerprint := "7956862649502044873")
*Theorems: each punctuation character in front of a text.* For all
characters $`s` and tokens $`u`: if $`\mathrm{spells}(s, u)`, then `,`
then $`s` spells $`\texttt{,}~u`. If
$`\mathrm{spells}_{\mathrm{any}}(s, u)`, then `{` then $`s` spells
$`\texttt{\{}~u` before any characters, and so do `}`, `)`, `:`, `(` and
`=` with their tokens. These are the cases of the previous theorems that
the proofs use.
:::

:::readable Fir.Text.Spells.tok_any (fingerprint := "558933299089106731")
*Theorem: a token in front of a text that is read before any characters.*
For every token $`t` that can be written, characters $`s` and tokens $`u`:
if $`\mathrm{spells}_{\mathrm{any}}(s, u)`, and $`s~c` is at the end of a
token for all characters $`c`, then
$`\mathrm{spells}_{\mathrm{any}}(\mathrm{spell}(t)~s, t~u)`.
:::

:::readable Fir.Text.spells_word (fingerprint := "4950589787715188689")
*Theorem: a word spells its token.* For every
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[word]
$`w`, $`\mathrm{spells}(w, \mathsf{word}~w)`: the case of
{ref "The-fir-specification--Text-format--Escapes-and-quoted-symbols"}[every token]
that the printer uses for an op's name.
:::

:::readable Fir.Text.Lexes.punct Fir.Text.Lexes.lparen Fir.Text.Lexes.rparen Fir.Text.Lexes.lbrace Fir.Text.Lexes.rbrace Fir.Text.Lexes.colon Fir.Text.Lexes.eq Fir.Text.Lexes.arrow (fingerprint := "11246764515322871985")
*Theorems: punctuation, read from the first character.* For every
punctuation token $`t` whose spelling is the characters $`p`, and all
characters $`c` and tokens $`u` with $`\mathrm{lexes}(c, u)`:
$`\mathrm{lexes}(p~c, t~u)`. The cases for `(`, `)`, `{`, `}`, `:`, `=`
and `->` follow.
:::

:::readable Fir.Text.Lexes.tok Fir.Text.Lexes.word Fir.Text.Lexes.value Fir.Text.Lexes.label Fir.Text.Lexes.sym Fir.Text.Lexes.locRef Fir.Text.Lexes.nat Fir.Text.Lexes.quote Fir.Text.Lexes.lit (fingerprint := "606311062853272660")
*Theorems: a token, read from the first character.* For every token $`t`
that can be written, whose spelling is the characters $`p`, and all
characters $`c` with $`\mathrm{boundary}(c)` and tokens $`u` with
$`\mathrm{lexes}(c, u)`: $`\mathrm{lexes}(p~c, t~u)`. The cases that the
proofs use, under the same conditions on $`c` and $`u`:

* a word $`w` lexes to $`\mathsf{word}~w`;
* for a name $`x`, `%` then $`x` lexes to $`\mathsf{value}~x`, and `^`
  then $`x` to $`\mathsf{label}~x`;
* for every string $`s`, the printer's spelling of the symbol $`s` lexes
  to $`\mathsf{sym}~s`;
* for every $`r < 2^{32}`, the printer's spelling of the location
  reference $`r` lexes to $`\mathsf{locref}~r`;
* for every natural number $`n`, its decimal digits lex to
  $`\mathsf{int}~n`: a line or a column of a location;
* for every string $`s`, $`s` quoted lexes to $`\mathsf{str}~s`;
* a word $`w` whose characters are $`p` lexes to $`\mathsf{word}~w`, for
  a word that the printer writes as it is, such as `func`.

These read a printed text piece by piece from its first character.
:::

:::readable Fir.Text.boundary_space (fingerprint := "3109007819735374284")
*Lemma: a space is at the end of a token.* For all characters $`c`, a space
then $`c` is at the end of a token.
:::

:::readable Fir.Text.SpellsEach Fir.Text.SpellsEach.map Fir.Text.SpellsEach.append (pin := Fir.Text.Spells) (fingerprint := "7819938177392578574")
*Definition and theorems: each string of a list spells its tokens.* A list
of strings $`s_1, \dots, s_n` spells the lists of tokens
$`t_1, \dots, t_m` _one by one_ when $`n = m` and
$`\mathrm{spells}(s_i, t_i)` for each $`i`.

* For every list $`x_1, \dots, x_n` and functions $`f` to strings and
  $`g` to tokens, if $`\mathrm{spells}(f(x), g(x))` for each $`x` of the
  list, then $`f(x_1), \dots, f(x_n)` spell
  $`g(x_1), \dots, g(x_n)` one by one.
* Two lists that spell one by one, one after the other, spell one by one.
:::

:::readable Fir.Text.spells_commaSep Fir.Text.spells_spaceSep (fingerprint := "3403337338728431291")
*Theorems: a list written with separators spells its tokens.* For every
list of strings $`s_1, \dots, s_n` that spells the lists of tokens
$`t_1, \dots, t_n` one by one:

* the strings written with `, ` between them spell
  $`t_1~\texttt{,}~t_2~\dots~\texttt{,}~t_n`;
* the strings written with a space between them spell
  $`t_1~t_2~\dots~t_n`.

The printer writes arguments, operands, results and attributes this way.
:::

:::readable Fir.Text.forall_mem_intercalate (fingerprint := "5940800335083962738")
*Lemma: what holds of a joined list holds of its parts.* For every test
$`P` on tokens, separator $`x` and lists of tokens $`t_1, \dots, t_n`: if
every token of $`t_1~x~t_2~\dots~x~t_n` passes $`P`, so does every token
of each $`t_i`. It hands the condition that tokens can be written down to
the elements of a list.
:::
