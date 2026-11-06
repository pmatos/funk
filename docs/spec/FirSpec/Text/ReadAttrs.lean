import VersoManual
import Fir.Text.ReadAttrs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the grammar step, which renders
`Fir.Text.ReadAttrs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The grammar step: readable blocks" =>

:::readable Fir.Text.Reads (pin := Fir.Text.Read) (pin := Fir.Text.Token) (fingerprint := "3025326747254618080")
*Definition: a reader reads tokens back.* A
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[reader]
takes a list of tokens, each with its position, and gives what it read and
the tokens after it, or an error. Let $`\mathit{read}` be a reader, $`f` a
map from what it reads, $`x` a value, $`u` a list of tokens without
positions, and $`S` a set of tokens. Then $`\mathit{read}` _reads $`u` as
$`x` before $`S`_, written $`\mathrm{reads}_f(\mathit{read}, u, x, S)`, when
on any tokens that hold $`u` and then some tokens $`v` whose first token,
if there is one, is in $`S`, the reader succeeds, $`f` maps what it read
to $`x`, and it leaves exactly $`v`:

$$`\begin{aligned} & \mathrm{reads}_f(\mathit{read}, u, x, S) \iff \\ & \forall\, \mathit{ts}, v.\ \mathrm{toks}(\mathit{ts}) = u~v \\ & \quad \wedge\ (v = \epsilon \vee \mathrm{first}(v) \in S) \\ & \implies \exists\, a, r.\ \mathit{read}(\mathit{ts}) = \mathsf{ok}(a, r) \\ & \quad \wedge\ f(a) = x \wedge \mathrm{toks}(r) = v \end{aligned}`

Here $`\mathrm{toks}(\mathit{ts})` is the tokens of $`\mathit{ts}` without
their positions, $`\mathrm{first}(v)` the first token of $`v`, $`a` what
the reader read and $`r` the tokens it left. As in the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens of a construct],
$`u~v` is $`u` followed by $`v`.

The positions are any, so what the reader reads holds positions that the
statement cannot know: $`f` is almost always $`\mathrm{erase}`, from the
{ref "The-fir-specification--Text-format--The-tree-that-the-grammar-reads"}[previous section],
and $`x` a tree without positions. $`S` says which tokens may follow: a
reader that reads as long as a token continues what it read needs a token
there that stops it.
:::

:::readable Fir.Text.map_tok_cons Fir.Text.not_cons_of_head (pin := Fir.Text.Token) (fingerprint := "5816524274964778390")
*Lemmas: proof plumbing on the first token.* Tokens whose first token,
without its position, is $`t` start with $`t` at some position, followed
by tokens that hold the others; and tokens whose first token is not $`t`
do not start with $`t`. The proofs of this
step use them to take tokens off the front one at a time.
:::

:::readable Fir.Text.intercalate_cons (fingerprint := "3496421127714282086")
*Lemma: proof plumbing on separators.* A list of lists written with a
separator $`s`, $`l~s~l_1~\dots~s~l_n`, is its first list, then $`s` and
each other list.
:::

:::readable Fir.Text.head?_append (fingerprint := "16091287264203044667")
*Lemma: proof plumbing on the first token.* If the first token of $`u`, if
any, and the first token of $`v`, if any, both pass a test, then so does
the first token of $`u~v`, if any.
:::

:::readable Fir.Text.expect_cons (pin := Fir.Text.expect) (fingerprint := "16554779249017004235")
*Theorem: the reader of one token reads it.* For every token $`t`, reason
and position, the reader that expects $`t` reads $`t` at the front of any
tokens and leaves the tokens after it.
:::

:::readable Fir.Text.Reads.more (pin := Fir.Text.readMore) (fingerprint := "9589081820413550885")
*Theorem: the rest of a list reads back when each element does.* Let $`\mathit{item}` be a reader,
and $`S` and $`S'` sets of tokens such that the comma is in $`S`, and every
token of $`S'` is in $`S` and is not a comma. For every list
$`x_1, \dots, x_n`, if $`\mathit{item}` reads the tokens $`u_i` as
$`g(x_i)` before $`S` for each $`i`, up to $`f`, then the
{ref "The-fir-specification--Text-format--Reading-the-grammar"}[reader of the rest of a list]
built on $`\mathit{item}` reads $`\texttt{,}~u_1~\dots~\texttt{,}~u_n` as
$`g(x_1), \dots, g(x_n)` before $`S'`, up to $`f` on each element.

The comma that follows each element but the last stops $`\mathit{item}`,
and the token after the list, which is not a comma, stops the reader of
the rest.
:::

:::readable Fir.Text.Attr.tokens_cons (pin := Fir.Attr.tokens) (pin := Fir.Text.Tok.startsAttr) (fingerprint := "5924600392021050269")
*Theorem: an attribute's tokens start with a token that starts an
attribute.* For every
{ref "The-fir-specification--Text-format--Grammar"}[attribute] $`a`, the
{ref "The-fir-specification--Text-format--Lexing-printed-text"}[tokens]
of $`a` are not empty, and the first is a word, an integer, a string or a
symbol.
:::

:::readable Fir.Text.commaAttrs (pin := Fir.Attr.tokens) (fingerprint := "13561104018607886205")
*Definition: the tokens of attributes, each after a comma.* For attributes
$`a_1, \dots, a_n`, the tokens
$`\texttt{,}~\mathrm{tokens}(a_1)~\dots~\texttt{,}~\mathrm{tokens}(a_n)`.
:::

:::readable Fir.Text.Attr.reads Fir.Text.Attr.readsArgs Fir.Text.Attr.readsMoreArgs (pin := Fir.Text.readAttr) (pin := Fir.Text.readAttrArgs) (pin := Fir.Text.readMoreAttrArgs) (pin := Fir.Attr.tokens) (fingerprint := "5750530247660356627")
*Theorems: an attribute, and an applied attribute's arguments, read
back.* For every attribute $`a`, list of
attributes $`a_1, \dots, a_n` and tokens $`v`, at any positions:

* on tokens that hold $`\mathrm{tokens}(a)`, then $`v` whose first token,
  if any, is not `(`, the reader of an attribute gives $`a` and leaves
  $`v`;
* on tokens that hold
  $`\mathrm{tokens}(a_1)~\texttt{,}~\dots~\texttt{,}~\mathrm{tokens}(a_n)~\texttt{)}~v`,
  the reader of an applied attribute's arguments gives
  $`a_1, \dots, a_n` and leaves $`v`;
* on tokens that hold
  $`\texttt{,}~\mathrm{tokens}(a_1)~\dots~\texttt{,}~\mathrm{tokens}(a_n)~\texttt{)}~v`,
  the reader of the arguments after the first gives $`a_1, \dots, a_n` and
  leaves $`v`.

The `(` is excluded because a word followed by `(` is read as an applied
attribute. The three are proved together, since an applied attribute holds
attributes. Nothing is asked of the attribute: the readers take any word.
:::

:::readable Fir.Text.readType_reads (pin := Fir.Text.readType) (pin := Fir.Attr.IsType) (fingerprint := "5398126215091845394")
*Theorem: a type reads back.* For every attribute $`a` that is
{ref "The-fir-specification--Text-format--Grammar"}[written as a type], a
word or a word applied to attributes, that can be written, the reader of a
type reads $`\mathrm{tokens}(a)` as $`(a, p_0)` before any token but `(`,
up to positions:

$$`\mathrm{reads}_{\mathrm{erase}}(\mathrm{readtype}, \mathrm{tokens}(a), (a, p_0), \overline{\texttt{(}})`

Here $`\overline{\texttt{(}}` is the set of every token but `(`, and
$`p_0` the empty position. The reader of a type takes only a word or an
applied word, so the condition on $`a` is needed.
:::

:::readable Fir.Text.readAttrs_reads (pin := Fir.Text.readAttrs) (pin := Fir.Text.Tok.startsAttr) (fingerprint := "12773071372742214260")
*Theorem: the attributes of an op or an item read back.* For every list of
attributes $`a_1, \dots, a_n`, the reader of attributes reads
$`\mathrm{tokens}(a_1)~\dots~\mathrm{tokens}(a_n)` as
$`a_1, \dots, a_n`, without their positions, before any token that starts
no attribute and is not `(`: any token but a word, an integer, a string, a
symbol or `(`.

That reader reads as long as an attribute starts, so the token after the
list must start none, and must not be the `(` that would apply the last
word.
:::
