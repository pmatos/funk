import VersoManual
import Fir.Text.Tokens
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on lexing printed text, which renders
`Fir.Text.Tokens` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Lexing printed text: readable blocks" =>

:::readable Fir.Text.Tok.spell (pin := Fir.Text.printSymbol) (pin := Fir.printLocRef) (pin := Fir.Text.printInt) (pin := Fir.Text.quote) (pin := Nat.toDigits) (fingerprint := "6725213110965772062")
*Definition: the spelling of a token.* Every
{ref "The-fir-specification--Text-format--The-parser"}[token] $`t` has one
spelling, $`\mathrm{spell}(t)`, the text that the printer writes for it:

* $`\mathsf{value}~x` is spelled `%` then $`x`, and $`\mathsf{label}~\ell`
  is spelled `^` then $`\ell`;
* $`\mathsf{sym}~s` is spelled `@` then $`s` when $`s` is a
  {ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[word],
  and `@` then $`s` quoted otherwise;
* $`\mathsf{locref}~r` (`locRef` in the Lean) is spelled `@` then the
  decimal digits of $`r`;
* $`\mathsf{word}~w` is spelled $`w`;
* $`\mathsf{int}~i` is spelled with the decimal digits of $`i`, after `-`
  when $`i` is negative;
* $`\mathsf{str}~s` is spelled $`s` quoted: between two `"`, each
  character in the one spelling that the
  {ref "The-fir-specification--Text-format--Tokens"}[token grammar] gives
  it inside a string;
* each punctuation token is spelled as itself, from `(` to `->`;
* $`\mathsf{eof}` is spelled as the empty text $`\epsilon`: the end of the
  text has no characters.

Digits are written with no leading zero. The proof that the lexer reads a
printed module back compares what it reads with these spellings, so each
token needs exactly one.
:::

:::readable Fir.Text.Tok.Writable (pin := Fir.isName) (pin := Fir.isWord) (pin := Fir.Location.limit) (fingerprint := "11058920808801410295")
*Definition: a token that can be written.* A token $`t` _can be written_,
$`\mathrm{writable}(t)`, in these cases:

* $`\mathsf{value}~x` and $`\mathsf{label}~\ell` when $`x` and $`\ell`
  are
  {ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[names],
  one or more name characters;
* $`\mathsf{word}~w` when $`w` is a word;
* $`\mathsf{locref}~r` when $`r < 2^{32}`;
* $`\mathsf{eof}` never, since the printer does not write it;
* every other token always: every symbol, integer, string and punctuation
  token.

A module stores names as plain strings, so a value could be named `a b`;
printed, it would read back as two tokens. The proofs that follow assume
that every token of a module can be written, and the last of these
sections,
{ref "The-fir-specification--Text-format--Writable-tokens"}[writable tokens],
shows that every well-formed module meets this.
:::

:::readable Fir.Attr.tokens Fir.Attr.tokens.tokensList (fingerprint := "15613669296790130417")
*Definition: the tokens of an attribute.* The tokens of an
{ref "The-fir-specification--Text-format--Grammar"}[attribute], or of a
type, which is written as one, are:

$$`\begin{aligned} \mathrm{tokens}(\mathsf{word}~w) &= \mathsf{word}~w \\ \mathrm{tokens}(\mathsf{int}~i) &= \mathsf{int}~i \\ \mathrm{tokens}(\mathsf{str}~s) &= \mathsf{str}~s \\ \mathrm{tokens}(\mathsf{sym}~s) &= \mathsf{sym}~s \end{aligned}`

$$`\begin{aligned} & \mathrm{tokens}(\mathsf{app}~h~(a_1, \dots, a_n)) = \\ & \quad \mathsf{word}~h~\texttt{(}~\mathrm{tokens}(a_1)~\texttt{,}~\dots \\ & \quad \texttt{,}~\mathrm{tokens}(a_n)~\texttt{)} \end{aligned}`

Sequences of tokens are written side by side, as in the WebAssembly
specification: $`u~v` is the tokens $`u` followed by the tokens $`v`, and
a token stands for the sequence that holds it alone. The arguments of an
application are separated by $`\texttt{,}`, and an application with no
argument is $`\mathsf{word}~h~\texttt{(}~\texttt{)}`.

This section gives the tokens of every construct in the order that the
printer writes them, so that the printed text of a construct can be
compared with a list of tokens and its layout set aside.
:::

:::readable Fir.Location.tokens (fingerprint := "12101892751819525192")
*Definition: the tokens of a location.* The tokens of a
{ref "The-fir-specification--Abstract-syntax--Locations"}[location], as
the location table writes it:

$$`\begin{aligned} & \mathrm{tokens}(\mathsf{unknown}) = \mathsf{word}~\mathtt{unknown} \\ & \mathrm{tokens}(\mathsf{range}~\mathit{file}~l_1~c_1~l_2~c_2) = \\ & \quad \mathsf{str}~\mathit{file}~\texttt{:}~\mathsf{int}~l_1~\texttt{:}~\mathsf{int}~c_1 \\ & \quad \mathsf{word}~\mathtt{to}~\mathsf{int}~l_2~\texttt{:}~\mathsf{int}~c_2 \\ & \mathrm{tokens}(\mathsf{name}~n) = \\ & \quad \mathsf{word}~\mathtt{name}~\texttt{(}~\mathsf{str}~n~\texttt{)} \end{aligned}`

$$`\begin{aligned} & \mathrm{tokens}(\mathsf{callsite}~r_1~r_2) = \mathsf{word}~\mathtt{callsite} \\ & \quad \texttt{(}~\mathsf{locref}~r_1~\mathsf{word}~\mathtt{at}~\mathsf{locref}~r_2~\texttt{)} \\ & \mathrm{tokens}(\mathsf{fused}~r_1 \dots r_n) = \mathsf{word}~\mathtt{fused} \\ & \quad \texttt{(}~\mathsf{locref}~r_1~\texttt{,}~\dots~\texttt{,}~\mathsf{locref}~r_n~\texttt{)} \\ & \mathrm{tokens}(\mathsf{derived}~r) = \mathsf{word}~\mathtt{derived} \\ & \quad \texttt{(}~\mathsf{locref}~r~\texttt{)} \end{aligned}`
:::

:::readable Fir.defTokens Fir.defsTokens Fir.Succ.tokens (fingerprint := "9307918518628726768")
*Definition: the tokens of definitions and successors.* For every dialect
with a {ref "The-fir-specification--Text-format--Grammar"}[text format],
which writes each of its types as an attribute $`\mathrm{attr}(T)`:

* a definition $`x : T` of a value has the tokens
  $`\mathsf{value}~x~\texttt{:}~\mathrm{tokens}(\mathrm{attr}(T))`;
* a list of definitions has the tokens of each definition, separated by
  $`\texttt{,}`;
* a successor $`\ell(a_1, \dots, a_n)` has the tokens
  $`\mathsf{label}~\ell`, followed, when $`n > 0`, by
  $`\texttt{(}~\mathsf{value}~a_1~\texttt{,}~\dots~\texttt{,}~\mathsf{value}~a_n~\texttt{)}`.
:::

:::readable Fir.Operation.tokens Fir.Region.tokensList Fir.Block.tokensList Fir.Operation.tokensList (fingerprint := "41541705136619067")
*Definition: the tokens of ops, regions and blocks.* For every dialect with
a text format, an op with results $`d^*`, op instance $`o`, operands
$`x_1, \dots, x_m`, successors $`s_1, \dots, s_k`, regions and location
reference $`r` has, in order:

* when it has results, the tokens of the definitions $`d^*`, then
  $`\texttt{=}`;
* $`\mathsf{word}~\mathrm{name}(o)`, then the tokens of each attribute of
  $`o`, where $`\mathrm{name}(o)` and the attributes are what the dialect
  writes for $`o`;
* when $`m + k > 0`, the uses $`\mathsf{value}~x_1, \dots, \mathsf{value}~x_m`
  and the tokens of $`s_1, \dots, s_k`, separated by $`\texttt{,}`;
* the tokens of each of its regions;
* $`\mathsf{locref}~r`.

A region has the tokens $`\texttt{\{}`, then the tokens of its blocks, then
$`\texttt{\}}`. A block labelled $`\ell` has $`\mathsf{label}~\ell`, then,
when it has arguments, $`\texttt{(}`, the tokens of their definitions and
$`\texttt{)}`; then $`\texttt{:}` and the tokens of its ops, one after the
other. The four are defined together, since ops hold regions, which hold
blocks of ops.
:::

:::readable Fir.Func.tokens Fir.Item.tokens (fingerprint := "11368144789468871078")
*Definition: the tokens of a function and of an item.* For every dialect
with a text format, a function with symbol $`f`, parameters $`p^*`, result
types $`T_1, \dots, T_n` and blocks has the tokens:

$$`\begin{aligned} & \mathsf{word}~\mathtt{func}~\mathsf{sym}~f~\texttt{(}~\mathrm{tokens}(p^*)~\texttt{)} \\ & \quad \mathit{res}~\texttt{\{}~\mathrm{tokens}(\mathit{blocks})~\texttt{\}} \end{aligned}`

where $`\mathit{res}` is empty when $`n = 0`, and otherwise
$`\texttt{->}` followed by the tokens of $`\mathrm{attr}(T_1), \dots, \mathrm{attr}(T_n)`,
separated by $`\texttt{,}`. An item, which is a function, has the tokens of
its function.
:::

:::readable Fir.LocTable.tokens Fir.Module.tokens (fingerprint := "16307846641236868949")
*Definition: the tokens of the location table and of a module.* The
location table with entries $`r_1 = \mathit{loc}_1, \dots, r_n = \mathit{loc}_n`
has the tokens:

$$`\begin{aligned} & \mathsf{word}~\mathtt{locs}~\texttt{\{} \\ & \quad \mathsf{locref}~r_1~\texttt{=}~\mathrm{tokens}(\mathit{loc}_1)~\dots \\ & \quad \mathsf{locref}~r_n~\texttt{=}~\mathrm{tokens}(\mathit{loc}_n)~\texttt{\}} \end{aligned}`

For every dialect with a text format, a module has the tokens of each of
its items, in order, then the tokens of its location table. This is the
list that the lexer must read back from the printed module.
:::
