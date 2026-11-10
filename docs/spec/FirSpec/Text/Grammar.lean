import VersoManual
import Fir.Text.Grammar
import Fir.Text.Print
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the grammar, which renders
`Fir.Text.Grammar` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it. The grammar of a module opens the section.
-/

#doc (Manual) "Grammar: readable blocks" =>

:::moduleDocs (fingerprint := "16983865337719427217")
:::

A module is written by the grammar below, in the tokens of the
{ref "The-fir-specification--Text-format--Tokens"}[previous section], with
whitespace and comments between them. Words and punctuation in typewriter
type stand for themselves, and a row that starts with neither $`::=` nor
$`\mid` continues the row above it.

$$`\begin{array}{rcl} \mathit{module} & ::= & \mathit{item}^*~\mathit{locs} \\ \mathit{item} & ::= & \mathit{word}~\mathit{symbol}~\texttt{(}~\mathit{defs}^?~\texttt{)} \\ & & (\texttt{->}~\mathit{types})^?~\mathit{attr}^* \\ & & \texttt{\{}~\mathit{body}~\texttt{\}} \\ \mathit{body} & ::= & \mathit{block}^* \mid \mathit{item}^* \\ \mathit{block} & ::= & \mathit{label}~(\texttt{(}~\mathit{defs}~\texttt{)})^?~\texttt{:}~\mathit{op}^* \\ \mathit{op} & ::= & (\mathit{defs}~\texttt{=})^?~\mathit{word}~\mathit{attr}^* \\ & & \mathit{operands}^?~\mathit{region}^*~\mathit{locref} \\ \mathit{operands} & ::= & \mathit{value}~(\texttt{,}~\mathit{value})^* \\ & & (\texttt{,}~\mathit{succ})^* \\ & \mid & \mathit{succ}~(\texttt{,}~\mathit{succ})^* \\ \mathit{succ} & ::= & \mathit{label}~(\texttt{(}~\mathit{values}~\texttt{)})^? \\ \mathit{values} & ::= & \mathit{value}~(\texttt{,}~\mathit{value})^* \\ \mathit{region} & ::= & \texttt{\{}~\mathit{word}^?~\mathit{block}^*~\texttt{\}} \\ \mathit{defs} & ::= & \mathit{def}~(\texttt{,}~\mathit{def})^* \\ \mathit{def} & ::= & \mathit{value}~\texttt{:}~\mathit{type} \\ \mathit{types} & ::= & \mathit{type}~(\texttt{,}~\mathit{type})^* \\ \mathit{type} & ::= & \mathit{word} \mid \mathit{word}~\texttt{(}~\mathit{attrs}^?~\texttt{)} \\ \mathit{attrs} & ::= & \mathit{attr}~(\texttt{,}~\mathit{attr})^* \\ \mathit{attr} & ::= & \mathit{word} \mid \mathit{int} \mid \mathit{string} \\ & \mid & \mathit{symbol} \mid \mathit{word}~\texttt{(}~\mathit{attrs}^?~\texttt{)} \\ \mathit{locs} & ::= & \texttt{locs}~\texttt{\{}~\mathit{entry}^*~\texttt{\}} \\ \mathit{entry} & ::= & \mathit{locref}~\texttt{=}~\mathit{location} \\ \mathit{location} & ::= & \texttt{unknown} \\ & \mid & \mathit{string}~\texttt{:}~\mathit{nat}~\texttt{:}~\mathit{nat} \\ & & \texttt{to}~\mathit{nat}~\texttt{:}~\mathit{nat} \\ & \mid & \texttt{name}~\texttt{(}~\mathit{string}~\texttt{)} \\ & \mid & \texttt{callsite}~\texttt{(}~\mathit{locref} \\ & & \texttt{at}~\mathit{locref}~\texttt{)} \\ & \mid & \texttt{fused}~\texttt{(}~\mathit{locrefs}^?~\texttt{)} \\ & \mid & \texttt{derived}~\texttt{(}~\mathit{locref}~\texttt{)} \\ \mathit{locrefs} & ::= & \mathit{locref}~(\texttt{,}~\mathit{locref})^* \end{array}`

:::readable Fir.Attr (pin := Fir.Attr.print) (fingerprint := "2420144201630043887")
*Definition: an attribute, or a type, as written.* The grammar writes the
attributes of ops and items, and every type, as one kind of generic term:

```grammar Fir.Attr
\mathit{attr}
word \mathsf{word}~w
int  \mathsf{int}~i
str  \mathsf{str}~s
sym  \mathsf{sym}~s
app  \mathsf{app}~h~\mathit{attr}^*
```

Here $`w`, $`h` and $`s` are strings and $`i` an integer; $`w` and $`h`
can be written only when they are words, as the next blocks say. In text,
$`\mathsf{word}~w` is written $`w`, such as `nsw` or `i32`;
$`\mathsf{int}~i` is the integer $`i`; $`\mathsf{str}~s` is the string
$`s`, quoted; $`\mathsf{sym}~s` is a reference to the symbol $`s`, such as
`@sum`; and $`\mathsf{app}~h~a_1 \dots a_n` is the word $`h` applied to the
attributes $`a_1, \dots, a_n`, written `h(a₁, …, aₙ)`, such as
`vec(4, i32)`.

The core dialect does not use the applied form. It is there so that other
dialects can write structured attributes and types without a change to the
grammar. A word applied to no attributes, `h()`, is not the word `h`.
:::

:::readable Fir.Attr.repr Fir.Attr.reprList (fingerprint := "1789584298090586371")
*Definition: how Lean shows an attribute.* For tests and debugging, Lean
shows an attribute as the Lean term that builds it. This is written out by
hand, since the one Lean would derive is not proved to terminate (Lean marks it
partial), and no definition of the spec is partial (ADR-2026-10-30-1452). It plays no part
in the text format.
:::

:::readable Fir.Attr.Writable Fir.Attr.AllWritable (pin := Fir.isWord) (fingerprint := "17382987230614626094")
*Definition: an attribute that can be written.* An attribute can be
written as tokens when each word in it is a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[word]:

* $`\mathsf{word}~w` can be written when $`w` is a word;
* $`\mathsf{int}~i`, $`\mathsf{str}~s` and $`\mathsf{sym}~s` can always be
  written: a symbol whose name is not a word is quoted;
* $`\mathsf{app}~h~a_1 \dots a_n` can be written when $`h` is a word and
  each of $`a_1, \dots, a_n` can be written.

A list of attributes can be written when each of them can. A module whose
attributes cannot all be written has no text that reads back to it, so the
round trip asks this of every attribute that a dialect writes.
:::

:::readable Fir.Attr.IsType (fingerprint := "1425367503421061705")
*Definition: an attribute that is written as a type.* The attribute $`a`
is written as a type when it is $`\mathsf{word}~w` or
$`\mathsf{app}~h~a_1 \dots a_n`, and it can be written. An integer, a
string or a symbol is never a type. This is the grammar's
$`\mathit{type} ::= \mathit{word} \mid \mathit{word}~\texttt{(}~\mathit{attrs}^?~\texttt{)}`,
which the parser reads where a type stands.
:::

:::readable Fir.DialectText (fingerprint := "7609871035768420774")
*Definition: how a dialect writes its ops and types.* A
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect] that has
a text gives five functions:

* $`\mathrm{opname}(o)`, the name of the op instance $`o`, such as
  `add`;
* $`\mathrm{opattrs}(o)`, its attributes, such as the flag `nsw`;
* $`\mathrm{decodeop}(n, a^*, t^*, r^*)`, the op instance with the name
  $`n` and the attributes $`a^*` whose operands have the types $`t^*` and
  whose results have the types $`r^*`, which may be undefined when the
  dialect has no such op instance;
* $`\mathrm{tyattr}(t)`, the attribute that writes the type $`t`;
* $`\mathrm{decodety}(a)`, the type that the attribute $`a` writes, which
  may be undefined.

The parser reads an op back with $`\mathrm{decodeop}`, from what the text
shows of it: its name and attributes, and the types written where its
operands and results are defined. The parser has no code for any op of any
dialect beyond these functions.
:::

:::readable Fir.LawfulDialectText (pin := Fir.DialectSignature) (pin := Fir.DialectValidation) (fingerprint := "13427652001501799506")
*Definition: a dialect whose text is lawful.* Let $`d` be a dialect with its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature], which
gives each op instance $`o` its operand types $`\mathrm{sig}(o)` and its
result types $`\mathrm{ret}(o)`, its
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation rules],
which say which of its types are valid, and its text. The text of $`d` is
_lawful_ when seven laws hold, for every op instance $`o`, every type $`t`,
every name $`n`, every attribute $`a` and all lists $`a^*`, $`t^*` and
$`r^*`:

1. decoding what was encoded gives the op instance back:

   $$`\begin{aligned} \mathrm{decodeop}(&\mathrm{opname}(o), \mathrm{opattrs}(o), \\ &\mathrm{sig}(o), \mathrm{ret}(o)) = o \end{aligned}`

2. an op instance decodes only from its own spelling: if
   $`\mathrm{decodeop}(n, a^*, t^*, r^*) = o`, then $`\mathrm{opname}(o) = n`,
   $`\mathrm{opattrs}(o) = a^*`, $`\mathrm{sig}(o) = t^*` and
   $`\mathrm{ret}(o) = r^*`;
3. every valid type reads back: if $`t` is valid,
   $`\mathrm{decodety}(\mathrm{tyattr}(t)) = t`;
4. a type decodes only from its own spelling: if
   $`\mathrm{decodety}(a) = t`, then $`\mathrm{tyattr}(t) = a`;
5. $`\mathrm{opname}(o)` is a word;
6. every attribute of $`\mathrm{opattrs}(o)` can be written;
7. if $`t` is valid, $`\mathrm{tyattr}(t)` is written as a type.

The first four make each op instance and each valid type have exactly one
spelling. A type that is not valid, such as a core integer type wider
than 16,777,215, need not read back. The last three say that what the dialect writes
fits the grammar. With them, every valid module of the dialect is well
formed, and the round trip, proved in the sections that follow, rests on
these laws alone, for every dialect.
:::
