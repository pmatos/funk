import VersoManual
import Fir.Text.Read
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on reading the grammar, which renders
`Fir.Text.Read` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Reading the grammar: readable blocks" =>

:::moduleDocs (fingerprint := "12529259913768732986")
:::

:::readable Fir.Text.SDef (fingerprint := "2461358331634527445")
*Definition: a definition as written.* A definition `%x: T` is read as the
record:

```grammar Fir.Text.SDef
\mathit{sdef}
name,pos,ty,tyPos \begin{array}{l} \{\mathsf{name}~x,~\mathsf{pos}~p, \\ \enspace \mathsf{ty}~a,~\mathsf{ty\_pos}~q\,\} \end{array}
```

As in the
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[abstract syntax],
$`\{\mathsf{f}_1~A_1, \dots\}` is a record, with a field $`\mathsf{f}_i`
that holds an $`A_i` for each $`i`. Here $`x` is the value's name and $`p` its
{ref "The-fir-specification--Text-format--Round-trips"}[position],
$`a` the type as written, an
{ref "The-fir-specification--Text-format--Grammar"}[attribute], and $`q`
the type's position ($`\mathsf{ty\_pos}` is `tyPos` in the Lean). Decoding
rejects a type, or a value defined twice, at these positions.
:::

:::readable Fir.Text.SOp Fir.Text.SBlock Fir.Text.SRegion (fingerprint := "8449572933258008816")
*Definition: ops, blocks and regions as written.* An op, a block and a
region are read as these records, before any op is decoded:

```grammar Fir.Text.SOp
\mathit{sop}
results,name,namePos,attrs,operands,succs,regions,loc \begin{array}{l} \{\mathsf{results}~\mathit{sdef}^*, \\ \enspace \mathsf{name}~n,~\mathsf{name\_pos}~p, \\ \enspace \mathsf{attrs}~a^*, \\ \enspace \mathsf{operands}~(x, q)^*, \\ \enspace \mathsf{succs}~\mathit{succ}^*, \\ \enspace \mathsf{regions}~\mathit{sregion}^*, \\ \enspace \mathsf{loc}~r\,\} \end{array}
```

```grammar Fir.Text.SBlock
\mathit{sblock}
label,params,ops \begin{array}{l} \{\mathsf{label}~\ell, \\ \enspace \mathsf{params}~\mathit{sdef}^*, \\ \enspace \mathsf{ops}~\mathit{sop}^*\,\} \end{array}
```

```grammar Fir.Text.SRegion
\mathit{sregion}
kind,blocks \{\mathsf{kind}~k^?,~\mathsf{blocks}~\mathit{sblock}^*\}
```

An op keeps its results as written, its name $`n` with its position $`p`
($`\mathsf{name\_pos}` is `namePos` in the Lean), its attributes, each operand
$`x` with its position $`q`, its
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[successors],
its regions and its location reference $`r`. A block keeps its label, its
arguments as written and its ops; a region, the kind it names, if any, and
its blocks. Nothing here
depends on the dialect: the name and attributes of an op stay as written
until decoding.
:::

:::readable Fir.Text.SItem Fir.Text.SBody (fingerprint := "9276016701394299529")
*Definition: an item, and its body, as written.* An item is read as the
record below, and its body as blocks, or as a dialect set and items:

```grammar Fir.Text.SItem
\mathit{sitem}
kind,kindPos,name,params,paramAttrs,variadic,results,resultAttrs,attrs,body \begin{array}{l} \{\mathsf{kind}~k, \\ \enspace \mathsf{kind\_pos}~p, \\ \enspace \mathsf{name}~s, \\ \enspace \mathsf{params}~\mathit{sdef}^*, \\ \enspace \mathsf{param\_attrs}~((a, q)^*)^*, \\ \enspace \mathsf{variadic}~q^?, \\ \enspace \mathsf{results}~(a, q)^*, \\ \enspace \mathsf{result\_attrs}~((a, q)^*)^*, \\ \enspace \mathsf{attrs}~(a, q)^*, \\ \enspace \mathsf{body}~\mathit{sbody}\,\} \end{array}
```

```grammar Fir.Text.SBody
\mathit{sbody}
blocks \mathsf{blocks}~\mathit{sblock}^*
items  \mathsf{items}~\mathit{name}^*~\mathit{sitem}^*
```

An item keeps its kind $`k`, a word, with its position $`p`
($`\mathsf{kind\_pos}` is `kindPos` in the Lean), its symbol $`s`, its
parameters, the attributes after each parameter's type, the position of
the `...` that ends its parameters, if they end in it, each result type,
the attributes after each result's type but the last's, and its
attributes, each attribute $`a` with its position $`q`
($`\mathsf{param\_attrs}` and $`\mathsf{result\_attrs}` are
`paramAttrs` and `resultAttrs` in the Lean). The attributes after the last
result's type start its attributes: the grammar cannot tell them apart,
and decoding says whose they are. Its body is its blocks, or the dialect set and the items that it
holds; an empty body is no blocks. A `func` with blocks and a `module` with
a dialect set and items decode; the tree reads other kinds so that a later
kind needs no change to this step.
:::

:::readable Fir.Text.SModule (fingerprint := "2899039248715767664")
*Definition: a module as written.* A module is read as its dialect set,
the names it writes after the word `dialects`, then the entries of its data
layout, each attribute it writes after the word `layout` with its position,
then its items, then its
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table],
which has a fixed syntax and is read in full:

```grammar Fir.Text.SModule
\mathit{smodule}
dialects,layout,items,locs \begin{array}{l} \{\mathsf{dialects}~\mathit{name}^*, \\ \enspace \mathsf{layout}~(a, p)^*, \\ \enspace \mathsf{items}~\mathit{sitem}^*, \\ \enspace \mathsf{locs}~\mathit{table}\,\} \end{array}
```
:::

:::readable Fir.Text.After Fir.Text.Read Fir.Text.Read1 Fir.Text.After.here Fir.Text.After.next Fir.Text.After.then (fingerprint := "10570741050628781982")
*Definition: what a reader returns.* A reader takes the tokens that are
left, and returns what it read with the tokens after it, or the first
error. The tokens after it are a suffix of the tokens it was given, never
more, and a reader that reads at least one token returns strictly fewer.
The three helpers say so for reading nothing, for a token read by hand, and
for one reader after another. These bounds are what make the readers, which
call one another, end.
:::

:::readable Fir.Text.fail Fir.Text.expect Fir.Text.keyword Fir.Text.readMore (fingerprint := "6965504618080113712")
*Definition: the readers that the others are built from.* A reader that
expects one thing and finds a token $`t` fails at the position of $`t`,
with the reason "expected" the thing, "found" $`t`. Every list of tokens
ends with $`\mathsf{eof}`, so there is always a token to blame; on no
tokens at all, the reader fails at line 1, column 1, having "found the end
of the text". The
reader of one token, such as `(`, reads it or fails; the reader of a
keyword, such as `to`, reads that word. The reader of the rest of a list
reads a comma and an element with a given reader, as long as a comma
follows: the elements after the first of a list separated by commas.
:::

:::readable Fir.Text.readAttr Fir.Text.readAttrArgs Fir.Text.readMoreAttrArgs Fir.Text.readType Fir.Text.Tok.startsAttr Fir.Text.readAttrs (fingerprint := "9760399790842598158")
*Definition: reading attributes and types.* An attribute is a word
followed by `(`, which is the word applied to the attributes that follow,
up to `)` and separated by commas; or a word, an integer, a float literal,
a string or a symbol, which is that attribute; or else an error, "expected an
attribute". In an applied attribute, a token other than a comma or `)`
after an argument is an error.

A type is read in the same way, but only from a word or a word applied to
attributes; anything else is an error, "expected a type". The reader of
the attributes of an op or an item reads attributes, each with its
position, as long as the next token is a word, an integer, a float
literal, a string or a symbol.
:::

:::readable Fir.Text.readDefType Fir.Text.readDef Fir.Text.readDefs (fingerprint := "320528512199189741")
*Definition: reading definitions.* A definition is a value token, then
`:`, then a type, and is read with the positions of the value and of the
type. A list of definitions is one or more of them, separated by commas.
:::

:::readable Fir.Text.readSuccArgs Fir.Text.readSucc Fir.Text.readMoreOperands Fir.Text.readOperands Fir.Text.readOpLoc (fingerprint := "6159597756254706277")
*Definition: reading operands, successors and the location reference.* A
successor is a label, followed, when `(` follows it, by one or more values
that it passes, separated by commas, and `)`. An op's operands
and successors are read together, separated by commas: first the operands,
each a value with its position, as long as a comma and a value follow;
then the successors. An op may have operands only, successors only, both
or neither. Last comes the op's location reference; any other token there
is an error, "expected the op's location reference".
:::

:::readable Fir.Text.readKind Fir.Text.readBlocks Fir.Text.readOps Fir.Text.readOpWithResults Fir.Text.readOpBody Fir.Text.readRegions (fingerprint := "11848995529020059096")
*Definition: reading blocks, ops and regions.* These readers call one
another, since an op may own regions:

* Blocks are read as long as a label follows: the label, then its
  arguments in parentheses when `(` follows, then `:`, then its ops.
* Ops are read as long as one starts: with a value, the first of its
  results, or with a word, the name of an op without results.
* An op with results reads its definitions, separated by commas, then `=`,
  then its name, a word.
* The rest of an op is its attributes, then its operands and successors,
  then its regions, then its location reference.
* Regions are read as long as `{` follows: the region's kind, then its
  blocks, then `}`. A word right after the `{` is the region's kind, and
  no word there is the core's kind; a block starts with a label, so the
  two never meet.
:::

:::readable Fir.Text.readDialectName Fir.Text.readDialects (fingerprint := "11638523870589205576")
*Definition: reading a dialect set.* When the tokens start with the word
`dialects`, the set is the word after it, then each word after a comma, as
long as a comma follows; a token after `dialects` or after a comma that is
not a word is an error, "expected the name of a dialect". Otherwise the set
is empty, and nothing is read. A set starts a module, and a body of items
(ADR-2026-11-10-1510). A set that names no dialect is not written, so this
reads nothing of it.
:::

:::readable Fir.Text.readLayout (pin := Fir.Text.readType) (fingerprint := "7093527520123102893")
*Definition: reading a data layout.* When the tokens start with the word
`layout`, the layout is the type after it, with its position, then each
type after a comma, as long as a comma follows; each entry is read as a
type, a word or a word applied to attributes, and decoding says whether it
is an entry. Otherwise the layout is empty, and nothing is read. A layout
follows a module's dialect set, and a body of items has none.
:::

:::readable Fir.Text.readParam Fir.Text.readMoreParams Fir.Text.readParams Fir.Text.readResult (fingerprint := "13469694055812550233")
*Definition: reading parameters and results.* A parameter is a definition,
then the attributes after it. An item's parameters are `...` alone, or one
or more parameters separated by commas, which may end in `, ...`; the
reader keeps the position of the `...`. A result is a type, then the
attributes after it.
:::

:::readable Fir.Text.readItems Fir.Text.readItem (fingerprint := "13976377462153773885")
*Definition: reading items.* Items are read as long as a word, the item's
kind, follows; at the top of the module, the word `locs` starts the
location table instead. An item is its kind, then its symbol, then its
parameters in parentheses, which may be none, then, when `->` follows, one
or more results separated by commas, then its attributes, then its
body in braces. The attributes read with the last result start the item's
attributes. The body is a dialect set and items when it starts with a
word, and blocks otherwise.
:::
