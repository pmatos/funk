import VersoManual
import Fir.Syntax.Module
import Fir.Validation.Rules
import Fir.Text.Lexical
import Fir.Text.Print
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on modules, functions, blocks and ops,
which renders `Fir.Syntax.Module` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails when
the Lean changes under it.
-/

#doc (Manual) "Modules, functions, blocks and ops: readable blocks" =>

:::moduleDocs (fingerprint := "13439674276831334999")
:::

:::readable Fir.Name (pin := Fir.Func.Valid) (fingerprint := "11509972817217138124")
*Definition: the strings that refer to values, labels and symbols.* In
the syntax trees of a program, a value, a block label and a symbol are each
referred to by a string, stored without its sigil: the value `%x`, the label
`^loop` and the symbol `@f` of the text are stored as `x`, `loop` and `f`.
The Lean calls this string `Name`. The strings are stored as the producer
wrote them (ADR-2026-10-29-2014), and a program refers to a value only by
its string: which value the string stands for, and its type, are rules of
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation].
Validation restricts the strings of values and labels to the names defined
next; a symbol may be any string.
:::

:::readable Fir.isLetter Fir.isWordStart Fir.isNameChar Fir.isName Fir.isWord (pin := Fir.Func.Valid) (pin := Fir.Text.printSymbol) (fingerprint := "18103268847858425710")
*Definition: names and words.* A _name_ is one or more name characters,
and a _word_ is a name that starts with a letter or an underscore:

$$`\begin{array}{rcl} \mathit{letter} & ::= & \mathtt{A} \mid \dots \mid \mathtt{Z} \\ & \mid & \mathtt{a} \mid \dots \mid \mathtt{z} \\ \mathit{start} & ::= & \mathit{letter} \mid \mathtt{\_} \\ \mathit{char} & ::= & \mathit{start} \mid \mathtt{.} \\ & \mid & \mathtt{0} \mid \dots \mid \mathtt{9} \\ \mathit{name} & ::= & \mathit{char}~\mathit{char}^* \\ \mathit{word} & ::= & \mathit{start}~\mathit{char}^* \end{array}`

Here $`\mathit{char}` is a name character, and $`\mathit{start}` a
character that may start a word. The letters and digits are those of
ASCII. So `0` and `acc.1` are names, and `acc.1` is a word but `0` is not.
The Lean gives each class as a test on characters or strings: `isLetter`,
`isWordStart`, `isNameChar`, `isName` and `isWord`.

These classes decide what the text can write.
{ref "The-fir-specification--Validation--The-general-rules"}[Validation]
requires the string of every value and every label of a function to be a
name, so that every valid module can be written. A symbol may be any
string: the text writes it bare after `@` when it is a word, and quoted
otherwise.
:::

:::readable Fir.isDialectWord Fir.isWord_of_isDialectWord (fingerprint := "848065248179675490")
*Definition: a word of a dialect.* A word of a dialect other than the
core is a word that holds a `.`, such as `toy.cell`; the part before its
first `.` names its dialect. Every word of a dialect is a word. The kinds
of item that dialects register are such words (ADR-2026-11-10-2224), so
none of them is `func` or `module`, which are the core's, nor a word that
the grammar reserves, such as `dialects` or `locs`.
:::

:::readable Fir.Text.isHexDigit Fir.FloatLit Fir.FloatLit.valid (pin := Fir.FloatLit.print) (fingerprint := "11904308684752133396")
*Definition: a float literal, as written.* A hexadecimal digit is a
decimal digit or one of the lowercase letters `a` to `f`; uppercase letters
are not digits. A float literal is one of two kinds (ADR-2026-11-11-1438):

* $`\mathsf{dec}~s~w~f~x`, a decimal: `-` when the sign $`s` is set, the
  natural number $`w`, `.`, the digits $`f` as they are written, and then,
  when there is an exponent $`x`, `e` and $`x`, as in `-1.5e-7`;
* $`\mathsf{hex}~\mathit{ds}`, `0x` and the digits $`\mathit{ds}` as they
  are written, as in `0x7fc00000`.

Leading zeros of $`f` and of $`\mathit{ds}` are part of the literal. A
literal can be written when its fraction is one or more decimal digits, or
its hexadecimal digits are one or more hexadecimal digits. Which literals
spell a value of a float type is the
{ref "The-fir-specification--Text-format--Float-constants-in-text"}[core dialect's rule].
:::

:::readable Fir.Attr (pin := Fir.Attr.print) (fingerprint := "5017374719707371876")
*Definition: an attribute, or a type, as written.* The grammar writes the
attributes of ops and items, and every type, as one kind of generic term:

```grammar Fir.Attr
\mathit{attr}
word \mathsf{word}~w
int  \mathsf{int}~i
str  \mathsf{str}~s
sym  \mathsf{sym}~s
app  \mathsf{app}~h~\mathit{attr}^*
float \mathsf{float}~l
```

Here $`w`, $`h` and $`s` are strings and $`i` an integer; $`w` and $`h`
can be written only when they are words, as the next blocks say. In text,
$`\mathsf{word}~w` is written $`w`, such as `nsw` or `i32`;
$`\mathsf{int}~i` is the integer $`i`; $`\mathsf{str}~s` is the string
$`s`, quoted; $`\mathsf{sym}~s` is a reference to the symbol $`s`, such as
`@sum`; and $`\mathsf{app}~h~a_1 \dots a_n` is the word $`h` applied to the
attributes $`a_1, \dots, a_n`, written `h(a₁, …, aₙ)`, such as
`vec(4, i32)`; and $`\mathsf{float}~l` is the float literal $`l`, such as
`1.5` or `0x7fc00000`.

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

:::readable Fir.Attr.Writable Fir.Attr.AllWritable (pin := Fir.isWord) (pin := Fir.FloatLit.valid) (fingerprint := "995596476100570680")
*Definition: an attribute that can be written.* An attribute can be
written as tokens when each word in it is a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[word]:

* $`\mathsf{word}~w` can be written when $`w` is a word;
* $`\mathsf{int}~i`, $`\mathsf{str}~s` and $`\mathsf{sym}~s` can always be
  written: a symbol whose name is not a word is quoted;
* $`\mathsf{app}~h~a_1 \dots a_n` can be written when $`h` is a word and
  each of $`a_1, \dots, a_n` can be written.
* $`\mathsf{float}~l` can be written when the literal $`l` can.

A list of attributes can be written when each of them can. A module whose
attributes cannot all be written has no text that reads back to it, so the
round trip asks this of every attribute that a dialect writes.
:::

:::readable Fir.Succ (pin := Fir.Func.SuccValid) (pin := Fir.Succ.print) (fingerprint := "16157009433262250404")
*Definition: a successor.* A successor of a terminator is a block that
control may go to, with the values that it passes to that block's
arguments:

```grammar Fir.Succ
\mathit{succ}
label,args \{\mathsf{label}~\ell,~\mathsf{args}~x^*\}
```

As in the WebAssembly specification, $`\{\mathsf{f}_1~A_1, \dots\}` is a
record, with a field $`\mathsf{f}_i` that holds an $`A_i` for each $`i`.
Here and below, $`\ell` is a block label and $`x` a value name. In text,
the successor is written `^ℓ(%x, …)`, or `^ℓ` when it passes no values.

Blocks take arguments instead of φ-nodes (ADR-2026-10-29-2010): a jump
passes one value for each argument of its target, and the target's
arguments receive them.
{ref "The-fir-specification--Validation--The-general-rules"}[Validation]
requires a successor to name a block of its function other than the entry
block, the first block of the function, and to pass one value of the right
type for each of that block's arguments.
:::

:::readable Fir.Operation Fir.Block Fir.Region (pin := Fir.Func.OpValid) (pin := Fir.Func.Valid) (fingerprint := "2216873348528431298")
*Definition: operations, blocks and regions.* An _operation_ is one use of
an op in a block: it names the op's results, gives its op instance, names
its operands, and holds its successors, regions and location reference. A
block is a label, typed arguments and a list of operations. A region is
its kind and a list of blocks. The three are defined together, since an op
may own regions:

```grammar Fir.Operation
\mathit{operation}
results,op,operands,succs,regions,loc \begin{array}{l} \{\mathsf{results}~(x : t)^*, \\ \enspace \mathsf{op}~o, \\ \enspace \mathsf{operands}~x^*, \\ \enspace \mathsf{succs}~\mathit{succ}^*, \\ \enspace \mathsf{regions}~\mathit{region}^*, \\ \enspace \mathsf{loc}~r\,\} \end{array}
```

```grammar Fir.Block
\mathit{block}
label,params,body \begin{array}{l} \{\mathsf{label}~\ell, \\ \enspace \mathsf{params}~(x : t)^*, \\ \enspace \mathsf{body}~\mathit{operation}^*\,\} \end{array}
```

```grammar Fir.Region
\mathit{region}
kind,blocks \{\mathsf{kind}~k^?,~\mathsf{blocks}~\mathit{block}^*\}
```

Here $`t` is a type and $`o` an op instance of the
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect], $`r` a
{ref "The-fir-specification--Abstract-syntax--Locations"}[location reference],
and $`(x : t)^*` a sequence of value names, each with its type.

* $`\mathsf{results}` names each result of the op and gives its type.
* $`\mathsf{op}` is the op instance: the op, its attributes and the types it
  is used at.
* $`\mathsf{operands}` are the values that the op uses, by name.
* $`\mathsf{succs}` are its successors. Only terminators have them.
* $`\mathsf{regions}` are the regions that the op owns. No op of the core
  dialect has one. A dialect's op may own regions of the kinds that its op
  instance states, each a kind that a dialect registers with its own rule.
  The field is part of every op so that a dialect with regions needs no new
  syntax.
* $`\mathsf{loc}` is the reference of the op's location, which every op
  has.

For example, the text `%acc1: i32 = add nsw %acc, %i @3` is the op whose
results are $`(\mathit{acc1} : \mathsf{i32})`, whose op instance is
$`\mathsf{add}_{32}~\mathsf{nsw}`, whose operands are $`\mathit{acc}~i`,
with no successors, no regions and the location reference 3.

A block's $`\mathsf{params}` are its arguments, and its $`\mathsf{body}`
its operations. The first block of a region is its _entry_. A region names
its kind (ADR-2026-11-09-1543): no kind, $`k^? = \epsilon`, is the core's
kind, a control-flow graph of blocks whose ops run in order
(ADR-2026-10-29-2005), and a kind $`k` is a word of a dialect, such as
`toy.graph`. The text writes a region's kind as a word right after the
region's `{`, and writes nothing there for the core's kind
(ADR-2026-11-10-1530). Every op has
this one shape, whatever its dialect, so that a dialect adds ops without
new syntax (ADR-2026-10-29-2016), and a function is a control-flow graph of
blocks (ADR-2026-10-29-2005). What makes these terms well formed is
{ref "The-fir-specification--Validation--The-general-rules"}[validation]:
among other rules, every block holds at least one op, and its last op, and
only that one, is a terminator.
:::

:::readable Fir.Func (pin := Fir.Func.Valid) (pin := Fir.Func.print) (fingerprint := "15157222208701719689")
*Definition: a function.* A function is a symbol, typed parameters, the
types of its results, and a region, its body:

```grammar Fir.Func
\mathit{func}
name,params,results,body \begin{array}{l} \{\mathsf{name}~s, \\ \enspace \mathsf{params}~(x : t)^*, \\ \enspace \mathsf{results}~t^*, \\ \enspace \mathsf{body}~\mathit{region}\,\} \end{array}
```

$`s` is the function's symbol, any string. $`\mathsf{params}` are its
parameters, and $`\mathsf{results}` the types of what it returns: any
number of them, none included (ADR-2026-10-30-0816). In text, a function is
written `func @s(%x: t, …) -> t, … { … }`, with its blocks between the
braces, and with no arrow when it returns nothing. Its body is a region of
the core's kind, and its text names no kind: a word after the `{` of an
item starts the items of its body (ADR-2026-11-10-1530).

The parameters are the arguments of the entry block, the first block of
$`\mathsf{body}`;
{ref "The-fir-specification--Validation--The-general-rules"}[validation]
requires the entry block to declare none of its own. A function is
isolated from above (ADR-2026-10-29-2011): nothing
in it refers to a value outside it, and it reaches other functions only by
their symbols (ADR-2026-10-29-2012). So a function can be checked, run and
transformed on its own.
:::

:::readable Fir.DialectItem Fir.DialectItem.types (pin := Fir.DialectItem.print) (fingerprint := "343753791736889547")
*Definition: an item of a dialect's kind.* A dialect registers kinds of
item of its own, as it registers ops, so a new kind needs no new syntax
(ADR-2026-11-10-2224). An item of such a kind holds what the one
production of an item writes, with an empty body:

```grammar Fir.DialectItem
\mathit{ditem}
kind,name,params,results,attrs \begin{array}{l} \{\mathsf{kind}~k,~\mathsf{name}~s, \\ \enspace \mathsf{params}~(x : t)^*, \\ \enspace \mathsf{results}~t^*, \\ \enspace \mathsf{attrs}~\mathit{attr}^*\,\} \end{array}
```

$`k` is its kind, a word of a dialect such as `toy.cell`, and $`s` its
symbol, any string. Its attributes are the generic terms above, which the
dialect's rule for the kind reads, and say what a function's header cannot.
In text it is written `k @s(%x: t, …) -> t, … a … {`, then `}` on the next
line. $`\mathrm{types}(i)` is the types it states: its parameters' types,
then its results.
:::

:::readable Fir.Item Fir.Item.name Fir.Item.func? Fir.Item.func?_func Fir.Item.func?_module Fir.Item.func?_dialect Fir.Item.dialect? (fingerprint := "2482776140988760982")
*Definition: an item.* An item is one entry of a module: a function, a
module nested in it (ADR-2026-11-10-1510), or an item of a kind that a
dialect registers (ADR-2026-11-10-2224):

```grammar Fir.Item
\mathit{item}
func \mathsf{func}~\mathit{func}
module \mathsf{module}~s~\mathit{name}^*~\mathit{item}^*
dialect \mathsf{dialect}~\mathit{ditem}
```

A module is a table of symbols, and fir lets such tables nest, as a device
module inside a host module does (ADR-2026-10-29-2016). A nested module
$`\mathsf{module}~s~x^*~i^*` has the symbol $`s`, its own dialect set
$`x^*` and its own items $`i^*`. Its set is its own, not its parent's, and
so are its symbols: an op refers by symbol only to an item of its own
table. In text it is written `module @s() { … }`, with its dialect set and
its items between the braces.

The symbol of an item, $`\mathrm{sym}(i)`, is the symbol of its function,
of its module or of its item of a dialect's kind. $`\mathrm{func?}(i)` is
the function $`f` when $`i` is $`\mathsf{func}~f`, and none otherwise;
$`\mathrm{dialect?}(i)` is the item $`d` when $`i` is
$`\mathsf{dialect}~d`, and none otherwise.
:::

:::readable Fir.Module Fir.Module.funcs (pin := Fir.Module.Valid) (pin := Fir.Module.print) (pin := Fir.LocTable.print) (fingerprint := "2006544800862020226")
*Definition: a module.* A module is its dialect set, its items, then its
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table]:

```grammar Fir.Module
\mathit{module}
dialects,items,locs \begin{array}{l} \{\mathsf{dialects}~\mathit{name}^*, \\ \enspace \mathsf{items}~\mathit{item}^*, \\ \enspace \mathsf{locs}~(r = \mathit{loc})^*\,\} \end{array}
```

The dialect set names the dialects other than the core whose words the
module writes; the core is in every module's set and is never named, and a
module whose set is empty uses the core alone. In text, the dialect set
comes first, when it names a dialect, then the items, and the table,
`locs { … }`, ends the module. One table serves every item, however deeply
it is nested.
$`\mathrm{funcs}(M)` is the sequence of the functions of the module $`M`,
in order: the $`\mathit{func}` of each item $`\mathsf{func}~\mathit{func}`.
The functions of a nested module are not among them: they are in its own
table.

A module is the unit that fir validates, runs and prints.
{ref "The-fir-specification--Validation--The-general-rules"}[Validation]
requires the location table to be well formed and each symbol table of the
module, its own and each nested module's, to be valid: each symbol names
one item of its table, and each function, and each item of a dialect's
kind, is valid in the context of its table.
:::
