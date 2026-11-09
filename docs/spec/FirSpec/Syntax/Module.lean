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

:::moduleDocs (fingerprint := "1086758024943119589")
:::

:::readable Fir.Name (pin := Fir.Func.Valid) (fingerprint := "9078334971116599343")
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

:::readable Fir.isLetter Fir.isWordStart Fir.isNameChar Fir.isName Fir.isWord (pin := Fir.Func.Valid) (pin := Fir.Text.printSymbol) (fingerprint := "7311467072228554417")
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

:::readable Fir.Operation Fir.Block Fir.Region (pin := Fir.Func.OpValid) (pin := Fir.Func.Valid) (fingerprint := "7685077818017998768")
*Definition: operations, blocks and regions.* An _operation_ is one use of
an op in a block: it names the op's results, gives its op instance, names
its operands, and holds its successors, regions and location reference. A
block is a label, typed arguments and a list of operations. A region is a
list of blocks. The three are defined together, since an op may own
regions:

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
blocks \{\mathsf{blocks}~\mathit{block}^*\}
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
  dialect has one, and validation requires every op to own none, so in fir
  today the field is always empty. It is part of every op so that a dialect
  with regions needs no new syntax.
* $`\mathsf{loc}` is the reference of the op's location, which every op
  has.

For example, the text `%acc1: i32 = add nsw %acc, %i @3` is the op whose
results are $`(\mathit{acc1} : \mathsf{i32})`, whose op instance is
$`\mathsf{add}_{32}~\mathsf{nsw}`, whose operands are $`\mathit{acc}~i`,
with no successors, no regions and the location reference 3.

A block's $`\mathsf{params}` are its arguments, and its $`\mathsf{body}`
its operations. The first block of a region is its _entry_. Every op has
this one shape, whatever its dialect, so that a dialect adds ops without
new syntax (ADR-2026-10-29-2016), and a function is a control-flow graph of
blocks (ADR-2026-10-29-2005). What makes these terms well formed is
{ref "The-fir-specification--Validation--The-general-rules"}[validation]:
among other rules, every block holds at least one op, and its last op, and
only that one, is a terminator.
:::

:::readable Fir.Func (pin := Fir.Func.Valid) (pin := Fir.Func.print) (fingerprint := "10507048764927280219")
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
braces, and with no arrow when it returns nothing.

The parameters are the arguments of the entry block, the first block of
$`\mathsf{body}`;
{ref "The-fir-specification--Validation--The-general-rules"}[validation]
requires the entry block to declare none of its own. A function is
isolated from above (ADR-2026-10-29-2011): nothing
in it refers to a value outside it, and it reaches other functions only by
their symbols (ADR-2026-10-29-2012). So a function can be checked, run and
transformed on its own.
:::

:::readable Fir.Item (fingerprint := "991640758304694106")
*Definition: an item.* An item is one entry of a module. Today every item
is a function:

```grammar Fir.Item
\mathit{item}
func \mathsf{func}~\mathit{func}
```

A module is a table of symbols, and fir must let such tables nest, as a
device module inside a host module would (ADR-2026-10-29-2016). A nested
module, a global or an external declaration would each be a new kind of
item, and a new alternative here. How dialects add kinds of item is not
decided yet, so fir defines only functions.
:::

:::readable Fir.Module Fir.Module.funcs (pin := Fir.Module.Valid) (pin := Fir.Module.print) (pin := Fir.LocTable.print) (fingerprint := "10891783193603547263")
*Definition: a module.* A module is its items, then its
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table]:

```grammar Fir.Module
\mathit{module}
items,locs \begin{array}{l} \{\mathsf{items}~\mathit{item}^*, \\ \enspace \mathsf{locs}~(r = \mathit{loc})^*\,\} \end{array}
```

In text, the items come first and the table, `locs { … }`, ends the module.
$`\mathrm{funcs}(M)` is the sequence of the functions of the module $`M`,
in order: the $`\mathit{func}` of each item $`\mathsf{func}~\mathit{func}`.

A module is the unit that fir validates, runs and prints.
{ref "The-fir-specification--Validation--The-general-rules"}[Validation]
requires each symbol to name one function, the location table to be well
formed, and each function to be valid in the context of the module.
:::
