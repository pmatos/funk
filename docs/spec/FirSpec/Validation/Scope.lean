import VersoManual
import Fir.Validation.Scope
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on scope and symbols, which renders
`Fir.Validation.Scope` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Scope and symbols: readable blocks" =>

:::moduleDocs (fingerprint := "7805917909892943464")
:::

:::readable Fir.Func.blocks Fir.Region.allBlocks Fir.Block.allBlocks Fir.Operation.regionBlocks Fir.Func.allBlocks (fingerprint := "1386367292862605520")
*Definition: the blocks of a function, at the top level and at any depth.*
The body of a
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[function]
$`f` is a region, a list of blocks. $`\mathrm{blocks}(f)` is that list, in
order, and its first block is the _entry block_ of $`f`.

An op may own regions, and the blocks of a region hold ops that may own
regions in turn. $`\mathrm{allblocks}(f)` lists every block of $`f` at any
depth: each block of the body, followed by the blocks nested in the regions
of its ops, depth first, and then the next block of the body.

Validation needs both lists. The control-flow graph, reachability and
dominance are about $`\mathrm{blocks}(f)`, the blocks that branches connect.
Names and their types are about $`\mathrm{allblocks}(f)`, so that a value
defined in a nested block still has one type. The two lists differ only
when an op owns a region, and no op of a valid function owns one yet.
:::

:::readable Fir.Block.defs Fir.Func.defs Fir.Func.typeOf Fir.Func.types (fingerprint := "16013911283360544923")
*Definition: the values a function defines, and their types.* A block
defines its arguments, then the results of its ops, in order. Each
definition is a pair $`x : t` of a value name and a type.
$`\mathrm{defs}(f)` is every definition of the function $`f`: its
parameters, then the definitions of each block of $`\mathrm{allblocks}(f)`,
in order.

$`\mathrm{type}_f(x)` is the type $`t` of the first definition $`x : t` in
$`\mathrm{defs}(f)`, and is undefined when $`f` defines no value named
$`x`. In a valid function every name has one definition, so "first" never
has to choose. The rules compare the types of the values an op uses with
$`\mathrm{type}_f`, so a value's type is written once, where it is defined.

$`\mathrm{types}(f)` is every type that the text of $`f` states: its result
types, then the type of each definition in $`\mathrm{defs}(f)`. Validation
asks each of them to be a valid type of the dialect.
:::

:::readable Fir.Func.block? (fingerprint := "8147301483788728811")
*Definition: the block with a label.* $`\mathrm{block}_f(l)` is the first
block of $`\mathrm{blocks}(f)` whose label is $`l`, and is undefined when
no block has that label. Only the top-level blocks count, since a branch
goes to a block of the same region. A successor names its target block by
label, and the rules find the target's arguments with
$`\mathrm{block}_f`.
:::

:::readable Fir.Operation.uses (fingerprint := "10050251926013518687")
*Definition: the values an op uses.* $`\mathrm{uses}(o)` is the operands of
the op $`o`, then the values it passes to its successors, in order. A
branch that passes $`x` to a block's argument uses $`x` as an operand
does, so the scope rule checks both.
:::

:::readable Fir.FuncType Fir.Func.type (fingerprint := "10799256863940444083")
*Definition: function types.* A function type gives the types of what a
function takes and of what it returns, any number of each, none included.

```grammar Fir.FuncType
\mathit{functype}
params,results   t^* \to r^*
```

The type of a function $`f`, $`\mathrm{type}(f)`, is $`t^* \to r^*`, where
$`t^*` are the types of its parameters, in order, and $`r^*` its result
types. A call is checked against it.
:::

:::readable Fir.Module.symbols (fingerprint := "7243029118963471953")
*Definition: the symbol table.* An op never holds a function: it names one
by its symbol, such as `@f` in the text, and the module's symbol table says what the
symbol stands for. $`\mathrm{symtab}_M(s)` is the type of the first function
of the module $`M` whose symbol is $`s`, and is undefined when no function
of $`M` has that symbol.

$$`\mathrm{symtab}_M(s) = \mathrm{type}(g)`

where $`g` is the first function of $`M` with the symbol $`s`.

A valid module has one function for each symbol. A call is valid only when
the symbol table gives its symbol the type the call states.
:::

:::readable Fir.OpContext (fingerprint := "11106651158325661476")
*Definition: the context of an op.* A dialect's rule for an op may look at
two things beyond the op itself, and at nothing else: the module's symbol
table, and the result types of the function that holds the op. An _op
context_ $`C` holds them: $`\mathrm{symtab}_C(s)` gives the function type
of the symbol $`s`, or is undefined, and $`\mathrm{results}_C` is the list
of result types. The core dialect reads the first for $`\mathsf{call}` and
the second for $`\mathsf{ret}`.
:::

:::readable Fir.FuncContext Fir.DialectView Fir.DialectView.id (fingerprint := "5122442552274979552")
*Definition: what a function rule sees.* A dialect's rule over a whole
function reads the module's symbol table, and nothing else of the module: a
_function context_ holds that table.

A function may hold the ops of several dialects, and a rule about a value
must count the uses of that value by all of them. So the dialect $`d` sees
a function of a dialect $`h` that holds it through a _view_: a map from
the ops of $`h` to those of $`d`, and a map from the types of $`h` to those
of $`d`. Each map gives nothing for an op or a type of another dialect. The
operands and the results of such an op stay visible. A dialect sees its own
functions through the identity view.
:::

:::readable Fir.DialectValidation (fingerprint := "14691305273018662797")
*Definition: what a dialect adds to validation.* The general rules of the
next sections hold for every
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect]. Each
dialect $`d` adds four things of its own:

* which of its types are valid, written $`\vdash_d t~\text{valid}`;
* $`\mathrm{refs}_d(\mathit{op})`, the symbols that the op instance
  $`\mathit{op}` refers to; validation checks that each one names a
  function of the module;
* its own rule for an op instance in an op context, written
  $`C \vdash_d \mathit{op}~\text{valid}`, beyond the general rules;
* its own rule for a whole function in a function context and through a
  view, written $`C, v \vdash_d f~\text{valid}`, for what no rule of one
  op can state, such as a value that must be used exactly once.
  Validation calls this rule on every function, also on one that breaks
  other rules, so the rule assumes nothing about the function.

The {ref "The-fir-specification--Validation--Core-rules"}[core rules] give
these for the core dialect: for example, $`\mathsf{ret}` must return the
function's result types, and $`\mathsf{call}` must match its callee's type.
The core dialect has no rule over a whole function.
:::
