import VersoManual
import Fir.Validation.Rules
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the general rules, which renders
`Fir.Validation.Rules` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The general rules: readable blocks" =>

:::moduleDocs (fingerprint := "14819655843938608632")
:::

:::readable Fir.ModuleContext (fingerprint := "12420361802815271715")
*Definition: the context of a function.* A function is checked in the
context of its module, and the rules read two things of the module: its
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table],
and the references that its
{ref "The-fir-specification--Abstract-syntax--Locations"}[location table]
has. A _module context_ $`C` holds them: $`\mathrm{symtab}_C(s)` is the
function type of the symbol $`s`, or is undefined, and $`\mathrm{locs}_C`
is the list of the table's references.
:::

:::readable Fir.Func.SuccValid (pin := Fir.Func.entryLabel?) (pin := Fir.Func.block?) (pin := Fir.Func.typeOf) (fingerprint := "15074293607687035826")
*Definition: a valid successor.* A successor $`l(x_1, \dots, x_n)`,
written `^l(%x1, …, %xn)` in the text, names the label $`l` of the block
that a branch goes to and the values $`x_1, \dots, x_n` that it passes to
that block's arguments. It is valid in the function $`f` when:

$$`\dfrac{\begin{array}{c} \mathrm{entry}(f) \neq l \qquad \mathrm{block}_f(l) = b \\ \mathrm{args}(b) = (y_1 : t_1) \dots (y_m : t_m) \\ n = m \qquad \mathrm{type}_f(x_k) = t_k \text{ for each } k \end{array}}{f \vdash l(x_1, \dots, x_n)~\text{valid}}`

Here $`\mathrm{entry}(f)` is the label of the
{ref "The-fir-specification--Validation--Dominance"}[entry block] of $`f`
(the premise holds when $`f` has none), $`\mathrm{block}_f(l)` the first
top-level block with the label $`l`, $`\mathrm{args}(b)` the arguments
that $`b` declares, and $`\mathrm{type}_f(x)` the type of the value $`x`.

So a branch passes one value of the right type for each argument of its
target (ADR-2026-10-29-2010). No branch may go to the entry block: it has
no predecessors, and its arguments are the function's parameters.
:::

:::readable Fir.Func.RegionsValid (pin := Fir.DialectValidation) (fingerprint := "6570281988972527310")
*Definition: the valid regions of an op.* Let $`o` be an op of the
function $`f`, checked in the module context $`C`, let $`p` be its op
instance, and let $`d` be the dialect. The regions of $`o` are valid when:

$$`\dfrac{\begin{array}{c} \mathrm{regions}(o) = r_1 \dots r_n \qquad \mathrm{kinds}(p) = k_1 \dots k_n \qquad \mathrm{kind}(r_j) = k_j \\ \mathrm{isword}(k_j) \qquad k_j \in \mathrm{kinds}_d \qquad (\mathrm{symtab}_C), \mathrm{id}, f \vdash_d r_j : k_j~\text{valid} \ \text{ for each } j \end{array}}{C, f \vdash \mathrm{regions}(o)~\text{valid}}`

In words: the op owns one region for each kind that its op instance
states, in order, each region names that kind, the kind is a word that the
dialect registers, and the region obeys the rule of its kind, in the
context of the module's symbol table and through the identity view. A kind
is a word of a dialect, never the core's, so an op that owns a region of
the core's kind, or any region when its op instance states none, is
invalid. No core op states a region, so a core op that owns one is invalid
(ADR-2026-11-10-1941).
:::

:::readable Fir.Func.RegionsValid.noCoreRegion Fir.Func.regionsValid_of_nil (fingerprint := "11311767626596888277")
*Theorems: valid regions of an op.* An op whose regions are valid owns no
region of the core's kind, since each of its regions names a kind. And an
op that owns no region, of an op instance that states none, has valid
regions: every core op that owns no region.
:::

:::readable Fir.Func.OpValid (pin := Fir.Operation.uses) (pin := Fir.DialectSignature) (fingerprint := "16606214502766472009")
*Definition: a valid op.* Let $`o` be the op at index $`i` of the block
$`b` of the function $`f`, checked in the module context $`C`, let $`l`
be the label of $`b`, let $`p` be its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[op instance], and
let $`d` be the dialect of $`p`. The op is valid when every premise of this
rule holds:

$$`\dfrac{\begin{array}{c} C, f \vdash \mathrm{regions}(o)~\text{valid} \\ \mathrm{type}_f(\mathrm{operands}(o)) = \mathrm{sig}(p) \\ \mathrm{results}(o) = (y : t)^* \qquad t^* = \mathrm{ret}(p) \\ \mathrm{term}(p) \iff i + 1 = |\mathrm{body}(b)| \\ |\mathrm{succs}(o)| = \mathrm{nsucc}(p) \\ \neg\,\mathrm{term}(p) \implies \mathrm{succs}(o) = \epsilon \\ f \vdash s~\text{valid} \ \text{ for each } s \in \mathrm{succs}(o) \\ \mathrm{inscope}_f(x, l, i) \text{ for each } x \in \mathrm{uses}(o) \\ \mathrm{symtab}_C(g) \text{ defined, each } g \in \mathrm{refs}_d(p) \\ (\mathrm{symtab}_C, \mathrm{results}(f)) \vdash_d p~\text{valid} \\ \mathrm{loc}(o) \in \mathrm{locs}_C \end{array}}{C, f, b, i \vdash o~\text{valid}}`

Here $`\mathrm{regions}(o)`, $`\mathrm{operands}(o)`, $`\mathrm{results}(o)`,
$`\mathrm{succs}(o)` and $`\mathrm{loc}(o)` are the parts of the op
$`o`, $`\mathrm{body}(b)` is the ops of $`b`, $`\mathrm{results}(f)` is the
result types of $`f`, and $`\mathrm{type}_f(\mathrm{operands}(o))` is the
type of each operand, in turn. In words, the premises say:

* Its regions are valid, by the rule for the valid regions of an op above:
  they have the kinds that its op instance states, and each obeys the rule
  of its kind. No core op states a region.
* Its operands are values that $`f` defines, with the types
  $`\mathrm{sig}(p)` that the op instance takes, as many as it takes.
* Its results have the types $`\mathrm{ret}(p)` that the op instance gives.
* It is a terminator, $`\mathrm{term}(p)`, exactly when it is the last op of
  its block.
* It has as many successors as its op instance says,
  $`\mathrm{nsucc}(p)`, and none at all when it is not a terminator,
  whatever its dialect says.
* Each successor is valid, by the rule for a valid successor above.
* Each value it uses, an operand or a value passed to a successor, is
  {ref "The-fir-specification--Validation--Dominance"}[in scope] at the op.
* Each symbol it refers to names a function of the module.
* Its dialect's own rule holds, in the op context of the module's symbol
  table and the result types of $`f`.
* Its location reference is a key of the module's location table
  (ADR-2026-10-29-2013).

$`\mathrm{sig}`, $`\mathrm{ret}`, $`\mathrm{term}` and $`\mathrm{nsucc}` are
the dialect's
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] of an op
instance: its operand types, its result types, whether it is a terminator,
and its number of successors. $`\mathrm{refs}_d` and
$`\vdash_d` are what the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[dialect adds to validation].
:::

:::readable Fir.Func.InnerOpValid Fir.Operation.innerOps (fingerprint := "9676253623755961838")
*Definition: a valid op inside a region.* An op inside a region of an op
of the function $`f` is checked by the general rules that do not depend on
the kind of its region. Let $`o` be such an op, $`p` its op instance and
$`d` the dialect. It is valid in the module context $`C` when:

$$`\dfrac{\begin{array}{c} C, f \vdash \mathrm{regions}(o)~\text{valid} \\ \mathrm{type}_f(\mathrm{operands}(o)) = \mathrm{sig}(p) \\ \mathrm{results}(o) = (y : t)^* \qquad t^* = \mathrm{ret}(p) \\ |\mathrm{succs}(o)| = \mathrm{nsucc}(p) \qquad \neg\,\mathrm{term}(p) \implies \mathrm{succs}(o) = \epsilon \\ \mathrm{isname}(l) \text{ and } \mathrm{type}_f(x^*) \text{ defined, each } l(x^*) \in \mathrm{succs}(o) \\ \mathrm{symtab}_C(g) \text{ defined, each } g \in \mathrm{refs}_d(p) \\ (\mathrm{symtab}_C, \mathrm{results}(f)) \vdash_d p~\text{valid} \qquad \mathrm{loc}(o) \in \mathrm{locs}_C \end{array}}{C, f \vdash o~\text{valid inside}}`

These are the premises of a
valid op, but for three that the kind of the region decides: where the op
may stand in its block, where its successors go, and which values it may
use. A successor still names a block by a name, and passes values that
$`f` defines. The rule of the region's kind says the rest. The ops inside
the regions of an op, $`\mathrm{inner}(o)`, are the ops of each block of
each of its regions, and not deeper.
:::

:::readable Fir.Block.InRegionOf Fir.Block.InRegionOf.mono Fir.Block.mem_allBlocks Fir.Region.mem_allBlocks_cases Fir.Block.mem_allBlocks_cases Fir.Operation.mem_regionBlocks_cases Fir.Func.mem_allBlocks_cases (pin := Fir.Func.allBlocks) (fingerprint := "12115075447680226974")
*Theorems: where a block of a function sits.* A block $`b` is _in a region
of_ a list of blocks $`L` when some op of some block of $`L` owns a region
that holds $`b`. Every block of a list is among its blocks at any depth.
And every block of $`\mathrm{allblocks}(f)` is a block of the body of $`f`,
or a block in a region of $`\mathrm{allblocks}(f)`. So every op of a
function at any depth is an op of its body, or an op inside a region of an
op of the function, and the rules below cover each op once.
:::

:::readable Fir.Func.inner_of_noRegions (fingerprint := "14527961165736990592")
*Theorem: no region, no op inside one.* When no op of $`f` owns a region,
at any depth, every op inside a region of $`f` is valid: there is none.
:::

:::readable Fir.Func.Valid (pin := Fir.isName) (pin := Fir.isNameChar) (pin := Fir.isWordStart) (pin := Fir.isLetter) (pin := Fir.Func.types) (fingerprint := "15276493308517073629")
*Definition: a valid function.* The function $`f` is valid in the module
context $`C` when every premise of this rule holds, where
$`B = \mathrm{blocks}(f)` and $`d` is the dialect of $`f`:

$$`\dfrac{\begin{array}{c} \mathrm{kind}(\mathrm{body}(f)) = \epsilon \\ B = e~b^* \qquad \mathrm{args}(e) = \epsilon \\ \mathrm{reachable}_f(\mathrm{label}(b)) \ \text{ for each } b \in B \\ \text{the labels of } B \text{ are distinct} \\ \text{the names of } \mathrm{defs}(f) \text{ are distinct} \\ \mathrm{isname}(x) \ \text{ for each value name } x \\ \text{in } \mathrm{defs}(f) \text{ and each label } x \\ \text{of a block in } \mathrm{allblocks}(f) \\ \vdash_d t~\text{valid} \ \text{ for each } t \in \mathrm{types}(f) \\ \mathrm{body}(b) \neq \epsilon \ \text{ for each } b \in B \\ C, f, b, i \vdash o~\text{valid for each } b \in B \\ \text{and each op } o \text{ at an index } i \text{ of } b \\ C, f \vdash o'~\text{valid inside for each } o' \in \mathrm{inner}(o) \\ \text{and each op } o \text{ of a block of } \mathrm{allblocks}(f) \\ (\mathrm{symtab}_C), \mathrm{id} \vdash_d f~\text{valid} \end{array}}{C \vdash f~\text{valid}}`

In words:

* The body is a region of the core's kind, a control-flow graph
  (ADR-2026-10-29-2005): it names no kind (ADR-2026-11-10-1530).
* The body has an entry block $`e`, and $`e` declares no arguments of its
  own: its arguments are the function's parameters.
* Every block is reachable from the entry (ADR-2026-10-30-0817). This is
  stricter than LLVM, which accepts blocks the entry cannot reach.
* No two top-level blocks share a label, and no two definitions share a
  name: each value has one definition, as SSA requires.
* Every value name and every label, at any depth, is spelled with name
  characters: $`\mathrm{isname}(x)` holds when $`x` is a
  {ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[name],
  one or more of the ASCII letters, the digits, `_` and `.`. So every valid
  function can be written in the text.
* Every type that the function states, its result types and the type of
  every definition, is valid for its dialect.
* Every block holds at least one op, and every op is valid.
* Every op inside a region of an op, at any depth, is valid inside it, by
  the general rules; the rule of the region's kind, which the valid regions
  of its owner ask for, says the rest.
* The function obeys its dialect's
  {ref "The-fir-specification--Validation--Scope-and-symbols"}[own rule over a whole function],
  in the context of the module's symbol table and through the identity view.

A function's symbol may be any string: the text quotes it when it is not a
word.
:::

:::readable Fir.Location.WellFormed Fir.LocTable.Valid (pin := Fir.LocTable.InLimits) (pin := Fir.Location.numbers) (pin := Fir.Location.limit) (pin := Fir.Location.refs) (fingerprint := "11508244414306764901")
*Definition: a well-formed location and a valid location table.* A
{ref "The-fir-specification--Abstract-syntax--Locations"}[location] is
_well formed_ when:

* it is a source range $`\text{file}:l_1:c_1~\mathsf{to}~l_2:c_2` with
  $`1 \le l_1`, and either $`l_1 < l_2`, or $`l_1 = l_2` and
  $`c_1 = 0 \vee c_2 = 0 \vee c_1 \le c_2`;
* it is $`\mathsf{fused}(r^*)` with at least two references in $`r^*`;
* or it is of any other kind.

A column of 0 is unknown, so it places no condition, and an end equal to
the start is an empty range.

A location table $`(r_1 = \mathit{loc}_1) \dots (r_n = \mathit{loc}_n)` is
_valid_ when:

* its references increase, $`r_1 < r_2 < \dots < r_n`, so each is unique and
  one table has one spelling;
* the reference of every entry, every reference that its location is built
  from, and every line and column of a range are below $`2^{32}`, so every
  implementation can hold them in 32 bits;
* every entry is well formed;
* every reference $`r` that the location $`\mathit{loc}_k` is built from,
  by $`\mathsf{callsite}`, $`\mathsf{fused}` or $`\mathsf{derived}`, is
  below $`r_k` and is the reference of an entry of the table. Since the
  references increase, that entry comes before it, so no location refers
  to itself, directly or not.
:::

:::readable Fir.DialectItem.Valid (pin := Fir.isDialectWord) (pin := Fir.DialectItem.types) (fingerprint := "16285291260031980")
*Definition: a valid item of a dialect's kind.* The
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[item]
$`i` of a dialect's kind is valid in the function context $`C` when every
premise of this rule holds, where $`d` is the dialect:

$$`\dfrac{\begin{array}{c} \mathrm{isdialectword}(\mathrm{kind}(i)) \qquad \mathrm{kind}(i) \in \mathrm{itemkinds}_d \\ \mathrm{isname}(x) \ \text{ for each parameter } x \text{ of } i \\ \text{the names of the parameters of } i \text{ are distinct} \\ \vdash_d t~\text{valid} \ \text{ for each } t \in \mathrm{types}(i) \\ \text{each attribute of } i \text{ can be written} \\ C, \mathrm{id} \vdash_d i~\text{valid} \end{array}}{C \vdash i~\text{valid}}`

In words: its kind is a word of a dialect, a word that holds a `.`, and
the dialect registers it; its parameters are named by distinct names; every
type it states, its parameters' and its results', is valid for the dialect;
every attribute can be written as a token; and the item obeys the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[dialect's rule]
for its kind, through the identity view (ADR-2026-11-09-1543). The dialect
reads its kinds by name, so a sum of dialects sends the item to the
dialect that registers its kind.
:::

:::readable Fir.Module.context Fir.SymbolTable.context Fir.SymbolTable.Valid Fir.Module.Valid (fingerprint := "17696861027737048487")
*Definition: a valid symbol table and a valid module.* The context of the
module $`M`, $`\mathrm{ctx}(M)`, is its symbol table $`\mathrm{symtab}_M`
and the references of its location table. A module holds a
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
at each level of nesting: its own, and that of each module nested in it
(ADR-2026-11-10-1510). In a module whose location table has the references
$`K`, the context of the table $`T`, $`\mathrm{ctx}_K(T)`, is the symbol
table of the functions of $`T`, $`\mathrm{symtab}_T`, and $`K`. The table
$`T` is valid in $`K` when:

$$`\dfrac{\begin{array}{c} \text{the symbols of } \mathrm{items}(T) \text{ are distinct} \\ \mathrm{ctx}_K(T) \vdash f~\text{valid} \\ \text{for each } f \in \mathrm{funcs}(T) \\ (\mathrm{symtab}_T) \vdash i~\text{valid} \\ \text{for each } i \in \mathrm{ditems}(T) \\ \text{the names of } \mathrm{dialects}(T) \text{ are distinct words} \end{array}}{K \vdash T~\text{valid}}`

and $`M` is valid when its location table is, and each of its tables is:

$$`\dfrac{\begin{array}{c} \mathrm{locs}(M) \text{ is a valid table} \\ \mathrm{keys}(M) \vdash T~\text{valid} \\ \text{for each } T \in \mathrm{tables}(M) \end{array}}{\vdash M~\text{valid}}`

Here $`\mathrm{items}(T)` is the items of $`T`, functions, nested modules
and items of a dialect's kind, $`\mathrm{funcs}(T)` its functions,
$`\mathrm{ditems}(T)` its items of a dialect's kind, each checked in the
function context of the symbols of $`T`, and $`\mathrm{dialects}(T)` its
dialect set, all in order; $`\mathrm{locs}(M)` is the location table of
$`M`, $`\mathrm{keys}(M)` its references, and $`\mathrm{tables}(M)` the
tables of $`M`, its own first. One location table serves every table.

A symbol names one item of its table, of whatever kind, so a function, a
module and an item of a dialect's kind never share a symbol of one table; a nested module
may reuse a symbol of its parent's table, since it is a table of its own.
Each function is checked against the symbols of its own table, so a call
names a function of its own table: never one of a nested module, of its
parent, or a module. Since symbols are distinct, the symbol table gives
each symbol the type of its one function, and a call names exactly one
callee. Which dialects a table's set may name, and that the words of its
functions keep to it, is the rule of
{ref "The-fir-specification--Sums-of-dialects--A-module___s-dialect-set"}[a module's dialect set],
which reads words through the dialect's text.
:::

:::readable Fir.Module.Valid.table Fir.Module.Valid.funcs Fir.Module.Valid.symbolsUnique Fir.Module.Valid.dialectNames Fir.Module.Valid.dialectsUnique (fingerprint := "14505164559828351400")
*Theorem: what a valid module's own table gives.* For every valid module
$`M`, its own table is valid in $`\mathrm{keys}(M)`. So each function of
$`M` is valid in $`\mathrm{ctx}(M)`, the functions of $`M` have distinct
symbols, and the names of $`\mathrm{dialects}(M)` are distinct words. The
chapters on the text and on execution read a valid module through these,
and look only at its own functions.
:::

:::readable Fir.Module.valid_of_flat (fingerprint := "12487538470488893174")
*Theorem: a module with no nested module.* A module $`M` whose items are
all functions has one table, its own. So $`M` is valid when the symbols of
its items are distinct, its location table is valid, each of its functions
is valid in $`\mathrm{ctx}(M)`, and the names of $`\mathrm{dialects}(M)`
are distinct words. The tests prove their modules valid this way.
:::

:::readable Fir.TypesValid (fingerprint := "4327058517537719696")
*Definition: an op instance with valid types.* The op instance $`p` has
_valid types_ when each of its operand types $`\mathrm{sig}(p)` and each of
its result types $`\mathrm{ret}(p)` is valid for its dialect:

$$`\dfrac{\begin{array}{c} \vdash_d t~\text{valid for each } t \in \mathrm{sig}(p) \\ \vdash_d t~\text{valid for each } t \in \mathrm{ret}(p) \end{array}}{\mathrm{typesvalid}(p)}`

It reads no context: it is a property of the op instance alone, where the
dialect's op rule also reads the symbol table and the function's result
types. Every op of a valid function has an op instance with valid types,
since the rules check its operand and result types against the types of
the values it uses and defines. The
{ref "The-fir-specification--Execution--What-the-lawful-class-gives"}[poison obligations]
speak only of such op instances (ADR-2026-10-29-2006).
:::
