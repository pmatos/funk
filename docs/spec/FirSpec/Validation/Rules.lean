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

:::moduleDocs (fingerprint := "14621842834150240363")
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

:::readable Fir.Func.OpValid (pin := Fir.Operation.uses) (pin := Fir.DialectSignature) (fingerprint := "5008303483154810361")
*Definition: a valid op.* Let $`o` be the op at index $`i` of the block
$`b` of the function $`f`, checked in the module context $`C`, let $`l`
be the label of $`b`, let $`p` be its
{ref "The-fir-specification--Abstract-syntax--Dialects"}[op instance], and
let $`d` be the dialect of $`p`. The op is valid when every premise of this
rule holds:

$$`\dfrac{\begin{array}{c} \mathrm{regions}(o) = \epsilon \\ \mathrm{type}_f(\mathrm{operands}(o)) = \mathrm{sig}(p) \\ \mathrm{results}(o) = (y : t)^* \qquad t^* = \mathrm{ret}(p) \\ \mathrm{term}(p) \iff i + 1 = |\mathrm{body}(b)| \\ |\mathrm{succs}(o)| = \mathrm{nsucc}(p) \\ \neg\,\mathrm{term}(p) \implies \mathrm{succs}(o) = \epsilon \\ f \vdash s~\text{valid} \ \text{ for each } s \in \mathrm{succs}(o) \\ \mathrm{inscope}_f(x, l, i) \text{ for each } x \in \mathrm{uses}(o) \\ \mathrm{symtab}_C(g) \text{ defined, each } g \in \mathrm{refs}_d(p) \\ (\mathrm{symtab}_C, \mathrm{results}(f)) \vdash_d p~\text{valid} \\ \mathrm{loc}(o) \in \mathrm{locs}_C \end{array}}{C, f, b, i \vdash o~\text{valid}}`

Here $`\mathrm{regions}(o)`, $`\mathrm{operands}(o)`, $`\mathrm{results}(o)`,
$`\mathrm{succs}(o)` and $`\mathrm{loc}(o)` are the parts of the op
$`o`, $`\mathrm{body}(b)` is the ops of $`b`, $`\mathrm{results}(f)` is the
result types of $`f`, and $`\mathrm{type}_f(\mathrm{operands}(o))` is the
type of each operand, in turn. In words, the premises say:

* The op owns no region. Region rules come with the first dialect whose
  ops have regions; no core op has one.
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

:::readable Fir.Func.Valid (pin := Fir.isName) (pin := Fir.isNameChar) (pin := Fir.isWordStart) (pin := Fir.isLetter) (pin := Fir.Func.types) (fingerprint := "15966897255941960890")
*Definition: a valid function.* The function $`f` is valid in the module
context $`C` when every premise of this rule holds, where
$`B = \mathrm{blocks}(f)` and $`d` is the dialect of $`f`:

$$`\dfrac{\begin{array}{c} B = e~b^* \qquad \mathrm{args}(e) = \epsilon \\ \mathrm{reachable}_f(\mathrm{label}(b)) \ \text{ for each } b \in B \\ \text{the labels of } B \text{ are distinct} \\ \text{the names of } \mathrm{defs}(f) \text{ are distinct} \\ \mathrm{isname}(x) \ \text{ for each value name } x \\ \text{in } \mathrm{defs}(f) \text{ and each label } x \\ \text{of a block in } \mathrm{allblocks}(f) \\ \vdash_d t~\text{valid} \ \text{ for each } t \in \mathrm{types}(f) \\ \mathrm{body}(b) \neq \epsilon \ \text{ for each } b \in B \\ C, f, b, i \vdash o~\text{valid for each } b \in B \\ \text{and each op } o \text{ at an index } i \text{ of } b \\ (\mathrm{symtab}_C), \mathrm{id} \vdash_d f~\text{valid} \end{array}}{C \vdash f~\text{valid}}`

In words:

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

:::readable Fir.Module.context Fir.Module.Valid (fingerprint := "13918725921862657793")
*Definition: a valid module.* The context of the module $`M`,
$`\mathrm{ctx}(M)`, is its symbol table $`\mathrm{symtab}_M` and the
references of its location table. $`M` is valid when:

$$`\dfrac{\begin{array}{c} \text{the symbols of } \mathrm{funcs}(M) \text{ are distinct} \\ \mathrm{locs}(M) \text{ is a valid table} \\ \mathrm{ctx}(M) \vdash f~\text{valid} \\ \text{for each } f \in \mathrm{funcs}(M) \\ \text{the names of } \mathrm{dialects}(M) \text{ are distinct words} \end{array}}{\vdash M~\text{valid}}`

Here $`\mathrm{funcs}(M)` is the functions of $`M`, in order,
$`\mathrm{locs}(M)` its location table, and $`\mathrm{dialects}(M)` its
dialect set. Which dialects the set may name, and that the words of $`M`
keep to it, is the rule of
{ref "The-fir-specification--Sums-of-dialects--A-module___s-dialect-set"}[a module's dialect set],
which reads words through the dialect's text. Since symbols are distinct, the
symbol table gives each symbol the type of its one function, and a call
names exactly one callee.
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
speak only of such op instances (ADR-2026-11-02-1515).
:::
