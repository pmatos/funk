import VersoManual
import Fir.Execution.RunItems
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the items a run gives each op, which
renders `Fir.Execution.RunItems` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The items a run gives each op: readable blocks" =>

:::moduleDocs (fingerprint := "6344713252701432534")
:::

:::readable Fir.FieldPlace Fir.LayoutPlace Fir.StartAlloc Fir.RunItems Fir.RunItems.empty Fir.RunItems.withAddrs Fir.RunItems.withResolvers (pin := Fir.Memory.Policy.canonical) (pin := Fir.Memory.Resolver.canonical) (fingerprint := "2411160191474670788")
*Definition: the items a run gives each op.* An op may name an item of
its module by its symbol, as `call` names a function. A run gives each
op's rule the items that ops name, beside each memory's layout entry (the
human's ruling of 2026-11-16 on #236). Today these are the
{ref "The-fir-specification--Validation--The-data-layout___s-rules"}[aggregates' layouts]:
$`L.\mathrm{layout}(s)` is the layout with the symbol $`s`, if there is
one, given as its memory, its size, its alignment and its placed fields.
A placed field is its offset $`o`, its step $`t` from one element to the
next, and its count $`c^?` when it is a repeated field, so its element
$`i` starts at $`o + i \cdot t`. The empty record gives no item.

The record also carries the run's
{ref "The-fir-specification--Memory--Address-policies"}[address policy]
for each memory, by its number in the data layout: $`L.\mathrm{addrs}(n)`.
It is no item of the module, and it is the canonical policy unless the run
says otherwise, so the empty record and a module's own items give it. The
spec's runs replace it by every policy in turn
({ref "The-fir-specification--Memory--Runs-under-every-address-policy"}[runs under every policy]):
$`L[\mathrm{addrs} := g]` is $`L` with the policies $`g`.

It carries the run's
{ref "The-fir-specification--Memory--Address-resolvers"}[address resolver]
for each memory too, $`L.\mathrm{resolvers}(n)`, the canonical resolver
unless the run says otherwise, and $`L[\mathrm{resolvers} := k]` is $`L` with
the resolvers $`k`. The spec's runs replace it by each resolver that they
keep.

Last, the record lists the allocations the run starts with,
$`L.\mathrm{starts}`, in order, none unless the run says otherwise. A
starting allocation $`(n, k, \alpha, c, \vec{x})` lives in the memory
that the data layout numbers $`n`: it has the kind $`k`, the alignment
$`\alpha`, it is constant when $`c` is, and $`\vec{x}_u` are its units in
a memory of $`u`-bit units. Each global of the run's table gives one
({ref "The-fir-specification--Memory--The-memories-a-run-starts-with"}[the memories a run starts with]),
and each function another, of the kind `function` (the human's ruling of
2026-11-19 on #235, Q1). With them, $`L.\mathrm{global}(s)` gives where
the global with the symbol $`s` starts, if there is one: its memory's
number $`m` and its allocation's id in that memory, which
$`\mathsf{globaladdr}` reads (#237), and $`L.\mathrm{func}(f)` where the
function with the symbol $`f` starts, its allocation's id in memory 0,
which $`\mathsf{funcaddr}` reads (#235); none unless the run says
otherwise.

The record is the same for every dialect: its numbers count units of a
memory of the module, and a step is already rounded, so no rule needs a
dialect's types to read it, and a sum gives it to both its sides as it
is. Every obligation and guarantee of the semantics with memory holds for
every record $`L`, with no hypothesis on it, and so for every address
policy. So an item that an op
names, the address of a global (#237) or of a function (#235), is a new
field of this record, and the statements of those obligations and
guarantees stay as they are.
:::

:::readable Fir.Field.place Fir.Aggregate.place Fir.Global.startId? Fir.InitPiece.startUnits Fir.Global.start Fir.funcStart Fir.Func.startId? Fir.RunItems.ofTable Fir.Module.runItems (pin := Fir.Field.shape) (pin := Fir.roundUp) (pin := Fir.InitPiece.unitCount) (pin := Fir.Memory.encodePtr) (fingerprint := "1416953201794327785")
*Definition: the items of a table.* In the memory $`n` of a module whose
data layout is $`l`, a field of the type $`t` is placed at its offset,
with its count, and with the step $`\mathrm{roundUp}(u, a)`, where one
value of $`t` takes $`u` units aligned to $`a`; a type that may not be a
field has no units, and so a step of $`0`. A layout is placed by placing
each of its fields in its own memory.

A global $`g` of $`T` starts as the allocation of kind `global` in its
memory $`n`, with its alignment and its constness. Its units are its
initializer's pieces in order, cut to its size $`S`, then zeros up to
$`S` (the human's ruling of 2026-11-20 on #237, Q1): $`\mathsf{units}(U,
\ldots)` gives each $`U` cut to $`u` bits, $`\mathsf{zeros}(N)` gives
$`N` zeros, and $`\mathsf{addr}(@s, K)` gives the pointer to the global
$`@s` of $`T` plus $`K` as a store of it writes it, $`\mathrm{encodePtr}`
of the memory $`m` of $`@s`, in the $`\mathrm{unitCount}` units that
validation counts, the units of $`m`'s pointer width in memory $`n`. That
pointer's id is $`@s`'s place among the globals of $`T` in memory $`m`,
counted from $`0`, which is where the run starts it. An address of a
symbol that names no global of $`T`, which validation rejects, gives no
units.

A function of $`T` starts as the allocation of kind `function` in memory
0, aligned to 1, constant, and with no units, so that every access through
its address is out of bounds (the human's ruling of 2026-11-19 on #235,
Q1).

A run of a function of the symbol table $`T` gives each op the first
layout of $`T` with each symbol, placed, under the canonical policy and
resolver, and starts with the allocation of each global of $`T`, in $`T`'s
order, then with that of each function of $`T`, in $`T`'s order: the
items of its own table, not those of a table nested in it or around it
(the human's ruling of 2026-11-20 on #237, Q3). It places each global of
$`T` as an address in an initializer reads it: the first global of $`T`
with a symbol, in its memory, at its place among the globals of $`T` in
that memory. It places the first function of $`T` with a symbol $`f` in
memory 0, after the globals of $`T` in memory 0, at its place among the
functions of $`T`: the $`i`th function, counted from 0, of a table with
$`g` globals in memory 0 has the id $`g + i`. A
module's own items,
$`\mathrm{items}(M)`, are those of its own table, in its data layout:
the items that the runs the modes report give each op.
:::

:::readable Fir.LayoutPlace.ref Fir.RunItems.ofTable_ref (pin := Fir.SymbolTable.layouts) (pin := Fir.LayoutRef) (fingerprint := "2870024278288114846")
*Definition and theorem: a run gives an op the layout that validation
checks it against.* What the rule of an op sees of a placed layout is its
memory and the count of each of its fields. For every data layout $`l`,
table $`T` and symbol $`s`, the layout that a run of a function of $`T`
gives an op for $`s`, seen so, is the layout of $`s` that
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation]
reads, $`\mathrm{layouts}_T(s)`: both are the first layout of $`T` with
that symbol, or none. So an op that validation accepts in $`T` finds, in
every run, a layout of $`s` of the memory and with the fields it was
checked against.
:::

:::readable Fir.RunItems.ofTable_globalMem (pin := Fir.SymbolTable.globalMems) (pin := Fir.Global.startId?) (fingerprint := "5994983646569678989")
*Theorem: a run gives an op the global that validation checks it
against.* For every data layout $`l`, table $`T` and symbol $`s`, the
memory in which a run of a function of $`T` places the global $`s` is the
memory that
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation]
reads for it, $`\mathrm{globals}_T(s)`: both are the first global of $`T`
with that symbol, or none. So a $`\mathsf{globaladdr}` that validation
accepts in $`T` finds, in every run, a global of $`s` in the memory it
was checked against.
:::

:::readable Fir.RunItems.ofTable_func Fir.RunItems.ofTable_func_ne (pin := Fir.SymbolTable.symbols) (fingerprint := "7310570643088980784")
*Theorems: a run gives each function of the table an allocation of its
own.* For every data layout $`l`, table $`T` and symbol $`f`, a run of a
function of $`T` places $`f` exactly when
{ref "The-fir-specification--Validation--Scope-and-symbols"}[validation]
finds a function of $`T` with that symbol, $`\mathrm{symtab}_T(f)`. So a
$`\mathsf{funcaddr}` that validation accepts in $`T` finds its function's
allocation in every run. And two different symbols are placed at two
different allocations, so two functions' addresses are different pointers.
:::
