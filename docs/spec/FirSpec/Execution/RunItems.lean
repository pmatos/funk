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

:::moduleDocs (fingerprint := "12899288408955897722")
:::

:::readable Fir.FieldPlace Fir.LayoutPlace Fir.RunItems Fir.RunItems.empty Fir.RunItems.withAddrs (pin := Fir.Memory.Policy.canonical) (fingerprint := "17370728466934174662")
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

The record is the same for every dialect: its numbers count units of a
memory of the module, and a step is already rounded, so no rule needs a
dialect's types to read it, and a sum gives it to both its sides as it
is. Every obligation and guarantee of the semantics with memory holds for
every record $`L`, with no hypothesis on it, and so for every address
policy. So a later item that an op
names, the address of a function (#235) or of a global (#237), is a new
field of this record, and the statements of those obligations and
guarantees stay as they are.
:::

:::readable Fir.Field.place Fir.Aggregate.place Fir.RunItems.ofTable Fir.Module.runItems (pin := Fir.Field.shape) (pin := Fir.roundUp) (fingerprint := "17179416892505133197")
*Definition: the items of a table.* In the memory $`n` of a module whose
data layout is $`l`, a field of the type $`t` is placed at its offset,
with its count, and with the step $`\mathrm{roundUp}(u, a)`, where one
value of $`t` takes $`u` units aligned to $`a`; a type that may not be a
field has no units, and so a step of $`0`. A layout is placed by placing
each of its fields in its own memory.

A run of a function of the symbol table $`T` gives each op the first
layout of $`T` with each symbol, placed, under the canonical policy. A
module's own items,
$`\mathrm{items}(M)`, are those of its own table, in its data layout:
the items that the runs the modes report give each op.
:::

:::readable Fir.LayoutPlace.ref Fir.RunItems.ofTable_ref (pin := Fir.SymbolTable.layouts) (pin := Fir.LayoutRef) (fingerprint := "10020164216687375419")
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
