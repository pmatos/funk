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

:::moduleDocs (fingerprint := "4475197527233375913")
:::

:::readable Fir.FieldPlace Fir.LayoutPlace Fir.RunItems Fir.RunItems.empty (fingerprint := "3632280138649651812")
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

The record is the same for every dialect: its numbers count units of a
memory of the module, and a step is already rounded, so no rule needs a
dialect's types to read it, and a sum gives it to both its sides as it
is. Every obligation and guarantee of the semantics with memory holds for
every record $`L`, with no hypothesis on it. So a later item that an op
names, the address of a function (#235) or of a global (#237), is a new
field of this record, and the statements of those obligations and
guarantees stay as they are.
:::

:::readable Fir.Field.place Fir.Aggregate.place Fir.RunItems.ofTable Fir.Module.runItems (pin := Fir.Field.shape) (pin := Fir.roundUp) (fingerprint := "16227008318984617599")
*Definition: the items of a table.* In the memory $`n` of a module whose
data layout is $`l`, a field of the type $`t` is placed at its offset,
with its count, and with the step $`\mathrm{roundUp}(u, a)`, where one
value of $`t` takes $`u` units aligned to $`a`; a type that may not be a
field has no units, and so a step of $`0`. A layout is placed by placing
each of its fields in its own memory.

A run of a function of the symbol table $`T` gives each op the first
layout of $`T` with each symbol, placed. A module's own items,
$`\mathrm{items}(M)`, are those of its own table, in its data layout:
the items that the runs the modes report give each op.
:::
