import VersoManual
import Fir.Gpu.Ops
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the abstract syntax of `gpu`, which
renders `Fir.Gpu.Ops` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails when
the Lean changes under it.
-/

#doc (Manual) "The GPU dialect's abstract syntax: readable blocks" =>

:::moduleDocs (fingerprint := "17999411893607134800")
:::

:::readable Fir.Gpu.Dim Fir.Gpu.Query Fir.Gpu.Op (fingerprint := "2806191881920580656")
*Definition: the ops of `gpu`.* A _dimension_ $`d` is one of the three
dimensions of the grid of work-items, $`x`, $`y` or $`z`. A _question_
$`q` is one of four facts about the work-item that runs a kernel: its id
within its work-group, the id of its work-group, the number of work-items
in a work-group, and the number of work-groups. An op instance of `gpu`
either asks one question in one dimension and gives its answer as an
integer of $`N` bits, or allocates room for $`c` values of the core type
$`t` in work-group memory, the memory $`n` of the host's data layout,
aligned to $`a` units or to the type's default alignment there when $`a` is
absent, for the whole run of the kernel:

$$`\begin{array}{lcl} d & ::= & x \mid y \mid z \\ q & ::= & \mathsf{work\_item\_id} \mid \mathsf{work\_group\_id} \mid \mathsf{work\_group\_size} \mid \mathsf{num\_work\_groups} \\ \mathit{op} & ::= & \mathsf{query}_N~q~d \mid \mathsf{alloc}_n~t~c~a \end{array}`

The Lean spells the questions `workItemId`, `workGroupId`, `workGroupSize`
and `numWorkGroups`. Work-group memory is not a memory of `gpu`'s own: it
is any memory that the host's data layout declares, and the allocation op
is what gives it its meaning (the human's ruling of 2026-11-16 on #212).
:::

:::readable Fir.GpuExt Fir.Gpu.instDialectName Fir.GpuDialect Fir.CoreGpu (fingerprint := "7237063387894194917")
*Definition: the dialect `gpu`, over the core, and its sum with the core.*
`gpu` on its own has the ops above and no types of its own, and its name is
$`\texttt{gpu}`, the word before the $`.` of each of its words. Over the
core, its ops are used at the core's types, so they give the core's
integers. The sum of the core and `gpu` holds the ops and types of both,
and is the dialect that `funk`, `fir-ref fmt`, `fir-ref validate` and
`fir-ref run` read: a module that names
`gpu` in its dialect set may use its ops, and every other module may not.
:::

:::readable Fir.Gpu.Op.sig Fir.Gpu.Op.returnTypes Fir.Gpu.instDialectSignature (fingerprint := "5043009942651367281")
*Definition: the signature of each op of `gpu`.* Every op of `gpu` takes no
operand. A question gives one integer of its width, and an allocation the
core's pointer of its memory:

$$`\mathsf{query}_N~q~d \quad [\,] \to [\mathsf{i}N] \qquad \mathsf{alloc}_n~t~c~a \quad [\,] \to [\mathsf{ptr}\langle n\rangle]`

No op of `gpu` ends a block, has a successor or owns a region.
:::
