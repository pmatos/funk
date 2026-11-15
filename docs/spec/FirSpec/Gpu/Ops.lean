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

:::moduleDocs (fingerprint := "2916898914113186508")
:::

:::readable Fir.Gpu.Dim Fir.Gpu.Query Fir.Gpu.Op (fingerprint := "11182156384170231395")
*Definition: the ops of `gpu`.* A _dimension_ $`d` is one of the three
dimensions of the grid of work-items, $`x`, $`y` or $`z`. A _question_
$`q` is one of four facts about the work-item that runs a kernel: its id
within its work-group, the id of its work-group, the number of work-items
in a work-group, and the number of work-groups. An op instance of `gpu`
asks one question in one dimension and gives its answer as an integer of
$`N` bits:

$$`\begin{array}{lcl} d & ::= & x \mid y \mid z \\ q & ::= & \mathsf{work\_item\_id} \mid \mathsf{work\_group\_id} \mid \mathsf{work\_group\_size} \mid \mathsf{num\_work\_groups} \\ \mathit{op} & ::= & \mathsf{query}_N~q~d \end{array}`

The Lean spells the questions `workItemId`, `workGroupId`, `workGroupSize`
and `numWorkGroups`.
:::

:::readable Fir.GpuExt Fir.Gpu.instDialectName Fir.GpuDialect Fir.CoreGpu (fingerprint := "7237063387894194917")
*Definition: the dialect `gpu`, over the core, and its sum with the core.*
`gpu` on its own has the ops above and no types of its own, and its name is
$`\texttt{gpu}`, the word before the $`.` of each of its words. Over the
core, its ops are used at the core's types, so they give the core's
integers. The sum of the core and `gpu` holds the ops and types of both,
and is the dialect that `funk`, `fir-ref fmt` and `fir-ref validate` read
(`fir-ref run` reads the core alone until a work-item runs): a module that names
`gpu` in its dialect set may use its ops, and every other module may not.
:::

:::readable Fir.Gpu.Op.sig Fir.Gpu.Op.returnTypes Fir.Gpu.instDialectSignature (fingerprint := "18040486421864665858")
*Definition: the signature of each op of `gpu`.* Every op of `gpu` takes no
operand and gives one integer of its width:

$$`\mathsf{query}_N~q~d \quad [\,] \to [\mathsf{i}N]`

No op of `gpu` ends a block, has a successor or owns a region.
:::
