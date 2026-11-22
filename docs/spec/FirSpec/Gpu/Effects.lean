import VersoManual
import Fir.Gpu.Effects
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the effects of `gpu`, which renders
`Fir.Gpu.Effects` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The GPU dialect's effects: readable blocks" =>

:::moduleDocs (fingerprint := "14849123397262844484")
:::

:::readable Fir.Gpu.Op.effects Fir.Gpu.instDialectEffects (fingerprint := "5101052619392698901")
*Definition: the effects of `gpu`.* Every question of `gpu` declares the
empty effect set: it reads, writes, allocates and frees no memory, is never
UB, makes no poison and is not control. An allocation declares one effect,
as `alloca` does: it allocates in the memory of its result,

$$`\mathrm{effects}(\mathsf{alloc}_n~t~c~a) = \{\mathsf{allocates}~n\}`

It is never UB, makes no poison, is not control, and frees nothing: its
allocation lives for the whole run. The poison class of every op is
$`\mathsf{propagates}`, which holds trivially of an op with no operand.
The memories it may name are the core's, so the memory of an allocation is
named by its number.
:::

:::readable Fir.Gpu.instDialectMemOver (fingerprint := "658585008972803282")
*Definition: the memories of `gpu`.* `gpu` names each memory of the core
as the core does, and has no memory of its own: it gives a declared memory
its meaning, work-group memory, through the op that allocates there (the
human's ruling of 2026-11-16 on #212).
:::
