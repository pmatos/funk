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

:::moduleDocs (fingerprint := "13115067901382636711")
:::

:::readable Fir.Gpu.instDialectEffects (fingerprint := "875869409922791238")
*Definition: the effects of `gpu`.* Every op of `gpu` declares the empty
effect set: it reads, writes, allocates and frees no memory, is never UB,
makes no poison and is not control. Its poison class is
$`\mathsf{propagates}`, which holds trivially of an op with no operand.
The memories it may name are the core's.
:::

:::readable Fir.Gpu.instDialectMemOver (fingerprint := "658585008972803282")
*Definition: the memories of `gpu`.* `gpu` names each memory of the core
as the core does, and has no memory of its own yet.
:::
