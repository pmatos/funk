import VersoManual
import Fir.Execution.TraceWorldRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the world gives, on traced
states that refine others, which renders `Fir.Execution.TraceWorldRefine`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "What the world gives, on refined traced states: readable blocks" =>

:::moduleDocs (fingerprint := "14022969830338930580")
:::

:::readable Fir.TraceState.fromWorldPtr Fir.TraceState.fromWorldPtr_congr (fingerprint := "4857588348589565361")
*Definition: reading back a pointer the world gives.* In the traced state
$`s`, where the memory numbered $`n` is $`\mu(n)`, a pointer $`p` of the
memory numbered $`n` that the world gives reads back as:

$$`\mathrm{back}_s(n, p) = \begin{cases} p & p.\mathrm{prov} = \mathsf{none} \\ p[\mathrm{prov} := a] & p.\mathrm{prov} = h,\ s.\mathrm{escaped}_h = (\mu(n), a) \\ \mathsf{none} & \text{otherwise} \end{cases}`

It depends only on the escaped list.
:::

:::readable Fir.WorldAct.apply_isRefinedBy Fir.WorldAct.applyAll_isRefinedBy (fingerprint := "1664751869759991694")
*Theorem: the world's actions keep refinement.* For traced states
$`s \sqsubseteq s'`, when the world can take its actions on $`s'`, leaving
$`t'`, it can take them on $`s`, leaving some $`t \sqsubseteq t'`.
:::
