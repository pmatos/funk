import VersoManual
import Fir.Core.Rounding
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on rounding modes, which renders
`Fir.Core.Rounding` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Rounding modes: readable blocks" =>

:::moduleDocs (fingerprint := "958897365895229616")
:::

:::readable Fir.Core.RoundingMode (fingerprint := "958897365895229616")
*Definition: the rounding mode.* Every float op that rounds carries one of
five modes, IEEE 754's rounding-direction attributes (§4.3):
$`\mathsf{rne}`, to nearest with ties to even; $`\mathsf{rna}`, to
nearest with ties away from zero; $`\mathsf{rtp}`, toward $`+\infty`;
$`\mathsf{rtn}`, toward $`-\infty`; and $`\mathsf{rtz}`, toward zero
(ADR-2026-11-11-1801). M1's
{ref "The-fir-specification--Validation--Core-rules"}[validation]
accepts only $`\mathsf{rne}`, the one mode that Lean's float model
computes; the others are hooks in the format for a later milestone, and
the rules read every mode as $`\mathsf{rne}`.
:::
