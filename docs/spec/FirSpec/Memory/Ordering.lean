import VersoManual
import Fir.Memory.Ordering
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the ordering of an access, which renders
`Fir.Memory.Ordering` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The ordering of an access: readable blocks" =>

:::moduleDocs (fingerprint := "9301993891163757794")
:::

:::readable Fir.Memory.Ordering (fingerprint := "9301993891163757794")
*Definition: the ordering of an access.* Every load and store carries one
of seven orderings: $`\mathsf{nonatomic}`, a plain access, and the atomic
orderings $`\mathsf{unordered}`, $`\mathsf{monotonic}`,
$`\mathsf{acquire}`, $`\mathsf{release}`, $`\mathsf{acq\_rel}` and
$`\mathsf{seq\_cst}` (ADR-2026-11-09-1542). M1 has one thread, and its
{ref "The-fir-specification--Validation--Core-rules"}[validation]
accepts only $`\mathsf{nonatomic}`; the others are hooks in the format
for a concurrency model.
:::
