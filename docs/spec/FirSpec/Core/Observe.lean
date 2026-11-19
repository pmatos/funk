import VersoManual
import Fir.Core.Observe
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pointers of the core's values,
which renders `Fir.Core.Observe` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The pointers of the core's values: readable blocks" =>

:::moduleDocs (fingerprint := "16947091722005604509")
:::

:::readable Fir.PoisonOr.ptrsOf Fir.PoisonOr.mapPtr Fir.Core.Ty.ptrs Fir.Core.Ty.mapPtrs (fingerprint := "14569961712294482548")
*Definition: the pointers of a core value.* A value of $`\mathtt{ptr}\langle
n\rangle` that is the pointer $`p` holds $`(n, p)`; poison and the values of
integer and float types hold none. Replacing by $`f` gives $`f_n(p)`, or
poison, for a pointer, and leaves every other value as it is.
:::

:::readable Fir.Core.instTyPointers Fir.Core.instHasPtrs (fingerprint := "12370704274255137694")
*Theorem: the core's values hold pointers.* The pointers of the core's
values, and their replacement, meet the laws of values that hold pointers:
replacing a pointer by itself changes nothing, a pointer refines only
itself, and poison refines everything.
:::
