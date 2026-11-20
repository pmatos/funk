import VersoManual
import Fir.Sum.Pointers
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pointers of a sum's values, which renders
`Fir.Sum.Pointers` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The pointers of a sum's values: readable blocks" =>

:::moduleDocs (fingerprint := "16661022798378911552")
:::

:::readable Fir.instTyPointersEmpty Fir.instTyPointersSum Fir.instTyPointersSumTy (fingerprint := "16661022798378911552")
*Theorem: a sum's values hold pointers.* A value of a summed type holds the
pointers it holds on its own side, and replacing them acts on its own side,
so the laws of values that hold pointers hold for the sum when they hold
for both sides. `Empty` has no value, so its values hold no pointer.
:::
