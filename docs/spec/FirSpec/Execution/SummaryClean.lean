import VersoManual
import Fir.Execution.SummaryClean
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on values with no poison, which renders
`Fir.Execution.SummaryClean` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Values with no poison: readable blocks" =>

:::moduleDocs (fingerprint := "6760647252257904763")
:::

:::readable Fir.DVals.Clean Fir.Env.Clean (fingerprint := "8528918267713506938")
*Definition: values with no poison.* A list of values is _clean_ when no
value of it is poison, and an environment is clean when no value it binds
is.
:::

:::readable Fir.HVector.clean_toDVals Fir.mem_of_lookup Fir.Env.Clean.value Fir.Env.Clean.bind Fir.Env.Clean.params Fir.Env.Clean.mapM_value Fir.Env.Clean.operands (pin := Fir.HVector.Any) (fingerprint := "16217548363197934412")
*Theorems: a clean environment gives clean values.* The values of an
operand vector are clean exactly when no element of it is poison. A name
that a list looks up is bound in it, so a value that a clean environment
binds is not poison, and neither are the values or the operands found in
it. Binding clean values in a clean environment leaves it clean, so
parameters bound to arguments with no poison make a clean environment.
:::
