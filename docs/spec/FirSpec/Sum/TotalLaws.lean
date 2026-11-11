import VersoManual
import Fir.Sum.TotalLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the totality of a sum and a lift,
which renders `Fir.Sum.TotalLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Totality of a sum and a lift: readable blocks" =>

:::moduleDocs (fingerprint := "7712376717763871251")
:::

:::readable Fir.Dialect.sum.memTotal_inl Fir.Dialect.sum.lawfulTotal (fingerprint := "9807430110070738834")
*Theorems: a sum lawful in its totality.* An op of the base that is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory]
in the base is total with memory in the sum: at each naming of the sum's
memories, it runs by the base's rule at that naming composed with the
base's memory map, with its results mapped to the sum's types, and mapping
keeps an outcome. An op of the extension runs by its own rule. So two
dialects lawful in their totality make a sum lawful in its totality, when
the extension accepts every type that the base accepts.
:::

:::readable Fir.Dialect.lift.memTotal_lift Fir.Dialect.lift.lawfulTotal Fir.Dialect.lift.sum_lawfulTotal (fingerprint := "12896621153139610250")
*Theorems: a lift lawful in its totality.* An op of an extension that is
total with memory over what it depends on is total with memory in the lift:
it runs by its own rule, at the naming composed with the lift's memory map,
with its values crossing the inclusion. So the lift of an extension lawful
in its totality is lawful in its totality, and so is its sum with a larger
base lawful in its totality, when the extension accepts each type of what
it depends on whose inclusion the larger base accepts.
:::
