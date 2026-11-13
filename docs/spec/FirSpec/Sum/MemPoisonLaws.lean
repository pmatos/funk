import VersoManual
import Fir.Sum.MemPoisonLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the poison of a sum and a lift with
memory, which renders `Fir.Sum.MemPoisonLaws` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "Poison of a sum and a lift, with memory: readable blocks" =>

:::moduleDocs (fingerprint := "12152904006492761881")
:::

:::readable Fir.Dialect.sum.memPropagates_inl Fir.Dialect.sum.memReturnsOnDefined_inl Fir.Dialect.sum.lawfulMemPoison (fingerprint := "16217014605909200678")
*Theorems: a sum lawful in its poison with memory.* An op of the base that
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[propagates poison with memory]
in the base propagates it with memory in the sum: at each naming of the
sum's memories, it runs by the base's rule at that naming composed with the
base's memory map, on its operands moved to the base's types, with its
results moved to the sum's. Moving a vector between the two keeps which
values are poison, and mapping the results keeps the memories and the
paths that end in UB. So the operands that fill a poison in the base fill
it in the sum, from the same memories. An op of the base that returns a
result on defined operands with memory does so in the sum, and an op of the
extension runs by its own rule. So two dialects lawful in their poison with
memory make a sum lawful in its poison with memory, when the extension
accepts every type that the base accepts.
:::

:::readable Fir.Dialect.lift.memPropagates_lift Fir.Dialect.lift.memReturnsOnDefined_lift Fir.Dialect.lift.lawfulMemPoison Fir.Dialect.lift.sum_lawfulMemPoison (pin := Fir.TyIncl.Lawful) (fingerprint := "7332727358763415093")
*Theorems: a lift lawful in its poison with memory.* An op of an extension
that propagates poison with memory over what it depends on propagates it
with memory in the lift, when the inclusion is lawful: it runs by its own
rule at the naming composed with the lift's memory map, with its values
crossing the inclusion, and a lawful inclusion keeps which values are
poison. So does a result on defined operands. So the lift of an extension
lawful in its poison with memory is lawful in its poison with memory over a
larger base that is, and so is its sum with that base, when the inclusion
is lawful and the extension accepts each type of what it depends on whose
inclusion the larger base accepts.
:::
