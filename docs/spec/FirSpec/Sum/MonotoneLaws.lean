import VersoManual
import Fir.Sum.MonotoneLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the monotonicity of a sum and a lift,
which renders `Fir.Sum.MonotoneLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Monotonicity of a sum and a lift: readable blocks" =>

:::moduleDocs (fingerprint := "3125227822728952579")
:::

:::readable Fir.Dialect.sum.memMonotone_inl Fir.Dialect.sum.lawfulMonotone (fingerprint := "1098510505309069486")
*Theorems: a sum lawful in its monotonicity.* An op of the base that is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]
in the base is monotone with memory in the sum: at each naming of the sum's
memories, it runs by the base's rule at that naming composed with the
base's memory map. Operands of the sum's types refine others exactly when
they do at the base's types, and moving the results to the sum's types
keeps their refinement. An op of the extension runs by its own rule. So two
dialects lawful in their monotonicity make a sum lawful in its
monotonicity, when the extension accepts every type that the base accepts.
:::

:::readable Fir.Dialect.lift.memMonotone_lift Fir.Dialect.lift.lawfulMonotone Fir.Dialect.lift.sum_lawfulMonotone (pin := Fir.TyIncl.Lawful) (fingerprint := "17817172563814927175")
*Theorems: a lift lawful in its monotonicity.* An op of an extension that
is monotone with memory over what it depends on is monotone with memory in
the lift, when the inclusion is lawful: it runs by its own rule, at the
naming composed with the lift's memory map, with its values crossing the
inclusion, which keeps their refinement both ways. So the lift of an
extension lawful in its monotonicity is lawful in its monotonicity, and so
is its sum with a larger base lawful in its monotonicity, when the
extension accepts each type of what it depends on whose inclusion the
larger base accepts.
:::
