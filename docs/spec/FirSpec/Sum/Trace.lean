import VersoManual
import Fir.Sum.Trace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the traced semantics of a sum, which renders
`Fir.Sum.Trace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The traced semantics of a sum: readable blocks" =>

:::moduleDocs (fingerprint := "9406702412001711321")
:::

:::readable Fir.Act.inl Fir.Act.inr Fir.TraceM.mapActs_liftMem (fingerprint := "2600471622454697333")
*Definitions: acts of a side.* An act $`\langle e, a\rangle` of the left
side is the act $`\langle \mathsf{inl}~e, \mathsf{inl}~a\rangle` of a sum,
and one of the right side $`\langle \mathsf{inr}~e, \mathsf{inr}~a\rangle`.

*Theorem: the lift shows no act.* Mapping the acts of a computation of the
state layer, lifted onto the memories of the traced state, changes nothing.
:::

:::readable Fir.Dialect.sum.DVal.ofSum? Fir.Dialect.sum.DVal.toSum (fingerprint := "1910056289437756262")
*Definitions: typed values of the base, within the sum.* A typed value of
$`\mathit{base} \boxplus e` whose type is of the base is a typed value of
the base, and every typed value of the base is one of the sum, at the
base's type seen in the sum; a value of a type of $`e` is none of the
base's.
:::

:::readable Fir.Dialect.sum.instDialectTrace Fir.Dialect.sum.event_isRefinedBy_refl Fir.Dialect.sum.event_isRefinedBy_trans (fingerprint := "12886927047803689425")
*Definition: the sum's traced semantics.* The events of $`\mathit{base} \boxplus e`
are $`\mathrm{Event}(\mathit{base}) \oplus \mathrm{Event}(e)`, and the
world's answers $`\mathrm{Answer}(\mathit{base}) \oplus \mathrm{Answer}(e)`;
one event refines another when both are of the same side and refine there.
An op of $`e` runs, exits and picks its callee by $`e`'s traced rules,
and an op of the base by the base's, where the run names each memory of the base as the sum does, its
results seen at the sum's types; each act of a side is the sum's act on
that side. An external call whose arguments and result types are all of
the base runs by the base's external-call rule, its results seen at the
sum's types; any other runs by $`e`'s, which sees the sum's types.
Refinement of the sum's events is reflexive, and transitive,
when each side's is.
:::

:::readable Fir.Dialect.sum.opLiftsMem_inl Fir.Dialect.sum.opLiftsMem_inr Fir.Dialect.sum.opLiftsMem Fir.Dialect.sum.liftsMem (fingerprint := "4830633370830775924")
*Theorems: a sum of lifts lifts.* An op that lifts its rule with memory on
its side lifts it in the sum: the lift shows no act, and mapping the
results to the sum's types commutes with it. So a sum of two dialects whose
traced semantics lift their semantics with memory lifts its own.
:::
