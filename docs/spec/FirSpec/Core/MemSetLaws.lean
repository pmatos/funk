import VersoManual
import Fir.Core.MemSetLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the fill obligations, which
renders `Fir.Core.MemSetLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fill obligations: readable blocks" =>

:::moduleDocs (fingerprint := "17500434639180486599")
:::

:::readable Fir.Core.setUnit_isRefinedBy Fir.Core.replicate_isRefinedBy (pin := Fir.Core.setUnit) (fingerprint := "7968529785779016675")
*Theorems: the units of a refining value refine.* If $`v \sqsubseteq v'`
then $`\mathrm{setunit}_u(v) \sqsubseteq \mathrm{setunit}_u(v')`: a
poison unit is refined by every unit, and a defined value refines only
itself. So $`n` copies of the one refine $`n` copies of the other, unit
by unit.
:::

:::readable Fir.Core.memSet_denote (pin := Fir.Core.memSetRule) (fingerprint := "11995573317938595982")
*Theorem: $`\mathsf{memset}` runs by its rule.* With memory,
$`\mathsf{memSet}_N~o~V~W` on the destination $`p`, the value $`v` and the
length $`l` runs the
{ref "The-fir-specification--Memory--Fill-rules"}[rule]
$`\mathrm{memset}_{V,W,N}(p, v, l)`.
:::

:::readable Fir.Core.setLenRule_cases Fir.Core.memSetRule_cases Fir.Core.memSet_ownRuleHas (pin := Fir.Core.setLenRule) (pin := Fir.OwnRuleHas) (fingerprint := "5281468782115948542")
*Theorems: the cases of the rule.* The rule of a defined length ends in
one of three ways: it returns no result at once, it is UB, or it is a
store with no result. So a property holds of it when it holds of those
three. A property holds of the whole rule when it holds of the rule of
every defined length and a choice of bits keeps it; and it holds of what
the op runs by its own rule when it holds of the rule on every operand
vector.
:::

:::readable Fir.Core.memSet_writesNot Fir.Core.memSet_readsNot Fir.Core.memSet_allocatesNot (pin := Fir.WritesNot) (pin := Fir.ReadsNot) (pin := Fir.AllocatesNot) (pin := Fir.Core.Op.effects) (fingerprint := "1442642215344245289")
*Theorems: a fill touches only its own memory.* For every memory $`x`
other than $`\rho(N)`, the memory it declares that it writes,
$`\mathsf{memSet}_N~o~V~W` writes no unit of $`x`; and for every memory
$`x`, its own included, it does not read $`x` and neither allocates nor
frees in $`x`. Each holds of a store, of returning at once and of UB, and
a choice keeps it.
:::

:::readable Fir.Core.memSet_memTotal Fir.Core.memSet_finitelyMany (pin := Fir.MemTotal) (pin := Fir.FinitelyMany) (fingerprint := "15731757981292051423")
*Theorems: a fill has an outcome, and finitely many.* From any memories,
$`\mathsf{memSet}_N~o~V~W`
{ref "The-fir-specification--Memory--Totality-with-memory"}[has an outcome],
and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many]:
at most one that ends for each length, and a poison length chooses one of
$`2^W`.
:::

:::readable Fir.Core.setLenRule_refines Fir.Core.memSet_memMonotone (pin := Fir.StateRefinedBy) (pin := Fir.MemMonotone) (fingerprint := "3612226713995249194")
*Theorems: a fill is monotone.* On the same length, a pointer and a value
that refine others give a rule that refines the others': a poison pointer
with a length other than 0 is UB, which every outcome refines, and on
equal pointers the units of the one value refine those of the other, so
the store refines from refining memories. So $`\mathsf{memSet}_N~o~V~W` is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]:
a defined length refines only itself, and a poison length may choose the
value that refines it.
:::
