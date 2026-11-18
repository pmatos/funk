import VersoManual
import Fir.Execution.MemoryChoiceLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on choices in the state layer, which
renders `Fir.Execution.MemoryChoiceLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Choices in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "15354973541174894382")
:::

:::readable Fir.SetM.stateChoose_apply Fir.SetM.chooseBind_apply (pin := Fir.instMonadChoiceStateT) (fingerprint := "8421021278155478931")
*Theorems: how a choice ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, a choice of $`w` bits from the state $`S` ends with some
bits $`b` and the state $`S`, and never in UB. So a choice of $`w` bits
then $`f` ends from $`S` as $`f(b)` ends from $`S`, for some bits $`b`.
:::

:::readable Fir.HasOutcome.chooseBind Fir.FinitelyMany.chooseBind (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (fingerprint := "10053839021527493084")
*Theorems: a choice keeps an outcome, and finitely many.* A choice then
$`f` {ref "The-fir-specification--Memory--Totality-with-memory"}[has an outcome]
when $`f(b)` has one for every $`b`, and it has
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many]
when each $`f(b)` has: $`w` bits take $`2^w` values.
:::

:::readable Fir.WritesNot.chooseBind Fir.AllocatesNot.chooseBind Fir.ReadsNot.chooseBind (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (pin := Fir.ReadsNot) (fingerprint := "10386338095518392322")
*Theorems: a choice touches no memory.* For every memory $`x`, a choice
then $`g` meets each
{ref "The-fir-specification--Memory--Memory-obligations"}[obligation]
that $`g(b)` meets for every $`b`: it writes no unit of $`x`, it neither
allocates nor frees in $`x`, and it does not read $`x`. The choice reads
nothing, so the run from the memories with $`x` replaced may make the same
choice.
:::

:::readable Fir.StateRefinedBy.chooseBind Fir.StateRefinedBy.chooseBind_left (pin := Fir.StateRefinedBy) (fingerprint := "13025057416441741324")
*Theorems: choices refine.* A choice then $`f'` refines a choice then
$`f` when $`f'(b)` refines $`f(b)` for every $`b`. And a computation
$`c'` refines a choice then $`f` when it refines $`f(b)` for some $`b`:
the choice may give $`b`. So a poison operand chosen as bits is refined by
the defined value that the choice may give.
:::
