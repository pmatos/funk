import VersoManual
import Fir.Execution.MemoryBindLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on sequences in the state layer, which
renders `Fir.Execution.MemoryBindLaws` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Sequences in the state layer: readable blocks" =>

:::moduleDocs (fingerprint := "3708391135293129920")
:::

:::readable Fir.SetM.stateBind_apply (fingerprint := "4921407586925901364")
*Theorem: how a sequence ends.* In the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad, the sequence $`c \mathbin{>\!\!>\!\!=} f` ends from the
state $`S` with $`e` when $`c` ends from $`S` with a result $`a` and a
state $`S_1`, and $`f(a)` ends from $`S_1` with $`e`; or in UB, for the
reason that $`c` ends in UB from $`S`.
:::

:::readable Fir.HasOutcome.bind Fir.FinitelyMany.bind (pin := Fir.HasOutcome) (pin := Fir.FinitelyMany) (fingerprint := "13315568131302932131")
*Theorems: the outcomes of a sequence.* When $`c` and every $`f(a)`
{ref "The-fir-specification--Memory--Totality-with-memory"}[have an outcome],
so does $`c \mathbin{>\!\!>\!\!=} f`: $`c` ends in UB, which the sequence
does too, or with a result, from which $`f` has an outcome. When they have
{ref "The-fir-specification--Memory--Ops-of-finitely-many-outcomes"}[finitely many],
so does the sequence: each of its results is one of $`f`'s, after one of
$`c`'s finitely many.
:::

:::readable Fir.WritesNot.bind Fir.AllocatesNot.bind (pin := Fir.WritesNot) (pin := Fir.AllocatesNot) (fingerprint := "11010922900940451825")
*Theorems: a sequence touches what its parts touch.* When neither $`c`
nor any $`f(a)` writes a unit of the memory $`x`, the sequence writes
none: the contents of $`x` before it are a prefix of those after $`c`,
which are a prefix of those after it. When neither allocates nor frees in
$`x`, the sequence does neither.
:::

:::readable Fir.StateRefinedBy.bind (pin := Fir.StateRefinedBy) (fingerprint := "14535693222181596984")
*Theorem: a sequence refines another when its parts do.* When $`c'`
refines $`c` with results related by $`r`, and, for results $`a`, $`a'`
related by $`r`, $`f'(a')` refines $`f(a)` with results related by $`r'`,
then $`c' \mathbin{>\!\!>\!\!=} f'` refines $`c \mathbin{>\!\!>\!\!=} f`
with results related by $`r'`, from memories that
{ref "The-fir-specification--Memory--Refining-memories"}[refine] others.
:::
