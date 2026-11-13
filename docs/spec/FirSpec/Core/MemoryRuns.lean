import VersoManual
import Fir.Core.MemoryRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core functions with memory, which
renders `Fir.Core.MemoryRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core functions with memory: readable blocks" =>

:::moduleDocs (fingerprint := "7749102457304684616")
:::

:::readable Fir.Core.lawfulDialectTotal (fingerprint := "7465536416105822801")
*Theorem: the core dialect is lawful in its totality.* Each core
terminator and each core op with no callee is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory]:
the core dialect is lawful, and its semantics with memory lifts its
semantics in the set monad.
:::

:::readable Fir.Core.lawfulDialectMonotone (fingerprint := "853410003265425313")
*Theorem: the core dialect is lawful in its monotonicity.* Each core
terminator and each core op with no callee is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory]:
the core dialect is lawful, and its semantics with memory lifts its
semantics in the set monad.
:::

:::readable Fir.Core.lawfulDialectMemPoison (fingerprint := "10064458873019723603")
*Theorem: the core dialect is lawful in its poison with memory.* Each valid
core op instance that propagates poison
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[propagates it with memory]
and returns a result on some defined operands with memory, at every naming
of the core's memories: the core dialect is lawful, and its semantics with
memory lifts its semantics in the set monad.
:::

:::readable Fir.Core.memRuns_args_isRefinedBy (pin := Fir.Core.opsMonotone_all) (fingerprint := "14354991659016519450")
*Theorem: refined arguments, with memory, for every core module.* For
every core module $`M`, valid or not, every function $`f` of it, and every
naming of the core's memories, the behaviour with memory of $`f` on
arguments $`\vec{v}'` refines its behaviour with memory on
$`\vec{v} \sqsubseteq \vec{v}'`, calls and recursion included: every core
op that runs by its own rule is monotone at every width, so it is monotone
with memory, and the
{ref "The-fir-specification--Memory--Refined-arguments-and-memories"}[theorem on refined arguments and memories]
applies from the empty memories.
:::

:::readable Fir.Core.memNeverStuck Fir.Core.memProgress (pin := Fir.Core.inModule_of_valid) (fingerprint := "9635650436885863802")
*Theorem: every function of a valid core module has no stuck path and has
progress, with memory.* For every valid core module $`M`, every function
$`f` of $`M`, every vector $`v^*` of values of its parameter types, and
every naming of the core's memories, the runs with memory of $`f` on
$`v^*` have no stuck path and have an outcome at every budget, calls and
recursion included. Each function of $`M`
{ref "The-fir-specification--Execution--Core-functions-with-calls"}[runs within M],
and so runs within it with memory at every naming.
:::
