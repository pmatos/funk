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

:::moduleDocs (fingerprint := "10953727801353079974")
:::

:::readable Fir.Core.lawfulDialectTotal (fingerprint := "7465536416105822801")
*Theorem: the core dialect is lawful in its totality.* Each core
terminator and each core op with no callee is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory]:
the core dialect is lawful, and its semantics with memory lifts its
semantics in the set monad.
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
