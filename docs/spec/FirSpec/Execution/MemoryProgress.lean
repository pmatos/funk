import VersoManual
import Fir.Execution.MemoryProgress
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on progress with memory, which renders
`Fir.Execution.MemoryProgress` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Progress and no stuck path, with memory: readable blocks" =>

:::moduleDocs (fingerprint := "12998060254520900076")
:::

:::readable Fir.Module.calls_memNoStuck Fir.Module.calls_memHasPath (pin := Fir.HasOutcome) (fingerprint := "17375378244954417757")
*Theorem: in a module whose functions are all valid and run within it with
memory, the run from any op of any of its functions, from any memories, has
no stuck path, and has a path when every op that runs by its own rule has
an outcome.* Let every function of the module $`M` be valid in a module
context $`C` and run within $`M` with memory, for a dialect whose ops have
a semantics in the state layer. Take any budget $`n`, function $`f` of
$`M`, block $`b` of $`f`, index $`i` less than the number of ops of $`b`,
environment $`E` that holds every value in scope at the op at index $`i`
of $`b`, and memories $`S`. Let $`o^*` be the ops of $`b` from index $`i`
on. Then:

* $`\mathrm{run}_M(n, f, E, o^*) \mathbin{@} S` has no stuck path;
* if every op of every block of every function of $`M` that is a
  terminator or calls no function has an outcome from any memories, on
  every operand vector, it has a path.

Here $`\mathrm{run}_M(n, f, E, o^*)` is the interpreter's run of the ops
$`o^*` in the state layer, and $`\cdot \mathbin{@} S` reads it
{ref "The-fir-specification--Memory--How-a-run-with-memory-ends"}[from the memories S].

The proof is the one of
{ref "The-fir-specification--Execution--Progress-with-calls"}[progress with calls],
by induction on $`n`, for every function of $`M` at once and from every
memories. Each step goes on from the memories that the step before it
ended with, which the induction covers. A call runs its callee from the
memories with a new frame entered, and the caller goes on, after the frame
is left, from the memories that the callee's return ends with; the callee
returns values of the call's result types, whatever it did to the
memories.
:::

:::readable Fir.NoStuck.finish Fir.HasPath.finish (pin := Fir.Result.finish) (fingerprint := "11051480644896066662")
*Theorems: what a function does with its ops' run.* A function returns
what its entry block's ops return, or runs out of fuel when they do; it has
no stuck path when they have none, and a path when they have one.
:::

:::readable Fir.Func.memNeverStuck Fir.Func.memProgress (pin := Fir.NeverStuck) (pin := Fir.Progress) (fingerprint := "14390080740948530134")
*Theorem: every function of a module whose functions are all valid and run
within it with memory has no stuck path with memory, and has progress
with memory when its dialect is lawful in its totality, calls and recursion
included.* Take a naming $`\rho` of a dialect's memories, with unit widths
$`u`. Let every function of the module $`M` be valid in a module context
$`C` and run within $`M` with memory at that naming. For every function
$`f` of $`M` and every vector $`v^*` of values of its parameter types, let
$`R` be the
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]
of $`f` on $`v^*`:

* $`R` has no stuck path: at every budget $`n`, no path of $`R_n` is
  stuck;
* if the dialect is lawful in its totality, $`R` has progress: at every
  budget $`n`, $`R_n` has some outcome.

This holds whatever the ops do to the memories. A dialect whose ops touch
no memory meets the hypotheses when its module's functions are valid and
run within the module, as the
{ref "The-fir-specification--Memory--Core-functions-with-memory"}[core dialect]
does.
:::
