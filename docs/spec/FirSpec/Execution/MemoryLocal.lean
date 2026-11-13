import VersoManual
import Fir.Execution.MemoryLocal
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on progress with memory without calls,
which renders `Fir.Execution.MemoryLocal` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Progress and no stuck path with memory, without calls: readable blocks" =>

:::moduleDocs (fingerprint := "4393808398232784306")
:::

:::readable Fir.Func.local_memNoStuck Fir.Func.local_memHasPath (pin := Fir.Func.MemInModule) (pin := Fir.HasOutcome) (fingerprint := "13219923234541825755")
*Theorem: the run with memory of a valid function without calls, from any
op of any of its blocks, from any memories, has no stuck path, and has a
path when its ops have outcomes.* Let $`f` be valid in a module context
$`C`, let no op of $`f` call a function, and let $`f` run within the
module $`M` with memory, for a dialect whose ops have a semantics in the
state layer. Take any budget $`n`, block $`b` of $`f`, index $`i` less
than the number of ops of $`b`, environment $`E` that holds every value in
scope at the op at index $`i` of $`b`, and memories $`S`. Let $`o^*` be
the ops of $`b` from index $`i` on. Then:

* $`\mathrm{run}_M(n, f, E, o^*) \mathbin{@} S` has no stuck path;
* if every op of every block of $`f` has an outcome from any memories, on
  every operand vector, it has a path.

Neither $`M` nor its other functions need be valid. The proof is the one of
{ref "The-fir-specification--Memory--Progress-and-no-stuck-path___-with-memory"}[progress with memory],
by induction on $`n`, from every memories, with no call to follow.
:::

:::readable Fir.Func.memNeverStuck_of_local Fir.Func.memProgress_of_local (pin := Fir.Func.InModuleAt) (pin := Fir.NeverStuck) (pin := Fir.Progress) (fingerprint := "8198465358761813026")
*Theorem: a valid function without calls has no stuck path with memory,
and has progress.* Let $`f` be valid in a module context, let no op of
$`f` call a function, and let $`f` run within the module $`M` with memory
at the naming $`\rho` of the dialect's memories, whose layout entries are
$`\ell`. Then, for every vector $`v^*` of values of its parameter types,
the runs with memory of $`f` on $`v^*`, at $`\ell` and $`\rho`, have no
stuck path at any budget, jumps and loops included; and, when the dialect
is {ref "The-fir-specification--Memory--Totality-with-memory"}[lawful in its totality],
they have an outcome at every budget. Each op of $`f` calls no function,
so it runs by its own rule, and it is a valid op instance, since $`f` is
valid.
:::
