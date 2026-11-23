import VersoManual
import Fir.Execution.CallsProgress
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a path at every budget, with calls,
which renders `Fir.Execution.CallsProgress` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "A path at every budget, with calls: readable blocks" =>

:::moduleDocs (fingerprint := "2101263609893668858")
:::

:::readable Fir.Module.calls_hasPath (pin := Fir.HasPath) (fingerprint := "13309462935759499599")
*Theorem: in a module whose functions are all valid and run within it,
the run from any op of any of its functions has a path when every op that
runs by its own rule is total.* Let every function of the module $`M` be
valid in a module context $`C` and run within $`M`, and let every op of
every block of every function of $`M` that is a terminator or calls no
function be {ref "The-fir-specification--Execution--Poison-classes"}[total],
and the rule of every op that picks its callee be total too. Take any
budget $`n`, function $`f` of $`M`, block $`b` of $`\mathrm{blocks}(f)`,
index $`i` less than the number of ops of $`b`, and environment $`E` that
holds every value in scope at the op at index $`i` of $`b`. Let $`o^*` be
the ops of $`b` from index $`i` on. Then $`\mathrm{run}_M(n, f, E, o^*)`
has a path: it may end in some way.

The proof is by induction on $`n`, as for no stuck path. An op that runs by
its own rule has an outcome, since it is total. An op with a callee needs
no rule of its own: its way to go on is its callee's run, which the
induction covers (ADR-2026-10-29-2006). An op whose callee is picked first
runs its rule, which has an outcome since it is total; with no step left,
the path runs out of fuel there, and otherwise the call goes on as a call
of the symbol it picks. A callee that ends with UB or out of fuel ends its
caller so, and that is a way to end.
:::

:::readable Fir.Func.progress_of_inModule (pin := Fir.Progress) (fingerprint := "4773122609838617562")
*Theorem: every function of a module whose functions are all valid and
run within it has progress when every op that runs by its own rule is
total, calls and recursion included.* Let every function of the module
$`M` be valid in a module context $`C` and run within $`M`, let every op
of every block of every function of $`M` that is a terminator or calls no
function be total, and so the rule of every op that picks its callee. For
every function $`f` of $`M` and every vector $`v^*` of values of its
parameter types, $`\mathrm{runs}_M(f)(v^*)` has
{ref "The-fir-specification--Execution--Fuel-and-progress"}[progress]: at
every budget $`n`, $`\mathrm{runs}_M(f)(v^*)_n` has some outcome.

A run may call any function of $`M`, itself included, as deep as its fuel
allows. Every function of every valid core module meets the hypotheses, as
the section on
{ref "The-fir-specification--Execution--Core-functions-with-calls"}[core functions with calls]
shows.
:::
