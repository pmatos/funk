import VersoManual
import Fir.Gpu.Runs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the runs of the core and `gpu`, which
renders `Fir.Gpu.Runs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Runs of the core and gpu: readable blocks" =>

:::moduleDocs (fingerprint := "6556637306803068017")
:::

:::readable Fir.Gpu.coreGpu_lawfulEffects Fir.Gpu.coreGpu_lawfulTotal Fir.Gpu.coreGpu_lawfulMonotone Fir.Gpu.coreGpu_lawfulMemPoison (fingerprint := "2096482798007682310")
*Theorems: the sum is lawful.* At every work-item, the sum of the core and
`gpu` is lawful in its effects, its totality, its monotonicity and its
poison with memory, since both sides are and `gpu` accepts each type that
the core accepts.
:::

:::readable Fir.Gpu.memMonotone_all (fingerprint := "3037100186864541020")
*Theorem: every op of the sum is monotone with memory.* Each op of `gpu`
is monotone with memory at every width (the section on work-group
allocation). So each op of the sum that runs by its own rule, a terminator or an op with no
callee, is monotone with memory at every width, valid or not: a core op by
the core's guarantee, and an op of `gpu` by its own.
:::

:::readable Fir.Gpu.inModule_of_valid Fir.Gpu.inModuleAt_of_valid (fingerprint := "10589849443278182106")
*Theorems: a valid function of the sum runs within its module.* A core op
of the sum is valid when the core can write the function's result types
and the op obeys the core's rule over the symbols whose types are all the
core's. So a valid `call` names a function of the module whose type is the
call's, `ret` returns the function's result types, and the core's jumps
keep to their successors. An op of `gpu` is no terminator and calls no
function. So a valid function of the sum runs within its module, and,
since each of its terminators is the core's and is tied, it runs within it
with memory, wherever a run names the sum's memories.
:::

:::readable Fir.Gpu.fuelMonotone Fir.Gpu.progress Fir.Gpu.neverStuck (fingerprint := "1902991765062497967")
*Theorems: every function of each table runs well.* At every work-item,
wherever a run names the sum's memories, the runs with memory of every
function of every module of the sum are fuel-monotone. For each table $`t`
of a valid module $`M`, its own or that of a module nested in it at any
depth, each function of $`t`, run in $`M.\mathrm{nest}(t)` on any
arguments, has an outcome at every budget, and no path of its run is
stuck, calls and recursion included. These are the core's guarantees of
progress, for the sum, and for a device module's kernels.
:::

:::readable Fir.Gpu.args_isRefinedBy (fingerprint := "3317227888454036313")
*Theorem: refined arguments.* At every work-item, wherever a run names the
sum's memories, on arguments that refine others, the observable runs with
memory of every function of every module of the sum, the module of a nested
table included, refine its observable runs on those others, calls and
recursion included.
:::

:::readable Fir.Gpu.opsFinite_gpu Fir.Gpu.opsFinite (fingerprint := "4862271034210431619")
*Theorems: the sum's ops have finitely many outcomes.* Each op of `gpu` has
one outcome with memory, at every layout and naming: a question its
results, and an allocation its one allocation. So each op of the sum
that runs by its own rule has finitely many outcomes with memory, a core
op by the core's own count.
:::

:::readable Fir.Gpu.replaceBody_isRefinedBy_of_from (fingerprint := "12042385926450760296")
*Theorem: congruence in the callee.* At every work-item, wherever a run
names the sum's memories, let $`t` be a table of a valid module $`M` and
$`g` a function of $`t`. Replace the body of $`g` in $`M.\mathrm{nest}(t)`
with one under which $`g`, run in the new module from given memories,
refines $`g` in the old. Then every function of $`t` is refined with memory
in the new module, calls and recursion included. It asks for no budget,
whatever the parameter types of $`g` and whatever its new body does to the
memories.
:::
