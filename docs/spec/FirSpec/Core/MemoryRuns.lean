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

:::moduleDocs (fingerprint := "13837067142324860801")
:::

:::readable Fir.Core.lawfulDialectTotal (fingerprint := "7465536416105822801")
*Theorem: the core dialect is lawful in its totality.* Each core
terminator and each core op with no callee is
{ref "The-fir-specification--Memory--Totality-with-memory"}[total with memory],
at every layout and naming: it is total in the set monad, and it is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied].
:::

:::readable Fir.Core.lawfulDialectMonotone (fingerprint := "853410003265425313")
*Theorem: the core dialect is lawful in its monotonicity.* Each core
terminator and each core op with no callee is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory],
at every layout and naming: it is monotone in the set monad, and it is
tied.
:::

:::readable Fir.Core.lawfulDialectMemPoison (fingerprint := "10064458873019723603")
*Theorem: the core dialect is lawful in its poison with memory.* Each valid
core op instance that propagates poison
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[propagates it with memory]
and returns a result on some defined operands with memory, at every layout
and naming of the core's memories: it meets both in the set monad, and it
is tied.
:::

:::readable Fir.Core.funcRuns (pin := Fir.Func.memRuns) (fingerprint := "15348739681123349600")
*Definition: the runs of a function of a core module.* For a core module
$`M` and a core function $`f`, the runs of $`f` are its
{ref "The-fir-specification--Memory--Runs-with-memory"}[runs with memory]
at the module's layout, where the core's memory $`x` is the module's memory
$`x`: on each vector $`v^*` of values of its parameter types, poison
included, and at each budget $`n`, the run of the interpreter in the state
layer over the set monad, from the empty memories, with $`n` steps of fuel,
by the core's semantics with memory, with each memory's entry in the
module's data layout. An observer sees what it returns. They are the
{ref "The-fir-specification--Execution--Core-values"}[runs of a core function]
whose observations are the lists of values returned, and the runs that the
modes report. The equivalence experiment of #282 and congruence in the
callee are about them.
:::

:::readable Fir.Core.Op.liftsSetM_of_terminator Fir.Core.Op.memMonotone_all (pin := Fir.Core.Op.liftsSetM) (pin := Fir.Core.Op.monotone_all) (fingerprint := "13096568096900556014")
*Theorems: every core terminator is tied, and every core op that runs by
its own rule is monotone with memory.* Each core terminator touches no
memory, so it is
{ref "The-fir-specification--Memory--The-core___s-rules-with-memory"}[tied].
Each core terminator and each core op with no callee, at every width, valid
or not, is
{ref "The-fir-specification--Memory--Monotonicity-with-memory"}[monotone with memory],
at every layout and naming: it is monotone in the set monad and tied. These
are what the theorems below ask of the core's ops, so an op that touches
memory, which is not a terminator, joins them with its own case of the
second.
:::

:::readable Fir.Core.inModuleAt_of_inModule Fir.Core.inModuleAt_of_valid (pin := Fir.Core.inModule_of_valid) (pin := Fir.Func.InModule.inModuleAt_of_tied) (fingerprint := "10953520611792496938")
*Theorems: a core function that runs within a module runs within it with
memory.* For every core module $`M`, every core function $`f` that
{ref "The-fir-specification--Execution--Core-functions-with-calls"}[runs within M],
and every layout and naming of the core's memories, $`f` runs within $`M`
with memory, since each of its terminators is tied. So does every core
function {ref "The-fir-specification--Validation--The-general-rules"}[valid]
in the context of $`M`.
:::

:::readable Fir.Core.fuelMonotone Fir.Core.neverStuck Fir.Core.progress Fir.Core.runsWell (pin := Fir.Core.RunsWell) (fingerprint := "8733541239344487932")
*Theorem: the runs with memory of every core function are fuel-monotone.*
For every core module $`M`, every function $`f`, every vector $`v^*` of
values of its parameter types and every layout and naming of the core's
memories, the runs with memory of $`f` on $`v^*` are fuel-monotone, calls
and recursion included, as the runs with memory of
{ref "The-fir-specification--Memory--Runs-with-memory-at-every-budget"}[every function]
are.

*Theorem: every function of a valid core module runs well with memory.*
If moreover $`M` is valid and $`f` is a function of $`M`, those runs have
no stuck path and have an outcome at every budget, so they
{ref "The-fir-specification--Execution--The-tracer-subset"}[run well],
calls and recursion included. Every function of $`M` runs within $`M`
with memory, and the core dialect is lawful in its totality.
:::

:::readable Fir.Core.runsWell_of_local Fir.Core.callFree_runsWell Fir.Core.callFree_fuelMonotone Fir.Core.callFree_progress Fir.Core.callFree_neverStuck (pin := Fir.Core.CallFree) (fingerprint := "5063858304775921035")
*Theorem: every valid core function that runs within itself runs well with
memory.* For every core module $`M`, every core function $`f` valid in the
context of $`M` that
{ref "The-fir-specification--Execution--Progress-with-jumps-and-loops"}[runs within itself],
every vector $`v^*` of values of its parameter types and every layout and
naming of the core's memories, the runs with memory of $`f` on $`v^*` run
well, jumps and loops included.

*Theorem: every valid core function without calls runs well with memory.*
For every core module $`M`, every core function $`f` without a
$`\mathsf{call}` op valid in the context of $`M`, every vector $`v^*` of
values of its parameter types and every layout and naming of the core's
memories, the runs with memory of $`f` on $`v^*` run well, jumps and loops
included. So each of the three holds on its own for every function without
calls of a valid core module. $`f`
{ref "The-fir-specification--Execution--Core-functions-without-calls"}[runs within itself],
each of its terminators is tied, and each of its ops is total with memory,
so the theorems on
{ref "The-fir-specification--Memory--Progress-and-no-stuck-path-with-memory___-without-calls"}[progress with memory without calls]
apply. Only $`f` need be valid, not its module.
:::

:::readable Fir.Core.tracer_runsWell Fir.Core.tracer_fuelMonotone Fir.Core.tracer_progress Fir.Core.tracer_neverStuck (pin := Fir.Core.InTracer) (fingerprint := "14461548596925548796")
*Theorem: every function of the tracer subset in a valid core module runs
well with memory.* For every valid core module $`M`, every function $`f`
of $`M` in the
{ref "The-fir-specification--Execution--The-tracer-subset"}[tracer subset],
every vector $`v^*` of values of its parameter types and every layout and
naming of the core's memories, the runs with memory of $`f` on $`v^*` run
well, and so each of the three holds on its own. $`f` runs straight, so it
runs within itself, and the theorems on progress with memory without calls
apply.
:::

:::readable Fir.Core.args_isRefinedBy (pin := Fir.Core.opsMonotone_all) (fingerprint := "3686017503688643883")
*Theorem: refined arguments, with memory, for every core module.* For
every core module $`M`, valid or not, every function $`f` of it, and every
layout and naming of the core's memories, the behaviour with memory of
$`f` on arguments $`\vec{v}'` refines its behaviour with memory on
$`\vec{v} \sqsubseteq \vec{v}'`, calls and recursion included: every core
op that runs by its own rule is monotone at every width and tied, so it is
monotone with memory, and the
{ref "The-fir-specification--Memory--Refined-arguments-and-memories"}[theorem on refined arguments and memories]
applies from the empty memories. So a call on arguments that refine others
refines the call on those others.
:::

:::readable Fir.Core.memReplaceBody_isRefinedBy Fir.Core.memCaller_isRefinedBy (pin := Fir.FuncRuns.BoundedBy) (fingerprint := "18431638885631279976")
*Theorem: congruence in the callee, with memory, for every valid core
module.* Let $`M` be a valid core module, $`g` a function of $`M`, $`b` a
new body for $`g`, and $`M'` the module with $`g`'s body replaced by
$`b`. Take a layout and naming of the core's memories. If $`g` in $`M'`,
run from any memories, refines $`g` in $`M`, the memories it ends with
included, and the runs of $`g` in $`M'` from given memories are bounded by
some budget, then every function $`f` of $`M` is refined with memory by
its counterpart in $`M'`, calls and recursion included. It is the
{ref "The-fir-specification--Memory--Replacing-a-callee___-with-memory"}[theorem on replacing a callee with memory],
for the core dialect, which is lawful in its monotonicity and whose values'
refinement is reflexive and transitive. A function of $`M` other than $`g`,
a caller of it or not, is so refined by itself in $`M'`. The bound
replaces the finitely many argument vectors of runs in the set monad: a
call starts from its caller's memories, of which there are infinitely many,
and a callee that touches memory may depend on them.
{ref "The-fir-specification--Memory--Congruence-in-a-core-callee"}[Congruence in a core callee]
asks for no bound, since every core op has finitely many outcomes.
:::
