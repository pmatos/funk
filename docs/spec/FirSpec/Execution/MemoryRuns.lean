import VersoManual
import Fir.Execution.MemoryRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on runs with memory, which renders
`Fir.Execution.MemoryRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Runs with memory: readable blocks" =>

:::moduleDocs (fingerprint := "2221092474660519569")
:::

:::readable Fir.MonadMorphism.liftState Fir.MonadMorphism.liftState_mapsFrame (fingerprint := "8015592493867984939")
*Definition: a computation with no memory, in the layer.* For a lawful
monad $`m`, a computation $`x` of $`m` runs in the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] by
keeping the state: $`\mathrm{lift}(x)(S) = \mathrm{map}_{a \mapsto (a, S)}(x)`.
This is a monad morphism from $`m` to the layer over it.

*Theorem: lifting keeps frames.* When a frame of $`m` is the computation
itself, as in the set monad, lifting keeps frames: entering a call and
leaving it at once gives back the memories,
$`\mathrm{exit}(\mathrm{enter}(S)) = S`.
:::

:::readable Fir.MonadMorphism.liftState_keeps Fir.SetM.ub_bind (pin := Fir.MonadMorphism.KeepsChoiceUB) (fingerprint := "750416787570381964")
*Theorem: lifting keeps choice and UB.* Lifting into the layer keeps a
choice of $`w` bits: choosing and then keeping the state is choosing in
the layer. It keeps UB when, in $`m`, UB ends a path whatever follows it:
$`\mathsf{ub}~r \mathbin{>\!\!>\!\!=} f = \mathsf{ub}~r` for every $`f`.

*Theorem: UB in the set monad ends a path.* In the set monad,
$`\mathsf{ub}~r \mathbin{>\!\!>\!\!=} f = \{\mathsf{ub}~r\}`: UB has no
result for $`f` to go on from.
:::

:::readable Fir.DialectDenote.liftState Fir.DialectDenote.liftState_mapsDenote (fingerprint := "1253374098376535126")
*Definition: a semantics with no memory, in the layer.* A dialect whose
ops have their semantics in $`m` has one in the state layer over $`m`:
each op runs by its rule in $`m` and keeps the memories,
$`\mathrm{denote}_o(\vec{v}) = \mathrm{lift}(\mathrm{denote}^m_o(\vec{v}))`
and the same for $`\mathrm{exit}_o`. Lifting keeps this semantics, by its
definition.
:::

:::readable Fir.DialectDenote.ext Fir.LiftsSetM (pin := Fir.DialectMemDenote) (fingerprint := "7736019510220318093")
*Theorem: semantics are equal op by op.* Two semantics of a dialect in one
monad are equal when each op means the same in both and each terminator
goes to the same places.

*Definition: a dialect that lifts the set monad.* A dialect's
{ref "The-fir-specification--Memory--Memory-obligations"}[semantics with memory]
_lifts_ its semantics in the set monad when, at every naming $`\rho` of its
memories and all layout entries $`\ell` of the run's memories, it is that
semantics lifted into the layer:
$`\mathrm{denote}^{\ell,\rho}_o = \mathrm{lift} \circ \mathrm{denote}_o` and the same
for $`\mathrm{exit}_o`. This ties the two semantics of a dialect whose ops
touch no memory, such as the core dialect, the dialects of the tests and
their sums and lifts. A dialect with an op that touches memory has no such
tie, since the op has no semantics in the set monad.
:::

:::readable Fir.OpLiftsSetM Fir.LiftsSetM.opLifts Fir.LiftsSetM.ofOpLifts (fingerprint := "981677484677804318")
*Definition: an op that touches no memory.* An op $`o` of a dialect is
_tied_ when, at every naming $`\rho` of the dialect's memories and all
layout entries $`\ell` of the run's memories, on every operand vector
$`\vec{v}`,
$`\mathrm{denote}^{\ell,\rho}_o(\vec{v}) = \mathrm{lift}(\mathrm{denote}_o(\vec{v}))`,
and the same for $`\mathrm{exit}_o`: it runs with memory by its rule in
the set monad and keeps the memories. This is the tie of one op, so a
dialect can tie each op on its own, and an op that touches memory can sit
beside tied ones with a proof of its own.

*Theorem: a dialect lifts the set monad exactly when every op is tied.* In
a dialect that lifts the set monad every op is tied, and a dialect whose
every op is tied lifts the set monad, since semantics are equal op by op.
:::

:::readable Fir.Func.memRun_eq (fingerprint := "543011805792552046")
*Theorem: with no memory touched, a run with memory is a run.* For a
dialect whose semantics in the layer is its semantics in the set monad,
lifted, the run with memory of every function from any memories $`S` is
its run in the set monad, each path keeping $`S`:

$$`\mathrm{run}^{\mathrm{mem}}_{M,f}(\vec{v}, k)(S) = \mathrm{map}_{r \mapsto (r, S)}(\mathrm{run}_{M,f}(\vec{v}, k))`

The proof is the
{ref "The-fir-specification--Execution--Monad-morphisms"}[interpreter's morphism theorem]
for the lift, which keeps each op's semantics and keeps frames.
:::

:::readable Fir.Func.memRuns (pin := Fir.Memory.Memories.empty) (fingerprint := "4862065050169048951")
*Definition: the runs with memory of a function.* Where a run names the
dialect's memory $`x` as $`\rho(x)`, whose layout entry is
$`\ell(\rho(x))`, the run with memory of the function $`f` of the module
$`M` on $`\vec{v}` with $`k` steps is its run in the state layer over the
set monad, by the dialect's semantics with memory at $`\ell` and $`\rho`,
from the empty memories. A run of a module gives each memory its entry in
the module's data layout, as `fir-ref`'s modes do. An observer sees what
it returns, not the memories it ends with,
until observations at the end of a run are designed (#233). So the runs
with memory of a function are runs in the sense of the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcomes],
and refinement, fuel monotonicity and progress speak of them.
:::

:::readable Fir.Func.memRuns_eq (fingerprint := "15889437290703559384")
*Theorem: the runs with memory of a dialect that lifts the set monad are
its runs.* At every naming of its memories, a function's runs with memory
are its runs in the set monad, by the theorem above, since its semantics
with memory is its semantics in the set monad, lifted.
:::

:::readable Fir.Func.memRuns_replaceBody_isRefinedBy_of_lawful (fingerprint := "259226704881877648")
*Theorem: congruence in the callee, with no memory touched.* For a lawful
dialect that lifts the set monad, in a valid module, replacing the body of
a function with one that refines it with memory refines every function of
the module with memory, under the conditions of the theorem on runs, the
finitely many argument vectors included: its runs with memory are its
runs. Refined arguments with memory, and congruence with memory for a
dialect whose ops touch memory, hold of every dialect lawful in its
monotonicity
({ref "The-fir-specification--Memory--Replacing-a-callee___-with-memory"}[replacing a callee, with memory]).
Fuel monotonicity and progress hold of the runs with memory of every
dialect, whatever its ops do to the memories
({ref "The-fir-specification--Memory--Runs-with-memory-at-every-budget"}[runs with memory at every budget],
{ref "The-fir-specification--Memory--Progress-and-no-stuck-path___-with-memory"}[progress with memory]).
:::
