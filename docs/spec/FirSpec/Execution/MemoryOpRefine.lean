import VersoManual
import Fir.Execution.MemoryOpRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on monotonicity with memory, which
renders `Fir.Execution.MemoryOpRefine` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Monotonicity with memory: readable blocks" =>

:::moduleDocs (fingerprint := "16656510284723147131")
:::

:::readable Fir.StateRefinedBy (pin := Fir.SetM.IsRefinedBy) (pin := Fir.Ev.IsRefinedBy) (fingerprint := "12617051221931686737")
*Definition: computations with memory that refine others.* For a
relation $`r` on results, a computation $`c'` of the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer]
refines $`c` when, from states $`S \sqsubseteq S'`
({ref "The-fir-specification--Memory--Refining-memories"}[refining memories]),
each way $`c'(S')` may end is allowed by a way $`c(S)` may end: UB, which
allows anything, or, for a result $`a'` with the state $`T'`, a result $`a`
with a state $`T` such that $`r(a, a')` and $`T \sqsubseteq T'`.

$$`\forall S \sqsubseteq S'.\ \forall e' \in c'(S').\ \exists e \in c(S).\ e = \mathsf{ub} \lor (e = (a, T) \land e' = (a', T') \land r(a, a') \land T \sqsubseteq T')`
:::

:::readable Fir.StateRefinedBy.lift Fir.StateRefinedBy.of_lift Fir.StateRefinedBy.map (fingerprint := "10539029185112644879")
*Theorems: lifting and mapping keep refinement.* Computations $`s` and
$`t` of the set monad, run in the state layer, keep the states they start
from, so they refine each other there exactly as they do in the set monad:
the lift of $`t` refines the lift of $`s` when $`t` refines $`s`, and
conversely when it does from one state that refines itself. Mapping the
results of two computations by a map $`f` that takes results related by
$`r` to results related by $`r'` keeps refinement.
:::

:::readable Fir.OpMemMonotone Fir.MemMonotone Fir.LawfulDialectMonotone (pin := Fir.OpMonotone) (fingerprint := "8181747639553358221")
*Definitions: monotone with memory, and a dialect lawful in its
monotonicity.* In a semantics of a dialect in the state layer, the op $`o`
is monotone when, on operand vectors $`\vec{v} \sqsubseteq \vec{v}'`
position by position, $`\mathrm{denote}_o(\vec{v}')` refines
$`\mathrm{denote}_o(\vec{v})` with its results refining position by
position, when $`o` is not a terminator, and $`\mathrm{exit}_o(\vec{v}')`
refines $`\mathrm{exit}_o(\vec{v})` with the same exit, when it is: from
memories that refine others, as the relation above says.

An op is _monotone with memory_ when it is monotone in the dialect's
semantics with memory at every naming $`\rho` of its memories, with any
layout entries. A dialect is _lawful in its monotonicity_ when every valid op
instance that is a terminator or calls no function is monotone with
memory. The class asks for no semantics in the set monad, so a dialect
whose ops touch memory can meet it. It is what refinement with memory asks
of a dialect, as
{ref "The-fir-specification--Execution--Poison-classes"}[monotonicity] in
the set monad is what refinement asks of runs in the set monad.
:::

:::readable Fir.MemMonotone.ofLifts Fir.MemMonotone.setM Fir.LawfulDialectMonotone.ofLawful (pin := Fir.OpLiftsSetM) (fingerprint := "17237915660719983917")
*Theorems: monotonicity with memory, for an op that touches no memory.* An
op that is
{ref "The-fir-specification--Memory--Runs-with-memory"}[tied] and
monotone in the set monad is monotone with memory: its rule keeps the
memories it starts from, and so their refinement. In a dialect that lifts
the set monad, every op is tied, and an op monotone with memory is monotone
in the set monad too. So a lawful dialect that lifts the set monad is
lawful in its monotonicity: so are the dialects of the tests that lift the
set monad, and the core dialect is, op by op, from each op's own tie. The
alloc dialect of the tests, whose op allocates, lifts no semantics in the
set monad; it is lawful in its monotonicity by its semantics with memory
alone.
:::
