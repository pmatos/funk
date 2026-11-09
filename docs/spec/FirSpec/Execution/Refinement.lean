import VersoManual
import Fir.Execution.Refinement
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refinement, which renders
`Fir.Execution.Refinement` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refinement: readable blocks" =>

:::moduleDocs (fingerprint := "17708591231383344787")
:::

:::readable Fir.Outcome.IsRefinedBy (fingerprint := "12394458454088004366")
*Definition: one outcome allows another.* A source
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome]
$`s` allows a target outcome $`t`, written $`s \sqsubseteq t`, in exactly
these cases:

$$`\mathsf{ub}~r \sqsubseteq t`

$$`\mathsf{fuel\_exhausted} \sqsubseteq \mathsf{fuel\_exhausted}`

$$`\mathsf{ret}~a \sqsubseteq \mathsf{ret}~b \iff a \sqsubseteq b`

UB in the source allows any target outcome, since the source promised
nothing. Two returns agree when the target's observation
{ref "The-fir-specification--Execution--Values-and-refinement"}[refines]
the source's, so a returned poison allows any returned value. A source
that diverges allows only a target that diverges. Nothing else is allowed:
a source that returns does not allow UB, nor divergence, in the target.
:::

:::readable Fir.Behaviour.IsRefinedBy (fingerprint := "10967825991267535108")
*Definition: one behaviour refines another.* A target behaviour $`T`
refines a source behaviour $`S` when every outcome of the target is allowed
by some outcome of the source:

$$`S \sqsubseteq T \iff \forall t \in T.\ \exists s \in S.\ s \sqsubseteq t`

This is the correctness criterion of every compiler pass and every
backend: what the compiled code may do, the source must allow. The target
may do less than the source, for example by fixing a choice that
$`\mathsf{freeze}` leaves open, and it may do anything where the source
has UB. That freedom is what lets a compiler optimize, and the relation
draws its limit.
:::

:::readable Fir.Behaviour.ub_isRefinedBy (fingerprint := "18049635087314843505")
*Theorem: a source that may hit UB is refined by every target.* If
$`\mathsf{ub}~r \in S` for some reason $`r`, then $`S \sqsubseteq T` for
every behaviour $`T`.

UB on one choice of the source is enough: every target outcome is allowed
by that UB. This is the rule that lets a compiler assume that UB does not
happen.
:::

:::readable Fir.Outcome.isRefinedBy_refl Fir.Outcome.isRefinedBy_trans Fir.Behaviour.isRefinedBy_refl Fir.Behaviour.isRefinedBy_trans (fingerprint := "1315522947282396139")
*Theorem: refinement of outcomes, and of behaviours, is reflexive when
refinement of observations is reflexive, and transitive when that is
transitive.*

* If $`o \sqsubseteq o` for every observation $`o`, then
  $`t \sqsubseteq t` for every outcome $`t`, and $`B \sqsubseteq B` for
  every behaviour $`B`.
* If refinement of observations is transitive, then $`s \sqsubseteq m` and
  $`m \sqsubseteq t` give $`s \sqsubseteq t` for outcomes, and
  $`A \sqsubseteq B` and $`B \sqsubseteq C` give $`A \sqsubseteq C` for
  behaviours.

Transitivity is what makes a pipeline of correct passes correct: each pass
refines the output of the one before, so the last output refines the
first input.
:::

:::readable Fir.FuncRuns (fingerprint := "9412822538535874787")
*Definition: the runs of a function.* For argument vectors in a set $`A`,
the runs of a function give, for each argument vector $`a \in A` and each
budget $`n`, the run $`F(a)_n` of the function on $`a` at budget $`n`.
For a function of a module, $`A` is the set of argument vectors of its
parameter types; the section on
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function]
gives them.
:::

:::readable Fir.FuncRuns.IsRefinedBy (fingerprint := "15717838552818472061")
*Definition: one function refines another.* A target function $`G`
refines a source function $`F` when, on every argument vector $`a`, the
target's observable behaviour refines the source's:

$$`\begin{aligned} & F \sqsubseteq G \\ \iff\ & \forall a \in A.\ \mathrm{obs}(F(a)) \sqsubseteq \mathrm{obs}(G(a)) \end{aligned}`

Here $`\mathrm{obs}(F(a))` is the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour]
of the runs of $`F` on $`a`. Every argument vector counts, poison
included, since a value of $`\mathsf{i}N` may be poison and a caller may
pass one. This is the relation that a pass which rewrites a function must
meet.
:::

:::readable Fir.FuncRuns.isRefinedBy_refl Fir.FuncRuns.isRefinedBy_trans (fingerprint := "13690962484335325785")
*Theorem: refinement of functions is reflexive when refinement of
observations is reflexive, and transitive when that is transitive.* Under
the first condition $`F \sqsubseteq F` for every function's runs $`F`;
under the second, $`F \sqsubseteq G` and $`G \sqsubseteq H` give
$`F \sqsubseteq H`. So a function may be left as it is, and passes that
each refine a function may run one after another.
:::
