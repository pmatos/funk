import VersoManual
import Fir.Execution.Fuel
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on fuel and progress, which renders
`Fir.Execution.Fuel` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Fuel and progress: readable blocks" =>

:::readable Fir.FuelMonotone (fingerprint := "8062891189301265866")
*Definition: fuel monotonicity.* The interpreter counts its steps against
a budget, its _fuel_, so that every run ends: a loop that would go on
forever runs out of fuel instead. A run $`R`, given at every budget
$`n` as $`R_n`, is _fuel-monotone_ when, for all budgets $`n \le m` and
every outcome $`t` other than $`\mathsf{fuel\_exhausted}`:

* _up_: if $`t \in \mathrm{out}(R_n)`, then $`t \in \mathrm{out}(R_m)`. A
  return or UB that a budget reaches, every larger budget reaches too.
* _down_: if $`t \in \mathrm{out}(R_m)`, then $`t \in \mathrm{out}(R_n)`
  or $`\mathsf{fuel\_exhausted} \in \mathrm{out}(R_n)`. A return or UB
  that a larger budget reaches, a smaller one reaches too, unless it can
  run out of fuel there.

Here $`\mathrm{out}(R_n)` is the set of
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcomes]
of the run at budget $`n`. Fuel is a device of the interpreter, not of
the program, so more fuel must never change how a run that ends, ends.
With this property, the observable behaviour does not depend on how the
interpreter counts its steps, and refinement between two functions does
not depend on how many steps each takes.
:::

:::readable Fir.Progress (fingerprint := "9427979162653009165")
*Definition: progress.* A run has _progress_ when, at every budget, it has
some outcome:

$$`\forall n.\ \exists t.\ t \in \mathrm{out}(R_n)`

An empty behaviour, with no outcome at all, refines every source (see the
{ref "The-fir-specification--Execution--Refinement"}[next section]), so a
run with no outcome would pass for a correct one. Progress rules out only
that: a run that has an outcome on one path may still lose others.
:::

:::readable Fir.NeverStuck (fingerprint := "15966192700417047357")
*Definition: no stuck path.* At every budget, no path of the run is
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck]:

$$`\forall n.\ R_n \text{ is not stuck}`

Which paths get stuck can depend on choices, so a run could be stuck on
some paths and have outcomes on others. Those paths would be missing from
its behaviour, and a behaviour with fewer outcomes refines more sources.
:::

:::readable Fir.observable_eq_at (pin := Fir.observable) (fingerprint := "3307528036184768448")
*Theorem: for a fuel-monotone run, the run at a budget that cannot run out
of fuel shows exactly the observable behaviour.* Let $`R` be fuel-monotone, and let $`N` be a budget
at which $`R` cannot run out of fuel:
$`\mathsf{fuel\_exhausted} \notin \mathrm{out}(R_N)`. Then for every
outcome $`t`,

$$`t \in \mathrm{obs}(R) \iff t \in \mathrm{out}(R_N)`

The
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour]
$`\mathrm{obs}(R)` holds each return and UB that some budget reaches, and
$`\mathsf{fuel\_exhausted}` only when every budget runs out of fuel, so it
looks at infinitely many runs. This bridge lemma lets a test harness judge
a function by one run, at a budget large enough that no path runs out: the
returns and UB of that run are exactly those of the function.
:::

:::readable Fir.observable_nonempty (pin := Fir.observable) (fingerprint := "5075025416827717144")
*Theorem: with progress, the observable behaviour is not empty.* If a run
$`R` has progress, then some outcome $`t` is in $`\mathrm{obs}(R)`.

Progress speaks of each budget, and the observable behaviour of all
budgets together, so this is the step that connects them. Either every
budget can run out of fuel, and then $`\mathsf{fuel\_exhausted}` is in the
observable behaviour; or some budget cannot, and then the outcome that
progress gives at that budget is a return or UB, which the observable
behaviour holds. It is what rules out an empty behaviour, which would
refine every source.
:::
