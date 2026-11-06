import VersoManual
import Fir.Execution.Behaviour
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on outcomes and behaviours, which
renders `Fir.Execution.Behaviour` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Outcomes and behaviours: readable blocks" =>

:::readable Fir.Outcome (fingerprint := "2974526082486249930")
*Definition: an outcome.* An outcome is how one run of a function ends,
seen from outside. Each dialect fixes the kind of its observations, what an
observer sees of a return; in the core dialect it is the list of returned
values.

```grammar Fir.Outcome
\mathit{outcome}
ret             \mathsf{ret}~o
ub              \mathsf{ub}~\mathit{reason}
fuelExhausted   \mathsf{fuel\_exhausted}
```

* $`\mathsf{ret}~o`: the run returns, and an observer sees the observation
  $`o`.
* $`\mathsf{ub}~\mathit{reason}`: the run hits {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[immediate UB]. The
  reason is for people, and refinement ignores it.
* $`\mathsf{fuel\_exhausted}` (`fuelExhausted` in the Lean): the run used
  up its budget of steps before it ended. In an observable behaviour,
  below, it stands for a run that never ends.
:::

:::readable Fir.Result (fingerprint := "11598918657883269255")
*Definition: a result.* A result is how a run ends when it neither hits UB
nor gets stuck: it returns, or runs out of fuel.

```grammar Fir.Result
\mathit{result}
ret             \mathsf{ret}~o
fuelExhausted   \mathsf{fuel\_exhausted}
```

UB and stuck are not results, because the interpreter carries them apart
from the values it computes: UB as an effect, and stuck on each path, as
below.
:::

:::readable Fir.Ev (fingerprint := "2983337237760179787")
*Definition: one way a computation may end.* A computation that produces
values of a set $`A` ends with a value of $`A`, or with immediate UB.

```grammar Fir.Ev
\mathit{end}_A
ok   \mathsf{ok}~a \quad (a \in A)
ub   \mathsf{ub}~\mathit{reason}
```
:::

:::readable Fir.SetM (pin := Fir.SetM.instMonad) (pin := Fir.SetM.instMonadChoice) (pin := Fir.SetM.instMonadUB) (fingerprint := "1177755487130324875")
*Definition: the set monad.* $`\mathsf{freeze}` of poison may choose any value,
so one function on one input can run in many ways. The interpreter
computes all of them at once by reading each computation as the set of
the ways it may end: a computation of values of $`A` is a set of
$`\mathit{end}_A`. This reading is called the set monad, and the
interpreter runs in it to compute a function's behaviour.

The ways to build computations read as follows. A computation that ends
at once with $`a` is the set $`\{\mathsf{ok}~a\}`. To run $`x`, then run
$`g` on the value that $`x` ends with, written
$`x \mathbin{>\!\!>\!\!=} g`, collects every way $`g(a)` may end for each
value $`a` that $`x` may end with, and every UB of $`x`:

$$`\begin{aligned} x \mathbin{>\!\!>\!\!=} g = {} & \{ e \mid \exists a.\ \mathsf{ok}~a \in x \,\wedge\, e \in g(a) \} \\ \cup {} & \{ \mathsf{ub}~r \mid \mathsf{ub}~r \in x \} \end{aligned}`

The two effects of the core dialect are

$$`\mathrm{choose}(w) = \{ \mathsf{ok}~b \mid b \text{ a vector of } w \text{ bits} \}`

$$`\mathrm{ub}(r) = \{ \mathsf{ub}~r \}`

so a choice may end with any bits, and UB ends the computation: what
follows it never runs.
:::

:::readable Fir.Stuck (fingerprint := "4791329397428074215")
*Definition: why a path is stuck.* A path of a run is _stuck_ when it
reaches a case that validation rules out, such as a use of a value that
was never defined, or an operand of the wrong type. It carries a reason,
for people. A stuck path is neither an outcome nor UB: `fir-ref` reports
it as stuck. The obligations of the
{ref "The-fir-specification--Execution--Fuel-and-progress"}[next section]
state that a valid module never gets stuck, and later sections prove it.
:::

:::readable Fir.Run (fingerprint := "13360745407864905462")
*Definition: a run at one budget.* A run at one fuel budget is the set of
the ways its paths may end. Each path ends with a result, with immediate
UB, or stuck:

$$`\begin{aligned} \mathit{path\_end} ::= {} & \mathsf{ret}~o \mid \mathsf{fuel\_exhausted} \\ \mid {} & \mathsf{ub}~\mathit{reason} \mid \mathsf{stuck}~s \end{aligned}`

Stuck is part of each path, not a mark on the whole set, because which
paths get stuck can depend on choices: in a module that has not been
validated, $`\mathsf{freeze}` and then $`\mathsf{cond\_br}` can lead to a
block that uses an undefined value on one path only. This is the set that
the interpreter computes.
:::

:::readable Fir.Run.outcomes Fir.Run.IsStuck (fingerprint := "6991509419242234263")
*Definition: the outcomes of a run, and a stuck run.* The outcomes
$`\mathrm{out}(R)` of a run $`R` at one budget are the ends of its paths,
as in the previous definition, with the stuck ends left out: a return, UB
or running out of fuel is an outcome of $`R` when some path of $`R` ends
with it.

$$`\begin{aligned} \mathsf{ret}~o \in \mathrm{out}(R) & \iff \mathsf{ret}~o \in R \\ \mathsf{ub}~r \in \mathrm{out}(R) & \iff \mathsf{ub}~r \in R \end{aligned}`

$$`\begin{aligned} & \mathsf{fuel\_exhausted} \in \mathrm{out}(R) \\ \iff\ & \mathsf{fuel\_exhausted} \in R \end{aligned}`

No outcome comes from a path that ends $`\mathsf{stuck}~s`. The run is
_stuck_ when some path of it ends stuck: $`\exists s.\ \mathsf{stuck}~s \in R`.
Outcomes and stuck are kept apart so that refinement compares only
outcomes, while a stuck run is reported on its own.
:::

:::readable Fir.Behaviour (fingerprint := "8033448681392590586")
*Definition: a behaviour.* A behaviour is a set of outcomes: every way that
a function, run on one input, may end. A run that never chooses has one
outcome; $`\mathsf{freeze}` of poison may give it several
(ADR-2026-10-29-2017).
:::

:::readable Fir.observable (fingerprint := "443252409836460758")
*Definition: the observable behaviour of a run that takes fuel.* Let
$`R_n` be the run at budget $`n`, for every $`n`. Its observable behaviour
$`\mathrm{obs}(R)` holds each return and each UB that some budget reaches,
and $`\mathsf{fuel\_exhausted}` when every budget can run out of fuel:

$$`\begin{aligned} \mathsf{ret}~o \in \mathrm{obs}(R) & \iff \exists n.\ \mathsf{ret}~o \in \mathrm{out}(R_n) \\ \mathsf{ub}~r \in \mathrm{obs}(R) & \iff \exists n.\ \mathsf{ub}~r \in \mathrm{out}(R_n) \end{aligned}`

$$`\begin{aligned} & \mathsf{fuel\_exhausted} \in \mathrm{obs}(R) \\ \iff\ & \forall n.\ \mathsf{fuel\_exhausted} \in \mathrm{out}(R_n) \end{aligned}`

Running out of fuel at one budget says only that the budget was too small;
running out at every budget is divergence, a run that never ends. So the
observable behaviour does not depend on any one budget. The runs of a
function of a module on its arguments are such a run, and the function's
observable behaviour on those arguments is this set: it is what
refinement compares.
:::
