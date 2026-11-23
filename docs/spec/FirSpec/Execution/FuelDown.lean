import VersoManual
import Fir.Execution.FuelDown
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a run that runs out of fuel with less
fuel, which renders `Fir.Execution.FuelDown` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "A run that runs out of fuel, with less fuel: readable blocks" =>

:::moduleDocs (fingerprint := "3584457174899988588")
:::

:::readable Fir.Func.runOps_exhausted_down (pin := Fir.Ahead) (fingerprint := "5164694788063173760")
*Theorem: a run that runs out of fuel runs out of fuel with fewer steps.*
For every module $`M`, budget $`n`, number of steps $`j`, function $`f`,
environment $`E` and ops $`o^*`, with
$`R_m = \mathrm{run}_M(m, f, E, o^*)` for every budget $`m`:

$$`\begin{aligned} & \mathsf{fuel\_exhausted} \in R_{n + j} \\ \implies\ & \mathsf{fuel\_exhausted} \in R_n \end{aligned}`

The smaller run takes the same path and runs out sooner. On a call whose
callee is picked and that has no step left for the call, the smaller run
runs out of fuel after the rule. On any other call, the
callee with $`j` fewer steps runs out of fuel too, or returns what it
returned, leaving $`j` fewer steps, as the section on
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function]
proves; the caller then goes on with $`j` fewer steps. The section on
{ref "The-fir-specification--Execution--Replacing-a-callee"}[replacing a callee]
uses this to find, for each argument vector, a budget from which a run
never runs out of fuel, unless it runs out at every budget.
:::
