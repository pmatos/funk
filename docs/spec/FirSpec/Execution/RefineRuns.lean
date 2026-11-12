import VersoManual
import Fir.Execution.RefineRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refined arguments, which renders
`Fir.Execution.RefineRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refined arguments: readable blocks" =>

:::moduleDocs (fingerprint := "15695279757290185778")
:::

:::readable Fir.Func.runs_isRefinedBy_of_calls (pin := Fir.CallsRefined) (pin := Fir.Func.OpsMonotone) (pin := Fir.Behaviour.IsRefinedBy) (pin := Fir.Outcome.IsRefinedBy) (pin := Fir.observable) (fingerprint := "17030029660348966586")
*Theorem: on refined arguments, a function refines itself in a module
that runs each call as the source does.* In every dialect, let the target
module $`M'`
run each call as the source module $`M` does, with some bound $`\beta`:
each symbol names the same function in both, or a
{ref "The-fir-specification--Execution--Calls-as-black-boxes"}[black box].
Let every function of $`M` have
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops],
and let $`f` be a function with monotone ops. Then for all argument
vectors $`a` and $`a'` of the parameter types of $`f` with
$`a_i \sqsubseteq a'_i` for each $`i`:

$$`\mathrm{obs}(F_M(a)) \sqsubseteq \mathrm{obs}(F_{M'}(a'))`

where $`F_M(a)` is the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[runs]
of $`f` in $`M` on $`a`, and $`\mathrm{obs}` their
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[observable behaviour].
Calls and recursion are included. Both function-level refinement theorems,
on refined arguments below and on
{ref "The-fir-specification--Execution--Replacing-a-callee"}[replacing a callee],
are instances of this one.

Each outcome of the target is allowed, as
{ref "The-fir-specification--Execution--Refinement"}[refinement]
asks, by an outcome of the source:

* A return or UB at some budget: the source hits UB at some budget, which
  allows anything, or returns at some budget values that the target's
  refine, by the section on
  {ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[returns and UB].
* Divergence, when the target runs out of fuel at every budget. If the
  source hits UB at some budget, that allows it. If not, then at each
  budget $`N` the target runs out of fuel at $`(\beta + 1) \cdot (N + 1)`,
  on a path that the source allows at $`N`, by the section on
  {ref "The-fir-specification--Execution--Running-out-of-fuel___-followed-back"}[running out of fuel]:
  so the source runs out of fuel at every $`N`, and diverges.

The theorem asks nothing of validity: it compares outcomes, and a stuck
path is none. It means most for valid modules, whose runs have no stuck
path and an outcome at every budget, so that neither behaviour is empty
or misses a path.
:::

:::readable Fir.Func.runs_args_isRefinedBy (fingerprint := "670706871179699855")
*Theorem: refined arguments.* In every dialect, let every function of the module $`M`
have monotone ops, and let $`f` be a function with monotone ops. Then for
all argument vectors $`a` and $`a'` of the parameter types of $`f` with
$`a_i \sqsubseteq a'_i` for each $`i`, a poison replaced by any value of
its type for example:

$$`\mathrm{obs}(F_M(a)) \sqsubseteq \mathrm{obs}(F_M(a'))`

Calls and recursion are included. It is the case of the previous theorem
where the target module is the source, every symbol names the same
function, and there is no black box.

A call passes its arguments to its callee, so a call on arguments that
refine others refines the call on those others. This is the counterpart,
for a whole function, of
{ref "The-fir-specification--Execution--Poison-classes"}[monotonicity],
which speaks only of ops that run by their own rule: a call has no rule
of its own (ADR-2026-10-29-2006). A compiler may then, for example, pass
a defined value where the source passed poison, or replace an argument
by one that a pass has refined.
:::
