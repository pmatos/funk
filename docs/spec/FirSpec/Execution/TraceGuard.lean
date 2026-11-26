import VersoManual
import Fir.Execution.TraceGuard
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on guards, which renders
`Fir.Execution.TraceGuard` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Guards: the source path that a proof of refinement picks: readable blocks" =>

:::moduleDocs (fingerprint := "57255181865954138")
:::

:::readable Fir.TCfg.Next Fir.TCfg.Next.move (fingerprint := "7921536623754248073")
*Definition: a step of a frame.* A configuration goes on, by a step that
stays in its frame, to another, after the marked trace $`t` and with $`F`
steps of fuel: an op by its own rule, with one of its outcomes; a call of
an external declaration, with one of the external-call rule's outcomes; a
terminator that jumps; or a call whose callee returns at the budget $`U`,
with $`U + \delta + 1` steps of fuel, where $`\delta` is the steps that the
call takes before its callee's. These are the moves other than entering a
callee.

*Theorem.* A step of a frame is a move.
:::

:::readable Fir.TCfg.Next.tAllowed (fingerprint := "9392347268017015659")
*Theorem: the step, then the path.* When a step of a frame goes from
$`c` to $`c_1` after acts that the target's $`t'` refine, each path of the
target that $`c_1`'s run allows, after $`t'`, is allowed by $`c`'s run:
the step, then the path, with the step's fuel added to the budget and, for
a callee that returns, its steps left added to the return's.
:::

:::readable Fir.TCfg.Matched (fingerprint := "7865944623453864213")
*Definition: matched configurations.* The source's configuration is matched
with the target's when both run the same ops of the same function, from
an environment and a traced state that the target's refine.
:::

:::readable Fir.TCfg.Guard Fir.TCfg.Guard.always Fir.TCfg.Guard.eq (fingerprint := "12001343867501197807")
*Definition: a guard.* A guard of the source module $`M` and the target
module $`M'`, under an agreement of two external calls, is a set $`G` of
pairs of configurations, the source's first, closed in three ways:

* when the target goes on by a step of its frame from a pair of $`G`, and
  the source has a step of its frame that ends matched with the target's,
  with acts that the target's refine, the source has such a step that ends
  in a pair of $`G`;
* when the target enters a callee that both modules run, and the source
  calls it on arguments that the target's refine, with acts that the
  target's refine and from a traced state that the target's refines, the
  source has such a call whose entry into the callee is paired with the
  target's in $`G`;
* when the target calls an external declaration, and the source calls it
  in the same way, the source has such a call where the two agree.

No clause says that the source has a step: each says only which of its
steps to take.

*Theorems.* Where two external calls always agree, the set of all pairs is
a guard. In one module, under an agreement that every call has with
itself, the pairs of equal configurations form a guard, when the
refinement of values and of acts is reflexive: the source takes the
target's own step.
:::

:::readable Fir.TraceCallsRefined.callee_allowed (fingerprint := "17626441752865209854")
*Theorem: a callee, allowed.* A return or UB of a call's callee in the
target, in its frame, is allowed at some budget by the source's callee in
its frame, on arguments and from a traced state that the target's refine:
the same function, when its run of ops from a frame entered is allowed
(the induction) from the entry paired in a guard, or a traced black box.
:::
