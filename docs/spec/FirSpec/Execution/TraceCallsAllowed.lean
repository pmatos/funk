import VersoManual
import Fir.Execution.TraceCallsAllowed
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on every return and UB of the target,
allowed call by call, which renders `Fir.Execution.TraceCallsAllowed`
(ADR-2026-11-05-2012). Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Every return and UB of the target, allowed, call by call: readable blocks" =>

:::moduleDocs (fingerprint := "15332149882466598087")
:::

:::readable Fir.TraceCallsRefined.callee_allowed (fingerprint := "7369591944401893609")
*Theorem: a callee, allowed.* A return or UB of a call's callee in the target, in its frame, is
allowed at some budget by the source's callee in its frame, on arguments
and from a traced state that the target's refine: the same function, when
its run of ops from a frame entered is allowed (the induction), or a
traced black box.
:::

:::readable Fir.Func.traceOps_tAllowed (fingerprint := "745176982441380073")
*Theorem: every return and UB of the target, allowed.* Let every call name
the same function in both modules or a traced black box, and the source
declare each symbol that the target declares. Let every terminator and
every op with no callee be monotone in the traced layer of marked traces,
among the ops of the source module's functions, of $`f` and of the ops
$`os`, and the external-call rule at each of their other ops. Then, from
environments $`\rho \sqsubseteq \rho'` and traced states $`s \sqsubseteq s'`,
each path of the target's run of
$`os` at any budget is allowed at some budget by the source's run of the
same ops, comparing acts. A callee's return at the budget $`N_1` and the
rest's at $`N_2` give the whole's at $`N_1 + N_2 + 1`.
:::
