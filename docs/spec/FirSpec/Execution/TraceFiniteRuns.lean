import VersoManual
import Fir.Execution.TraceFiniteRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on finitely many traces at one budget, which renders
`Fir.Execution.TraceFiniteRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Finitely many traces at one budget: readable blocks" =>

:::moduleDocs (fingerprint := "1522982593365390845")
:::

:::readable Fir.ExceptStepFinite Fir.ExceptStepFinite.pure Fir.ExceptStepFinite.liftExcept Fir.ExceptStepFinite.lift Fir.ExceptStepFinite.bind Fir.ExceptStepFinite.inFrame (fingerprint := "12872737153588007309")
*Definition.* A computation of the interpreter in the traced layer of
marked traces has finitely many outcomes when, from each state and for
each answer stream, the values it may end with, with marked traces whose
acts agree with the stream and the states, lie in one finite list.

*Theorems.* `pure` and a check have one outcome. An op's rule with finitely
many outcomes, run by the interpreter, has finitely many. A sequence of
computations with finitely many has finitely many, the second given the
rest of the stream after the first's acts. A run in a call's frame has its
ops' outcomes, its frame left.
:::

:::readable Fir.Func.traceOps_finite (fingerprint := "3034181259275600543")
*Theorem.* When every op that runs by its own rule has finitely many
outcomes in the traced layer of marked traces, given the world's answers,
a traced run of ops at one budget has finitely many, from any environment
and traced state, calls and recursion included.
:::
