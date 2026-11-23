import VersoManual
import Fir.Execution.TraceMoveFinite
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on finitely many moves, which renders
`Fir.Execution.TraceMoveFinite` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Finitely many moves: readable blocks" =>

:::moduleDocs (fingerprint := "18190458391005563071")
:::

:::readable Fir.List.exists_often_of_mem Fir.Act.agrees_actsOf_append (fingerprint := "10631168897226339898")
*Lemmas.* When each of infinitely many numbers is related to some element
of a list, one element is related to infinitely many of them. Acts that
agree with an answer stream, the first of them a call's, are the call's
acts agreeing with it, then the rest agreeing with it after them.
:::

:::readable Fir.Func.TCallsAt.finite (fingerprint := "14009579729718733153")
*Theorem: finitely many calls of an op.* When every op that runs by its
own rule, every external call and every rule that picks a callee has
finitely many outcomes, given the world's answers, an op calls, on its
operands and from a traced state, finitely many symbols on finitely many
arguments, after finitely many steps and acts that agree with an answer
stream, from finitely many traced states: one callee when it names it, and
one for each outcome of the rule that picks it otherwise.
:::

:::readable Fir.TCfg.moves_finite Fir.TCfg.calls_finite (fingerprint := "12551552209528122028")
*Theorems: finitely many moves.* Under the same hypothesis, a
configuration has finitely many moves of at most two steps of fuel whose
acts agree with an answer stream: the outcomes of its first op, each with
the configuration it goes on to; the outcomes of its external call; the
callee it may enter; and the returns of a callee with one step of fuel. Its
first op calls finitely many functions of the module, after finitely many
steps and acts that agree with the stream, from finitely many traced
states. Two steps, not one, since an op that picks its callee spends its
rule's step and the call's before the callee runs.
:::
