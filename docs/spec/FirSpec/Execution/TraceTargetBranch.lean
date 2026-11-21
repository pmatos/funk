import VersoManual
import Fir.Execution.TraceTargetBranch
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the target's branch of moves, which shows its whole stream, which renders
`Fir.Execution.TraceTargetBranch` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The target's branch: readable blocks" =>

:::moduleDocs (fingerprint := "15377116653020393417")
:::

:::readable Fir.exists_seq_of_step (fingerprint := "17767689729752815650")
*Theorem: dependent choice.* Given a first element that meets $`P_0`, and, at
each place $`i`, for each element that meets $`P_i` a next that meets
$`P_{i+1}` and is related to it by $`R_i`, there is a sequence of elements,
each meeting $`P` at its place and related to the next. It follows from the
axiom of choice.
:::

:::readable Fir.Stream.Closed Fir.Stream.Closed.drop Fir.Stream.Closed.avail Fir.Stream.Cons.append Fir.TBranch.pre_succ (fingerprint := "5465568138423741501")
*Definition: a closed stream.* A stream is closed when, once it has no act at
a place, it has none at any later place.

*Theorems.* A closed stream after some places is closed, and has acts at
every place before one where it has an act. A trace that shows a stream's
first acts, then a trace that shows acts of the stream after them, shows
acts of the stream. One more move of a branch puts its marked trace at the
end.
:::

:::readable Fir.Module.not_callChain_of_seq (fingerprint := "10193846424752753883")
*Theorem: an endless chain of calls.* A sequence of op lists, each starting
with a call of a function whose entry block is the next, starts no chain of
calls of any length: a chain ends at ops that do not start with such a
call.
:::

:::readable Fir.TBranchT Fir.TGood.branch (fingerprint := "10938712079326238891")
*Definition: a branch of the target.* Configurations $`c_0, c_1, \ldots`,
each going on to the next by a move of the marked trace $`t_i` with fuel
$`F_i`, each showing the stream $`T_i` with the deadlines $`K_i` at
unboundedly many budgets, where $`T_{i+1}` and $`K_{i+1}` are $`T_i` and
$`K_i` after the move, whose acts are acts of $`T_i`, and each deadline past
them at least its steps.

*Theorem.* Under the hypotheses of the pigeonhole step, a configuration whose
run shows a stream at unboundedly many budgets starts a branch of the target,
by the pigeonhole step at each configuration and dependent choice.
:::

:::readable Fir.TBranchT.stream_eq Fir.TBranchT.cons_pre Fir.TBranchT.exhaustive Fir.TBranchT.acts_eq Fir.TBranchT.tShows (fingerprint := "16447143394530488718")
*Theorems: the branch shows its whole stream.* The stream of $`c_{i+j}` is
that of $`c_i` after the acts of the $`j` moves between them, and the moves
from $`c_i` show acts of its stream. Each act of the stream of $`c_i` is
shown by some moves from it. Otherwise the moves from some configuration on
would show no act, each deadline would then cap their steps, so from some
move on each would show no step. A move with no step enters a callee, so
from there the ops start an endless chain of calls, and a run of such ops
shows nothing at any budget (`Func.traceOps_silent`), against the act still
due.

So the acts of the moves from $`c_i` are its stream, when that stream is
closed, and each configuration of the branch shows its stream at every
budget, with the deadlines of the moves from it.
:::
