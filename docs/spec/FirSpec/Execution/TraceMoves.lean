import VersoManual
import Fir.Execution.TraceMoves
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on configurations of a traced run of ops and their moves, which renders
`Fir.Execution.TraceMoves` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Configurations and their moves: readable blocks" =>

:::moduleDocs (fingerprint := "16508911543304979288")
:::

:::readable Fir.TCfg Fir.TCfg.exh Fir.TCfg.ub (fingerprint := "13457895528575087257")
*Definitions: configurations.* A configuration of a traced run of ops is a
function $`f`, its environment, the ops still to run and the traced state.
Its run in $`M` at each budget is $`f`'s traced run of those ops. The paths
that run out of fuel are those that end $`\mathsf{fuelExhausted}`, by their
marked traces; it hits UB at the budget $`n` for the reason $`r` after a
marked trace $`m` when a path ends so.
:::

:::readable Fir.TCfg.Move (fingerprint := "10586812879306018311")
*Definition: a move.* A configuration goes on to the next in $`M` after the
marked trace $`t` with $`F` steps of fuel:

* by its first op, which runs by its own rule, with one of its outcomes after
  $`t`, binding its results, with $`F = 1`;
* by its terminator, which jumps after $`t` to a block of the function, with
  $`F = 1`;
* by a call to a declaration, which runs by the external-call rule with one
  of its outcomes after $`t`, binding its results, with $`F = 1`;
* by a call, which enters the callee's entry block with a frame entered, after
  no marked trace, with $`F = 1`;
* by a call whose callee returns at the budget $`U` after $`t`, in a traced
  state with its frame left, binding its results, with $`F = U + 1`.
:::

:::readable Fir.Func.traceCall_retPaced Fir.Func.traceCall_retPaced_le Fir.Func.traceCall_cut_ret (fingerprint := "13240732546906488507")
*Theorems: a callee's return.* When every path of every op and
of every external call shows exactly one
step, a return of a callee's ops in its frame with $`k` steps left after the
marked trace $`t` at the budget $`U` shows a step, and leaves
$`U - k \ge \mathrm{ticks}(t)`. When $`W` exceeds the length of every chain of
calls of the module, $`U - k \le W \cdot \mathrm{ticks}(t)`.

Cut to a budget $`n < U`, the return comes back with $`k - (U - n)` steps left
when $`k \ge U - n`. Otherwise the callee runs out of fuel at $`n`, after a
marked trace that starts $`t`, of at most $`n` steps, which is all of $`t` or
has $`n \le W m + c` for its $`m` steps and a chain of $`c` calls.
:::

:::readable Fir.TCfg.exh_zero Fir.TCfg.Move.tStep Fir.TCfg.Move.ub Fir.TCfg.Move.callHead (fingerprint := "13676758166879624154")
*Theorems: moves move runs.* With no fuel a run runs out of fuel after no
marked trace. When every path of every op and
of every external call shows exactly one step, each move
of a configuration is a move, in the sense of runs, of the paths of its run
that run out of fuel. UB of the configuration a move goes on to is UB of the
configuration after the move's marked trace. A move that shows no step
enters a callee: it goes on to the entry block of its first op's callee.
:::
