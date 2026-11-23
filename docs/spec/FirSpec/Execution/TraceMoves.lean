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

:::moduleDocs (fingerprint := "15131467457563937667")
:::

:::readable Fir.TCfg Fir.TCfg.exh Fir.TCfg.ub (fingerprint := "13457895528575087257")
*Definitions: configurations.* A configuration of a traced run of ops is a
function $`f`, its environment, the ops still to run and the traced state.
Its run in $`M` at each budget is $`f`'s traced run of those ops. The paths
that run out of fuel are those that end $`\mathsf{fuelExhausted}`, by their
marked traces; it hits UB at the budget $`n` for the reason $`r` after a
marked trace $`m` when a path ends so.
:::

:::readable Fir.TCfg.Move (fingerprint := "15249237135957554293")
*Definition: a move.* A configuration goes on to the next in $`M` after the
marked trace $`t` with $`F` steps of fuel:

* by its first op, which runs by its own rule, with one of its outcomes after
  $`t`, binding its results, with $`F = 1`;
* by its terminator, which jumps after $`t` to a block of the function, with
  $`F = 1`;
* by a call to a declaration, which runs by the external-call rule with one
  of its outcomes after $`t`, binding its results, with $`F = \delta + 1`;
* by a call, which enters the callee's entry block with a frame entered,
  with $`F = \delta + 1`;
* by a call whose callee returns at the budget $`U` after $`t`, in a traced
  state with its frame left, binding its results, with
  $`F = U + \delta + 1`.

In the last three, the op calls the symbol after the marked trace $`t_0`
and $`\delta` steps of fuel: with $`t_0` empty and $`\delta = 0` when it
names its callee, and after its rule's trace and $`\delta = 1` when the rule
picks it (#235); the move's marked trace is $`t_0` followed by the call's.
:::

:::readable Fir.TCfg.exh_zero Fir.Func.TCallsAt.ticks Fir.TCfg.Move.tStep Fir.TCfg.Move.ub Fir.TCfg.Move.callHead (fingerprint := "2270039748249535211")
*Theorems: moves move runs.* With no fuel a run runs out of fuel after no
marked trace. When every path of every op, of every external call and of
every rule that picks a callee shows exactly one step, the acts of a call
before its callee show as many steps as the call takes before its callee's,
none or one, and each move
of a configuration is a move, in the sense of runs, of the paths of its run
that run out of fuel. UB of the configuration a move goes on to is UB of the
configuration after the move's marked trace. A move that shows no step
enters a callee: it goes on to the entry block of its first op's callee.
:::
