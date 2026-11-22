import VersoManual
import Fir.Execution.TraceMoveSel
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the pigeonhole step of the target's branch, which renders
`Fir.Execution.TraceMoveSel` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The pigeonhole step: readable blocks" =>

:::moduleDocs (fingerprint := "4591464512892131575")
:::

:::readable Fir.TGood.move (fingerprint := "4591464512892131575")
*Theorem: the pigeonhole step.* Let every path of every op and of every
external call show exactly one step, and every op that runs by its own
rule, and every external call,
have finitely many outcomes,
given the world's answers. A configuration $`c` whose run shows $`T` with
$`K` at unboundedly many budgets goes on by a move of the marked trace $`t`
to a configuration whose run shows $`T` after $`t`'s acts, with the
deadlines less $`t`'s steps, at unboundedly many budgets. The move's acts are
acts of $`T`, and each deadline past them is at least its steps.

The proof takes, for each $`m`, a path at a budget of at least $`m` that sees
$`T` for $`m` acts, and asks which move it starts with:

* _A move of one step of fuel._ There are finitely many, given the answers
  that $`T` fixes, so one of them is taken by infinitely many of the paths.
* _A callee whose returns show unboundedly many steps._ Cut at a budget past
  the deadline of the acts asked for, each such return runs out of fuel
  inside the callee after a path that sees those acts. So the move that
  enters the callee is taken.
* _Returns with boundedly many steps._ Each return then takes at most a
  bounded budget, and the callee has finitely many returns there, given the
  answers, so one return is taken by infinitely many of the paths.
:::
