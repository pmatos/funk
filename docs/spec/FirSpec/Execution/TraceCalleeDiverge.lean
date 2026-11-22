import VersoManual
import Fir.Execution.TraceCalleeDiverge
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on divergence across black boxes, which renders
`Fir.Execution.TraceCalleeDiverge` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Divergence across black boxes: readable blocks" =>

:::moduleDocs (fingerprint := "3787497955749702246")
:::

:::readable Fir.Stream.eq_cat Fir.TBranch.acts_isRefinedBy (fingerprint := "17651258247569114743")
*Theorems.* A stream whose first acts are those of $`l` is $`l`, then the
stream after $`|l|` places. When each move of one branch shows acts refined
by the other's move, the streams of the two branches refine each other.
:::

:::readable Fir.TCfg.Follows.allows (fingerprint := "11220466069967125270")
*Theorem: divergence across black boxes.* Let every path of every op and
of every external call show
exactly one step, every op that runs by its own rule, and every external call,
have finitely many
outcomes, given the world's answers, the target $`M'` run each call as the
source $`M` does, and the ops of $`M`'s functions that run by their own rule
be monotone. A target configuration that shows a closed stream $`T` at every
budget is allowed, with $`T`, by every source configuration that follows it.

The target has a branch of moves that shows all of $`T` (the target's
branch). Suppose the source did not allow $`T`. Then at each move of the
target the source follows with a move of its own, whose acts the target's
refine, and does not allow the stream after it either. By dependent choice
the source has a branch of its own, which shows at every budget a stream
refined by $`T`. So the source allows $`T` after all.
:::
