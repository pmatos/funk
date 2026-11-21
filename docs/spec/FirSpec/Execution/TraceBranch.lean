import VersoManual
import Fir.Execution.TraceBranch
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on streams of acts and branches of moves in the traced layer, which renders
`Fir.Execution.TraceBranch` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Streams of acts and branches of moves: readable blocks" =>

:::moduleDocs (fingerprint := "7136385774755592332")
:::

:::readable Fir.Step.upTo_append_of_ticks_le Fir.Step.prefix_upTo (fingerprint := "9444690325363593714")
*Theorems: the first steps of a marked trace.* When $`t` has at most $`N`
steps, the first $`N` steps of $`t \mathbin{+\!\!+} r` are $`t`, then the
first steps of $`r`; and a marked trace $`t` of at most $`N` steps that starts
$`m` starts the first $`N` steps of $`m`.
:::

:::readable Fir.Stream.Avail Fir.Stream.Cons Fir.Stream.cat Fir.Stream.Cons.cat Fir.Stream.Cons.cat_prefix Fir.Stream.Avail.of_cat (fingerprint := "10699450385828981440")
*Definitions: streams of acts.* A stream $`S` gives each place $`i` an act or
none. It has at least $`k` acts when every place below $`k` has one. A trace
$`l` shows acts of $`S` when each act of $`l` is $`S`'s at its place. The
stream $`l \cdot S` is the acts of $`l`, then $`S`'s, each moved up by the
length of $`l`.

*Theorems.* A trace $`l \mathbin{+\!\!+} m` shows acts of $`l \cdot S` when
$`m` shows acts of $`S`; a prefix of $`l` shows acts of $`l \cdot S` for
every $`S`; and when $`l \cdot S` has at least $`k` acts, $`S` has at least
$`k - |l|`.
:::

:::readable Fir.TShows Fir.TStep Fir.TStep.deadline Fir.TShows.step (fingerprint := "296284468361919577")
*Definition: a run shows a stream.* Take a run by the marked traces of its
paths that run out of fuel at each budget. It shows the stream $`S` with the
deadlines $`K` when, at every budget $`n`, it has such a path whose acts are
acts of $`S` at their places, and, whenever $`S` has $`k` acts and
$`K(k) \le n`, at least $`k` acts within its first $`K(k)` steps.

*Definition: a move.* A run $`R` goes on by a move to the run $`R_1` after the
marked trace $`t` with $`F` steps of fuel, $`t` having at most $`F` steps,
when at each budget $`n`: either $`n < F` and $`R` has a path at $`n` that is a
prefix of $`t`, or, for some budget $`n_1 < n` with $`n \le n_1 + F`, every
path $`m_1` of $`R_1` at $`n_1` gives the path $`t \mathbin{+\!\!+} m_1` of
$`R` at $`n`. The deadline of $`k` acts before the move is $`F` plus the
deadline of the acts left after $`t`'s, or $`F` when $`t` shows all $`k`.

*Theorem.* A run that goes on by a move to one that shows $`S` with $`K`
shows the stream $`\mathrm{acts}(t) \cdot S` with those deadlines.
:::

:::readable Fir.TBranch.pre Fir.TBranch.fuel Fir.TBranch.pre_prefix Fir.TBranch.ticks_pre_le Fir.TBranch.realized (fingerprint := "14978829185162282791")
*Definitions: a branch of moves.* A branch is runs $`R_0, R_1, \ldots`, each
going on to the next by the move of $`t_i` with fuel $`F_i`. From run $`i`,
$`j` moves have the marked trace $`t_i \mathbin{+\!\!+} \cdots
\mathbin{+\!\!+} t_{i+j-1}` and the fuel $`F_i + \cdots + F_{i+j-1}`.

*Theorems.* More moves start with fewer, and moves take at most their fuel
in steps. At each budget, run $`i` has a path that starts with the moves from
it whose fuel the budget covers, and is a prefix of some moves.
:::

:::readable Fir.TBranch.acts Fir.TBranch.acts_eq Fir.TBranch.acts_some Fir.TBranch.deadline Fir.TBranch.tShows (fingerprint := "4441907504722914768")
*Definitions: the stream of a branch.* The acts of a branch from run $`i` give
each place the act there of some moves from $`i` that reach it, and none when
no number of moves does. The deadline of $`k` acts is the fuel of some moves
that show $`k` acts, or $`0` when none do.

*Theorems.* The acts of any moves are the branch's at their places, and each
act of the branch is one of some moves. Each run of a branch shows, at every
budget, the acts of all the moves from it, one after the other, with those
deadlines.
:::
