import VersoManual
import Fir.Execution.TraceGood
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on a run that shows a stream at unboundedly many budgets, which renders
`Fir.Execution.TraceGood` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "A stream at unboundedly many budgets: readable blocks" =>

:::moduleDocs (fingerprint := "10726824725437512295")
:::

:::readable Fir.Stream.drop Fir.Stream.dropK Fir.TGood.Sees Fir.TGood (fingerprint := "8509045638980318254")
*Definitions: seeing a stream.* The stream $`T` after $`a` places gives place
$`i` the act $`T(i + a)`; the deadlines $`K` after $`a` acts and $`j` steps
give $`k` acts the deadline $`K(k + a) - j`. A marked trace $`m` sees $`T`
with the deadlines $`K` for $`k` acts when its acts are acts of $`T` at their
places and, for each $`k' \le k` that $`T` has, its first $`K(k')` steps show
at least $`k'` acts.

A run shows $`T` with $`K` at unboundedly many budgets, $`\mathsf{good}(R, T,
K)`, when for each $`k` and each budget $`B` it has a path that runs out of
fuel at some budget $`n \ge B` and sees $`T` for $`k` acts. This asks for
less than showing $`T` at every budget: a budget that holds only some of the
acts is not asked to show them. So cutting a callee down to a smaller budget,
which may cost $`W` steps of fuel for each of its steps, never makes a
deadline grow.
:::

:::readable Fir.TGood.Sees.mono Fir.TGood.Sees.cons_prefix Fir.TGood.Sees.avail_of_drop Fir.TGood.Sees.steps_le Fir.TGood.Sees.shift Fir.TGood.Sees.of_prefix (fingerprint := "5740372686558716648")
*Theorems: seeing a stream after a marked trace.* A trace that sees a stream
for $`k` acts sees it for fewer. When $`t \mathbin{+\!\!+} m_1` sees $`T` for
$`k` acts: $`t`'s acts are acts of $`T`; when $`T` after them has $`x`
acts, $`T` has $`x + |\mathrm{acts}(t)|`; and the deadline of each number
of acts beyond $`t`'s, within $`k`, is at least $`t`'s steps. When it sees
$`T` for $`k + |\mathrm{acts}(t)|` acts, $`m_1` sees $`T` after $`t`'s acts
for $`k` acts, with the deadlines less $`t`'s steps. A
prefix of a trace that sees $`T` for $`k` acts, with more steps than every
deadline of at most $`k` acts, sees it for $`k` acts too.
:::

:::readable Fir.TGood.ofShows Fir.TGood.after Fir.Stream.Cons.agrees (fingerprint := "9245393976935472349")
*Theorems.* A run that shows a stream at every budget shows it at
unboundedly many. When the paths of a run that go on after the marked trace
$`t` by paths of $`R_1` see a stream at unboundedly many budgets, for each
number of acts, $`R_1` shows the stream after $`t`'s acts, with the deadlines
less $`t`'s steps, at unboundedly many budgets; $`t` shows the stream's first
acts; and each deadline past them is at least $`t`'s steps. A trace that
shows acts of a stream of acts agrees with the stream's answers.
:::
