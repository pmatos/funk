import VersoManual
import Fir.Execution.TraceShowsObs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on streams of acts and the outcomes that diverge, which renders
`Fir.Execution.TraceShowsObs` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Streams and outcomes that diverge: readable blocks" =>

:::moduleDocs (fingerprint := "3061130062146177519")
:::

:::readable Fir.Stream.IsRefinedBy Fir.Stream.ShowsRefined Fir.Stream.IsRefinedBy.cat Fir.Stream.ShowsRefined.cat Fir.List.isRefinedBy_of_getElem? (fingerprint := "263845681657554132")
*Definitions: refinement of streams.* The stream $`S` is refined by $`T` when
the same places have acts and each act of $`S` is refined by $`T`'s at its
place. The trace $`l` is refined by the first acts of $`T` when each act of
$`l` is refined by $`T`'s at its place.

*Theorems.* With $`l \sqsubseteq l'`, a stream $`S` refined by $`T` gives
$`l \cdot S` refined by $`l' \cdot T`, and a trace $`m` refined by the first
acts of $`T` gives $`l \mathbin{+\!\!+} m` refined by the first acts of
$`l' \cdot T`. Lists with acts at the same places, each refined by the
other's, refine each other.
:::

:::readable Fir.TOutcome.Diverges Fir.TOutcome.act?_closed Fir.TRun.exh Fir.TShows.ofObservable (fingerprint := "8434146031405778013")
*Definitions.* An outcome diverges when it is $`\mathsf{diverge}~t` or
$`\mathsf{reacts}~T`. The paths of a run that run out of fuel are taken by
their marked traces at each budget.

*Theorems.* The stream of an outcome that diverges is closed. A run whose
observable behaviour includes an outcome that diverges shows its outcome's
stream at every budget.
:::

:::readable Fir.Nat.exists_least Fir.Stream.exists_list Fir.Stream.Closed.eq_list Fir.List.prefix_of_getElem? (fingerprint := "18198400503372416797")
*Theorems: lemmas on numbers, lists and streams.* A property that some
number has, a least number has. A stream with acts at its first $`q` places
has them as those of a list of length $`q`. A closed stream with no act at
some place has acts exactly at the places of a list. A list whose acts are
another's at their places starts that list.
:::

:::readable Fir.TShows.toObservable Fir.TOutcome.isRefinedBy_of_stream Fir.TOutcome.stream_isRefinedBy (fingerprint := "10998708434489005952")
*Theorems: from streams to outcomes.* A run that shows a closed stream at
every budget diverges: silently, after the stream's acts, when the stream
ends, and with the stream as its infinite trace when it does not. Its
outcome's stream is the stream. An outcome that diverges is refined by
another that diverges exactly when its stream is refined by the other's.
:::
