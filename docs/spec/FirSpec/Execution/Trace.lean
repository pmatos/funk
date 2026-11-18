import VersoManual
import Fir.Execution.Trace
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on traces of events, which renders
`Fir.Execution.Trace` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Traces of events: readable blocks" =>

:::moduleDocs (fingerprint := "16837739857232725315")
:::

:::readable Fir.Act (fingerprint := "5574297282604202850")
*Definition: an act.* An _act_ is an event $`e` that a run shows to the
world, with the world's answer $`a`, written $`\langle e, a\rangle`. A
dialect says what its events and answers are. A trace is a list of acts,
or, for a run that shows acts forever, an infinite sequence of them.
:::

:::readable Fir.Act.isRefinedBy_refl Fir.Act.isRefinedBy_trans (pin := Fir.instHRefinementAct) (fingerprint := "13735593932531479724")
*Definition: one act refines another.* The act $`\langle e', a'\rangle`
refines $`\langle e, a\rangle` when the event $`e'` refines $`e`, with
poison refined as for values, and the answers are the same:

$$`\langle e, a\rangle \sqsubseteq \langle e', a'\rangle \iff e \sqsubseteq e' \land a = a'`

*Theorem: refinement of acts is a preorder.* It is reflexive and
transitive when refinement of events is.
:::

:::readable Fir.TOutcome Fir.TOutcome.act? Fir.TOutcome.before (fingerprint := "12100416140504337342")
*Definition: how a traced run ends.* A traced outcome is one of:

$$`\mathsf{ret}~t~o \quad \mathsf{ub}~t~r \quad \mathsf{diverge}~t \quad \mathsf{reacts}~T`

a return of the observation $`o` after the finite trace $`t`; UB for the
reason $`r` after $`t`; silent divergence after $`t`; or an infinite trace
$`T`, of a run that shows acts forever. Its act at place $`i`,
$`\mathrm{act}_i`, is the act at that place of its trace, if there is one,
and $`\mathrm{before}_i` is the list of its first $`i` acts, or all of
them when there are fewer.
:::

:::readable Fir.TOutcome.ShowsRefined Fir.TOutcome.IsRefinedBy (pin := Fir.TOutcome.instHRefinement) (fingerprint := "15454297988416176158")
*Definition: one traced outcome allows another.* The outcome $`u` _shows_
the finite trace $`t` when, at each place $`i` of $`t`, $`u` has an act that
refines $`t_i`. A source outcome allows a target outcome in exactly these
cases:

$$`\mathsf{ub}~t~r \sqsubseteq u \iff u \text{ shows } t`

$$`\mathsf{ret}~t~a \sqsubseteq \mathsf{ret}~t'~b \iff t \sqsubseteq t' \land a \sqsubseteq b`

$$`\mathsf{diverge}~t \sqsubseteq \mathsf{diverge}~t' \iff t \sqsubseteq t'`

$$`\mathsf{reacts}~T \sqsubseteq \mathsf{reacts}~T' \iff \forall i,\ T_i \sqsubseteq T'_i`

where two finite traces refine when they have the same length and refine
act by act. So UB in the source allows only a target that first shows the
source's events, and then anything. A source that returns, falls silent or
shows acts forever allows only a target that does the same, with the same
answers, and with events and an observation that refine the source's.
:::

:::readable Fir.List.IsRefinedBy.getElem?_some Fir.TOutcome.IsRefinedBy.acts (fingerprint := "7694300390048205915")
*Theorem: a refined outcome shows the source's trace.* When $`s
\sqsubseteq u`, at each place where $`s` has an act $`a`, $`u` has an act
$`b` with $`a \sqsubseteq b`. For two lists that refine, this is
refinement at each place of the first.
:::

:::readable Fir.TOutcome.isRefinedBy_refl Fir.TOutcome.isRefinedBy_trans (fingerprint := "3060194883275845904")
*Theorem: refinement of traced outcomes is a preorder.* It is reflexive and
transitive when refinement of acts and of observations is. For
transitivity through UB, the target shows what the middle outcome shows,
and so shows what the source's UB asks for.
:::

:::readable Fir.TBehaviour Fir.TBehaviour.IsRefinedBy Fir.TBehaviour.ub_isRefinedBy (pin := Fir.TBehaviour.instHRefinement) (fingerprint := "11860949638645221893")
*Definition: a traced behaviour.* A traced behaviour is a set of traced
outcomes. A target behaviour $`B'` refines a source behaviour $`B` when
every outcome of $`B'` is allowed by some outcome of $`B`:

$$`B \sqsubseteq B' \iff \forall u \in B',\ \exists s \in B,\ s \sqsubseteq u`

*Theorem: UB before any act allows anything.* A source that may hit UB
before it shows an act is refined by every target.
:::

:::readable Fir.TBehaviour.isRefinedBy_refl Fir.TBehaviour.isRefinedBy_trans (fingerprint := "8876478455010859854")
*Theorem: refinement of traced behaviours is a preorder.* It is reflexive,
and transitive, so a pipeline of correct passes is correct, when
refinement of acts and of observations is.
:::

:::readable Fir.World Fir.TOutcome.InWorld Fir.TOutcome.before_length Fir.TOutcome.inWorld_exists (fingerprint := "7738410486850217835")
*Definition: a world.* A world $`w` answers each event $`e` from the acts
shown before it, $`w(t, e)`. A traced outcome is _shown at_ $`w` when the
answer of each of its acts is the world's answer to its event, after the
acts before it: $`a_i = w(\mathrm{before}_i, e_i)`.

*Theorem: every outcome is shown at some world.* When answers have a
default, the world that answers the event at place $`i` with the answer
there, and with the default elsewhere, shows the outcome, since the acts
before place $`i` are $`i` acts.
:::

:::readable Fir.TBehaviour.atWorld Fir.TBehaviour.isRefinedBy_iff_world (fingerprint := "7203226736189649960")
*Definition: a behaviour at a world.* $`B|_w` is the set of the outcomes of
$`B` shown at $`w`.

*Theorem: refinement holds for every world.* A target behaviour refines a
source behaviour exactly when, at every world $`w`, each outcome of
$`B'|_w` is allowed by an outcome of $`B`:

$$`B \sqsubseteq B' \iff \forall w,\ \forall u \in B'|_w,\ \exists s \in B,\ s \sqsubseteq u`

The source's outcome shows the same answers as the target's. Where the
source shows poison in an event, the target may show any value, and the
world's answer to the target's event is an answer to the source's, whose
poison may be any value (ADR-2026-11-09-1540).
:::

:::readable Fir.TOutcome.ofOutcome Fir.TBehaviour.ofBehaviour (fingerprint := "8968012538506122234")
*Definition: a behaviour with no event.* An
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[outcome]
of M0 is a traced outcome with an empty trace:
$`\mathsf{ret}~o \mapsto \mathsf{ret}~[]~o`,
$`\mathsf{ub}~r \mapsto \mathsf{ub}~[]~r` and
$`\mathsf{fuel\_exhausted} \mapsto \mathsf{diverge}~[]`. A behaviour is the
traced behaviour of its outcomes so read.
:::

:::readable Fir.TOutcome.ofOutcome_isRefinedBy_iff Fir.TBehaviour.ofBehaviour_isRefinedBy_iff (fingerprint := "4733776834347560190")
*Theorem: with no event, traced refinement is refinement.* Two outcomes
refine as traced outcomes with empty traces exactly when they
{ref "The-fir-specification--Execution--Refinement"}[refine] as outcomes,
and two behaviours refine as traced behaviours exactly when they refine as
behaviours.
:::
