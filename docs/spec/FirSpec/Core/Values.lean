import VersoManual
import Fir.Core.Values
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core values, which renders
`Fir.Core.Values` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Core values: readable blocks" =>

:::readable Fir.Core.Ty.toType (pin := Fir.PoisonOr) (fingerprint := "11451694641911891388")
*Definition: the values of the core types.* A value of
$`\mathsf{i}N` is poison or a vector of $`N` bits, and $`\mathsf{ptr}` has
no values in M0:

$$`\llbracket \mathsf{i}N \rrbracket = (\mathbb{B}^N)_{\mathsf{poison}} \qquad \llbracket \mathsf{ptr} \rrbracket = \emptyset`

Here $`\mathbb{B}^N` is the set of vectors of $`N` bits, and
$`A_{\mathsf{poison}}` adds
{ref "The-fir-specification--Execution--Values-and-refinement"}[poison] to
a set $`A`. A vector of $`N` bits exists for every $`N`, so every width is
treated alike (ADR-2026-10-29-2007). The meaning of a pointer waits for the
memory model, which is not decided yet, so validation rejects every value
of type $`\mathsf{ptr}`.
:::

:::readable Fir.Core.Ty.IsRefinedBy (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "4971053852378255705")
*Definition: refinement of core values.* A value of $`\mathsf{i}N` is
refined as a value that may be poison: poison is refined by every value of
$`\mathsf{i}N`, and a vector of bits only by itself.

$$`v \sqsubseteq_{\mathsf{i}N} w \iff v = \mathsf{poison} \,\lor\, v = w`

$`\mathsf{ptr}` has no values, so there is nothing to refine. Typed core
values refine as
{ref "The-fir-specification--Execution--Values-and-refinement"}[typed values]
do: same type, and a value that refines.
:::

:::readable Fir.Core.Obs (pin := Fir.List.IsRefinedBy) (pin := Fir.instHRefinementDVal) (fingerprint := "5117441070640449670")
*Definition: the observation of a core function.* What an observer sees of
a return of a core function is the list of typed values it returns, any
number of them (ADR-2026-10-30-0816). A returned list is refined by a list
of the same length, position by position, as
{ref "The-fir-specification--Execution--Values-and-refinement"}[lists] are,
and each typed value by one of the same type whose value refines it:

$$`(t, v) \sqsubseteq (t', v') \iff t = t' \,\wedge\, v \sqsubseteq_t v'`

So a returned poison may become any value of its type, and a returned
value must stay as it is.
:::

:::readable Fir.Core.poison_isRefinedBy (fingerprint := "10660277837214815142")
*Theorem: a returned poison is refined by any returned value of its type.*
For every width $`w` and every $`b \in \llbracket \mathsf{i}w \rrbracket`,
poison included:

$$`\mathsf{ret}~[(\mathsf{i}w, \mathsf{poison})] \sqsubseteq \mathsf{ret}~[(\mathsf{i}w, b)]`

This is the rule for poison of fir's refinement (ADR-2026-10-29-2008),
for the outcomes of M0: a function that returns poison may be compiled to
one that returns any value.
:::

:::readable Fir.Core.Ty.isRefinedBy_refl Fir.Core.Ty.isRefinedBy_trans Fir.Core.Obs.isRefinedBy_refl Fir.Core.Obs.isRefinedBy_trans Fir.Core.behaviour_isRefinedBy_trans (fingerprint := "14417651866553052101")
*Theorem: refinement of core values and of observations is reflexive and
transitive, and refinement of behaviours of core functions is
transitive.*

* For every core type $`t`: $`v \sqsubseteq_t v`; and $`u \sqsubseteq_t v`
  and $`v \sqsubseteq_t w` give $`u \sqsubseteq_t w`.
* The same holds for observations: lists of returned typed values.
* For behaviours $`A`, $`B` and $`C` of core functions,
  $`A \sqsubseteq B` and $`B \sqsubseteq C` give $`A \sqsubseteq C`.

These are the conditions that the general theorems on
{ref "The-fir-specification--Execution--Refinement"}[refinement] ask of
observations, met for the core dialect. With them, a pipeline of correct
passes over core functions is correct.
:::

:::readable Fir.Core.FuncRuns (fingerprint := "3777233791884609069")
*Definition: the runs of a core function.* For parameter types
$`t_1, \dots, t_n`, the runs of a core function give its run on each
argument vector
$`(v_1, \dots, v_n) \in \llbracket t_1 \rrbracket \times \dots \times \llbracket t_n \rrbracket`,
at each budget, with returned lists as observations. A value of
$`\mathsf{i}N` may be poison, so poison arguments are among the argument
vectors, and
{ref "The-fir-specification--Execution--Refinement"}[refinement of functions]
covers them.
:::

:::readable Fir.Core.funcRuns_isRefinedBy_trans Fir.Core.funcRuns_isRefinedBy_refl (fingerprint := "17415001696825900729")
*Theorem: refinement of core functions is transitive and reflexive.* For
the runs $`F`, $`G` and $`H` of core functions with the same parameter
types, $`F \sqsubseteq G` and $`G \sqsubseteq H` give $`F \sqsubseteq H`,
and $`F \sqsubseteq F`.
:::
