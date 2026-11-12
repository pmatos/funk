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

:::moduleDocs (fingerprint := "9715545657570832416")
:::

:::readable Fir.Core.Ty.toType (pin := Fir.PoisonOr) (pin := Fir.Core.floatWidth) (fingerprint := "16673355204431494593")
*Definition: the values of the core types.* A value of
$`\mathsf{i}N` is poison or a vector of $`N` bits, a value of
$`\mathsf{float}\langle e,m \rangle` is poison or a vector of
$`1 + e + m` bits, its raw bit pattern, and a value of
$`\mathsf{ptr}\langle N \rangle` is poison or a
{ref "The-fir-specification--Memory--The-memory-model"}[pointer]:

$$`\llbracket \mathsf{i}N \rrbracket = (\mathbb{B}^N)_{\mathsf{poison}} \qquad \llbracket \mathsf{float}\langle e,m \rangle \rrbracket = (\mathbb{B}^{1+e+m})_{\mathsf{poison}} \qquad \llbracket \mathsf{ptr}\langle N \rangle \rrbracket = \mathit{Ptr}_{\mathsf{poison}}`

Here $`\mathbb{B}^N` is the set of vectors of $`N` bits, and
$`A_{\mathsf{poison}}` adds
{ref "The-fir-specification--Execution--Values-and-refinement"}[poison] to
a set $`A`. A vector of $`N` bits exists for every $`N`, so every width is
treated alike (ADR-2026-10-29-2007). A float value is its bit pattern, as
IEEE 754 encodes it: a sign bit, then the exponent, then the mantissa. So
two NaNs with different bits are different values, and the ops of a float
type say which bits they give (ADR-2026-11-09-1549). A pointer, of the set
$`\mathit{Ptr}`, is the allocation it has provenance for, if any, and an
offset into it, in the units of its memory (ADR-2026-11-09-1542). It has no
address. Which memory a pointer belongs to is its type's business, so a
pointer value does not name it, and every pointer type has the same
values.
:::

:::readable Fir.Core.Ty.IsRefinedBy (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "18213522499732200753")
*Definition: refinement of core values.* A value of every core type is
refined as a value that may be poison: poison is refined by every value of
its type, a vector of bits only by itself, and a pointer only by itself,
its provenance and its offset alike.

$$`v \sqsubseteq_{t} w \iff v = \mathsf{poison} \,\lor\, v = w`

Typed core
values refine as
{ref "The-fir-specification--Execution--Values-and-refinement"}[typed values]
do: same type, and a value that refines.
:::

:::readable Fir.Core.Obs (pin := Fir.List.IsRefinedBy) (pin := Fir.instHRefinementDVal) (pin := Fir.Core.Ty.IsRefinedBy) (fingerprint := "16613570527610667338")
*Definition: the observation of a core function.* What an observer sees of
a return of a core function is the list of typed values it returns, any
number of them (ADR-2026-10-29-2008). A returned list is refined by a list
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
$`\mathsf{i}N` or of a float type may be poison, so poison arguments are
among the argument
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
