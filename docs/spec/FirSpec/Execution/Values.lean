import VersoManual
import Fir.Execution.Values
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on values and refinement, which renders
`Fir.Execution.Values` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Values and refinement: readable blocks" =>

:::readable Fir.PoisonOr (fingerprint := "17169256414108514350")
*Definition: a value that may be poison.* For a set of values $`A`, the
set $`A_{\mathsf{poison}}` holds every value of $`A`, and one more element,
$`\mathsf{poison}`, which stands for a value that a failed op left behind
instead of a result.

```grammar Fir.PoisonOr
A_{\mathsf{poison}}
poison   \mathsf{poison}
value    a \quad (a \in A)
```

The integers of the core dialect are such values: a value of
$`\mathsf{i}N` is $`\mathsf{poison}` or a vector of $`N` bits. In the Lean,
a value $`a` of $`A` is written $`\mathsf{value}~a`, as LeanMLIR writes it.
Poison exists so that an op can fail without making the whole run
undefined; the
{ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[next section]
says why fir needs both poison and immediate UB.
:::

:::readable Fir.HRefinement (fingerprint := "16723662750960563249")
*Definition: refinement.* Refinement is the relation that says when one
thing may stand in for another. It is written

$$`a \sqsubseteq b`

and read "$`a` is refined by $`b`": $`b` does nothing that $`a` does not
allow. A compiler is correct when the program it produces refines the
program it was given. The relation is defined level by level: for values
and lists of values in this section, then for outcomes, behaviours and
functions in the section on
{ref "The-fir-specification--Execution--Refinement"}[refinement]. The two
sides may be of different kinds, though every instance in this chapter
relates things of one kind.
:::

:::readable Fir.PoisonOr.IsRefinedBy (fingerprint := "3337330117320181529")
*Definition: refinement of values that may be poison.* Poison is refined by
every value, and a value other than poison only by itself:

$$`v \sqsubseteq w \iff v = \mathsf{poison} \,\lor\, v = w`

So a compiler may replace a poison by any value it likes, such as whatever
a register happens to hold, but it may never change a value that is not
poison. In particular, a value is never refined by poison.
:::

:::readable Fir.TyRefinement (fingerprint := "13912094953098128847")
*Definition: how a dialect refines its values.* Each dialect says, for each
of its types $`t`, when one value of $`t` is refined by another. Write
$`\llbracket t \rrbracket` for the set of values of type $`t`, which the
dialect gives
({ref "The-fir-specification--Abstract-syntax--Dialects"}[dialects]). The
dialect gives a relation $`\sqsubseteq_t` on $`\llbracket t \rrbracket` for
each $`t`. For the core dialect it is the refinement of values that may be
poison, above.
:::

:::readable Fir.DVal Fir.instHRefinementDVal Fir.DVal.isRefinedBy_trans (fingerprint := "14896415709458877968")
*Definition: a typed value, and its refinement.* An op consumes and
produces typed values: pairs $`(t, v)` of a type $`t` and a value
$`v \in \llbracket t \rrbracket`. A typed value is refined by a value of the
same type that refines it:

$$`(t, v) \sqsubseteq (t', v') \iff t = t' \,\wedge\, v \sqsubseteq_t v'`

*Theorem: typed values refine transitively when values do.* If, for every
type $`t`, $`\sqsubseteq_t` is transitive, then so is the refinement of
typed values: $`x \sqsubseteq y` and $`y \sqsubseteq z` give
$`x \sqsubseteq z`.
:::

:::readable Fir.List.IsRefinedBy Fir.List.isRefinedBy_trans (fingerprint := "15616140829063086083")
*Definition: refinement of lists.* A list is refined by a list of the same
length whose elements refine its own, position by position:

$$`\begin{aligned} & [a_1, \dots, a_n] \sqsubseteq [b_1, \dots, b_m] \\ \iff\ & n = m \,\wedge\, \forall i.\ a_i \sqsubseteq b_i \end{aligned}`

A function returns a list of values, so this is how what it returns is
compared.

*Theorem: lists refine transitively when their elements do.* If the
refinement of elements is transitive, then $`as \sqsubseteq bs` and
$`bs \sqsubseteq cs` give $`as \sqsubseteq cs`, for lists of one kind of
element.
:::

:::readable Fir.PoisonOr.poison_isRefinedBy Fir.PoisonOr.isRefinedBy_refl Fir.PoisonOr.isRefinedBy_trans (fingerprint := "5762587255094126963")
*Theorem: poison is refined by every value, and refinement of values that
may be poison is reflexive and transitive.* For all $`v`, $`w` and $`x` in
$`A_{\mathsf{poison}}`:

$$`\mathsf{poison} \sqsubseteq w \qquad v \sqsubseteq v`

$$`v \sqsubseteq w \,\wedge\, w \sqsubseteq x \implies v \sqsubseteq x`

The first is the rule that lets a compiler choose any value for a poison.
Reflexivity says that leaving a value alone is always correct, and
transitivity that two correct replacements in a row are correct, which is
what lets a compiler run one pass after another.
:::
