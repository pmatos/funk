import VersoManual
import Fir.Core.FreezeLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on freeze obligations, which renders
`Fir.Core.FreezeLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Freeze obligations: readable blocks" =>

:::moduleDocs (fingerprint := "12474189112956974592")
:::

:::readable Fir.Core.freeze_denote (pin := Fir.Core.freezeValue) (pin := Fir.Core.Op.denote?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "2648535899064136977")
*Theorem: what $`\mathsf{freeze}` may give.* For every width $`w`, every
$`a \in \llbracket \mathsf{i}w \rrbracket` and every way $`e` to end,
$`\mathsf{freeze}_w` on $`a` may end with $`e` exactly when $`e` is
$`\mathsf{ok}~(b)`, with the result vector $`(b)` whose one element is
$`b`, for some $`b` of $`w` bits such that $`a` is poison or $`a = b`:

$$`\begin{aligned} & e \in \mathrm{denote}_{\mathsf{freeze}_w}(a) \\ \iff\ & \exists b.\ e = \mathsf{ok}~(b) \\ & \quad \wedge\, (a = \mathsf{poison} \,\lor\, a = b) \end{aligned}`

So $`\mathsf{freeze}` of a value gives that value, $`\mathsf{freeze}` of
poison gives every vector of $`w` bits, each as one way the op may end,
and no way is poison or UB. The
{ref "The-fir-specification--Execution--The-freeze-rule"}[rule] is written
with the choice effect, for any monad; this theorem reads it in the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad],
where the obligations are stated, and the two proofs below rest on it.
:::

:::readable Fir.Core.freeze_total Fir.Core.freeze_monotone (pin := Fir.OpTotal) (pin := Fir.OpMonotone) (fingerprint := "18238832793253815085")
*Theorem: $`\mathsf{freeze}` is total and monotone.* For every width
$`w`, under fir's execution rules, $`\mathsf{freeze}_w` is
{ref "The-fir-specification--Execution--Poison-classes"}[total] and
{ref "The-fir-specification--Execution--Poison-classes"}[monotone].

It is total because every operand has some outcome: a value gives itself,
and poison gives, for one, the vector $`0`. It is monotone because a
poison operand allows every vector: let $`a'` refine $`a`. When $`a` is
poison, whatever $`\mathsf{freeze}` gives on $`a'` it may give on $`a`
too. When $`a` is a value, $`a'` is that same value, and gives the same.
The results are values, never poison, and each refines itself.
$`\mathsf{freeze}` is an exception to poison propagation, so these are the
only obligations it has.
:::
