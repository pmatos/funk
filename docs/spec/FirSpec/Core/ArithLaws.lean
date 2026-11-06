import VersoManual
import Fir.Core.ArithLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on constant obligations, which renders
`Fir.Core.ArithLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Constant obligations: readable blocks" =>

:::readable Fir.Core.const_returnsOnDefined Fir.Core.const_total (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.Core.constValue) (pin := Fir.Core.Op.denote?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "2023729354523156256")
*Theorem: $`\mathsf{const}` returns a result on defined operands, and is
total.* For every width $`w` and every vector $`c` of $`w` bits, under
fir's execution rules, $`\mathsf{const}_w~c`
{ref "The-fir-specification--Execution--Poison-classes"}[returns a result on defined operands]
and is {ref "The-fir-specification--Execution--Poison-classes"}[total].

$`\mathsf{const}_w~c` has no operands, so its only operand vector is the
empty one, $`()`, which holds no poison. On it, its
{ref "The-fir-specification--Execution--Arithmetic-rules"}[rule] ends in
one way, with the result $`c`:

$$`\mathrm{denote}_{\mathsf{const}_w~c}() = \{ \mathsf{ok}~(c) \}`

Here $`(c)` is the result vector whose one element is $`c`, as $`()` is
the empty one. That one way is the result on defined operands that the first obligation
asks for, and the outcome that totality asks for on every operand vector.
The section on
{ref "The-fir-specification--Execution--Core-poison-classes"}[core poison classes]
proves the other two obligations of $`\mathsf{const}` for any semantics;
these two depend on its rule, so they are proved here.
:::

:::readable Fir.Core.poison_returnsOnDefined Fir.Core.poison_total Fir.Core.poison_denote (pin := Fir.ReturnsOnDefined) (pin := Fir.OpTotal) (pin := Fir.Core.poisonValue) (pin := Fir.Core.Op.denote?) (pin := Fir.instDialectDenoteCoreDialectSetM) (fingerprint := "3584212295673655336")
*Theorem: $`\mathsf{poison}` returns a result on defined operands, and is
total.* For every width $`w`, under fir's execution rules,
$`\mathsf{poison}_w` returns a result on defined operands and is total
(ADR-2026-11-03-1615).

*Theorem: $`\mathsf{poison}` gives the poison of its type, and nothing
else.* For every width $`w`, the only way $`\mathsf{poison}_w` ends, on
its one operand vector, is with the poison of $`\mathsf{i}w`: no defined
value, and no UB.

$$`e \in \mathrm{denote}_{\mathsf{poison}_w}() \iff e = \mathsf{ok}~(\mathsf{poison})`

The result is poison, but the operands, of which there are none, hold no
poison, so this is a result on defined operands, which is all that the
obligation asks: it speaks of the operands, not of the result. The
obligations hold of many rules; the last theorem states which one
$`\mathsf{poison}` has, read in the set monad, so that a reader, or a
proof, can rely on it producing poison and only poison.
:::

:::readable Fir.Core.addValues_poison Fir.Core.addValues_isRefinedBy (pin := Fir.Core.addValues) (pin := Fir.PoisonOr.IsRefinedBy) (fingerprint := "12816903678639790972")
*Theorem: a poison operand of the sum gives poison.* For every width
$`N` and all $`a, b \in \llbracket \mathsf{i}N \rrbracket`, if
$`a = \mathsf{poison}` or $`b = \mathsf{poison}`, the
{ref "The-fir-specification--Execution--Arithmetic-rules"}[sum without flags]
$`a + b` is $`\mathsf{poison}`.

*Theorem: the sum of refined operands refines the sum.* For all
$`a, b, a', b' \in \llbracket \mathsf{i}N \rrbracket`, if
$`a \sqsubseteq a'` and $`b \sqsubseteq b'`, then
$`a + b \sqsubseteq a' + b'`.

Here $`a + b` is the sum modulo $`2^N` when both operands are values, and
poison otherwise, and $`\sqsubseteq` is the
{ref "The-fir-specification--Execution--Core-values"}[refinement of core values]:
poison is refined by every value, and a value only by itself. These are
the two facts that the next section's proofs that $`\mathsf{add}` is
lawful need of the sum, stated here with the rule they are about.
:::
