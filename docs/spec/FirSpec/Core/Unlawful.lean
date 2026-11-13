import VersoManual
import Fir.Core.Unlawful
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on semantics that the obligations
reject, which renders `Fir.Core.Unlawful` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Semantics the obligations reject: readable blocks" =>

:::moduleDocs (fingerprint := "4845064695708264964")
:::

:::readable Fir.Core.Unlawful.add_typesValid Fir.Core.Unlawful.sdiv_typesValid (pin := Fir.TypesValid) (fingerprint := "5393438447920550166")
*Theorem: $`\mathsf{add}_1` with no flags and $`\mathsf{sdiv}_8` without
$`\mathsf{exact}` are valid op instances.* $`\mathsf{add}` at
$`\mathsf{i1}` with no flags, and $`\mathsf{sdiv}` at $`\mathsf{i8}`
without $`\mathsf{exact}`, have operand and result types that validation
accepts
({ref "The-fir-specification--Validation--The-general-rules"}[the general rules]).

The obligations speak only of valid op instances, so each rejection below
is shown at one of these two, which validation accepts and which calls no
function.
:::

:::readable Fir.Core.Unlawful.noOutcome Fir.Core.Unlawful.noOutcome_unlawful (pin := Fir.LawfulDialectPoison) (pin := Fir.OpTotal) (fingerprint := "17321106791354160400")
*Definition: a semantics in which no op has any outcome.* Every op, on
every operand vector, has the empty set of ways to end, and so does every
terminator's exit.

*Theorem: such a semantics is not {ref "The-fir-specification--Execution--Poison-classes"}[lawful].* Totality asks that
$`\mathsf{add}_1` have some outcome on the operands
$`(\mathsf{poison}, \mathsf{poison})`, and here it has none. A semantics
like this would drop every path of every run, and an empty behaviour
refines every source, so without totality it would pass for correct.
:::

:::readable Fir.Core.Unlawful.poisonIsUB Fir.Core.Unlawful.poisonIsUB_unlawful (pin := Fir.LawfulDialectPoison) (pin := Fir.UBByOwnRules) (pin := Fir.HVector.Any) (fingerprint := "1528769472209587911")
*Definition: a semantics in which poison is UB.* Every op is immediate UB
on an operand vector some element of which is poison, and returns some
result on every other operand vector. Every terminator's exit is UB.

*Theorem: such a semantics is not lawful.* Its $`\mathsf{add}_1` is UB on
$`(\mathsf{poison}, \mathsf{poison})`. The {ref "The-fir-specification--Execution--Poison-classes"}[clause] "UB only by the
op's own rules" then asks for operands with no poison on which $`\mathsf{add}_1` is
UB too, and there are none: on them it returns a result. This semantics
turns every poison operand into UB, which would undo the deferral that
poison exists for.
:::

:::readable Fir.Core.Unlawful.sdivOld Fir.Core.Unlawful.oldSDiv Fir.Core.Unlawful.oldSDiv_not_monotone Fir.Core.Unlawful.oldSDiv_unlawful (pin := Fir.LawfulDialectPoison) (pin := Fir.OpMonotone) (pin := Fir.Ev.IsRefinedBy) (pin := Fir.Core.Ty.IsRefinedBy) (fingerprint := "1600389928004172081")
*Definition: the rejected rule for $`\mathsf{sdiv}`.* Under it, a poison
dividend by $`-1` gives poison. For $`a, b \in \llbracket \mathsf{i}N \rrbracket`:

$$`\begin{aligned} & \mathrm{sdiv}_{\mathrm{old}}(a, b) = \\ & \quad \begin{cases} \mathsf{ub} & \text{if } b = \mathsf{poison} \\ \mathsf{ub} & \text{if } a = \mathsf{poison},\ b = 0 \\ \mathsf{poison} & \text{if } a = \mathsf{poison},\ b \ne 0 \\ \mathsf{ub} & \text{if } b = 0 \\ \mathsf{ub} & \text{if } a = \mathrm{min}_N,\ b = -1 \\ a \div b & \text{otherwise} \end{cases} \end{aligned}`

Here $`\mathrm{min}_N` is the signed minimum of $`N` bits, and $`\div`
signed division rounding towards zero. In the semantics built from it,
$`\mathsf{sdiv}` follows this rule, and every other op, and every exit, is
UB.

*Theorem: $`\mathsf{sdiv}_8` under the rejected rule is not monotone.*
{ref "The-fir-specification--Execution--Poison-classes"}[Monotonicity] fails here:
$`(\mathrm{min}_8, -1)` refines $`(\mathsf{poison}, -1)`, since poison is
refined by every value. On $`(\mathrm{min}_8, -1)` the rule is UB, but on
$`(\mathsf{poison}, -1)` it gives only poison, which does not allow UB.

*Theorem: so the semantics is not lawful.* A lawful dialect needs every
valid op that calls no function to be monotone, and $`\mathsf{sdiv}_8` is
not. This is why fir's $`\mathsf{sdiv}` by $`-1` is immediate UB on a
poison dividend.
:::

:::readable Fir.Core.Unlawful.fillZero Fir.Core.Unlawful.fillZero_fills (pin := Fir.HVector.IsFilledBy) (pin := Fir.HVector.Any) (pin := Fir.HVector.Forall₂) (fingerprint := "10563675819995500177")
*Definition: each poison replaced by zero.* For an operand vector
$`\vec{v}` of core values, $`\mathrm{fill}_0(\vec{v})` replaces each poison
of an integer or float type by the value $`0` of its type, and each poison
pointer by the pointer with no provenance at offset $`0`, and keeps every
other element.

*Theorem: replacing each poison by zero fills a vector.* For every
operand vector $`\vec{v}`, $`\mathrm{fill}_0(\vec{v})` has no poison, and
agrees with $`\vec{v}` wherever $`\vec{v}` is not poison: it
{ref "The-fir-specification--Execution--Poison-classes"}[fills]
$`\vec{v}`.
:::

:::readable Fir.Core.Unlawful.alwaysUB Fir.Core.Unlawful.alwaysUB_propagatesPoison Fir.Core.Unlawful.alwaysUB_unlawful (pin := Fir.LawfulDialectPoison) (pin := Fir.PropagatesPoison) (pin := Fir.ReturnsOnDefined) (fingerprint := "6137449382103902958")
*Definition: a semantics in which every op is always UB.* Every op, on
every operand vector, and every terminator's exit, is immediate UB.

*Theorem: under it, every core op propagates poison.* Both clauses of
{ref "The-fir-specification--Execution--Poison-classes"}[propagation] hold for every op $`o`: no operand vector gives a result, so
poison out holds with nothing to check, and the UB on a poison operand is
matched by the UB on the vector that replaces each poison by zero.

*Theorem: but such a semantics is not lawful.* A lawful dialect needs
$`\mathsf{add}_1` to return a result on some operands with no poison, and
here it never returns. Without that obligation, a semantics that makes
every op UB would pass. Exceptions are exempt from it, so an exception
that is always UB, such as $`\mathsf{unreachable}`, stays allowed.
:::

:::readable Fir.Core.Unlawful.memUnlawful Fir.Core.Unlawful.all_memUnlawful (pin := Fir.LawfulDialectMem) (pin := Fir.DialectMemDenote.ofSetM) (fingerprint := "1637578780204857706")
*Theorems: the obligations with memory reject the same semantics.* Each of
the four semantics above is a semantics in the set monad. Lifted into the
state layer, as the semantics with memory of a dialect whose ops touch no
memory, it runs each op by its rule and keeps the memories. In such a
dialect it is
{ref "The-fir-specification--Memory--Poison-obligations-with-memory"}[lawful with memory],
in its poison, its totality and its monotonicity, exactly when the poison
obligations hold. So the obligations with memory reject each
semantics that the poison obligations reject: no outcome, poison as UB, the
rejected rule for $`\mathsf{sdiv}`, and always UB.
:::
