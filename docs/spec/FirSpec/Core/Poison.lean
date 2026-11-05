import VersoManual
import Fir.Core.Poison
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core poison classes, which
renders `Fir.Core.Poison` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core poison classes: readable blocks" =>

:::readable Fir.Core.Op.poisonClass (fingerprint := "10406232888193993161")
*Definition: the poison class of each core op.* Nineteen core ops
{ref "The-fir-specification--Execution--Poison-classes"}[propagate poison],
and six are exceptions:

$$`\begin{aligned} \mathsf{propagates}:\ & \mathsf{const},\ \mathsf{poison},\ \mathsf{add}, \\ & \mathsf{sub},\ \mathsf{mul},\ \mathsf{sdiv},\ \mathsf{udiv}, \\ & \mathsf{srem},\ \mathsf{urem},\ \mathsf{and},\ \mathsf{or}, \\ & \mathsf{xor},\ \mathsf{shl},\ \mathsf{lshr},\ \mathsf{ashr}, \\ & \mathsf{icmp},\ \mathsf{zext},\ \mathsf{sext},\ \mathsf{trunc} \end{aligned}`

$$`\begin{aligned} \mathsf{exception}:\ & \mathsf{select},\ \mathsf{freeze},\ \mathsf{br}, \\ & \mathsf{cond\_br},\ \mathsf{ret},\ \mathsf{call} \end{aligned}`

The definition lists every op, with no case for the rest, so a new core op
does not build until it declares its class (ADR-2026-11-03-0600).
$`\mathsf{cond\_br}` is `condBr` in the Lean. The Lean checks the
exceptions against one instance of every core op.
:::

:::readable Fir.Core.Ty.IsPoison (fingerprint := "16563849751577617349")
*Definition: which core values are poison.* A value of $`\mathsf{i}N` is
poison when it is $`\mathsf{poison}`; $`\mathsf{ptr}` has no values, so
none is poison. These are the poison values of the core dialect's types,
which the obligations speak of.
:::

:::readable Fir.Core.Ty.poison_isRefinedBy (pin := Fir.Core.Ty.IsRefinedBy) (fingerprint := "16560125237719402665")
*Theorem: a poison core value is refined by every value of its type.* For
every core type $`t` and all $`p, v \in \llbracket t \rrbracket`: if $`p` is
poison, then $`p \sqsubseteq_t v`.

This is the first clause of a
{ref "The-fir-specification--Execution--Poison-classes"}[lawful dialect],
for the core dialect: it ties the dialect's refinement of values to its
poison.
:::

:::readable Fir.Core.const_propagatesPoison Fir.Core.const_monotone Fir.Core.poison_propagatesPoison Fir.Core.poison_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.OpMonotone) (fingerprint := "10814135831303282794")
*Theorem: $`\mathsf{const}` and $`\mathsf{poison}` propagate poison and are
monotone, whatever the semantics of the core ops.* For every width $`w`
and value $`c`, the ops $`\mathsf{const}_w~c` and $`\mathsf{poison}_w`
propagate poison, and are {ref "The-fir-specification--Execution--Poison-classes"}[monotone], under any meaning that the
core ops are given.

Neither op has operands. So no operand vector holds a poison, and both
clauses of propagation hold with nothing to check. And the only operand
vector is the empty one, which only refines itself, so monotonicity asks
only that each op refine itself, which it does. The theorems hold for every
semantics because they never look at what the ops compute. Their totality
and their results on defined operands do depend on it, and are proved with
their rules, in the sections after the interpreter.
:::
