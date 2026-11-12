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

:::moduleDocs (fingerprint := "5577034158708694857")
:::

:::readable Fir.Core.Op.poisonClass (fingerprint := "15558358313852990599")
*Definition: the poison class of each core op.* Twenty-eight core ops
{ref "The-fir-specification--Execution--Poison-classes"}[propagate poison],
and seven are exceptions:

$$`\begin{aligned} \mathsf{propagates}:\ & \mathsf{const}_N,\ \mathsf{const}_{e,m},\ \mathsf{poison},\ \mathsf{add}, \\ & \mathsf{sub},\ \mathsf{mul},\ \mathsf{sdiv},\ \mathsf{udiv}, \\ & \mathsf{srem},\ \mathsf{urem},\ \mathsf{and},\ \mathsf{or}, \\ & \mathsf{xor},\ \mathsf{shl},\ \mathsf{lshr},\ \mathsf{ashr}, \\ & \mathsf{icmp},\ \mathsf{fcmp},\ \mathsf{zext},\ \mathsf{sext},\ \mathsf{trunc}, \\ & \mathit{fbin},\ \mathit{funary},\ \mathsf{fma},\ \mathsf{bitcast}^{\to \mathsf{i}},\ \mathsf{bitcast}^{\mathsf{i} \to}, \\ & \mathsf{sitofp},\ \mathsf{uitofp} \end{aligned}`

$$`\begin{aligned} \mathsf{exception}:\ & \mathsf{select},\ \mathsf{freeze},\ \mathsf{br}, \\ & \mathsf{cond\_br},\ \mathsf{ret},\ \mathsf{unreachable},\ \mathsf{call} \end{aligned}`

The definition lists every op, with no case for the rest, so a new core op
does not build until it declares its class (ADR-2026-11-03-0600).
$`\mathsf{cond\_br}` is `condBr` in the Lean. The Lean checks the
exceptions against one instance of every core op.
:::

:::readable Fir.Core.Ty.IsPoison (fingerprint := "4747879516839045781")
*Definition: which core values are poison.* A value of $`\mathsf{i}N`, of
$`\mathsf{float}\langle e,m \rangle` or of
$`\mathsf{ptr}\langle N \rangle` is poison when it is $`\mathsf{poison}`.
These are the poison values of the core dialect's types, which the
obligations speak of.
:::

:::readable Fir.Core.Ty.poison_isRefinedBy (pin := Fir.Core.Ty.IsRefinedBy) (fingerprint := "7175011835509932689")
*Theorem: a poison core value is refined by every value of its type.* For
every core type $`t` and all $`p, v \in \llbracket t \rrbracket`: if $`p` is
poison, then $`p \sqsubseteq_t v`.

This is the first clause of a
{ref "The-fir-specification--Execution--Poison-classes"}[lawful dialect],
for the core dialect: it ties the dialect's refinement of values to its
poison.
:::

:::readable Fir.Core.const_propagatesPoison Fir.Core.const_monotone Fir.Core.fconst_propagatesPoison Fir.Core.fconst_monotone Fir.Core.poison_propagatesPoison Fir.Core.poison_monotone (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.OpMonotone) (fingerprint := "18306094282312137454")
*Theorem: $`\mathsf{const}` and $`\mathsf{poison}` propagate poison and are
monotone, whatever the semantics of the core ops.* For every width $`w`
and value $`c`, every format $`\mathsf{float}\langle e,m \rangle` and
bits $`v`, the ops $`\mathsf{const}_w~c`, $`\mathsf{const}_{e,m}~v` and
$`\mathsf{poison}_w` propagate poison, and are {ref "The-fir-specification--Execution--Poison-classes"}[monotone], under any meaning that the
core ops are given.

The meaning of the core ops is given separately, by their execution rules
in the sections after the interpreter. The theorems here take it as a
parameter, so they hold for fir's meaning, and also for the candidate
meanings that the
{ref "The-fir-specification--Execution--Semantics-the-obligations-reject"}[next section]
rejects.

None of the three has operands. So no operand vector holds a poison, and both
clauses of propagation hold with nothing to check. And the only operand
vector is the empty one, which only refines itself, so monotonicity asks
only that each op refine itself, which it does. The theorems hold for every
semantics because they never look at what the ops compute. Their totality
and their results on defined operands do depend on it, and are proved with
their rules, in the sections after the interpreter.
:::
