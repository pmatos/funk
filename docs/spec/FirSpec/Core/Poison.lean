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

:::moduleDocs (fingerprint := "3217551763663330731")
:::

:::readable Fir.Core.Op.poisonClass (fingerprint := "16688119724987337294")
*Definition: the poison class of each core op.* Forty-three core ops
{ref "The-fir-specification--Execution--Poison-classes"}[propagate poison],
and seven are exceptions:

$$`\begin{aligned} \mathsf{propagates}:\ & \mathsf{const}_N,\ \mathsf{const}_{e,m},\ \mathsf{poison},\ \mathsf{add}, \\ & \mathsf{sub},\ \mathsf{mul},\ \mathsf{sdiv},\ \mathsf{udiv}, \\ & \mathsf{srem},\ \mathsf{urem},\ \mathsf{and},\ \mathsf{or}, \\ & \mathsf{xor},\ \mathsf{shl},\ \mathsf{lshr},\ \mathsf{ashr}, \\ & \mathsf{icmp},\ \mathsf{fcmp},\ \mathsf{zext},\ \mathsf{sext},\ \mathsf{trunc}, \\ & \mathit{fbin},\ \mathit{funary},\ \mathsf{fma},\ \mathsf{bitcast}^{\to \mathsf{i}},\ \mathsf{bitcast}^{\mathsf{i} \to}, \\ & \mathsf{sitofp},\ \mathsf{uitofp},\ \mathsf{fpext},\ \mathsf{fptrunc},\ \mathsf{ptradd}, \\ & \mathsf{fieldaddr},\ \mathsf{fptosi},\ \mathsf{fptoui},\ \mathsf{alloca}, \\ & \mathsf{load},\ \mathsf{store},\ \mathsf{load}~\mathsf{ptr},\ \mathsf{store}~\mathsf{ptr}, \\ & \mathsf{load}~\mathsf{float},\ \mathsf{store}~\mathsf{float},\ \mathsf{memcpy}, \\ & \mathsf{memmove},\ \mathsf{memset} \end{aligned}`

$$`\begin{aligned} \mathsf{exception}:\ & \mathsf{select},\ \mathsf{freeze},\ \mathsf{br}, \\ & \mathsf{cond\_br},\ \mathsf{ret},\ \mathsf{unreachable},\ \mathsf{call} \end{aligned}`

$`\mathsf{alloca}`, like $`\mathsf{const}` and $`\mathsf{poison}`, has
no operands, so it propagates poison whatever its rule. $`\mathsf{load}`
is UB on a poison pointer, since some defined pointer in its place faults,
so it propagates poison too, and so does $`\mathsf{store}`, which gives no
result and is UB on a poison pointer for the same reason; a poison value
it stores as poison units. The load and store of a pointer,
$`\mathsf{load}~\mathsf{ptr}` and $`\mathsf{store}~\mathsf{ptr}`
(`loadPtr` and `storePtr` in the Lean), propagate poison as
$`\mathsf{load}` and $`\mathsf{store}` do, and so do the load and store
of a float, $`\mathsf{load}~\mathsf{float}` and
$`\mathsf{store}~\mathsf{float}` (`loadFloat` and `storeFloat`).
$`\mathsf{memcpy}` and $`\mathsf{memmove}` (`memCopy`) give no result
and do nothing for a length of 0. With another length, a poison pointer is
UB, since a pointer with no provenance in its place faults, and a poison
length runs as some length, chosen, so it is UB only where some length
is: they propagate poison too. So does $`\mathsf{memset}` (`memSet`), in
its pointer and its length as they do, and it writes a poison value as
poison units, as $`\mathsf{store}` does.
The definition lists every op, with no case for the rest, so a new core op
does not build until it declares its class (ADR-2026-11-03-0600).
$`\mathsf{cond\_br}` is `condBr` in the Lean. The Lean checks the
exceptions against one instance of every core op.
:::

:::readable Fir.Core.Ty.IsPoison (fingerprint := "6476707130089650496")
*Definition: which core values are poison.* A value of $`\mathsf{i}N`, of
$`\mathsf{float}\langle e,m \rangle` or of
$`\mathsf{ptr}\langle N \rangle` is poison when it is $`\mathsf{poison}`.
These are the poison values of the core dialect's types, which the
obligations speak of.
:::

:::readable Fir.Core.Ty.poison_isRefinedBy (pin := Fir.Core.Ty.IsRefinedBy) (fingerprint := "7506654877269647067")
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

:::readable Fir.Core.alloca_propagatesPoison (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (fingerprint := "8834273668863875278")
*Theorem: $`\mathsf{alloca}` propagates poison, whatever the semantics of
the core ops.* For every kind, type, count, alignment and memory,
$`\mathsf{alloca}` propagates poison under any meaning that the core ops
are given in the set monad. Like $`\mathsf{const}`, it has no operands, so
no operand vector holds a poison, and both clauses hold with nothing to
check. Its rule needs memory, so its other obligations are those with
memory, proved by
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[its own rule].
:::
