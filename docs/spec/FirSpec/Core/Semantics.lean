import VersoManual
import Fir.Core.Semantics
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core op semantics, which renders
`Fir.Core.Semantics` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Core op semantics: readable blocks" =>

:::moduleDocs (fingerprint := "8908722822994727884")
:::

:::readable Fir.Core.Op.denote? (fingerprint := "7653001876836925693")
*Definition: the rule of each core op that is not a terminator.* For
every way of computing with the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[choice and UB effects],
each core op that is not a terminator, other than $`\mathsf{call}`, has the
rule of its family, which takes its operand values and gives its one
result:

* $`\mathsf{const}_N~c` and $`\mathsf{poison}_N`: the
  {ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules];
* $`\mathsf{add}_N~\phi`, $`\mathsf{sub}_N~\phi` and
  $`\mathsf{mul}_N~\phi`: the rules with flags of the
  {ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules];
* $`\mathsf{sdiv}_N`, $`\mathsf{udiv}_N`, with or without
  $`\mathsf{exact}`, $`\mathsf{srem}_N` and $`\mathsf{urem}_N`: the
  {ref "The-fir-specification--Execution--Division-rules"}[division rules],
  each turned into a rule that may end with UB;
* $`\mathsf{freeze}_N`: the
  {ref "The-fir-specification--Execution--The-freeze-rule"}[freeze rule],
  the one rule that chooses;
* $`\mathsf{and}_N`, $`\mathsf{or}_N`, $`\mathsf{xor}_N`,
  $`\mathsf{shl}_N`, $`\mathsf{lshr}_N` and $`\mathsf{ashr}_N`: the
  {ref "The-fir-specification--Execution--Bitwise-and-shift-rules"}[bitwise and shift rules];
* $`\mathsf{icmp}_N~p` and $`\mathsf{select}_N`: the
  {ref "The-fir-specification--Execution--Comparison-and-selection-rules"}[comparison and selection rules];
* $`\mathsf{zext}_{M \to N}`, $`\mathsf{sext}_{M \to N}` and
  $`\mathsf{trunc}_{M \to N}`: the
  {ref "The-fir-specification--Execution--Width-change-rules"}[width change rules].

$`\mathsf{call}` and the terminators have none here: a call's meaning is
the run of its callee, and a terminator's rule says where control goes.
The rules are written once, for every way of computing with these
effects, so the spec's set of the ways a run may end and the tree of
choices that `fir-ref run` walks share them.
:::

:::readable Fir.Core.Op.exit? (fingerprint := "14161872408466095758")
*Definition: the rule of each core terminator.* For every way of
computing with the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[UB effect],
the terminators $`\mathsf{br}` and $`\mathsf{cond\_br}` have the
{ref "The-fir-specification--Execution--Branch-rules"}[branch rules], and
$`\mathsf{ret}` the rule of the
{ref "The-fir-specification--Execution--Control-flow-rules"}[control-flow rules].
Each takes the terminator's operand values and says where control goes.
Every op that is not a terminator has none here.
:::

:::readable Fir.Core.Op.hasRules (pin := Fir.instDialectDenoteCoreDialectSetM) (pin := Fir.instDialectCallCoreDialect) (pin := Fir.Core.Op.callTarget?) (pin := Fir.Core.Op.denote?) (pin := Fir.Core.Op.exit?) (fingerprint := "7015844231653859016")
*Definition: an op has rules.* A core op has rules when one of the two
blocks above gives it a rule, as an op that is not a terminator or as a
terminator, or when it calls a function, whose run is its meaning. Every core op
has rules: tests check one instance of each op, $`\mathsf{add}` with each
set of flags and $`\mathsf{icmp}` with each predicate among them, and
$`\mathsf{call}` counts through its callee.

*Definition: the core dialect's semantics.* In the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad], the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[meaning]
of a core op $`o` on the operand values $`v^*` is its rule:

$$`\mathrm{denote}_o(v^*) = \begin{cases} r(v^*) & \text{if } o \text{ has a rule } r \\ \emptyset & \text{otherwise} \end{cases}`

and $`\mathrm{exit}_o(v^*)` likewise, from the rules of the terminators.
$`\emptyset` is the computation with no outcome: it has no way to end.

*Definition: the core ops that call a function.* $`\mathrm{callee}(o)` is
the function that the
{ref "The-fir-specification--Execution--Call-rules"}[call rules] give: $`f`
for $`\mathsf{call}~f : t^* \to r^*`, and none for every other op.

An op with no rule has no outcome. That is not a stand-in meaning: the
{ref "The-fir-specification--Execution--Poison-classes"}[totality obligation]
rejects it, so the poison obligations of a dialect cannot be proved while
one of its valid op instances that runs by its own rule lacks its rules,
unless one of its operand types has no value (ADR-2026-10-30-1855).
$`\mathsf{call}` has no rule here, and its meaning has no outcome, but no
run reaches it: the interpreter runs the callee of an op that has one
instead. So a call has no op-level obligation (ADR-2026-11-02-1514).
:::
