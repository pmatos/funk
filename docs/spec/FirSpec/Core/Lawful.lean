import VersoManual
import Fir.Core.Lawful
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core dialect's poison
obligations, which renders `Fir.Core.Lawful` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The core dialect's poison obligations: readable blocks" =>

:::moduleDocs (fingerprint := "11746787569716277188")
:::

:::readable Fir.Core.Op.propagates_all Fir.Core.load_propagatesPoison Fir.Core.store_propagatesPoison Fir.Core.loadPtr_propagatesPoison Fir.Core.storePtr_propagatesPoison Fir.Core.loadFloat_propagatesPoison Fir.Core.storeFloat_propagatesPoison Fir.Core.memCopy_propagatesPoison Fir.Core.memSet_propagatesPoison Fir.Core.fieldAddr_propagatesPoison (pin := Fir.Core.Op.poisonClass) (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.HVector.IsFilledBy) (fingerprint := "7725863538073868586")
*Theorem: each core op that propagates poison does.* For every
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op] $`o`
whose
{ref "The-fir-specification--Execution--Core-poison-classes"}[poison class]
is $`\mathsf{propagates}`, at every width, $`o`
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:
on operands of which one is poison, every result it returns is poison,
and it may hit UB only if it may hit UB on some operands that put a
defined value in place of each poison.

These are 43 ops: $`\mathsf{const}` at an integer type and at a float
type, $`\mathsf{poison}`, $`\mathsf{alloca}`, $`\mathsf{load}` and
$`\mathsf{store}` of an integer, of a pointer and of a float,
$`\mathsf{memcpy}` and $`\mathsf{memmove}` (`memCopy` in the Lean),
$`\mathsf{memset}` (`memSet`), $`\mathsf{add}`,
$`\mathsf{sub}`, $`\mathsf{mul}`, the four divisions $`\mathsf{sdiv}`,
$`\mathsf{udiv}`, $`\mathsf{srem}` and $`\mathsf{urem}`, the bitwise ops
$`\mathsf{and}`, $`\mathsf{or}` and $`\mathsf{xor}`, the shifts
$`\mathsf{shl}`, $`\mathsf{lshr}` and $`\mathsf{ashr}`, $`\mathsf{icmp}`,
$`\mathsf{fcmp}`, the width changes $`\mathsf{zext}`, $`\mathsf{sext}` and
$`\mathsf{trunc}`, the float arithmetic $`\mathit{fbin}`,
$`\mathit{funary}` and $`\mathsf{fma}`, the two bit casts, the two
conversions from integers $`\mathsf{sitofp}` and $`\mathsf{uitofp}`, the
two conversions between formats $`\mathsf{fpext}` and
$`\mathsf{fptrunc}`, the pointer offset $`\mathsf{ptradd}`, the two
conversions to integers $`\mathsf{fptosi}` and $`\mathsf{fptoui}`, and
the field address $`\mathsf{fieldaddr}`. Each proves it in the section of its family; $`\mathsf{alloca}`, like $`\mathsf{const}` and $`\mathsf{poison}`, has no operands, so it propagates poison whatever its rule, and
the loads and stores, $`\mathsf{fieldaddr}`, the copies and moves and
the fills have no outcome in the set monad, so they give no result and hit no UB there. The other
ops, $`\mathsf{select}`, $`\mathsf{freeze}`, $`\mathsf{br}`,
$`\mathsf{cond\_br}`, $`\mathsf{ret}`, $`\mathsf{unreachable}` and
$`\mathsf{call}`, are poison
exceptions with rules of their own.
:::

:::readable Fir.Core.pos_of_typesValid Fir.Core.Op.returnsOnDefined_valid (pin := Fir.TypesValid) (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.maxWidth) (pin := Fir.ReturnsOnDefined) (fingerprint := "18398628007073684114")
*Theorems: a valid core op instance with an operand of type
$`\mathsf{i}N` has $`N > 0`, and each valid core op that propagates poison returns a
result on defined operands.*

* If a core op instance is
  {ref "The-fir-specification--Validation--The-general-rules"}[valid],
  its types accepted by validation, and has an operand of type
  $`\mathsf{i}N`, then $`N > 0`: validation accepts $`\mathsf{i}N` only for
  $`1 \leq N \leq 16{,}777{,}215`.
* Every valid core op instance that touches no memory, reads no item of
  the run, and whose poison class is $`\mathsf{propagates}` returns a result on some operand vector
  with no poison.

$`\mathsf{poison}` returns one on the empty vector, where its result is
poison: the obligation asks for a result, not for a defined one
(ADR-2026-10-29-2006). The four divisions return one only at a width
above zero, where a divisor that is not zero exists, and the first theorem
gives that width. This is the one obligation that needs the op instance
to be valid (ADR-2026-10-29-2006). $`\mathsf{alloca}`, the loads and
stores, the copies and moves and the fills touch memory, and $`\mathsf{fieldaddr}`
reads an item: none has a rule in the set monad, so none gives a result
there. Each returns one with memory, by its own rule
(the
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[stack allocation obligations],
the {ref "The-fir-specification--Memory--Load-obligations"}[load obligations],
the {ref "The-fir-specification--Memory--Store-obligations"}[store obligations],
the {ref "The-fir-specification--Memory--Field-address-obligations"}[field address obligations],
the {ref "The-fir-specification--Memory--Copy-and-move-obligations"}[copy and move obligations]
and the {ref "The-fir-specification--Memory--Fill-poison-obligations"}[fill poison obligations]),
so the core dialect as a whole does not meet the lawful class in the set
monad, and meets the lawful classes with memory instead.
:::
