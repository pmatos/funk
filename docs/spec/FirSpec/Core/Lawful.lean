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

:::moduleDocs (fingerprint := "10829226034814001931")
:::

:::readable Fir.Core.Op.propagates_all (pin := Fir.Core.Op.poisonClass) (pin := Fir.PropagatesPoison) (pin := Fir.PoisonOut) (pin := Fir.UBByOwnRules) (pin := Fir.HVector.IsFilledBy) (fingerprint := "16426899403825358998")
*Theorem: each core op that propagates poison does.* For every
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op] $`o`
whose
{ref "The-fir-specification--Execution--Core-poison-classes"}[poison class]
is $`\mathsf{propagates}`, at every width, $`o`
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]:
on operands of which one is poison, every result it returns is poison,
and it may hit UB only if it may hit UB on some operands that put a
defined value in place of each poison.

These are 26 ops: $`\mathsf{const}` at an integer type and at a float
type, $`\mathsf{poison}`, $`\mathsf{add}`,
$`\mathsf{sub}`, $`\mathsf{mul}`, the four divisions $`\mathsf{sdiv}`,
$`\mathsf{udiv}`, $`\mathsf{srem}` and $`\mathsf{urem}`, the bitwise ops
$`\mathsf{and}`, $`\mathsf{or}` and $`\mathsf{xor}`, the shifts
$`\mathsf{shl}`, $`\mathsf{lshr}` and $`\mathsf{ashr}`, $`\mathsf{icmp}`,
$`\mathsf{fcmp}`, the width changes $`\mathsf{zext}`, $`\mathsf{sext}` and
$`\mathsf{trunc}`, the float arithmetic $`\mathit{fbin}`,
$`\mathit{funary}` and $`\mathsf{fma}`, and the two bit casts. Each proves it in the section of its family. The other
ops, $`\mathsf{select}`, $`\mathsf{freeze}`, $`\mathsf{br}`,
$`\mathsf{cond\_br}`, $`\mathsf{ret}`, $`\mathsf{unreachable}` and
$`\mathsf{call}`, are poison
exceptions with rules of their own.
:::

:::readable Fir.Core.pos_of_typesValid Fir.Core.Op.returnsOnDefined_valid (pin := Fir.TypesValid) (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.maxWidth) (pin := Fir.ReturnsOnDefined) (fingerprint := "3927830666421649206")
*Theorems: a valid core op instance with an operand of type
$`\mathsf{i}N` has $`N > 0`, and each valid core op that propagates poison returns a
result on defined operands.*

* If a core op instance is
  {ref "The-fir-specification--Validation--The-general-rules"}[valid],
  its types accepted by validation, and has an operand of type
  $`\mathsf{i}N`, then $`N > 0`: validation accepts $`\mathsf{i}N` only for
  $`1 \leq N \leq 16{,}777{,}215`.
* Every valid core op instance whose poison class is
  $`\mathsf{propagates}` returns a result on some operand vector with no
  poison.

$`\mathsf{poison}` returns one on the empty vector, where its result is
poison: the obligation asks for a result, not for a defined one
(ADR-2026-10-29-2006). The four divisions return one only at a width
above zero, where a divisor that is not zero exists, and the first theorem
gives that width. This is the one obligation that needs the op instance
to be valid (ADR-2026-10-29-2006).
:::

:::readable Fir.Core.lawfulDialectPoison (pin := Fir.LawfulDialectPoison) (pin := Fir.Core.Ty.Valid) (pin := Fir.Core.Ty.toType) (fingerprint := "4359772419578251092")
*Theorem: the core dialect is lawful.* Every core op instance whose types
validation accepts meets the
{ref "The-fir-specification--Execution--Poison-classes"}[poison obligations]:

* _Poison is refined by every value_: a poison of $`\mathsf{i}N`, of
  $`\mathsf{float}\langle e,m \rangle` or of
  $`\mathsf{ptr}\langle N \rangle` is refined by every value of its
  type, at every width, format and memory.
* _Propagation_: each op whose class is $`\mathsf{propagates}` propagates
  poison.
* _A result on defined operands_: each such op returns a result on some
  operand vector with no poison.
* _Totality_ and _monotonicity_: every terminator and every op with no
  callee, every core op but $`\mathsf{call}`, is total and monotone, at
  every width. A call is left out, since its meaning is its callee's run
  (ADR-2026-10-29-2006).

The core dialect is declared lawful with this proof. So every generic
theorem that asks for a lawful dialect holds for the core dialect: for
example, every function of a valid core module has an outcome at every
budget by the class alone, as the section on
{ref "The-fir-specification--Execution--What-the-lawful-class-gives"}[what the lawful class gives]
shows.
:::
