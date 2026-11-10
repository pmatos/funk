import VersoManual
import Fir.Core.Signature
import Fir.Validation.Rules
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core signatures, which renders
`Fir.Core.Signature` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Core signatures: readable blocks" =>

:::moduleDocs (fingerprint := "17172137080388402663")
:::

:::readable Fir.CoreDialect Fir.Core.i (fingerprint := "6975174900697461964")
*Definition: the core dialect.* The core dialect is the
{ref "The-fir-specification--Abstract-syntax--Dialects"}[dialect] whose op
instances are the
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core ops] and whose
types are the
{ref "The-fir-specification--Abstract-syntax--Core-types"}[core types]. It
is the first dialect of fir, and the one that every example of this
specification is written in. The Lean writes $`\mathsf{i}N` as `i N`, a
shorthand for the type `int N`.
:::

:::readable Fir.Core.Op.sig Fir.Core.Op.returnTypes (pin := Fir.Core.Op) (pin := Fir.Func.OpValid) (fingerprint := "5706628440802508344")
*Definition: the types of each core op's operands and results.* Each core op
takes operands and gives results of fixed types, which follow from the op
instance. As in the WebAssembly specification, $`[t_1^*] \to [t_2^*]`
says that an op takes operands of the types $`t_1^*`, in order, and gives
results of the types $`t_2^*`; $`[\,]` is the empty sequence. Here
$`\mathit{binop}_N` stands for any of $`\mathsf{add}_N`, $`\mathsf{sub}_N`
and $`\mathsf{mul}_N` with their flags, $`\mathsf{sdiv}_N` and
$`\mathsf{udiv}_N` with or without $`\mathsf{exact}`, $`\mathsf{srem}_N`,
$`\mathsf{urem}_N`, $`\mathsf{and}_N`, $`\mathsf{or}_N`, $`\mathsf{xor}_N`,
$`\mathsf{shl}_N`, $`\mathsf{lshr}_N` and $`\mathsf{ashr}_N`, and
$`\mathit{cvtop}_{M \to N}` for any of $`\mathsf{zext}_{M \to N}`,
$`\mathsf{sext}_{M \to N}` and $`\mathsf{trunc}_{M \to N}`:

$$`\begin{array}{ll} \mathsf{const}_N~c & [\,] \to [\mathsf{i}N] \\ \mathsf{poison}_N & [\,] \to [\mathsf{i}N] \\ \mathit{binop}_N & [\mathsf{i}N~\mathsf{i}N] \to [\mathsf{i}N] \\ \mathsf{icmp}_N~\mathit{pred} & [\mathsf{i}N~\mathsf{i}N] \to [\mathsf{i1}] \\ \mathsf{select}_N & [\mathsf{i1}~\mathsf{i}N~\mathsf{i}N] \to [\mathsf{i}N] \\ \mathit{cvtop}_{M \to N} & [\mathsf{i}M] \to [\mathsf{i}N] \\ \mathsf{freeze}_N & [\mathsf{i}N] \to [\mathsf{i}N] \\ \mathsf{br} & [\,] \to [\,] \\ \mathsf{cond\_br} & [\mathsf{i1}] \to [\,] \\ \mathsf{ret}~t^* & [t^*] \to [\,] \\ \mathsf{unreachable} & [\,] \to [\,] \\ \mathsf{call}~f : t^* \to r^* & [t^*] \to [r^*] \end{array}`

So $`\mathsf{select}_N` takes its $`\mathsf{i1}` condition first, a
$`\mathsf{ret}` takes the values it returns as its operands, and a
$`\mathsf{call}` takes its callee's arguments and gives its callee's
results. The Lean calls the two halves `sig` and `returnTypes`, and spells
$`\mathsf{cond\_br}` as `condBr`.

These types are what
{ref "The-fir-specification--Validation--The-general-rules"}[validation]
checks every op against: each operand must be a value of the operand's
type, and each result is declared with the result's type.
:::

:::readable Fir.Core.Op.isTerminator Fir.Core.Op.succCount (pin := Fir.instDialectSignatureCoreDialect) (fingerprint := "11134669087793284921")
*Definition: the core terminators and their successors.* $`\mathsf{br}`,
$`\mathsf{cond\_br}`, $`\mathsf{ret}~t^*` and $`\mathsf{unreachable}` are
the terminators of the core dialect, the ops that end a block.
$`\mathsf{br}` has one successor and $`\mathsf{cond\_br}` two; no other
core op has any, so $`\mathsf{ret}` leaves the function instead of going to
a block, and $`\mathsf{unreachable}` goes nowhere.

With the operand and result types above, these give the
{ref "The-fir-specification--Abstract-syntax--Dialects"}[signature] of the
core dialect: $`\mathrm{sig}_{\mathrm{core}}(o)` and
$`\mathrm{res}_{\mathrm{core}}(o)` are the two halves of the table above,
$`\mathrm{term}_{\mathrm{core}}(o)` is true exactly for $`\mathsf{br}`,
$`\mathsf{cond\_br}`, $`\mathsf{ret}~t^*` and $`\mathsf{unreachable}`, and
$`\mathrm{nsucc}_{\mathrm{core}}(o)` is 1 for $`\mathsf{br}`, 2 for
$`\mathsf{cond\_br}` and 0 otherwise. No core op owns a region:
$`\mathrm{kinds}_{\mathrm{core}}(o)` is empty for every op.
:::

:::readable Fir.Core.op (fingerprint := "1597957136772372945")
*Definition: a shorthand for an op with no regions.* The examples and checks of this
specification write a core op with a shorthand. It takes the op's results
$`(x : t)^*`, its op instance $`o`, its operands $`y^*`, and, when they are
given, its location reference $`r` and its successors $`\mathit{succ}^*`,
and builds the op

$$`\begin{aligned} \{&\mathsf{results}~(x : t)^*,~\mathsf{op}~o, \\ &\mathsf{operands}~y^*,~\mathsf{succs}~\mathit{succ}^*, \\ &\mathsf{regions}~\epsilon,~\mathsf{loc}~r\} \end{aligned}`

with no regions. When they are not
given, the location reference is 0 and there are no successors. Nothing
in the rules uses it; it is stated so that a reader can follow the ops of
the examples, such as
{ref "The-fir-specification--Validation--A-rejected-function"}[a rejected function]
and the {ref "The-fir-specification--Text-format--Example"}[example] of the
text format.

The Lean under this block ends with the core dialect's signature, which
assembles the four functions above.
:::
