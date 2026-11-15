import VersoManual
import Fir.Core.OpAttrs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on core op attributes, which renders
`Fir.Core.OpAttrs` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Core op attributes: readable blocks" =>

:::moduleDocs (fingerprint := "15784081672852081284")
:::

:::readable Fir.Core.WrapFlags (fingerprint := "2440796118969772124")
*Wrap flags.* The ops $`\mathsf{add}`, $`\mathsf{sub}` and $`\mathsf{mul}`
carry two flags. Each flag is a promise about the operands, and when the
promise is broken the result is
{ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison].

```grammar Fir.Core.WrapFlags
\mathit{flags}
nuw,nsw   \mathsf{nuw}^?~\mathsf{nsw}^?
```

* $`\mathsf{nuw}`, no unsigned wrap: read as unsigned integers, the
  operands give an exact result that fits in $`N` bits.
* $`\mathsf{nsw}`, no signed wrap: read as two's-complement signed
  integers, the operands give an exact result that fits in $`N` bits.

A flag is off unless the op sets it.
:::

:::readable Fir.Core.Pred (fingerprint := "11087752805963245739")
*Predicates.* A comparison asks one of ten questions about two integers.
$`\mathsf{eq}` and $`\mathsf{ne}` compare their bits. The $`\mathsf{s}`
predicates read the integers as signed, and the $`\mathsf{u}` predicates as
unsigned: $`\mathsf{lt}` is less than, $`\mathsf{le}` less or equal,
$`\mathsf{gt}` greater than and $`\mathsf{ge}` greater or equal.

```grammar Fir.Core.Pred
\mathit{pred}
eq,ne             \mathsf{eq} \mid \mathsf{ne}
slt,sle,sgt,sge   \mathsf{slt} \mid \mathsf{sle} \mid \mathsf{sgt} \mid \mathsf{sge}
ult,ule,ugt,uge   \mathsf{ult} \mid \mathsf{ule} \mid \mathsf{ugt} \mid \mathsf{uge}
```
:::

:::readable Fir.Core.FPred (fingerprint := "7187194159295087930")
*Float predicates.* A float comparison asks one of fourteen questions about
two floats (ADR-2026-11-09-1549). It compares the numbers they encode, so
$`-0` equals $`+0`. A NaN encodes no number, and a pair with a NaN is
_unordered_. The $`\mathsf{o}` predicates are _ordered_: each is false on
an unordered pair. The $`\mathsf{u}` predicates are _unordered_: each is
true on one. Otherwise $`\mathsf{eq}` is equal, $`\mathsf{ne}` not equal,
$`\mathsf{lt}` less than, $`\mathsf{le}` less or equal, $`\mathsf{gt}`
greater than and $`\mathsf{ge}` greater or equal. $`\mathsf{ord}` holds of
an ordered pair, and $`\mathsf{uno}` of an unordered one.

```grammar Fir.Core.FPred
\mathit{fpred}
oeq,one,olt,ole   \mathsf{oeq} \mid \mathsf{one} \mid \mathsf{olt} \mid \mathsf{ole}
ogt,oge,ord       \mathsf{ogt} \mid \mathsf{oge} \mid \mathsf{ord}
ueq,une,ult,ule   \mathsf{ueq} \mid \mathsf{une} \mid \mathsf{ult} \mid \mathsf{ule}
ugt,uge,uno       \mathsf{ugt} \mid \mathsf{uge} \mid \mathsf{uno}
```
:::

:::readable Fir.Core.FastMath Fir.Core.FastMath.Reserved (fingerprint := "1415803108012639584")
*Fast-math flags.* A float op carries the fast-math flags
(ADR-2026-11-09-1549). Each of the first three is a promise about the
op's operands or result:

```grammar Fir.Core.FastMath
\mathit{fmf}
nnan,ninf,nsz      \mathsf{nnan}^?~\mathsf{ninf}^?~\mathsf{nsz}^?
contract,reassoc   \mathsf{contract}^?~\mathsf{reassoc}^?
```

* $`\mathsf{nnan}`, no NaNs: no operand and no result is a NaN. A NaN
  operand or result gives
  {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison].
* $`\mathsf{ninf}`, no infinities: no operand and no result is an
  infinity. An infinite operand or result gives poison.
* $`\mathsf{nsz}`, no signed zeros: the sign of a zero result does not
  matter, so a zero result is $`+0` or $`-0`, a choice.

$`\mathsf{contract}` and $`\mathsf{reassoc}` are _reserved_: they are
permissions for passes, which M2's optimizer decides, not meanings of an
op. Validation rejects an op that carries either, and the rules ignore
them. A flag is off unless the op sets it.
:::

:::readable Fir.Core.FBin Fir.Core.FUnary (fingerprint := "2436778371239232809")
*Float operations.* The float arithmetic has six ops of two operands and
three of one (ADR-2026-11-09-1549). Each that rounds carries its
{ref "The-fir-specification--Abstract-syntax--Rounding-modes"}[rounding mode]
$`r`; validation accepts only $`\mathsf{rne}`, to nearest with ties to
even, and the rules read every mode as it.

```grammar Fir.Core.FBin
\mathit{fbin}
fadd,fsub,fmul,fdiv   \mathsf{fadd}~r \mid \mathsf{fsub}~r \mid \mathsf{fmul}~r \mid \mathsf{fdiv}~r
frem,fmod             \mathsf{frem} \mid \mathsf{fmod}
```

```grammar Fir.Core.FUnary
\mathit{funary}
fneg,fabs,sqrt   \mathsf{fneg} \mid \mathsf{fabs} \mid \mathsf{sqrt}~r
```

* $`\mathsf{fadd}` adds, $`\mathsf{fsub}` subtracts the second operand
  from the first, $`\mathsf{fmul}` multiplies and $`\mathsf{fdiv}` divides
  the first by the second.
* $`\mathsf{frem}` and $`\mathsf{fmod}` give the remainder of the first
  by the second, $`x - n \times y`, which is exact, so neither rounds. For
  $`\mathsf{frem}`, IEEE 754's remainder, $`n` is the quotient rounded to
  nearest, ties to even; for $`\mathsf{fmod}`, C's `fmod`, it is the
  quotient truncated. LLVM's `frem` is $`\mathsf{fmod}`, not
  $`\mathsf{frem}` (#310).
* $`\mathsf{fneg}` negates and $`\mathsf{fabs}` gives the absolute value;
  neither rounds. $`\mathsf{sqrt}` gives the square root, rounded with its
  mode.
:::
