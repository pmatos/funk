import VersoManual
import Fir.Core.FloatArith
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float arithmetic rules, which
renders `Fir.Core.FloatArith` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Float arithmetic rules: readable blocks" =>

:::moduleDocs (fingerprint := "8513493984461929586")
:::

:::readable Fir.Core.nanBits (fingerprint := "1042529435153672994")
*Definition: the NaN that a choice names.* For every format
$`\mathsf{float}\langle e,m \rangle` and $`c \in \mathbb{B}^{m+1}`, read as
a sign bit $`s`, its top bit, and $`m` bits $`p` below it,

$$`\mathrm{nan}_{e,m}(c) = s \cdot 1^{e} \cdot \begin{cases} p & \text{if } p \neq 0^{m} \\ 1\,0^{m-1} & \text{if } p = 0^{m} \end{cases}`

the bits of a sign, an exponent of all ones and a mantissa. A nonzero
$`p` is the mantissa as it is, and a zero one, which would spell an
infinity, stands for the quiet NaN, whose mantissa has only its top bit
set. So $`\mathrm{nan}_{e,m}` gives every NaN of the format, and nothing
else: at $`\mathsf{f32}`, $`c = 0` gives $`\mathtt{0x7fc00000}`, the top
bit alone $`\mathtt{0xffc00000}`, $`c = 1` the signalling NaN
$`\mathtt{0x7f800001}`, and all ones $`\mathtt{0xffffffff}`.
:::

:::readable Fir.Core.anyNaN Fir.Core.floatResult (fingerprint := "7172722748715513918")
*Definition: the result of a float op.* $`\mathrm{anynan}_{e,m}` chooses
$`m + 1` bits $`c` and gives the value $`\mathrm{nan}_{e,m}(c)`: every NaN
of the format is one way it ends.

A float op computes in Lean's model, whose format $`F` has $`e`
exponent bits and $`m` mantissa bits. Given the model's result $`u`,
computed from the operands read with $`\mathrm{unpack}_F`,

$$`\mathrm{result}_{e,m}(u) = \begin{cases} \mathrm{pack}_F(u) & \text{if } u \text{ is not a NaN} \\ \mathrm{anynan}_{e,m} & \text{if } u \text{ is a NaN} \end{cases}`

So the op makes a choice only when its result is a NaN, and every other
result is one bit pattern. A format that the model does not have, with
$`e < 2` or $`m = 0`, which validation rejects, gives
$`\mathrm{anynan}_{e,m}` on every operand, so that the rule is total.
:::

:::readable Fir.Core.FBin.model Fir.Core.FUnary.model (pin := Fir.Core.FBin) (pin := Fir.Core.FUnary) (pin := Fir.Core.remainder) (fingerprint := "11734426222456348426")
*Definition: what each float op computes in the model.* Each op is an
operation of Lean's float model on the format $`F`, or, for
$`\mathsf{frem}` and $`\mathsf{fmod}`, fir's
{ref "The-fir-specification--Execution--Float-remainder-rules"}[remainder] on the
model's numbers:

$$`\begin{array}{ll} \mathsf{fadd}: \mathrm{add}_F & \mathsf{fneg}: \mathrm{neg} \\ \mathsf{fsub}: \mathrm{sub}_F & \mathsf{fabs}: \mathrm{abs} \\ \mathsf{fmul}: \mathrm{mul}_F & \mathsf{sqrt}: \mathrm{sqrt}_F \\ \mathsf{fdiv}: \mathrm{div}_F & \mathsf{frem}: \mathrm{rem}^{\mathrm{near}}_F \\ \mathsf{fmod}: \mathrm{rem}^{\mathrm{trunc}}_F & \end{array}`

Each operation of two operands but the remainders, and
$`\mathrm{sqrt}_F`, rounds its exact result to nearest, ties to even, at
the format, and an exact result too large for it is an infinity. A
remainder is exact. $`\mathrm{neg}` and $`\mathrm{abs}` change
the sign of a number, an infinity or a zero, and give the model's one NaN
on a NaN.
:::

:::readable Fir.Core.fbinValues Fir.Core.funaryValue Fir.Core.fmaValues (fingerprint := "2976483791253547667")
*Definition: the rules of the float arithmetic.* For every format
$`\mathsf{float}\langle e,m \rangle` and values $`a`, $`b`, $`c` of it:

$$`\mathsf{fadd}_{e,m}(a, b) = \begin{cases} \mathrm{result}_{e,m}(\mathrm{add}_F(\mathrm{unpack}_F(a), \mathrm{unpack}_F(b))) & \text{if } a, b \in \mathbb{B}^{1+e+m} \\ \mathsf{poison} & \text{if } a \text{ or } b \text{ is poison} \end{cases}`

and $`\mathsf{fsub}`, $`\mathsf{fmul}`, $`\mathsf{fdiv}`, $`\mathsf{frem}`
and $`\mathsf{fmod}` likewise, with their operations. $`\mathsf{fneg}`, $`\mathsf{fabs}` and $`\mathsf{sqrt}`
apply theirs to $`\mathrm{unpack}_F(a)`, and

$$`\mathsf{fma}_{e,m}(a, b, c) = \mathrm{result}_{e,m}(\mathrm{fma}_F(\mathrm{unpack}_F(a), \mathrm{unpack}_F(b), \mathrm{unpack}_F(c)))`

on defined operands, $`a \times b + c` rounded once, and
$`\mathsf{poison}` when any operand is poison. None of them is ever UB.
:::
