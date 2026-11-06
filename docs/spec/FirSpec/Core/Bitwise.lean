import VersoManual
import Fir.Core.Bitwise
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on bitwise and shift rules, which renders
`Fir.Core.Bitwise` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Bitwise and shift rules: readable blocks" =>

:::readable Fir.Core.andValues Fir.Core.orValues Fir.Core.xorValues (pin := BitVec.and) (pin := BitVec.or) (pin := BitVec.xor) (fingerprint := "487211523789888471")
*Definition: the rules of $`\mathsf{and}`, $`\mathsf{or}` and
$`\mathsf{xor}`.* For every width $`N`, each op works on two vectors of
bits one bit at a time, and a poison operand, in either place, gives
poison. For $`a` and $`b` in $`\mathbb{B}^N`, the set of vectors of
$`N` bits, and each bit $`i`, from 0 to
$`N - 1`:

$$`\begin{aligned} \mathsf{and}_N(a, b)_i &= a_i \wedge b_i \\ \mathsf{or}_N(a, b)_i &= a_i \vee b_i \\ \mathsf{xor}_N(a, b)_i &= a_i \oplus b_i \end{aligned}`

Here $`a_i` is bit $`i` of $`a`, counting from the lowest, and $`\oplus` is
exclusive or. At $`\mathsf{i1}` the three ops are the boolean ops on the
bits 0 and 1. None of them is ever UB, and all three
{ref "The-fir-specification--Execution--Poison-classes"}[propagate poison]
(ADR-2026-10-30-0818).
:::

:::readable Fir.Core.shiftValues (fingerprint := "11993629658997560653")
*Definition: a shift, with its amount checked.* For every width $`N` and
every way $`s` of shifting a vector of $`N` bits by a number of places,
the shift of $`a` by the amount $`n` reads $`n` as unsigned. It gives
$`s(a, n)` when $`n < N`, and poison when $`n \geq N` or when either
operand is poison:

$$`\mathrm{shift}_s(a, n) = \begin{cases} s(a, n) & \text{if } n < N \\ \mathsf{poison} & \text{if } n \geq N \end{cases}`

for $`a` and $`n` in $`\mathbb{B}^N`, the set of vectors of $`N` bits, and
$`\mathrm{shift}_s(a, n)` is poison when $`a` or $`n` is poison.

Here a vector of bits stands for the number it writes in binary, as in the
{ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules].
One definition checks the amount for all three shifts, as LLVM does: a
shift by $`N` or more places has no defined result.
:::

:::readable Fir.Core.shlValues Fir.Core.lshrValues Fir.Core.ashrValues (pin := Fir.Core.shiftValues) (pin := BitVec.shiftLeft) (pin := BitVec.ushiftRight) (pin := BitVec.sshiftRight) (fingerprint := "7037673791125197716")
*Definition: the rules of $`\mathsf{shl}`, $`\mathsf{lshr}` and
$`\mathsf{ashr}`.* For every width $`N`, each is $`\mathrm{shift}_s`
above, with its own way $`s` of shifting. For $`a \in \mathbb{B}^N` and
an amount $`n < N`:

$$`\begin{aligned} \mathsf{shl}_N(a, n) &= (a \cdot 2^n) \bmod 2^N \\ \mathsf{lshr}_N(a, n) &= \lfloor a / 2^n \rfloor \\ \mathsf{ashr}_N(a, n) &= \lfloor \mathrm{signed}_N(a) / 2^n \rfloor \bmod 2^N \end{aligned}`

and each is poison when $`n \geq N` or an operand is poison.

* $`\mathsf{shl}` moves the bits of $`a` up by $`n` places and fills the
  low places with zeros.
* $`\mathsf{lshr}` moves them down and fills the high places with zeros.
* $`\mathsf{ashr}` moves them down and fills the high places with copies of
  the top bit, so it divides the signed value by $`2^n`, rounding towards
  minus infinity.

Here $`\mathrm{signed}_N(a)` is the integer that $`a` writes in two's
complement, and $`k \bmod 2^N` the vector of $`N` bits that writes the
remainder of $`k` divided by $`2^N`, as in the
{ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules].
Since poison is
{ref "The-fir-specification--Execution--Values-and-refinement"}[refined]
by every value, native code may give any value for
a shift by $`N` or more, so a backend may compile a shift to one x86-64
shift instruction, which masks the amount. A shift by less than $`N` must
give exactly the value above.
:::

:::readable Fir.Core.shiftValues_msb (pin := BitVec.msb) (fingerprint := "13704388932725673484")
*Theorem: a shift by an amount whose top bit is set is poison.* For every
width $`N`, every way $`s` of shifting, every value $`a` of
$`\mathsf{i}N`, poison included, and every $`n \in \mathbb{B}^N` whose top
bit is 1:

$$`\mathrm{shift}_s(a, n) = \mathsf{poison}`

An amount whose top bit is set is $`2^{N-1}` or more, which is never less
than $`N`. So no amount is read as a negative number, and no shift goes the
other way: a backend never has to handle a shift by a negative amount.
:::

:::readable Fir.Core.Table1 (fingerprint := "18356593340786296436")
*Definition: a truth table at $`\mathsf{i1}`, for the tests.* A list of
triples of one-bit vectors: two operands and the result an op gives on
them.
:::

:::readable Fir.Core.bitwiseRules (fingerprint := "10190629720676821821")
*Definition: the six rules of this section at one width, for the tests.*
The rules of $`\mathsf{and}`, $`\mathsf{or}`, $`\mathsf{xor}`,
$`\mathsf{shl}`, $`\mathsf{lshr}` and $`\mathsf{ashr}` at the width $`N`,
in a list, so that a test can check all six on the same operands.
:::
