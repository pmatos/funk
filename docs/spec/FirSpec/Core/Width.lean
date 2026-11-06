import VersoManual
import Fir.Core.Width
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on width change rules, which renders
`Fir.Core.Width` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Width change rules: readable blocks" =>

:::readable Fir.Core.zextValue (pin := BitVec.setWidth) (fingerprint := "5245716347567910269")
*Definition: the rule of $`\mathsf{zext}`.* For all widths $`M` and
$`N`, $`\mathsf{zext}_{M \to N}` of a vector of $`M` bits is the vector of
$`N` bits that writes the same number, modulo $`2^N`; of poison, it is
poison:

$$`\mathsf{zext}_{M \to N}(a) = a \bmod 2^N`

for $`a \in \mathbb{B}^M`, and $`\mathsf{zext}_{M \to N}(\mathsf{poison}) = \mathsf{poison}`.

Here $`\mathbb{B}^M` is the set of vectors of $`M` bits, a vector of bits
stands for the number it writes in binary, and $`k \bmod 2^N` is the vector of $`N` bits that writes the remainder of
$`k` divided by $`2^N`, as in the
{ref "The-fir-specification--Execution--Arithmetic-rules"}[arithmetic rules].
When $`M < N`, as validation asks, the result is $`a` with $`N - M` zeros
above it: read as unsigned, it equals $`a`. So $`\mathsf{zext}` of the
$`\mathsf{i8}` value $`-1`, all ones, to $`\mathsf{i32}` is 255. Width
changes are never UB, and a poison operand gives poison: they
{ref "The-fir-specification--Execution--Poison-classes"}[propagate poison].
:::

:::readable Fir.Core.sextValue (pin := BitVec.signExtend) (fingerprint := "113031403167316890")
*Definition: the rule of $`\mathsf{sext}`.* For all widths $`M` and
$`N`, $`\mathsf{sext}_{M \to N}` of a vector of $`M` bits is the vector of
$`N` bits that writes its signed value, modulo $`2^N`; of poison, it is
poison:

$$`\mathsf{sext}_{M \to N}(a) = \mathrm{signed}_M(a) \bmod 2^N`

for $`a \in \mathbb{B}^M`, and $`\mathsf{sext}_{M \to N}(\mathsf{poison}) = \mathsf{poison}`.

Here $`\mathrm{signed}_M(a)` is the integer that $`a` writes in two's
complement, as in the
{ref "The-fir-specification--Execution--Wrap-flag-rules"}[wrap flag rules].
When $`M < N`, the result is $`a` with $`N - M` copies of its top bit above
it: read as signed, it equals $`a`. So $`\mathsf{sext}` of the
$`\mathsf{i8}` value $`-1` to $`\mathsf{i32}` is $`-1`, and $`\mathsf{sext}`
of the $`\mathsf{i1}` value 1 is $`-1`, where $`\mathsf{zext}` gives 1.
:::

:::readable Fir.Core.truncValue (pin := BitVec.setWidth) (fingerprint := "5245716347567910269")
*Definition: the rule of $`\mathsf{trunc}`.* For all widths $`M` and
$`N`, $`\mathsf{trunc}_{M \to N}` of a vector of $`M` bits is the same
number modulo $`2^N`, as for $`\mathsf{zext}`; of poison, it is poison:

$$`\mathsf{trunc}_{M \to N}(a) = a \bmod 2^N`

for $`a \in \mathbb{B}^M`, and $`\mathsf{trunc}_{M \to N}(\mathsf{poison}) = \mathsf{poison}`.

When $`N < M`, as validation asks, the result keeps the low $`N` bits of
$`a` and drops the others, so $`\mathsf{trunc}` to $`\mathsf{i1}` gives the
lowest bit.

Validation admits $`\mathsf{zext}` and $`\mathsf{sext}` only when they
widen and $`\mathsf{trunc}` only when it narrows, but each rule gives a
value at every pair of widths: to the same width, all three give the
operand, and $`\mathsf{sext}` to a narrower width keeps the low bits. So
the three ops meet their poison obligations at every pair of widths, valid
or not.
:::
