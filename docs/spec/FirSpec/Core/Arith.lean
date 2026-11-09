import VersoManual
import Fir.Core.Arith
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on arithmetic rules, which renders
`Fir.Core.Arith` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Arithmetic rules: readable blocks" =>

:::moduleDocs (fingerprint := "13558055072320394658")
:::

:::readable Fir.Core.constValue Fir.Core.poisonValue (pin := Fir.PoisonOr) (fingerprint := "13574323644244185487")
*Definition: the rules of $`\mathsf{const}` and $`\mathsf{poison}`.* For
every width $`N` and every vector $`c` of $`N` bits,
$`\mathsf{const}_N~c` gives $`c`, and $`\mathsf{poison}_N` gives poison.
Neither has operands:

$$`\mathsf{const}_N~c\,() = c \qquad \mathsf{poison}_N\,() = \mathsf{poison}`

From this section on, the execution rule of an op is written as a function
of its operand values: $`\mathsf{add}_N(a, b)` is what $`\mathsf{add}_N`
gives on the operands $`a` and $`b`. A value of $`\mathsf{i}N` is
{ref "The-fir-specification--Execution--Core-values"}[poison or a vector of bits],
$`N` of them, and $`\mathbb{B}^N` is the set of vectors of $`N` bits.

These two rules are how a program writes a fixed value. A constant is
never poison, and $`\mathsf{poison}_N` is poison on every run, which is how
a program writes LLVM's poison constant. Neither is ever UB.
:::

:::readable Fir.Core.addValues (pin := BitVec.add) (fingerprint := "6425417634766469116")
*Definition: the rule of $`\mathsf{add}` without flags.* For every width
$`N`, $`\mathsf{add}_N` of two vectors of bits is their sum modulo
$`2^N`, and $`\mathsf{add}_N` of a poison operand, in either place, is
poison:

$$`\mathsf{add}_N(a, b) = (a + b) \bmod 2^N`

for $`a, b \in \mathbb{B}^N`, and $`\mathsf{add}_N(a, b)` is poison when
$`a` or $`b` is poison.

Here a vector of bits stands for the number it writes in binary, from
$`0` to $`2^N - 1`, and $`k \bmod 2^N` is the vector of $`N` bits that
writes the remainder of $`k` divided by $`2^N`. The sum wraps, as two's
complement addition does, so the same rule serves signed and unsigned
integers, and it is never UB. A poison operand gives poison: $`\mathsf{add}`
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison]
(ADR-2026-10-30-0818). The flags $`\mathsf{nuw}` and $`\mathsf{nsw}` are
the next section's.
:::
