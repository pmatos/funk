import VersoManual
import Fir.Core.FloatBitcast
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on bit cast rules, which renders
`Fir.Core.FloatBitcast` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Bit cast rules: readable blocks" =>

:::moduleDocs (fingerprint := "11113321670423418225")
:::

:::readable Fir.Core.bitcastValue (fingerprint := "11113321670423418225")
*Definition: the rule of $`\mathsf{bitcast}`.* For every width $`N`, a
bit cast of a vector of $`N` bits is that vector; of poison, it is poison:

$$`\mathsf{bitcast}(a) = a`

for $`a \in \mathbb{B}^N`, and $`\mathsf{bitcast}(\mathsf{poison}) = \mathsf{poison}`.

Both directions share this rule. A value of
$`\mathsf{float}\langle e,m \rangle` is a vector of $`1+e+m` bits, as a
value of $`\mathsf{i}N` with $`N = 1+e+m` is, so casting from the float to
the integer, or back, keeps every bit. No number is read: nothing rounds,
and a NaN's sign and payload come through as they are. A bit cast is never
UB, and a poison operand gives poison: it
{ref "The-fir-specification--Execution--Poison-classes"}[propagates poison].
:::
