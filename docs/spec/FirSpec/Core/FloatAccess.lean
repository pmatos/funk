import VersoManual
import Fir.Core.FloatAccess
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the float load and store rules,
which renders `Fir.Core.FloatAccess` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Float load and store rules: readable blocks" =>

:::moduleDocs (fingerprint := "1023514822293366223")
:::

:::readable Fir.Core.loadFloatResult Fir.Core.loadFloatRule Fir.Core.storeFloatRule (pin := Fir.Core.loadShape) (pin := Fir.Core.storeAlign) (pin := Fir.Core.storeUnits) (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.Memory.decodeInt) (pin := Fir.Memory.encodeInt) (pin := Fir.Core.Op) (fingerprint := "3579514735400200227")
*Definition: the rules of the load and store of a float.* Let a run's
memories have the layout entries $`\ell`, and let the run name the core's
memory $`x` as $`\rho(x)`. For $`\mathsf{load}_N~o~\mathsf{float}\langle e,m \rangle~a`
on the pointer $`p`, and $`\mathsf{store}_N~o~\mathsf{float}\langle e,m \rangle~a`
on the value $`v` and the pointer $`p`, let $`E = \ell(\rho(N))`,
$`W = 1 + e + m` the float's bits, and $`(k, b)` the
{ref "The-fir-specification--Memory--Load-rules"}[shape of a load] of
$`\mathsf{i}W` in $`E`: $`k = \lceil W / u_E \rceil` units, aligned to
$`a` when the op gives one, and otherwise to the least power of two that
is at least $`k`, the natural alignment of the float's size. In a monad
with UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]:

* if $`p` is poison, each rule is immediate UB, for the reason of
  $`\mathsf{load}` or $`\mathsf{store}`;
* otherwise the load is the
  {ref "The-fir-specification--Memory--The-memory-model"}[aligned load]
  through $`p`, from $`\rho(N)`, of $`k` units at the alignment $`b`,
  {ref "The-fir-specification--Memory--Values-in-units"}[decoded] in the
  byte order of $`E` as the integer of $`W` bits: the float whose bit
  pattern that integer is, or poison when a unit is poison or a pointer's
  fragment;
* and the store is the aligned store through $`p`, to $`\rho(N)`, at the
  alignment $`b`, of the encoding of $`v`'s bits in $`k` units of $`E`'s
  byte order, with the bits past $`W` zero, or $`k` poison units when $`v`
  is poison. It gives no result.

An access that faults is UB for the reason of its fault. The ordering
$`o` does not change the rules: validation accepts only
$`\mathsf{nonatomic}`.
:::

:::readable Fir.Core.storeFloatRule_eq Fir.Core.loadFloatResult_bits Fir.Core.loadFloatRule_sameUnits (pin := Fir.Core.loadRule) (pin := Fir.Core.storeRule) (pin := Fir.Core.loadResult) (fingerprint := "8992630105893003897")
*Theorems: a float in memory is the integer of its bits.* The store of a
float of $`\mathsf{float}\langle e,m \rangle` is the
{ref "The-fir-specification--Memory--Store-rules"}[store] of
$`\mathsf{i}W`, $`W = 1 + e + m`, with the same bits: the same units, at
the same alignment. The load of a float reads the units that the
{ref "The-fir-specification--Memory--Load-rules"}[load] of $`\mathsf{i}W`
reads, at the same alignment, and decodes them to the same bits. So a
float stored and loaded back is the same float, a NaN's payload and sign
included, a float loaded as $`\mathsf{i}W` gives its bit pattern, and an
$`\mathsf{i}W` loaded as a float gives the float with its bits.
:::
