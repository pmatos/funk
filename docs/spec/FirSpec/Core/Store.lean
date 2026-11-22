import VersoManual
import Fir.Core.Store
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the store rules, which renders
`Fir.Core.Store` (ADR-2026-11-05-2012). Each block explains declarations of
that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Store rules: readable blocks" =>

:::moduleDocs (fingerprint := "18264806575999898273")
:::

:::readable Fir.Core.storeAlign Fir.Core.storeAlign_eq Fir.Core.storeUnits (pin := Fir.MemLayout.intAlign) (pin := Fir.Core.loadShape) (pin := Fir.Memory.encodeInt) (fingerprint := "12379333368898911469")
*Definitions: the alignment and the units of a store.* A store of
$`\mathsf{i}W` to a memory whose
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[entry] is
$`e`, with the alignment $`a` when the op gives one, is an access aligned
as a load of $`\mathsf{i}W` is:

$$`\begin{cases} a & \text{if } a \text{ is given} \\ \mathrm{align}_e(\mathsf{i}W) & \text{otherwise} \end{cases}`

The units it writes for the value $`v` are the
{ref "The-fir-specification--Memory--Values-in-units"}[encoding] of $`v`
in the unit width and byte order of $`e`: $`\lceil W / u_e \rceil` units,
with the bits past $`W` in the last one zero, or as many poison units when
$`v` is poison. In memory 0, the $`\mathsf{i32}` `0x04030201` is the bytes
1, 2, 3 and 4, in that order, aligned to 4.
:::

:::readable Fir.Core.poisonStorePointer Fir.Core.storeRule (pin := Fir.MonadMemory) (pin := Fir.MonadUB) (pin := Fir.Core.Op) (fingerprint := "11456535394922517443")
*Definition: the rule of $`\mathsf{store}`.* Let a run's memories have the
layout entries $`\ell`, and let the run name the core's memory $`x` as
$`\rho(x)`. For $`\mathsf{store}_N~o~W~a` on the operands $`v`, the value,
and $`p`, the pointer, let $`e = \ell(\rho(N))`. In a monad with UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect]:

* if $`p` is poison, the rule is immediate UB, for the reason "a store
  through a poison pointer", whatever $`v` is: some defined pointer in its
  place faults, as one with no provenance does;
* otherwise it is the
  {ref "The-fir-specification--Memory--The-memory-model"}[aligned store]
  through $`p`, to the memory $`\rho(N)`, of the units of $`v` at the
  store's alignment, and it gives no result. An access that faults is UB
  for the reason of its fault: no provenance, freed, out of bounds or
  misaligned, in that order.

A poison value is stored as poison units, so a store of it is not UB by
itself, and a load of those units gives poison again. Whether a store
faults depends on the allocations and on how many units it writes, not on
what they hold. The ordering $`o` does not change the rule: validation
accepts only $`\mathsf{nonatomic}`.
:::
