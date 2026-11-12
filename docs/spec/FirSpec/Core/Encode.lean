import VersoManual
import Fir.Core.Encode
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core's values in memory, which
renders `Fir.Core.Encode` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core's values in memory: readable blocks" =>

:::moduleDocs (fingerprint := "1698454689595369772")
:::

:::readable Fir.DataLayout.pointer_pos (fingerprint := "15452446704807025419")
*Theorem: pointers have bits.* Each memory of a valid layout, the
default memory included, has pointers of at least one bit.
:::

:::readable Fir.Core.Ty.units? (fingerprint := "14989890563056299282")
*Definition: the size of a type.* In a memory whose units are $`u` bits
wide, under the layout $`l`:

$$`\mathrm{size}(\mathsf{i}N) = \lceil N / u \rceil \qquad \mathrm{size}(\mathsf{ptr}\langle N\rangle) = \lceil p_N / u \rceil`

where $`p_N` is the width of the pointers of memory $`N` in $`l`'s entry
for it. A float type has no size, nor has a pointer type whose memory
$`l` does not declare.
:::

:::readable Fir.Core.Ty.encode? Fir.Core.Ty.decode? (fingerprint := "9388341738214022395")
*Definition: the core's values in units.* A value of $`\mathsf{i}N` is
encoded and decoded as an integer of $`N` bits, and a value of
$`\mathsf{ptr}\langle N\rangle` as a pointer type that takes
$`\mathrm{size}(\mathsf{ptr}\langle N\rangle)` units, in the byte order
$`o`. A type without a size has neither.
:::

:::readable Fir.Core.Ty.encode?_length Fir.Core.Ty.units?_isSome (fingerprint := "554653787493576551")
*Theorem: an encoding takes its type's size.* When a value of $`t` has an
encoding $`\vec{x}`, $`\mathrm{size}(t) = |\vec{x}|`. Every integer type
has a size, and so has a pointer type whose memory the layout declares.
:::

:::readable Fir.Core.Ty.decode?_encode? (fingerprint := "2175914542106140325")
*Theorem: the core's values round trip.* For a valid layout, a valid type
$`t`, units of $`u > 0` bits and every byte order $`o`, decoding the
encoding of a value $`v` of $`t`, poison included, gives $`v` back.
:::
