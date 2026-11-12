import VersoManual
import Fir.Memory.EncodeLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the laws of values in units, which
renders `Fir.Memory.EncodeLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Laws of values in units: readable blocks" =>

:::moduleDocs (fingerprint := "17779421343732612243")
:::

:::readable Fir.ByteOrder.place_place Fir.ByteOrder.length_place Fir.ByteOrder.mem_place Fir.ByteOrder.place_replicate (fingerprint := "17239911817336278410")
*Theorem: placing in a byte order.* $`\mathrm{place}_o(\mathrm{place}_o(\vec{x})) = \vec{x}`.
Placing keeps the number of units and which units there are, and units
that are all the same stay as they are.
:::

:::readable Fir.Memory.le_mul_unitsFor Fir.Memory.unitsFor_pos (fingerprint := "4568264076784386149")
*Theorem: enough units.* If $`u > 0`, then $`w \le u \cdot \lceil w/u \rceil`:
the units hold every bit of the value. If also $`w > 0`, there is at
least one unit.
:::

:::readable Fir.Memory.length_digits Fir.Memory.length_encodeInt Fir.Memory.length_fragments Fir.Memory.length_encodePtr (fingerprint := "18215605909154878319")
*Theorem: an encoding takes the type's size.* An integer of $`w` bits,
poison included, takes $`\lceil w/u \rceil` units, and a pointer type that
takes $`k` units takes $`k`, for a pointer or poison, at every byte order.
:::

:::readable Fir.Memory.unitsValue_digits (fingerprint := "7939096903994925401")
*Theorem: digits stand for the number, cut.* $`\mathrm{digits}_k(n)`
stands for $`n \bmod 2^{u \cdot k}`.
:::

:::readable Fir.Memory.unitsValue_encodeInt (fingerprint := "12962096595814444783")
*Theorem: zero padding.* If $`u > 0`, the units of $`\mathrm{enc}_o(b)`,
placed back, stand for $`b` itself: every bit past $`b`'s width is zero.
:::

:::readable Fir.Memory.unitsValue_eq_none (fingerprint := "6385170251120287704")
*Theorem: units that are not all bits stand for no number.* If one of
$`\vec{x}` is poison or a pointer's fragment, $`\vec{x}` stands for no
number.
:::

:::readable Fir.Memory.decodeInt_eq_value Fir.Memory.decodeInt_ignores_padding (fingerprint := "13458802761632638884")
*Theorem: decoding ignores the padding.* $`\lceil w/u \rceil` units whose
placed units stand for $`n` decode to $`n \bmod 2^w`. So two such lists
whose numbers agree on their low $`w` bits decode to the same value,
whatever bits past $`w` they hold.
:::

:::readable Fir.Memory.decodeInt_encodeInt_value Fir.Memory.decodeInt_encodeInt_poison Fir.Memory.decodeInt_encodeInt (fingerprint := "9641002120602516439")
*Theorem: the integer law.* If $`u > 0` and $`w > 0`, then for every
byte order $`o` and every value $`v` of $`\mathsf{i}N`, $`N = w`, poison
included,

$$`\mathrm{dec}_o(\mathrm{enc}_o(v)) = v`
:::

:::readable Fir.Memory.decodePtr_encodePtr (fingerprint := "1201210544938447313")
*Theorem: the pointer law.* If a pointer takes $`k > 0` units, then for
every byte order $`o` and every value $`v` of the pointer type, poison
included, $`\mathrm{dec}_o(\mathrm{enc}_o(v)) = v`. The decoded pointer
keeps its provenance.
:::

:::readable Fir.Memory.mem_digits Fir.Memory.exists_mem_encodePtr (fingerprint := "2334556086378682468")
*Theorem: what the units are.* Every unit of an integer's digits is bits.
A pointer type that takes $`k > 0` units has, in each encoding, a unit
that is not bits: a fragment, or poison.
:::

:::readable Fir.Memory.decodeInt_encodePtr Fir.Memory.decodePtr_encodeInt (fingerprint := "2420642749408575033")
*Theorem: punned decodings give poison.* At any byte orders $`o` and
$`o'`, decoding as an integer the encoding of a pointer type that takes
$`k > 0` units gives $`\mathsf{poison}`, and so does decoding as a
pointer an integer's encoding.
:::

:::readable Fir.Memory.load_store_encodeInt Fir.Memory.load_store_encodePtr (fingerprint := "13725776296374384105")
*Theorem: through memory.* If storing $`\mathrm{enc}_o(v)` through $`p`
gives $`M'`, then loading from $`M'` the units of $`v`'s type through
$`p`, and decoding them, gives $`v` back, poison included: for an integer
of $`w > 0` bits in units of $`u > 0` bits, and for a pointer type that
takes $`k > 0` units, whose pointer keeps its provenance.
:::
