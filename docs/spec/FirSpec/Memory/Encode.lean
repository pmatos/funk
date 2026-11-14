import VersoManual
import Fir.Memory.Encode
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on values in units, which renders
`Fir.Memory.Encode` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Values in units: readable blocks" =>

:::moduleDocs (fingerprint := "18243812407679005324")
:::

:::readable Fir.ByteOrder.place (fingerprint := "1492561779768503232")
*Definition: placing units in a byte order.* A value's units are given
least significant first, $`\vec{x} = x_0 \ldots x_{k-1}`. The byte order
places them in memory:

$$`\mathrm{place}_{\mathsf{little}}(\vec{x}) = x_0 \ldots x_{k-1} \qquad \mathrm{place}_{\mathsf{big}}(\vec{x}) = x_{k-1} \ldots x_0`

Placing twice gives the units back, so decoding places them again.
:::

:::readable Fir.Memory.unitsFor Fir.MemLayout.bitsUnits_eq (pin := Fir.MemLayout.bitsUnits) (fingerprint := "8977425149999056970")
*Definition: how many units.* A value of $`w` bits takes
$`\lceil w / u \rceil` units of $`u` bits, computed as
$`\lfloor (w + u - 1) / u \rfloor`. It is the number of units that a
{ref "The-fir-specification--Abstract-syntax--Data-layouts"}[layout entry]
gives a value of $`w` bits, when $`u` is the entry's unit width.
:::

:::readable Fir.Memory.digits (fingerprint := "13858458388547642635")
*Definition: the digits of a number.* The $`k` digits of $`n` in base
$`2^u`, least significant first, are the units of bits

$$`\mathrm{digits}_k(n) = \mathsf{bits}~(n \bmod 2^u) ~ \mathrm{digits}_{k-1}(\lfloor n / 2^u \rfloor)`

with $`\mathrm{digits}_0(n) = \epsilon`. Digits past the most significant
one of $`n` are zero.
:::

:::readable Fir.Memory.unitsValue (fingerprint := "5468123204198996431")
*Definition: the number that units stand for.* Units of bits
$`\mathsf{bits}~b_0 \ldots \mathsf{bits}~b_{k-1}`, least significant first,
stand for $`\sum_i b_i \cdot 2^{u \cdot i}`. Units of which one is poison or
a pointer's fragment stand for no number.
:::

:::readable Fir.Memory.encodeInt (fingerprint := "1059651628212394042")
*Definition: an integer in units.* A value of $`\mathsf{i}N`, $`N = w`, in
units of $`u` bits placed in the byte order $`o`:

$$`\mathrm{enc}_o(b) = \mathrm{place}_o(\mathrm{digits}_{\lceil w/u \rceil}(b)) \qquad \mathrm{enc}_o(\mathsf{poison}) = \mathsf{poison}^{\lceil w/u \rceil}`

When $`w` is not a multiple of $`u`, the last digit holds bits past
$`w`, and they are zero (ADR-2026-11-12-2125; the human ruled it on
2026-11-11, on #231).
:::

:::readable Fir.Memory.decodeInt (fingerprint := "10745986782045874699")
*Definition: units as an integer.* Units $`\vec{x}` decode in the byte
order $`o` as a value of $`\mathsf{i}N`, $`N = w`, to

$$`\mathrm{dec}_o(\vec{x}) = n \bmod 2^w \quad \text{when } |\vec{x}| = \lceil w/u \rceil \text{ and } \mathrm{place}_o(\vec{x}) \text{ stands for } n`

and to $`\mathsf{poison}` otherwise. Cutting $`n` to its low $`w` bits
ignores the bits past $`w`, whatever they hold: an $`\mathsf{i}1` decoded
from the byte 0xFF is 1. A unit that is poison makes the value poison, and
so does a pointer's fragment: a punned load gives poison (the human's
ruling of 2026-11-11 on #231; ADR-2026-11-12-2125).
:::

:::readable Fir.Memory.fragments (fingerprint := "6762547574621767447")
*Definition: a pointer's fragments.* The $`k` fragments of the pointer
$`p` of the memory $`m`, least significant first, are
$`\mathsf{frag}~m~p~0 \ldots \mathsf{frag}~m~p~(k-1)`.
:::

:::readable Fir.Memory.encodePtr (fingerprint := "5372565945392989224")
*Definition: a pointer in units.* A value of the pointer type of the
memory $`m`, which takes $`k` units, placed in the byte order $`o`:

$$`\mathrm{enc}_o(p) = \mathrm{place}_o(\mathsf{frag}~m~p~0 \ldots \mathsf{frag}~m~p~(k-1)) \qquad \mathrm{enc}_o(\mathsf{poison}) = \mathsf{poison}^{k}`

Each unit holds a fragment of the pointer and its memory, so a pointer
copied unit by unit keeps its provenance (ADR-2026-11-09-1542).
:::

:::readable Fir.Memory.decodePtr (fingerprint := "2491161686553248570")
*Definition: units as a pointer.* Units $`\vec{x}` decode in the byte order
$`o` as a value of the pointer type of the memory $`m`, which takes $`k`
units, to $`p` when $`\mathrm{place}_o(\vec{x})` is the $`k` fragments of
$`p` of $`m`, in order, and to $`\mathsf{poison}` otherwise: units of
bits, poison, fragments of two pointers, fragments out of order and a
pointer of another memory are not a pointer of $`m`. In one memory a
pointer of $`m` always takes the same $`k` units, so its first units alone
are not one either.
:::
