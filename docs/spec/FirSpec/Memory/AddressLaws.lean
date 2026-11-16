import VersoManual
import Fir.Memory.AddressLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on address laws, which renders
`Fir.Memory.AddressLaws` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Address laws: readable blocks" =>

:::moduleDocs (fingerprint := "7400518912516959941")
:::

:::readable Fir.Memory.le_alignUp Fir.Memory.dvd_alignUp Fir.Memory.alignUp_eq (pin := Fir.Memory.alignUp) (fingerprint := "16294352692073450699")
*Theorems: aligning up.* $`c \le \lceil c \rceil_\alpha`, and for
$`\alpha > 0`, $`\alpha \mid \lceil c \rceil_\alpha`. A multiple $`x` of
$`\alpha > 0` with $`c \le x < c + \alpha` is $`\lceil c \rceil_\alpha`.
:::

:::readable Fir.Memory.roomFrom_eq_true Fir.Memory.Memory.fits_eq_true (pin := Fir.Memory.roomFrom) (pin := Fir.Memory.Memory.fits) (fingerprint := "5659000250134405349")
*Theorems: when an address fits.* The blocks leave room exactly when each
block but the allocation $`a` does. So $`x` fits $`a` in $`M` exactly
when $`M[a] = b` for some block $`b` of alignment $`\alpha` and size $`n`,
$`0 < x`, $`\alpha \mid x`, $`x + n < 2^P`, and every block $`M[j]`,
$`j \ne a`, leaves room for $`n` units from $`x`.
:::

:::readable Fir.Memory.Memory.fits_candidate (fingerprint := "11024852079216861317")
*Theorem: the candidates.* Let $`M[a]` be aligned to $`\alpha`. If some
address fits $`a`, then one of these fits it: $`\lceil 1 \rceil_\alpha`,
or $`\lceil y + n \rceil_\alpha` for a live block of $`M` at $`y` of size
$`n`. The proof takes a fitting $`x` and shows that $`x - \alpha` fits too
unless $`x` is one of them: when $`x - \alpha` does not fit, a live block
with an address overlaps it but not $`x`, so it ends between
$`x - \alpha` and $`x`, and $`x` is its end aligned up.
:::

:::readable Fir.Memory.fitAfter_fits Fir.Memory.fitAfter_isSome (pin := Fir.Memory.fitAfter) (fingerprint := "15471377055947891025")
*Theorems: an address just after a block.* An address that
$`\mathrm{after}_M(a)` gives fits $`a`. It gives one whenever the end of a
live block with an address, aligned up, fits $`a`.
:::

:::readable Fir.Memory.Memory.canonical_fits Fir.Memory.Memory.canonical_isSome Fir.Memory.Memory.exists_fits_iff (pin := Fir.Memory.Memory.canonical) (fingerprint := "14079776057487670775")
*Theorems: the canonical layout is an assignment that the spec allows.*
An address that the canonical layout gives $`a` fits $`a`, and it gives
one whenever an address fits $`a`. So some address fits $`a` exactly
when the canonical layout gives one, and it fits:

$$`(\exists x.\ \mathrm{fits}^P_M(a, x)) \iff \exists x.\ \mathrm{canon}^P_M(a) = x \land \mathrm{fits}^P_M(a, x)`

`fir-ref`, which runs the canonical layout, makes one of the choices that
the spec allows, and fails to give an address only where none fits.
:::
