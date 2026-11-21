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

:::moduleDocs (fingerprint := "13213713090563566759")
:::

:::readable Fir.Memory.le_alignUp Fir.Memory.dvd_alignUp Fir.Memory.alignUp_eq (pin := Fir.Memory.alignUp) (fingerprint := "16294352692073450699")
*Theorems: aligning up.* $`c \le \lceil c \rceil_\alpha`, and for
$`\alpha > 0`, $`\alpha \mid \lceil c \rceil_\alpha`. A multiple $`z` of
$`\alpha > 0` with $`c \le z < c + \alpha` is $`\lceil c \rceil_\alpha`.
:::

:::readable Fir.Memory.roomFrom_eq_true Fir.Memory.Memory.fits_eq_true (pin := Fir.Memory.roomFrom) (pin := Fir.Memory.Memory.fits) (fingerprint := "17166369630723595643")
*Theorems: when an address fits.* The blocks leave room exactly when each
block but the allocation $`a` does. So $`z` fits $`a` in $`M` exactly
when $`M[a] = b` for some block $`b` of alignment $`\alpha` and size $`n`,
$`lo \le z`, $`\alpha \mid z`, $`z + n \le hi`, and every block $`M[j]`,
$`j \ne a`, leaves room for $`n` units from $`z`.
:::

:::readable Fir.Memory.Memory.fits_candidate (fingerprint := "5584864563810579598")
*Theorem: the candidates.* Let $`M[a]` be aligned to $`\alpha`, and let
$`z` fit $`a`. Then $`z` is a candidate, $`\lceil lo \rceil_\alpha` or
$`\lceil y + n \rceil_\alpha` for a live block of $`M` at $`y` of size
$`n`, or a lower address fits $`a`. When $`z` is neither
$`\lceil lo \rceil_\alpha` nor has $`z - \alpha` fitting, a live block
with an address overlaps $`z - \alpha` but not $`z`, so it ends between
$`z - \alpha` and $`z`, and $`z` is its end aligned up.
:::

:::readable Fir.Memory.merge_min_le Fir.Memory.lowestFrom_fits Fir.Memory.lowestFrom_le_best Fir.Memory.lowestFrom_le_after (pin := Fir.Memory.lowestFrom) (fingerprint := "2681823001635160878")
*Theorems: the lowest candidate.* Keeping the lower of two addresses gives
one at most each. The walk gives an address that fits when the one it
starts from does, at most the one it starts from, and at most
$`\lceil y + n \rceil_\alpha` for each live block of its blocks at $`y`,
of size $`n`, for which that address fits.
:::

:::readable Fir.Memory.Memory.lowestFit_fits Fir.Memory.Memory.lowestFit_le (pin := Fir.Memory.Memory.lowestFit) (fingerprint := "16752950028399501019")
*Theorems: the lowest fit.* The address $`\mathrm{lowest}_M(a)` fits
$`a`, and for each $`z` that fits $`a` it gives an address at most $`z`.
The proof is by strong induction on $`z`: a candidate is at least the
lowest candidate, and otherwise a lower address fits.
:::

:::readable Fir.Memory.Memory.canonical_fits Fir.Memory.Memory.canonical_lowest Fir.Memory.Memory.canonical_isSome Fir.Memory.Memory.exists_fits_iff (pin := Fir.Memory.Memory.canonical) (fingerprint := "6191640778866544330")
*Theorems: the canonical layout is an assignment that the spec allows.*
An address that the canonical layout gives $`a` fits $`a`. When the
canonical address does not fit, the address it gives is at most every
address that fits: the lowest. It gives one whenever an address fits
$`a`. So some address fits $`a` exactly when the canonical layout gives
one, and it fits:

$$`(\exists z.\ \mathrm{fits}_M(a, z)) \iff \exists z.\ \mathrm{canon}_M(a) = z \land \mathrm{fits}_M(a, z)`

`fir-ref`, which runs the canonical layout, makes one of the choices that
the spec allows, and fails to give an address only where none fits.
:::
