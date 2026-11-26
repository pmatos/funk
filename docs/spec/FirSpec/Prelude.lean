import VersoManual
import Fir.Prelude
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on equality of names and numbers, which
renders `Fir.Prelude`. Each block explains declarations of that module and
pins their fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "Equality of names and numbers: readable blocks" =>

:::moduleDocs (fingerprint := "17973866696639677096")
:::

:::readable Fir.instBEqString (fingerprint := "420965800421861921")
*Definition: equality of strings.* Two strings are equal, by $`==`, when
they are the same string. Fir decides this by the decidable equality of
strings, so the kernel can compute it.
:::

:::readable Fir.instLawfulBEqString Fir.instLawfulBEqNat (fingerprint := "13734988783423336100")
*Theorem: equality of strings and of numbers is lawful.* For strings and
for natural numbers, $`a == b` holds exactly when $`a = b`. Both facts come
from decidable equality, with no axiom of choice.
:::

:::readable Fir.instBEqBitVec Fir.instLawfulBEqBitVec (fingerprint := "10155005471649708801")
*Definition and theorem: equality of bit vectors.* Two bit vectors of the
same width are equal, by $`==`, when they have the same bits, and
$`a == b` holds exactly when $`a = b`. Fir decides this by the decidable
equality of bit vectors, so the kernel can compute it, with no axiom of
choice.
:::
