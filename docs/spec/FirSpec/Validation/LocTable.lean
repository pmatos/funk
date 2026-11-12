import VersoManual
import Fir.Validation.LocTable
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the location table's rule, which
renders `Fir.Validation.LocTable` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The location table's rule: readable blocks" =>

:::moduleDocs (fingerprint := "9577522543187242690")
:::

:::readable Fir.Location.WellFormed Fir.LocTable.Valid (pin := Fir.LocTable.InLimits) (pin := Fir.Location.numbers) (pin := Fir.Location.limit) (pin := Fir.Location.refs) (fingerprint := "11508244414306764901")
*Definition: a well-formed location and a valid location table.* A
{ref "The-fir-specification--Abstract-syntax--Locations"}[location] is
_well formed_ when:

* it is a source range $`\text{file}:l_1:c_1~\mathsf{to}~l_2:c_2` with
  $`1 \le l_1`, and either $`l_1 < l_2`, or $`l_1 = l_2` and
  $`c_1 = 0 \vee c_2 = 0 \vee c_1 \le c_2`;
* it is $`\mathsf{fused}(r^*)` with at least two references in $`r^*`;
* or it is of any other kind.

A column of 0 is unknown, so it places no condition, and an end equal to
the start is an empty range.

A location table $`(r_1 = \mathit{loc}_1) \dots (r_n = \mathit{loc}_n)` is
_valid_ when:

* its references increase, $`r_1 < r_2 < \dots < r_n`, so each is unique and
  one table has one spelling;
* the reference of every entry, every reference that its location is built
  from, and every line and column of a range are below $`2^{32}`, so every
  implementation can hold them in 32 bits;
* every entry is well formed;
* every reference $`r` that the location $`\mathit{loc}_k` is built from,
  by $`\mathsf{callsite}`, $`\mathsf{fused}` or $`\mathsf{derived}`, is
  below $`r_k` and is the reference of an entry of the table. Since the
  references increase, that entry comes before it, so no location refers
  to itself, directly or not.
:::
