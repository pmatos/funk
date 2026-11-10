import VersoManual
import Fir.Sum.Inclusion
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on inclusions of types, which renders
`Fir.Sum.Inclusion` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "Inclusions of types: readable blocks" =>

:::moduleDocs (fingerprint := "15351923873579278708")
:::

:::readable Fir.TyIncl (fingerprint := "13161707640643539970")
*Definition: an inclusion of types.* An inclusion $`\iota` of the types
$`A` in the types $`B` has:

* a map of types $`\iota : A \to B`, and its projection
  $`\iota^{-1} : B \to A^?`, the type of $`A` that a type of $`B` is, if
  any;
* for each type $`a` of $`A`, a map of values
  $`\uparrow_\iota : [\![a]\!] \to [\![\iota(a)]\!]` and a map back
  $`\downarrow_\iota`.

Each undoes the other: $`\iota^{-1}(\iota(a)) = a`, a type that projects
to $`a` is $`\iota(a)`, $`\downarrow_\iota \uparrow_\iota x = x` and
$`\uparrow_\iota \downarrow_\iota x = x`.
:::

:::readable Fir.TyIncl.inl Fir.TyIncl.over Fir.TyIncl.comp (fingerprint := "13749068548928120790")
*Definition: three inclusions.*

* The types $`A` are included in $`A \uplus B` by $`\mathsf{inl}`, with
  $`\iota^{-1}(\mathsf{inl}\ a) = a` and no type of $`B` projecting. A value
  does not change. This is how the base of a sum is held.
* An inclusion $`\iota` of $`A` in $`B` gives one of $`A \uplus C` in
  $`B \uplus C`: $`\mathsf{inl}\ a \mapsto \mathsf{inl}\ \iota(a)` and
  $`\mathsf{inr}\ c \mapsto \mathsf{inr}\ c`. So the types of an extension
  over a base are included in those of the same extension over a larger
  base.
* Two inclusions compose: $`\kappa \circ \iota` maps types and values by
  $`\iota` then $`\kappa`, and projects by $`\kappa^{-1}` then
  $`\iota^{-1}`.

So the core is included in $`\mathrm{core} \boxplus a \boxplus b` by
$`\mathsf{inl} \circ \mathsf{inl}`.
:::

:::readable Fir.HVector.up Fir.HVector.down Fir.HVector.down_up Fir.HVector.up_down (fingerprint := "16789294650419697781")
*Definition: vectors across an inclusion.* $`\uparrow_\iota` moves a vector
of values of the types $`a^*` to the types $`\iota(a)^*`, position by
position, and $`\downarrow_\iota` moves it back. Each undoes the other.
:::

:::readable Fir.TyIncl.mapM_proj_map Fir.TyIncl.eq_map_of_mapM_proj (fingerprint := "6219706594578128904")
*Lemmas: lists of types across an inclusion.* Projecting the list
$`\iota(a)^*` gives $`a^*`, and a list of types of $`B` whose projection is
$`a^*` is $`\iota(a)^*`.
:::

:::readable Fir.TyIncl.Lawful (fingerprint := "18099840548668709562")
*Definition: a lawful inclusion.* An inclusion is lawful when crossing it
keeps which values are poison and which values refine others: for values
$`x, y` of a type of $`A`, $`\uparrow_\iota x` is poison exactly when $`x`
is, and $`\uparrow_\iota x \sqsubseteq \uparrow_\iota y` exactly when
$`x \sqsubseteq y`.
:::

:::readable Fir.TyIncl.lawful_inl Fir.TyIncl.Lawful.over Fir.TyIncl.Lawful.comp (fingerprint := "3718467128589929888")
*Lemmas: the three inclusions are lawful.* $`\mathsf{inl}` is lawful, since
a summed type's values are its side's. An inclusion over a lawful one is
lawful, and two lawful inclusions compose to a lawful one.
:::
