import VersoManual
import Fir.Sum.TextLaws
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the text of a sum, which renders
`Fir.Sum.TextLaws` (ADR-2026-11-05-2012). Each block explains declarations
of that module and pins their fingerprint; the build fails when the Lean
changes under it.
-/

#doc (Manual) "The text of a sum: readable blocks" =>

:::moduleDocs (fingerprint := "12504048324821814013")
:::

:::readable Fir.Dialect.sum.mapM_getLeft_map Fir.Dialect.sum.eq_map_of_mapM_getLeft (fingerprint := "10425250833271113799")
*Lemmas: the base's types in the sum's.* A list of the sum's types reads
back as a list of the base's types $`t^*` exactly when it is
$`(\mathsf{inl}\ t)^*`.
:::

:::readable Fir.Dialect.sum.decodeOp_ext Fir.Dialect.sum.decodeOp_base Fir.Dialect.sum.decodeTy_ext Fir.Dialect.sum.decodeTy_base (fingerprint := "14936538594500116695")
*Lemmas: where a word goes.* These restate the reader of the sum one case
at a time: a word of $`e`'s name goes to $`e`, and every other word to the
base.
:::

:::readable Fir.Dialect.sum.Routes (fingerprint := "2367031496180498621")
*Definition: every word goes to its own side.* The words of the base and of
$`e` _route_ when:

* no op name of the base names $`e`, and every op name of $`e` does;
* no valid type of the base names $`e`, and every valid own type of $`e`
  does.
:::

:::readable Fir.Dialect.sum.routes_of_lawful Fir.Dialect.sum.lawful Fir.Dialect.sum.lawful_iff Fir.Dialect.sum.names_disjoint (fingerprint := "1993604389849265224")
*Theorem: when the text of a sum is lawful.* Let the base and $`e` over
the base have
{ref "The-fir-specification--Text-format--Grammar"}[lawful text]. The text
of $`b \boxplus e` is lawful exactly when their words route.

If the words route, each op and each type is read back by the side that
wrote it, which reads it back by its own laws; and every op and type that
the sum reads, it reads on one side, whose laws say how it is written. If
the sum's text is lawful, reading back each word reaches the side that
wrote it, and the reader decides that side by the word alone, so the words
route. So a lawful sum has no op name on both of its sides.
:::

:::readable Fir.LawfulDialectName (fingerprint := "3078469256500740612")
*Definition: an extension that writes its words under its name.* The
extension $`e` over the base $`b` writes its words under its name $`n_e`
when, for every op $`q` of $`e` and every valid own type $`t` of $`e`:

* $`\mathrm{dialect}(\mathrm{opname}(q)) = n_e`, and every dialect of the
  words of $`q`'s attributes is in $`\mathrm{names}(b) \cdot n_e`;
* $`\mathrm{dialect}(\mathrm{head}(\mathrm{tyattr}(\mathsf{inr}\ t))) = n_e`,
  and every dialect of its words is in $`\mathrm{names}(b) \cdot n_e`;
* $`\mathrm{dialect}(k) = n_e` for every region kind $`k` that $`e`
  registers.

The extension may name the base's dialects in its attributes and types,
as a type of $`e` may take a core type as an argument.
:::

:::readable Fir.Dialect.sum.routes_of_names Fir.Dialect.sum.lawfulSet (fingerprint := "8881950472776581581")
*Theorems: names route every word.* If the base's
{ref "The-fir-specification--Sums-of-dialects--Words-and-dialect-sets"}[words stay in its set],
$`e` writes its words under its name, and $`n_e \notin \mathrm{names}(b)`,
then the words of the base and of $`e` route. The words of the sum then
stay in its set, $`\mathrm{names}(b) \cdot n_e`.

So a sum built on the core, one dialect at a time, each of a name not yet
in the sum, has lawful text at every step. The second is an instance, so a
nested sum finds the law for each level by itself.
:::

:::readable Fir.Dialect.sum.validRegion_ext (pin := Fir.Dialect.sum.ValidRegion) (fingerprint := "5882056062111048233")
*Theorem: a kind of the extension goes to the extension's rule.* Let the
base's words stay in its set, $`e` write its words under its name, and
$`n_e \notin \mathrm{names}(b)`. Then the base registers no kind that $`e`
registers, so for every such kind $`k`, a region obeys the rule of $`k` in
the sum exactly when it obeys $`e`'s rule for $`k`, through $`e`'s view.
:::

:::readable Fir.Dialect.sum.lawful_of_names Fir.Dialect.sum.validIsWellFormed Fir.Dialect.sum.printThenParse Fir.Dialect.sum.parse_wellFormed (fingerprint := "16980967360285776458")
*Theorems: the round trip over sums.* Let the base's words stay in its set,
$`e` write its words under its name, and $`n_e \notin \mathrm{names}(b)`.
Then $`b \boxplus e` has lawful text, and:

* every valid module is
  {ref "The-fir-specification--Text-format--Round-trips"}[well formed];
* $`\mathrm{parse}(\mathrm{print}(m)) = m` for every well-formed module $`m`;
* every module that the parser gives is well formed.

Each is the general theorem for a dialect with lawful text, applied to the
sum. They need no assumption beyond the names.
:::
