import VersoManual
import Fir.Validation.CheckModule
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on checking modules, which renders
`Fir.Validation.CheckModule` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Checking modules: readable blocks" =>

:::moduleDocs (fingerprint := "15112092378636218417")
:::

:::readable Fir.Location.malformed (pin := Fir.Location.WellFormed) (fingerprint := "313359748682067478")
*Definition: whether a location is well formed, and why not.* Whether a
location is
{ref "The-fir-specification--Validation--The-general-rules"}[well formed]
can be decided, kind by kind. When it is not, the problem says why: "a range
starts at line 1 or later" for a range that starts at line 0, "a range does
not end before it starts" for another range, and "a fused location fuses at
least two" for a $`\mathsf{fused}` location. Every other kind is well
formed, so its message, "the location is not well formed", is never given.
:::

:::readable Fir.locProblem Fir.LocTable.problems (fingerprint := "11296170998202653587")
*Definition: the check of a location table.* Each problem of the table
starts "location table: `@r`", for the reference $`r` of the entry it is
about. The check gives, in this order:

* "comes after `@a`: references are unique and in increasing order", for
  each reference $`r` whose predecessor $`a` is not below it;
* for each entry, in order: "holds a reference, line or column of 2^32 or
  more" when the entry is out of limits; "is not well formed", with the
  reason, when its location is not; and for each reference $`x` that its
  location is built from, unless $`x` is below $`r` and is the reference of
  an entry of the table, "refers to `@x`, which does not come before it"
  when the table holds $`x`, or "refers to `@x`, which the table does not
  hold" when it does not.

It looks references up in a hash set of the table's references, built once.
:::

:::readable Fir.pairwise_lt_iff_zip (fingerprint := "3088391998225526046")
*Theorem: a list of numbers increases when each one is below the next.* For
every list $`n_1 \dots n_k` of natural numbers, every element is below every
later one exactly when each element is below the next:

$$`\begin{aligned} & \forall i < j.\ n_i < n_j \\ \iff\ & \forall i < k.\ n_i < n_{i+1} \end{aligned}`

So the check compares each reference only with the next one, and still
decides the rule, which asks the references to increase.
:::

:::readable Fir.LocTable.problems_eq_nil (fingerprint := "12100878131095115224")
*Theorem: the check of a location table decides its validity.* For every
location table $`t`, the check of $`t` gives no problem exactly when $`t`
is a
{ref "The-fir-specification--Validation--The-general-rules"}[valid location table].
:::

:::readable Fir.Attr.writable Fir.Attr.allWritable Fir.Attr.writable_iff Fir.Attr.allWritable_iff Fir.instDecidableAllWritable (fingerprint := "9863646700279018290")
*Definition and theorems: whether attributes can be written.* Whether an
attribute can be
{ref "The-fir-specification--Abstract-syntax--Modules___-functions___-blocks-and-ops"}[written] is
decided term by term: a word when it is a word, an integer, a string or a
symbol always, and an applied attribute when its head is a word and each of
its arguments can be written. A list can be written when each of its
attributes can.

*Theorems:* the test of an attribute holds exactly when it can be written,
and the test of a list exactly when each of its attributes can be. So
whether a list of attributes can be written is decidable.
:::

:::readable Fir.DialectItem.problem Fir.DialectItem.kindProblems Fir.DialectItem.kindProblems_eq_nil_iff (fingerprint := "14805807463325893393")
*Definition and theorem: the problems of an item's kind.* A problem about
an item $`i` of a dialect's kind is placed at the symbol of $`i`. When no
dialect registers the kind $`k` of $`i`, the check gives "no dialect
registers the kind of item "$`k`"", and only that: a kind that no dialect
registers has no rule to break. When a dialect registers $`k` and $`i`
breaks its
{ref "The-fir-specification--Validation--Scope-and-symbols"}[rule], through
the identity view, the check gives "the item breaks the rule of its kind
"$`k`"".

*Theorem:* for every function context $`C` and item $`i`, these give no
problem exactly when $`k \in \mathrm{itemkinds}_d` and
$`C, \mathrm{id} \vdash_d i~\text{valid}`.
:::

:::readable Fir.DialectItem.problems Fir.DialectItem.problems_eq_nil_iff Fir.instDecidableDialectItemValid (pin := Fir.Text.quote) (fingerprint := "17337299590514458338")
*Definition and theorem: the check of an item of a dialect's kind.* The
check of the item $`i` of a dialect's kind, in the function context $`C`,
gives, in this order:

* "the kind "$`k`" is not a word of a dialect", when the kind $`k` of $`i`
  is not a word that holds a `.`;
* "the parameter `%`$`x` is not a name", for each parameter $`x` of $`i`
  that is not a name;
* "the item defines `%`$`x` more than once", for each parameter name that
  repeats one before it;
* "a type of the item is not valid", once, when a type that $`i` states is
  not valid;
* "an attribute of the item cannot be written", once, when one cannot;
* the problems of the kind of $`i`.

*Theorem:* for every function context $`C` and item $`i` of a dialect's
kind, the check gives no problem exactly when $`i` is
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in
$`C`. So whether it is valid is decidable.
:::

:::readable Fir.SymbolTable.lookup Fir.SymbolTable.lookup_agrees (fingerprint := "12308579040400648023")
*Definition and theorem: the lookup of a symbol table.* The
{ref "The-fir-specification--Validation--The-validation-check"}[lookup] of
the table $`T`, given a hash set of the references of the module's location
table, gives each symbol the type of the first function of $`T` with that
symbol, from a hash table built once, and has the references of the hash
set.

*Theorem:* for every table $`T` and every list of references $`K`, the
lookup of $`T` with a hash set of $`K` agrees with the context of $`T` in
$`K`, $`\mathrm{ctx}_K(T)`, that the rules use. So the theorems about the
check of a function apply to every function of $`T`, checked with the
lookup of $`T`.
:::

:::readable Fir.SymbolTable.problems (pin := Fir.Text.printSymbol) (pin := Fir.isWord) (fingerprint := "8597968925950264726")
*Definition: the check of a symbol table.* The check of the table $`T`,
given a hash set of the references of the module's location table, builds
the lookup of $`T` once, and gives, in this order:

* "the symbol `@s` names more than one item", placed at $`s`, for each
  symbol of an item of $`T`, of any kind, that repeats the
  symbol of an item before it;
* the
  {ref "The-fir-specification--Validation--Checking-functions"}[problems of each function]
  of $`T`, in order, checked with the lookup of $`T`;
* the problems of each item of a dialect's kind of $`T`, in order, checked
  in the function context of the symbols of $`T`;
* "the dialect set names $`x`, which is not a word", for each name $`x` of
  the dialect set of $`T` that is not a word;
* "the dialect set names $`x` more than once", for each name that repeats
  one before it.

A symbol in a message is spelled as the text writes it: bare when it is a
word, and quoted otherwise.
:::

:::readable Fir.SymbolTable.problems_eq_nil_iff (fingerprint := "7069496205811800726")
*Theorem: the check of a table decides its validity.* For every table
$`T` and every list of references $`K`, the check of $`T` with a hash set
of $`K` gives no problem exactly when $`T` is valid in $`K`.
:::

:::readable Fir.Module.problems (fingerprint := "12202654396669724762")
*Definition: the check of a module.* The check of the module $`M`,
$`\mathrm{problems}(M)`, builds a hash set of the references of its
location table once, and gives, in this order, the problems of the location
table, then the problems of each of its
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol tables],
its own first, each checked with that hash set, then the problems of its
{ref "The-fir-specification--Validation--Checking-the-data-layout"}[data layout],
then those of the memories that the types of each of its tables name.
:::

:::readable Fir.Module.problems_eq_nil_iff (fingerprint := "9852547177654724991")
*Theorem: the validation check decides validity.* For every dialect whose
types can be compared and whose own rules can be decided, and for every
module $`M` of that dialect, the check of $`M` gives no problem exactly
when $`M` is valid:

$$`\mathrm{problems}(M) = \epsilon \iff {} \vdash M~\text{valid}`

This is the theorem that the chapter builds up to. `fir-ref validate` runs
the check, so its verdict is the verdict of the rules on every module, and
the rules need no second, informal reading to be implemented.

So validity can be decided: whether a module is valid, by its check, and
whether a function is valid in a module context $`C`, by the check of the
function with a lookup made from $`C` itself.
:::
