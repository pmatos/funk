import VersoManual
import Fir.Validation.Tables
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on tables, which renders
`Fir.Validation.Tables` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Tables: readable blocks" =>

:::readable Fir.firsts Fir.getElem?_foldl_insertIfNew Fir.getElem?_firsts (fingerprint := "9794351328742573981")
*Definition and theorems: the first value of each key.* For a list $`l` of
pairs $`(k, v)` of a key and a value, $`\mathrm{firsts}(l)` is the hash
table that gives each key the value of its first pair in $`l`. It inserts
the pairs in order, and an insertion keeps a key's value when the table
already has one. Below, $`h[k]` is the value that the hash table $`h` gives
the key $`k`, and is undefined when $`k` is not a key of $`h`.

*Theorem:* for every list $`l` and key $`k`, $`\mathrm{firsts}(l)[k]` is
the value of the first pair of $`l` whose key is $`k`, and is undefined
when no pair has the key $`k`. That is the answer a search of $`l` from its
start gives, so the check can look a value's type up in constant time and
still agree with the rules, which speak of the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[first definition].

The proof goes through a more general theorem: inserting the pairs of $`l`
in this way into any table $`m` gives a table whose value at $`k` is
$`m[k]` when $`m` has the key $`k`, and otherwise the value of the first
pair of $`l` with the key $`k`, or none.
:::

:::readable Fir.grouped Fir.mem_getD_foldl_grouped Fir.contains_foldl_grouped Fir.mem_getD_grouped Fir.contains_grouped (fingerprint := "17977077737012576329")
*Definition and theorems: every value of each key.* For a list $`l` of
pairs $`(k, \mathit{vs})` of a key and a list of values,
$`\mathrm{grouped}(l)` is the hash table that gives each key all the values
of all its pairs. Below, $`h[k]^*` is the list that the table $`h` gives
the key $`k`, or the empty list when $`k` is not a key of $`h`.

*Theorems:* for every list $`l`, key $`k` and value $`v`,

* $`v` is in $`\mathrm{grouped}(l)[k]^*` exactly when some pair
  $`(k, \mathit{vs})` of $`l` has $`v` in $`\mathit{vs}`;
* $`k` is a key of $`\mathrm{grouped}(l)` exactly when some pair of $`l`
  has the key $`k`.

The check builds a function's
{ref "The-fir-specification--Validation--Reachability-and-dominance___-decided"}[graph]
and the sites where each value is defined with it, so a label that names
several blocks, or a value defined several times, keeps every one of them.
The proofs go through the same two statements for the pairs of $`l`
inserted into any starting table $`m`, where the values and keys of $`m`
count too.
:::

:::readable Fir.repeatsFrom Fir.repeats Fir.repeatsFrom_eq_nil Fir.repeats_eq_nil (fingerprint := "7311244009632777064")
*Definition and theorems: the elements that repeat.*
$`\mathrm{repeats}(l)` is the elements of the list $`l` that equal an
earlier element of $`l`, in order, once for each time they repeat. It walks
$`l` once, keeping the elements it has seen in a hash set.

*Theorem:* for every list $`l`, $`\mathrm{repeats}(l)` is empty exactly
when the elements of $`l` are distinct.

The check reports each repeated label and each value defined twice from
this list, and the theorem says that it reports none exactly when the
rules' "distinct" holds. The proof goes through the loop itself: started
with a set $`S` of elements already seen and a list $`a` of repeats already
found, it ends with no repeats exactly when $`a` is empty, no element of
$`l` is in $`S`, and the elements of $`l` are distinct.
:::

:::readable Fir.sameLists Fir.sameLists_iff (fingerprint := "2136587650984284499")
*Definition and theorem: comparing two lists.* $`\mathrm{same}(l_1, l_2)`
compares two lists element by element, in a loop, and is true when they
have the same length and equal elements at every position.

*Theorem:* for every two lists $`l_1` and $`l_2` whose elements can be
compared, $`\mathrm{same}(l_1, l_2)` is true exactly when $`l_1 = l_2`.

The check compares the types of an op's operands with those of its op
instance this way, so that it takes no stack per element of a long list.
:::
