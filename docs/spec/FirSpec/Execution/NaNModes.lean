import VersoManual
import Fir.Execution.NaNModes
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on exhaustive runs that try a few NaNs,
which renders `Fir.Execution.NaNModes` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "Exhaustive runs that try a few NaNs: readable blocks" =>

:::moduleDocs (fingerprint := "12466895454639907215")
:::

:::readable Fir.ChoiceTree.isNaNBits Fir.ChoiceTree.nanTries Fir.ChoiceTree.bitsFor Fir.ChoiceTree.tryAt (fingerprint := "15738451443851095608")
*Definition: the values that the walk tries at a choice.* A number $`n` is
the bits of a NaN of $`\mathsf{float}\langle e,m\rangle` when it has
$`1 + e + m` bits at most, every exponent bit set and a mantissa that is
not zero. At a NaN choice of $`w = m + 1` bits, given the numbers
$`\vec{n}`, the walk tries, each once and in this order:

* the positive quiet NaN, with only the top mantissa bit set: $`2^{m-1}`;
* for each $`n` of $`\vec{n}` that is the bits of a NaN of the format, its
  sign and mantissa: $`\lfloor n / 2^{e+m} \rfloor \cdot 2^m + (n \bmod 2^m)`.

It charges such a choice the fewest bits that count the values it tries,
$`\lfloor \log_2 (2k - 1) \rfloor` for $`k` values, so nothing for the
quiet NaN alone: with no numbers given, a run with any number of NaN choices
has one path through them. At a choice of the kind
$`\mathsf{bits}` it tries every one of the $`2^w` values and charges $`w`
bits, as exhaustive mode does.
:::

:::readable Fir.ChoiceTree.exploreNaN (fingerprint := "15436657046745643708")
*Definition: the walk that tries a few NaNs.* With the numbers
$`\vec{n}` and a budget of $`B` bits, the walk lists every leaf of a tree
that it reaches, each with the choices and the NaN choices on its path. A
leaf is listed with no choice. At a choice, it tries the values above and
walks the subtree of each with the budget less the bits it charges, adding
one choice to each leaf below, and one NaN choice when the choice is a
NaN's. When a choice charges more than the budget left, the walk gives
nothing, as exhaustive mode does past its budget.
:::

:::readable Fir.ChoiceTree.exploreNaN_sub (pin := Fir.ChoiceTree.Leaf.ev?) (fingerprint := "7931372983940954096")
*Theorem: the walk lists a part of the set.* Each leaf that the walk lists,
that has an outcome, is a way the tree may end: it is in the
{ref "The-fir-specification--Execution--Choice-trees"}[set of the tree]. Each
value the walk tries is a value of its choice, so each path it walks is a
path of the tree.
:::

:::readable Fir.ChoiceTree.collect_ne_nil Fir.ChoiceTree.nanTries_ne_nil Fir.ChoiceTree.tryAt_ne_nil Fir.ChoiceTree.exploreNaN_ne_nil (pin := Fir.ChoiceTree.collect) (fingerprint := "11230313631802834104")
*Theorem: the walk lists at least one leaf.* The walk tries at least one
value at every choice, the quiet NaN at a NaN choice and every value at
any other, so it lists at least one leaf of every tree.
:::

:::readable Fir.ChoiceTree.exploreNaN_toSet (pin := Fir.ChoiceTree.Leaf.ev?) (fingerprint := "16359155283225498577")
*Theorem: with no NaN choice, the walk lists the whole set.* When no leaf
that the walk lists made a NaN choice, it lists exactly the set of the
tree, as exhaustive mode does. A NaN choice on the way would have given
some leaf below it a NaN choice, since every subtree lists a leaf, so the
walk tried every value of every choice it met.
:::

:::readable Fir.Func.memExploreNaN_outcomes Fir.Func.memExploreNaN_stuck Fir.Func.memExploreNaN_exact (pin := Fir.Func.memTree) (pin := Fir.Run.outcomes) (pin := Fir.Run.IsStuck) (pin := Fir.ChoiceTree.Leaf.pathEnd) (fingerprint := "16347417481536343142")
*Theorems: the walk of a run with memory.* When the dialect's semantics in
the tree denotes its semantics with memory, each outcome that the walk
lists on the tree of a run with memory, and each stuck path, is one of the
run with memory at the fuel it runs with. When no path that it lists made a
NaN choice, it lists exactly the outcomes of the run.
:::
