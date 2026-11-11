import VersoManual
import Fir.Execution.StatePaths
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on how a run with memory ends, which
renders `Fir.Execution.StatePaths` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the build
fails when the Lean changes under it.
-/

#doc (Manual) "How a run with memory ends: readable blocks" =>

:::moduleDocs (fingerprint := "13135433263183756339")
:::

:::readable Fir.fromState (fingerprint := "6678452520667726865")
*Definition: a run from given memories.* A computation $`x` of the
interpreter in the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer], run
from the memories $`S` and read in the set monad, is
$`x \mathbin{@} S`: for each way $`x(S)` may end, $`\mathsf{ok}~(a, S')`
when it ends with the result $`a` and the memories $`S'`, the error when it
ends with one, whatever memories it reached, and $`\mathsf{ub}~r` when it
ends in UB.
:::

:::readable Fir.fromState_pure Fir.fromState_bind Fir.fromState_liftExcept Fir.fromState_lift Fir.fromState_inFrame (fingerprint := "7168398534361566954")
*Theorems: how each piece of a run ends, from given memories.*

* $`\mathrm{pure}(a) \mathbin{@} S = \mathrm{pure}(a, S)`.
* $`(x \mathbin{>\!\!>\!\!=} g) \mathbin{@} S = (x \mathbin{@} S) \mathbin{>\!\!>\!\!=} \lambda (a, S').\ g(a) \mathbin{@} S'`:
  the second computation runs from the memories that the first ended with.
* A check of the interpreter ends where it ends, and keeps $`S`.
* A computation $`c` of the layer, lifted, ends as $`c(S)` ends: an op's
  rule, from the memories the run has reached.
* A call's frame, $`\mathrm{frame}(x) \mathbin{@} S`, runs $`x` from
  $`\mathrm{enter}(S)` and leaves the frame on each path that ends with a
  result: its memories are $`\mathrm{exit}(S')`.

So each proof that follows a run in the set monad step by step has its
counterpart for a run with memory, each step from the memories that the
step before it ended with.
:::

:::readable Fir.Result.withState Fir.runFrom (fingerprint := "14228160234549358341")
*Definition: a run of ops from given memories.* A run of ops returns
values and the steps of fuel it leaves. Read from the memories $`S`, each
return $`\mathsf{ret}~(\vec{v}, k)` that ends with the memories $`S'`
becomes $`\mathsf{ret}~((\vec{v}, S'), k)`, and a path out of fuel shows no
memories.
:::

:::readable Fir.runFrom_bind Fir.runFrom_ret Fir.runFrom_exhausted Fir.runFrom_stuck (fingerprint := "11479725885105697702")
*Theorems: how a run of ops ends, from given memories.* A run of ops that
starts with a computation runs the rest from the memories that the
computation ended with. A return from $`S` returns with $`S`. A path out of
fuel is out of fuel, and a stuck path stuck, from any memories.
:::
