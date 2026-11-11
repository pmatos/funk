import VersoManual
import Fir.Execution.Calls
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on progress with calls, which renders
`Fir.Execution.Calls` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Progress with calls: readable blocks" =>

:::moduleDocs (fingerprint := "6437237094318477812")
:::

:::readable Fir.Func.InModule (fingerprint := "12828239508909637856")
*Definition: a function that runs within a module.* The ops of a function
$`f` _run within the module $`M`_ when, for every op $`o` of every block
of $`f`:

* if $`o` is not a terminator and calls the symbol $`s`,
  $`\mathrm{callee}(o) = s`, then the
  {ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
  of $`M` gives $`s` the type of the call:
  $`\mathrm{symtab}_M(s) = (\mathrm{sig}(o) \to \mathrm{ret}(o))`;
* if $`o` is a terminator, whenever $`\mathrm{exit}_o` may end with
  $`\mathsf{goto}~i`, on any operands, $`i < \mathrm{nsucc}(o)`, and $`o`
  has no result types;
* if $`o` is a terminator, whenever $`\mathrm{exit}_o` may end with
  $`\mathsf{ret}`, on any operands, its operand types are the result types
  of $`f`.

$`\mathrm{sig}(o)` and $`\mathrm{ret}(o)` are the operand and result types
of the op instance of $`o`, $`\mathrm{nsucc}(o)` its number of successors,
and $`\mathrm{callee}(o)` and $`\mathrm{exit}_o`, run in the set monad,
what the dialect
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[says of the op].
The two rules for terminators are those of a function that
{ref "The-fir-specification--Execution--Progress-with-jumps-and-loops"}[runs within itself].
The first is what a call needs: its callee is a function of the module,
which takes the call's operands and gives its results. A dialect's own
validation rule for a call must ask it, as the
{ref "The-fir-specification--Validation--Core-rules"}[core rule] for
$`\mathsf{call}` does. Here, as in every block of this section, the
dialect is one that the interpreter can run in the set monad, as for
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[the runs of a function].
:::

:::readable Fir.Func.Local.inModule (pin := Fir.Func.Local) (fingerprint := "1227078464402482988")
*Theorem: a function that runs within itself runs within every module.*
For every module $`M`, a function that runs within itself runs within
$`M`: it calls no function, so the rule for calls holds of none of its
ops, and its terminators keep to the same two rules.
:::

:::readable Fir.Module.calls_noStuck Fir.Module.calls_hasPath (pin := Fir.NoStuck) (pin := Fir.HasPath) (fingerprint := "6646656366771854317")
*Theorem: in a module whose functions are all valid and run within it,
the run from any op of any of its functions has no stuck path, and has a
path when every op that runs by its own rule is total.* Let every
function of the module $`M` be valid in a module context $`C` and run
within $`M`. Take any budget $`n`, function $`f` of $`M`, block $`b` of
$`\mathrm{blocks}(f)`, index $`i` less than the number of ops of $`b`,
and environment $`E` that
{ref "The-fir-specification--Execution--Scope-along-a-run"}[holds every value in scope]
at the op at index $`i` of $`b`. Let $`o^*` be the ops of $`b` from index
$`i` on. Then:

* $`\mathrm{run}_M(n, f, E, o^*)` has no stuck path: it may not end stuck;
* if every op of every block of every function of $`M` that is a
  terminator or calls no function is
  {ref "The-fir-specification--Execution--Poison-classes"}[total], it has a
  path: it may end in some way.

Here $`\mathrm{run}_M(n, f, E, o^*)` is the
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]'s
run of the ops $`o^*` of $`f`, in the set monad, in the environment
$`E`, with $`n` steps of fuel; a call runs its callee, a function of
$`M`, with the steps the caller has left.

The proof is by induction on $`n`, for every function of $`M` at once,
calls, recursion and mutual recursion included. A call is the one step
that the section on jumps does not take, and the section on
{ref "The-fir-specification--Execution--What-a-call-step-needs"}[what a call step needs]
gives its parts: the callee is found and starts, holding every value in
scope; it runs with fewer steps than the caller had, so the induction
covers it, however deep the calls go; it returns values of the call's
result types, which bind; and the caller goes on with the steps the
callee leaves, fewer again. An op with a callee needs no rule of its
own: its way to go on is its callee's run (ADR-2026-11-02-1514). A callee
that ends with UB or out of fuel ends its caller so, and that is a way
to end.
:::

:::readable Fir.Func.neverStuck_of_inModule Fir.Func.progress_of_inModule (pin := Fir.NeverStuck) (pin := Fir.Progress) (fingerprint := "6046331798023887031")
*Theorem: every function of a module whose functions are all valid and
run within it has no stuck path, and has progress when every op that runs
by its own rule is total, calls and recursion included.* Let every
function of the module $`M` be valid in a module context $`C` and run
within $`M`. For every function $`f` of $`M` and every vector $`v^*` of
values of its parameter types, let $`R = \mathrm{runs}_M(f)(v^*)`:

* $`R` has
  {ref "The-fir-specification--Execution--Fuel-and-progress"}[no stuck path]:
  at every budget $`n`, no path of $`R_n` is stuck;
* if every op of every block of every function of $`M` that is a
  terminator or calls no function is total, $`R` has
  {ref "The-fir-specification--Execution--Fuel-and-progress"}[progress]: at
  every budget $`n`, $`R_n` has some outcome.

Here $`\mathrm{runs}_M(f)(v^*)_n` is the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[run of f]
on $`v^*` with $`n` steps of fuel. A run may call any function of $`M`,
itself included, as deep as its fuel allows. Every function of every
valid core module meets the hypotheses, as the section on
{ref "The-fir-specification--Execution--Core-functions-with-calls"}[core functions with calls]
shows.
:::
