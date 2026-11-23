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

:::moduleDocs (fingerprint := "17310946611801040318")
:::

:::readable Fir.Func.InModule (fingerprint := "13287016285892771373")
*Definition: a function that runs within a module.* The ops of a function
$`f` _run within the module $`M`_ when, for every op $`o` of every block
of $`f`:

* if $`o` is not a terminator and calls the symbol $`s`,
  $`\mathrm{callee}(o) = s`, then the
  {ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
  of $`M` gives $`s` the type of the call:
  $`\mathrm{symtab}_M(s) = (\mathrm{sig}(o) \to \mathrm{ret}(o))`;
* if $`o` is not a terminator and its callee is picked, every symbol $`s`
  that $`\mathrm{pick}_o` may give, on any operands, is one the run can
  call: the module has a function, or an external declaration, with the
  symbol $`s` that takes the operands of $`o` but the first and gives its
  results;
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

:::readable Fir.Func.Local.inModule (pin := Fir.Func.Local) (fingerprint := "13658034343483084644")
*Theorem: a function that runs within itself runs within every module.*
For every module $`M`, a function that runs within itself runs within
$`M`: it calls no function, so the rules for calls hold of none of its
ops, and its terminators keep to the same two rules.
:::

:::readable Fir.Module.calls_noStuck (pin := Fir.NoStuck) (fingerprint := "12364694741275216170")
*Theorem: in a module whose functions are all valid and run within it,
the run from any op of any of its functions has no stuck path.* Let every
function of the module $`M` be valid in a module context $`C` and run
within $`M`. Take any budget $`n`, function $`f` of $`M`, block $`b` of
$`\mathrm{blocks}(f)`, index $`i` less than the number of ops of $`b`,
and environment $`E` that
{ref "The-fir-specification--Execution--Scope-along-a-run"}[holds every value in scope]
at the op at index $`i` of $`b`. Let $`o^*` be the ops of $`b` from index
$`i` on. Then $`\mathrm{run}_M(n, f, E, o^*)` has no stuck path: it may
not end stuck.

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
callee leaves, fewer again. An op whose callee is picked first runs its
rule, which ends with UB or a symbol the run can call; with no step left,
the path runs out of fuel there, and otherwise the call goes on as a call
of that symbol. A callee that ends with UB or out of fuel ends its caller
so, and that is not stuck.
:::

:::readable Fir.Func.neverStuck_of_inModule (pin := Fir.NeverStuck) (fingerprint := "9953210940248431412")
*Theorem: every function of a module whose functions are all valid and
run within it has no stuck path, calls and recursion included.* Let every
function of the module $`M` be valid in a module context $`C` and run
within $`M`. For every function $`f` of $`M` and every vector $`v^*` of
values of its parameter types, $`\mathrm{runs}_M(f)(v^*)` has
{ref "The-fir-specification--Execution--Fuel-and-progress"}[no stuck path]:
at every budget $`n`, no path of $`\mathrm{runs}_M(f)(v^*)_n` is stuck.

Here $`\mathrm{runs}_M(f)(v^*)_n` is the
{ref "The-fir-specification--Execution--The-runs-of-a-function___-and-fuel-monotonicity"}[run of f]
on $`v^*` with $`n` steps of fuel. A run may call any function of $`M`,
itself included, as deep as its fuel allows.
:::
