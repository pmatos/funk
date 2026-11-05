import VersoManual
import Fir.Execution.CallSteps
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what a call step needs, which renders
`Fir.Execution.CallSteps` (ADR-2026-11-05-2012). Each block states a theorem
of that module in words, and in notation where it helps, and pins its
fingerprint; the build fails when the Lean changes under it.
-/

#doc (Manual) "What a call step needs: readable blocks" =>

:::readable Fir.HasPath.bind (pin := Fir.HasPath) (fingerprint := "12286075038897393730")
*Theorem: a sequence has a path when its parts have one.* A run may end in
more than one way, for example where $`\mathsf{freeze}` picks a value, so
a computation of a run stands for the set of the ways it can end: with a
result,
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[stuck], or
with {ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[UB].
A computation
{ref "The-fir-specification--Execution--Reading-a-run-path-by-path"}[has a path]
when that set is not empty: the run has some behaviour. The proof of
progress shows this for every step of a run.

Run $`x`, then run $`g` on the result of $`x`: this sequencing is written
$`x \mathbin{>\!\!>\!\!=} g`. If $`x` has a path, and $`g\,a` has a path
for every result $`a` that $`x` can end with, then
$`x \mathbin{>\!\!>\!\!=} g` has a path.

$$`x \text{ has a path} \;\wedge\; \bigl(\forall a.\ x \leadsto a \implies g\,a \text{ has a path}\bigr) \;\implies\; x \mathbin{>\!\!>\!\!=} g \text{ has a path}`

Here $`x \leadsto a` says that $`x` can end with the result $`a`. A path of
$`x` that ends stuck or with UB is already a path of the whole. For a call,
$`x` is the callee's run and $`g` what the caller does after it returns.
:::

:::readable Fir.Module.func?_of_symbols (pin := Fir.Module.symbols) (pin := Fir.Module.func?) (fingerprint := "17384737556842784812")
*Theorem: the callee is found.* Suppose the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[symbol table]
of a module $`M` gives the symbol $`s` the function type $`t^* \to r^*`.
Then $`M` has a function $`g` with symbol $`s`, and the search that a run
makes for $`s` finds it. $`g` is one of the functions of $`M`, its
parameters have the types $`t^*`, and its results the types $`r^*`.

$$`\begin{aligned} \mathrm{symtab}_M(s) = (t^* \to r^*) \implies \exists g.\ & \mathrm{lookup}_M(s) = g \,\wedge\, g \in \mathrm{funcs}(M) \\ & \wedge\, \mathrm{type}(g) = (t^* \to r^*) \end{aligned}`

Here $`\mathrm{symtab}_M(s)` is the type that the symbol table of $`M`
gives $`s`, $`\mathrm{lookup}_M(s)` the first function of $`M` whose
symbol is $`s`, which is the one a call of $`s` runs, $`\mathrm{funcs}(M)`
the functions of $`M`, and $`\mathrm{type}(g)` the types of the parameters
and results of $`g`.
:::

:::readable Fir.ReturnsTypes Fir.ReturnsTypes.bind Fir.ReturnsTypes.of_stuck Fir.ReturnsTypes.exhausted Fir.ReturnsTypes.ret (fingerprint := "15698882366344932232")
*Definition: returning values of given types.* A computation $`s` of a run
_returns values of the types_ $`t^*` when every path of $`s` that ends
with a return returns values whose types are $`t^*`. Paths that are stuck,
end with UB or
{ref "The-fir-specification--Execution--Fuel-and-progress"}[run out of fuel]
return nothing, so they place no condition.

Four facts follow, one for each way the interpreter builds a computation:

* $`x \mathbin{>\!\!>\!\!=} g` returns values of the types $`t^*` when
  $`g\,b` does for every result $`b` that $`x` can end with.
* A stuck computation has no path that returns, so it meets the condition
  for any $`t^*`.
* So does a run that has run out of fuel.
* A return of the values $`v^*` meets it when the types of $`v^*` are
  $`t^*`.
:::

:::readable Fir.Func.runOps_returns (fingerprint := "3380631763683714867")
*Theorem: a function returns values of its result types.* Run any list of
ops in the context of a function $`f` and a module $`M`, from any
environment and with any amount of fuel. Every return of that run returns
values of the result types of $`f`. The
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
checks the types of the values before it returns them, so this holds
whatever the ops do, in every dialect.
:::

:::readable Fir.Func.enter_ok (pin := Fir.Func.enter) (fingerprint := "15860882159951368467")
*Theorem: the callee starts.* Let the entry block $`e` of a function $`f`
declare no arguments, and let the values $`v_1, \dots, v_n` have the types
of the parameters $`p_1, \dots, p_n` of $`f`. Then entering $`f` with them
succeeds: the run starts at the first op of $`e`, with each parameter bound
to its value.

$$`\mathrm{enter}_f(v_1, \dots, v_n) = \mathsf{ok}\bigl(\mathrm{body}(e),\ [p_1 \mapsto v_1, \dots, p_n \mapsto v_n]\bigr)`
:::

:::readable Fir.Env.scoped_entry (pin := Fir.Env.Scoped) (fingerprint := "12924488738984897184")
*Theorem: at the start of a function, binding its parameters holds every
value in scope.* An environment
{ref "The-fir-specification--Execution--Scope-along-a-run"}[holds every value in scope]
at an op when it binds each value
{ref "The-fir-specification--Validation--Dominance"}[in scope] there to a
value of the type the function gives it. Let $`f` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid function]
whose entry block $`e` declares no arguments. Binding the parameters of
$`f` to values of their types gives an environment that holds every value
in scope at the first op of $`e`.
:::

:::readable Fir.Func.scoped_results (pin := Fir.Env.Scoped) (fingerprint := "10844354965287207548")
*Theorem: an op's results join the scope.* Let $`f` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid function],
$`b` one of its blocks, and $`i` the index of an op of $`b`. Take an
environment that
{ref "The-fir-specification--Execution--Scope-along-a-run"}[holds every value in scope]
at that op. Binding the op's
results to values of their types gives an environment that holds every
value in scope at the next op, at index $`i + 1`.
:::
