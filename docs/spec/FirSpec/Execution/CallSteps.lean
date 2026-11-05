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

:::readable Fir.HasPath.bind (fingerprint := "13996799831989033988")
*Theorem: a sequence has a path when its parts have one.* A computation of a
run _has a path_ when it ends in at least one way: with a result, stuck, or
with UB. Run $`x`, then run $`g` on the result of $`x`; write this
$`x \mathbin{>\!\!>\!\!=} g`. If $`x` has a path, and $`g\,a` has a path for
every result $`a` that $`x` can end with, then $`x \mathbin{>\!\!>\!\!=} g`
has a path.

$$`\mathrm{HasPath}(x) \;\wedge\; \bigl(\forall a.\ x \leadsto a \implies \mathrm{HasPath}(g\,a)\bigr) \;\implies\; \mathrm{HasPath}(x \mathbin{>\!\!>\!\!=} g)`

Here $`x \leadsto a` says that $`x` can end with the result $`a`. A path of
$`x` that ends stuck or with UB is already a path of the whole. For a call,
$`x` is the callee's run and $`g` what the caller does after it returns.
:::

:::readable Fir.Module.func?_of_symbols (fingerprint := "10052408013798051213")
*Theorem: the callee is found.* Suppose the symbol table of a module $`M`
gives the symbol $`s` the function type $`t^* \to r^*`. Then $`M` has a
function $`g` with symbol $`s`, and the search that a run makes for $`s`
finds it. $`g` is one of the functions of $`M`, its parameters have the
types $`t^*`, and its results the types $`r^*`.

$$`\begin{aligned} M.\mathrm{symbols}(s) = (t^* \to r^*) \implies \exists g.\ & M.\mathrm{func?}(s) = g \,\wedge\, g \in M.\mathrm{funcs} \\ & \wedge\, \mathrm{params}(g) : t^* \,\wedge\, \mathrm{results}(g) = r^* \end{aligned}`
:::

:::readable Fir.ReturnsTypes Fir.ReturnsTypes.bind Fir.ReturnsTypes.of_stuck Fir.ReturnsTypes.exhausted Fir.ReturnsTypes.ret (fingerprint := "15698882366344932232")
*Definition: returning values of given types.* A computation $`s` of a run
_returns values of the types_ $`t^*` when every path of $`s` that returns
values returns values of the types $`t^*`. A path that is stuck, ends with
UB or runs out of fuel returns nothing, so it does not count.

Four facts follow, one for each way the interpreter builds a computation:

* $`x \mathbin{>\!\!>\!\!=} g` returns values of the types $`t^*` when
  $`g\,b` does for every result $`b` that $`x` can end with.
* A computation that is stuck returns nothing, so it returns values of any
  types.
* So does a run that has run out of fuel.
* Returning the values $`v^*` returns values of the types $`t^*` when the
  types of $`v^*` are $`t^*`.
:::

:::readable Fir.Func.runOps_returns (fingerprint := "3380631763683714867")
*Theorem: a function returns values of its result types.* Run the ops of a
function $`f` of a module $`M`, from any environment and with any amount of
fuel. Every return of that run returns values of the result types of $`f`.
The interpreter checks the types of the values before it returns them, so
this holds whatever the ops do, in every dialect.
:::

:::readable Fir.Func.enter_ok (fingerprint := "13439618187292554408")
*Theorem: the callee starts.* Let the entry block $`e` of a function $`f`
declare no arguments, and let the values $`v_1, \dots, v_n` have the types
of the parameters $`p_1, \dots, p_n` of $`f`. Then entering $`f` with them
succeeds: the run starts at the first op of $`e`, with each parameter bound
to its value.

$$`\mathrm{enter}_f(v_1, \dots, v_n) = \mathsf{ok}\bigl(\mathrm{body}(e),\ [p_1 \mapsto v_1, \dots, p_n \mapsto v_n]\bigr)`
:::

:::readable Fir.Env.scoped_entry (fingerprint := "16651072555452494143")
*Theorem: at the start of a function, its parameters are what is in scope.*
An environment _holds every value in scope_ at an op when it binds each
value in scope there to a value of the type the function gives it. Let
$`f` be a valid function whose entry block $`e` declares no arguments.
Binding the parameters of $`f` to values of their types gives an
environment that holds every value in scope at the first op of $`e`.
:::

:::readable Fir.Func.scoped_results (fingerprint := "14233224962868222099")
*Theorem: an op's results join the scope.* Let $`f` be a valid function,
$`b` one of its blocks, and $`i` the index of an op of $`b`. Take an
environment that holds every value in scope at that op. Binding the op's
results to values of their types gives an environment that holds every
value in scope at the next op, at index $`i + 1`.
:::
