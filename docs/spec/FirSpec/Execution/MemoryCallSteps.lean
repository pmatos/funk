import VersoManual
import Fir.Execution.MemoryCallSteps
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the steps of a call with memory,
which renders `Fir.Execution.MemoryCallSteps` (ADR-2026-11-05-2012). Each
block explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The steps of a call, with memory: readable blocks" =>

:::moduleDocs (fingerprint := "17976563511346448721")
:::

:::readable Fir.liftExcept_ok_bind Fir.NoStuck.map Fir.HasPath.map (fingerprint := "59618637625475726")
*Theorems: a check that passes, and a mapped computation.* A check of the
interpreter that passes with $`a` and then $`g` is $`g\,a`. Mapping what a
computation returns keeps that it
{ref "The-fir-specification--Execution--Reading-a-run-path-by-path"}[has no stuck path],
and that it has a path.
:::

:::readable Fir.NoStuck.fromState_bind Fir.HasPath.fromState_bind Fir.NoStuck.fromState_lift Fir.HasPath.fromState_lift Fir.fromState_lift_ok (pin := Fir.fromState) (fingerprint := "9062592938717625383")
*Theorems: paths from given memories.* Read a computation
{ref "The-fir-specification--Memory--How-a-run-with-memory-ends"}[from the memories S],
$`x \mathbin{@} S`. Then $`(x \mathbin{>\!\!>\!\!=} g) \mathbin{@} S` has no
stuck path when $`x \mathbin{@} S` has none and, for each result $`a` that
it ends with, with the memories $`S'`, $`(g\,a) \mathbin{@} S'` has none;
and the same holds of having a path.

$$`x \mathbin{@} S \text{ has a path} \;\wedge\; \bigl(\forall a\,S'.\ x \mathbin{@} S \leadsto (a, S') \implies (g\,a) \mathbin{@} S' \text{ has a path}\bigr) \;\implies\; (x \mathbin{>\!\!>\!\!=} g) \mathbin{@} S \text{ has a path}`

A computation $`c` of the state layer, lifted into the interpreter, is
never stuck, and has a path from $`S` when $`c(S)` may end in some way;
each result it ends with from $`S`, with the memories $`S'`, is one that
$`c(S)` may end with.
:::

:::readable Fir.MemReturnsTypes Fir.MemReturnsTypes.bind Fir.MemReturnsTypes.of_stuck Fir.MemReturnsTypes.exhausted Fir.MemReturnsTypes.ret Fir.MemReturnsTypes.inFrame Fir.Func.runOps_memReturns (fingerprint := "1137233387060230361")
*Definition and theorems: a function returns values of its result types,
with memory.* A run of ops $`x` _returns values of the types_ $`t^*` with
memory when, from any memories, every return of $`x` returns values of the
types $`t^*`, whatever memories it ends with. A sequence does when its
second part does on each result; a stuck run, a run out of fuel, and a
return of values of the types $`t^*` do; and a run in a call's frame does
when the run does, since the frame changes only the memories. So a run of
the ops of a function $`f` with memory returns values of the result types
of $`f`, for every dialect whose ops have a semantics in the state layer:
the interpreter checks them before it returns, whatever the ops do to the
memories.
:::

:::readable Fir.Func.MemInModule (fingerprint := "11963576496452871621")
*Definition: a function that runs within a module, with memory.* The ops
of a function $`f` _run within the module $`M` with memory_ when, for every
op $`o` of every block of $`f`:

* if $`o` is not a terminator and calls the symbol $`s`, the symbol table
  of $`M` gives $`s` the type of the call, as for a function that
  {ref "The-fir-specification--Execution--Progress-with-calls"}[runs within a module];
* if $`o` is a terminator, whenever $`\mathrm{exit}_o` may end with
  $`\mathsf{goto}~i` from any memories, on any operands,
  $`i < \mathrm{nsucc}(o)`, and $`o` has no result types;
* if $`o` is a terminator, whenever $`\mathrm{exit}_o` may end with
  $`\mathsf{ret}` from any memories, on any operands, its operand types
  are the result types of $`f`.

Here $`\mathrm{exit}_o` is the exit of $`o` in the state layer.
:::

:::readable Fir.Func.InModule.memInModule_liftState Fir.Func.InModuleAt Fir.Func.InModule.inModuleAt (pin := Fir.DialectDenote.liftState) (fingerprint := "1928419679928969135")
*Definition and theorems: running within a module, at a naming.* The ops of
$`f` run within $`M` with memory _at the naming_ $`\rho`, with unit widths
$`u`, when they run within it by the dialect's semantics with memory where
a run names the dialect's memory $`x` as $`\rho(x)`, whose units are
$`u(\rho(x))` bits wide. A function that runs within its module runs
within it with memory by its dialect's semantics in the set monad, lifted
into the state layer: each terminator goes where it goes in the set monad,
and keeps the memories. So, in a dialect that
{ref "The-fir-specification--Memory--Runs-with-memory"}[lifts the set monad],
a function that runs within its module runs within it with memory, at every
naming.
:::

:::readable Fir.Func.memRuns_enter (pin := Fir.Func.memRuns) (fingerprint := "2274960835630802990")
*Theorem: a run with memory that starts.* When a function $`f` starts on
its arguments, at its entry block's ops $`o^*` with the environment $`E`,
its runs with memory at a naming, at the budget $`n`, are
$`\mathrm{run}_M(n, f, E, o^*)` read from the empty memories with a frame
entered, finished: a return of its ops is a return of $`f`, and a run out of
fuel is one.
:::
