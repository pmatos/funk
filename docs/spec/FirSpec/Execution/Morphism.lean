import VersoManual
import Fir.Execution.Morphism
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on monad morphisms, which renders
`Fir.Execution.Morphism` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Monad morphisms: readable blocks" =>

:::readable Fir.MonadMorphism (fingerprint := "12632748386210839733")
*Definition: a translation between two readings of computations.* The
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
builds a run from a few steps: end at once with a value $`a`, written
$`\mathrm{pure}(a)`; run $`x`, then $`g` on its value, written
$`x \mathbin{>\!\!>\!\!=} g`; and apply a function $`h` to the value of
$`x`, written $`\mathrm{map}_h(x)`. A _monad_ is one way to
give these steps a meaning, such as the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad],
where a computation is the set of the ways it may end, or the
{ref "The-fir-specification--Execution--Choice-trees"}[tree of choices].

A _monad morphism_ $`\varphi` from a monad $`m` to a monad $`n` maps each
computation $`x` of $`m`, of any type, to a computation $`\varphi(x)` of
$`n` of the same type, and keeps the three steps:

$$`\varphi(\mathrm{pure}(a)) = \mathrm{pure}(a)`

$$`\varphi(x \mathbin{>\!\!>\!\!=} g) = \varphi(x) \mathbin{>\!\!>\!\!=} (a \mapsto \varphi(g(a)))`

$$`\varphi(\mathrm{map}_h(x)) = \mathrm{map}_h(\varphi(x))`

So translating a run step by step gives the same as translating the whole
run, which is what lets the next theorems carry the run in one monad over
to the run in the other.
:::

:::readable Fir.MonadMorphism.except (fingerprint := "17580491462413617975")
*Definition: a translation keeps errors.* A run's paths may also end
_stuck_, an error that the interpreter carries beside the monad's own
ways to end. For every set $`E` of errors, a monad morphism $`\varphi`
from $`m` to $`n` gives one from computations of $`m` whose paths may
also end with an error of $`E` to such computations of $`n`: it
translates the computation, and each path that ends with an error ends
with the same error after it.
:::

:::readable Fir.MonadMorphism.except_liftExcept Fir.MonadMorphism.except_lift (fingerprint := "18399010535387011980")
*Theorem: lifted steps translate as they are.* Two steps in the proofs
below. A step that ends at once, with an error or with a value, is
unchanged by the translation that keeps errors. And a computation $`x` of
$`m`, lifted to one whose paths may also end with an error, translates to
$`\varphi(x)`, lifted the same way.
:::

:::readable Fir.MonadMorphism.MapsDenote (pin := Fir.DialectDenote) (fingerprint := "2618859953134783425")
*Definition: a translation that keeps each op's semantics.* Let a dialect,
with the values of its types and its signatures, give its ops a {ref "The-fir-specification--Execution--Effects-and-op-semantics"}[semantics]
in both $`m` and $`n`. A monad morphism $`\varphi` from $`m` to $`n`
_keeps the semantics_ of the ops when, for every op $`o` and every operand
vector $`\vec{v}` of its operand types,

$$`\varphi(\mathrm{denote}^m_o(\vec{v})) = \mathrm{denote}^n_o(\vec{v})`

$$`\varphi(\mathrm{exit}^m_o(\vec{v})) = \mathrm{exit}^n_o(\vec{v})`

where the superscript names the monad in which the semantics is read.
Both what an op that is not a terminator gives and where a terminator
goes are kept.
:::

:::readable Fir.Func.runOps_map Fir.Func.run_map (fingerprint := "17187019605106353245")
*Theorem: the interpreter cannot tell the two monads apart.* Take any
dialect, with what the interpreter needs of it: the values of its types,
a test of whether two of its types are equal, its signatures, its calls,
and a semantics of its ops in both $`m` and $`n`. Let $`\varphi` be a monad morphism from $`m` to $`n` that keeps the semantics
of a dialect's ops, and $`\varphi_E` the translation that keeps errors,
for the errors of a stuck path. For every module $`M` of the dialect, every
function $`f`, every vector of arguments $`\vec{v}` of $`f`'s parameter
types and every fuel budget $`k`,

$$`\varphi_E(\mathrm{run}^m_{M,f}(\vec{v}, k)) = \mathrm{run}^n_{M,f}(\vec{v}, k)`

where $`\mathrm{run}^m_{M,f}(\vec{v}, k)` is the run of $`f` on $`\vec{v}`
with $`k` steps of fuel, read in $`m`. The first theorem says the same of
a run of any list of ops, for any function $`f` and environment, calls
included;
the second, about a whole function, follows from it.

The interpreter is written once, for any monad, so the proof translates it
step by step: each op's step by the hypothesis, and every other step,
such as looking up a value or calling a function, because the translation
keeps the three steps. This is what ties `fir-ref`'s runs, in the tree of
choices, to the run in the set monad that gives a function its meaning.
:::
