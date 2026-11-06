import VersoManual
import Fir.Execution.SetRuns
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on reading a run path by path, which
renders `Fir.Execution.SetRuns` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Reading a run path by path: readable blocks" =>

:::readable Fir.SetM.run_pure Fir.SetM.run_bind Fir.SetM.run_liftExcept Fir.SetM.run_lift (fingerprint := "4071084253136644651")
*Theorem: how each way of building a computation ends.* The
{ref "The-fir-specification--Execution--The-interpreter"}[interpreter]
computes in the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set monad],
with one more way for a path to end: it may be stuck. So a computation
$`x` of a run is the set of the ways its paths may end, each of them one of

$$`\mathit{end} ::= \mathsf{ok}~a \mid \mathsf{stuck}~s \mid \mathsf{ub}~r`

a result $`a`, stuck for the reason $`s`, or immediate UB for the reason
$`r`. We write $`e \in x` when $`x` may end with $`e`, and $`x \leadsto a`
when $`x` may end with the result $`a`, that is when
$`\mathsf{ok}~a \in x`. Four facts say how each way of building a
computation ends:

* The computation $`\{\mathsf{ok}~a\}`, which ends at once with $`a`, ends
  with $`\mathsf{ok}~a` and in no other way.
* Run $`x`, then $`g` on the result of $`x`, written
  $`x \mathbin{>\!\!>\!\!=} g`: a path of it goes through a result $`a` of
  $`x` and ends as a path of $`g\,a` ends, or it ends where $`x` is stuck
  or hits UB.
* A check of the interpreter, such as looking a name up in the
  environment, has one answer and makes no choice: a value $`a`, or stuck
  for a reason $`s`. Made a computation of the run, read as one whose ends
  are its answers, it ends with that answer and in no other way: it is $`\{\mathsf{ok}~a\}` or $`\{\mathsf{stuck}~s\}`.
* The semantics of an op is a computation of the set monad: it may end
  with a value or with UB, and is never stuck. Made a computation of the
  run, it ends with $`\mathsf{ok}~a` exactly when the op's computation may
  end with $`a`, with $`\mathsf{ub}~r` exactly when the op's computation
  may hit UB with the reason $`r`, and in no other way.

The second fact, in symbols:

$$`\begin{aligned} & e \in x \mathbin{>\!\!>\!\!=} g \\ \iff\ & \exists a.\ x \leadsto a \,\wedge\, e \in g\,a \\ \vee\ & \exists s.\ \mathsf{stuck}~s \in x \,\wedge\, e = \mathsf{stuck}~s \\ \vee\ & \exists r.\ \mathsf{ub}~r \in x \,\wedge\, e = \mathsf{ub}~r \end{aligned}`

The four facts hold for any kind of error in place of stuck; the
interpreter uses them with stuck. A run is built from these four pieces,
so every proof about runs in the sections that follow takes a run apart
along them.
:::

:::readable Fir.NoStuck Fir.HasPath (fingerprint := "2417873641739743497")
*Definition: a computation with no stuck path, and a computation that has
a path.* A computation $`x` has _no stuck path_ when it may not end stuck,
for any reason. It _has a path_ when it may end in some way:

$$`\mathrm{nostuck}(x) \iff \forall s.\ \mathsf{stuck}~s \notin x`

$$`x \text{ has a path} \iff \exists e.\ e \in x`

They are the two
{ref "The-fir-specification--Execution--Fuel-and-progress"}[obligations]
of no stuck path and progress, read one computation at a time instead of
one whole run. The proofs of the next sections follow a run step by step
and show one or the other of each step, with the facts below. A
computation with no path is the empty set: a path that reaches it has no
way to end, so it drops out of the run.
:::

:::readable Fir.NoStuck.pure' Fir.NoStuck.liftExcept_ok Fir.NoStuck.lift Fir.NoStuck.bind (fingerprint := "5336409005677587399")
*Theorem: no stuck path, piece by piece.* For results of any kind:

* $`\{\mathsf{ok}~a\}` has no stuck path.
* A check that succeeds with a value $`a` has no stuck path.
* The semantics of an op, made a computation of the run, has no stuck
  path.
* $`x \mathbin{>\!\!>\!\!=} g` has no stuck path when $`x` has none, and
  $`g\,a` has none for every result $`a` that $`x` may end with:

$$`\begin{aligned} & \mathrm{nostuck}(x) \\ \wedge\ & \bigl(\forall a.\ x \leadsto a \implies \mathrm{nostuck}(g\,a)\bigr) \\ \implies\ & \mathrm{nostuck}(x \mathbin{>\!\!>\!\!=} g) \end{aligned}`

So to show that no path of a run is stuck, it is enough to show, at each
step, that every check the interpreter makes there succeeds.
:::

:::readable Fir.HasPath.pure' Fir.HasPath.bind_ok Fir.HasPath.bind_lift (fingerprint := "16521507716419951768")
*Theorem: a path, piece by piece.* For results of any kind:

* $`\{\mathsf{ok}~a\}` has a path.
* $`x \mathbin{>\!\!>\!\!=} g` has a path when $`x` may end with some
  result $`a` and $`g\,a` has a path.
* Let $`c` be the semantics of an op, which may end in some way. Then $`c`,
  made a computation of the run and followed by $`g`, has a path when
  $`g\,a` has a path for every value $`a` that $`c` may end with.

Unlike no stuck path, a path needs only one way on at each step. The last
fact is where an op's semantics comes in: it must not be the empty set,
which the
{ref "The-fir-specification--Execution--Poison-classes"}[totality obligation]
asks of every op. When $`c` hits UB, that is already a path. The rule for
sequencing in general, which a call needs, is in the section
{ref "The-fir-specification--Execution--What-a-call-step-needs"}[what a call step needs].
:::
