import VersoManual
import Fir.Execution.EnvRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refined environments, which renders
`Fir.Execution.EnvRefine` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refined environments: readable blocks" =>

:::moduleDocs (fingerprint := "13860081481177104000")
:::

:::readable Fir.DVal.type_eq_of_isRefinedBy Fir.DVals.types_eq_of_isRefinedBy Fir.DVals.length_eq_of_isRefinedBy (pin := Fir.instHRefinementDVal) (pin := Fir.List.IsRefinedBy) (fingerprint := "12804861348215119863")
*Theorems: refinement keeps types and lengths.* In every dialect, with
its refinement of values:

* if the typed value $`(t, v)` is refined by $`(t', v')`, then $`t = t'`;
* if the list of typed values $`u^*` is refined by $`u'^*`, then the two
  lists have the same types, position by position, and the same length.

A typed value is
{ref "The-fir-specification--Execution--Values-and-refinement"}[refined]
only by a value of its own type, and a list only by a list of its length
whose elements refine its own. So every check of the interpreter that
looks at types or counts, such as the check of a callee's arguments or of
a block's arguments, decides alike on a list and on a list that refines
it.
:::

:::readable Fir.HVector.toDVals_isRefinedBy (pin := Fir.HVector.Forall₂) (pin := Fir.HVector.toDVals) (fingerprint := "9266708787873397849")
*Theorem: vectors that refine position by position give lists that
refine.* For every list of types $`t_1, \dots, t_n` and values
$`v_i, v'_i \in \llbracket t_i \rrbracket` with $`v_i \sqsubseteq_{t_i} v'_i`
for each $`i`:

$$`\begin{aligned} & [(t_1, v_1), \dots, (t_n, v_n)] \\ \sqsubseteq\ & [(t_1, v'_1), \dots, (t_n, v'_n)] \end{aligned}`

An op's semantics works on vectors of values, one of each type of its
signature, and an environment holds typed values; this carries the
refinement of the one to the other.
:::

:::readable Fir.Env.IsRefinedBy (fingerprint := "9175744602071411945")
*Definition: an environment refined by another.* An
{ref "The-fir-specification--Execution--The-interpreter"}[environment]
$`E` is refined by $`E'`, written $`E \sqsubseteq E'`, when both bind the
same names in the same order, and each value of $`E'` refines the value
that $`E` binds at the same place:

$$`\begin{aligned} & [x_1 \mapsto w_1, \dots, x_n \mapsto w_n] \\ \sqsubseteq\ & [x'_1 \mapsto w'_1, \dots, x'_m \mapsto w'_m] \end{aligned}`

holds exactly when $`n = m` and, for each $`i`, $`x_i = x'_i` and
$`w_i \sqsubseteq w'_i`.

Refined arguments refine a run because the run only passes values on: it
looks them up by name, checks their types and hands them to ops, to
successors and to callees. This relation is what holds between the source's
environment and the target's at every step.
:::

:::readable Fir.Env.IsRefinedBy.zip_append (pin := Fir.List.IsRefinedBy) (fingerprint := "6260386824660073815")
*Theorem: binding refined values keeps an environment refined.* If
$`E \sqsubseteq E'` and the lists of typed values $`u^*` and $`u'^*`
satisfy $`u^* \sqsubseteq u'^*`, then for every list of names $`x^*`:

$$`[x^* \mapsto u^*] \cdot E \sqsubseteq [x^* \mapsto u'^*] \cdot E'`

Here $`[x^* \mapsto u^*] \cdot E` pairs each name with the value at its
place, up to the end of the shorter list, in front of $`E`. An op's
results, a block's arguments and a callee's parameters are all bound so.
:::

:::readable Fir.Env.IsRefinedBy.lookup Fir.Env.IsRefinedBy.value Fir.Env.IsRefinedBy.mapM_value (pin := Fir.Env.value) (fingerprint := "2288385506341218324")
*Theorems: what the refining environment finds, the refined one finds.*
Let $`E \sqsubseteq E'`.

* If the first pair for the name $`x` in $`E'`, its latest definition,
  holds the typed value $`w'`, then the first pair for $`x` in $`E` holds
  a $`w` with $`w \sqsubseteq w'`.
* So if the value of $`x` in $`E'` is found, $`E'(x) = w'`, then
  $`E(x) = w` is found too, with $`w \sqsubseteq w'`.
* And if the values of the names $`x_1, \dots, x_n` are all found in
  $`E'`, as the list $`w'^*`, then they are all found in $`E`, as a list
  $`w^*` with $`w^* \sqsubseteq w'^*`.

A name that the target's run finds, the source's run finds too, with a
value that the target's refines. The last is what a jump looks up.
:::

:::readable Fir.Env.operands_cons_ok Fir.Env.IsRefinedBy.operands (pin := Fir.Env.operands) (pin := Fir.HVector.Forall₂) (fingerprint := "12120129880752582993")
*Theorems: the operands that the refining environment finds, the refined
one finds, refined.* Let $`E \sqsubseteq E'`, in a dialect whose types can
be compared for equality. If the
{ref "The-fir-specification--Execution--The-interpreter"}[operands]
of the types $`t^*` named $`x^*` are found in $`E'`, as the vector
$`v'^*`, then they are found in $`E`, as a vector $`v^*` whose values
$`v'^*` refine position by position: $`v_i \sqsubseteq_{t_i} v'_i`.

So an op of the target runs on operands that refine those of the same op
in the source, which is where
{ref "The-fir-specification--Execution--Poison-classes"}[monotonicity]
applies.

The proof takes the operands one at a time, by a plumbing lemma: the
operands of the types $`t\,t^*` named $`x\,x^*` are found as $`v\,v^*`
exactly when $`E(x)` is a value $`v` of the type $`t`, and the operands
of the types $`t^*` named $`x^*` are found as $`v^*`.
:::

:::readable Fir.Func.jump_eq_ok Fir.Func.jump_of Fir.Env.IsRefinedBy.jump (pin := Fir.Func.jump) (pin := Fir.Func.block?) (fingerprint := "17995951777421580479")
*Theorems: a jump from the refining environment goes where the jump from
the refined one goes.* Let $`E \sqsubseteq E'`, in a dialect whose types
can be compared for equality. If, for a function $`f`
and the successors of a terminator, the
{ref "The-fir-specification--Execution--The-interpreter"}[jump]
to the successor $`i` from $`E'` goes to the block $`b` in the
environment $`E'_1`, then the jump to the successor $`i` from $`E` goes to
the same block $`b`, in an environment $`E_1` with $`E_1 \sqsubseteq E'_1`.

It rests on two plumbing lemmas, which together say what a jump does: a
jump to the successor
$`i` from $`E` goes to $`b` in $`E_1` exactly when the successor $`i`
exists, with the label $`l` and the names $`y^*`; $`b` is the first block
of $`f` with the label $`l`; the values $`w^*` of $`y^*` are found in $`E`;
they are as many as the arguments of $`b`, and of their types; and
$`E_1 = [z^* \mapsto w^*] \cdot E`, for the names $`z^*` of the arguments
of $`b`.

Which successor a terminator takes is decided by its own rule, before the
jump. Once that is fixed, the target and the source go to the same block
together.
:::

:::readable Fir.Func.enter_eq_ok Fir.Func.enter_isRefinedBy (pin := Fir.Func.enter) (fingerprint := "14850641996949605453")
*Theorems: a function entered on refined arguments starts where it starts
on the others.* Let $`u^* \sqsubseteq u'^*` be lists of typed values, in
a dialect whose types can be compared for equality. If
{ref "The-fir-specification--Execution--The-interpreter"}[entering]
the function $`f` with $`u'^*` starts at the ops $`p^*` in the environment
$`G'`, then entering $`f` with $`u^*` starts at the same ops $`p^*`, in an
environment $`G` with $`G \sqsubseteq G'`.

It rests on a plumbing lemma that says what entering does: if entering
$`f` with $`u^*` starts at $`p^*` in $`G`, then $`f` has a first block
$`e`, which declares no arguments; the types of $`u^*` are the parameter types of
$`f`; $`p^*` is the body of $`e`; and $`G` binds the parameters of $`f`
to $`u^*`.

A call of the same function in the source and the target, on arguments of
which the target's refine the source's, starts both callees at the same
op, so that the proof can follow them together.
:::
