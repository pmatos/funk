import VersoManual
import Fir.Execution.Environment
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the environment of a run, which
renders `Fir.Execution.Environment` (ADR-2026-11-05-2012). Each block
explains declarations of that module and pins their fingerprint; the
build fails when the Lean changes under it.
-/

#doc (Manual) "The environment of a run: readable blocks" =>

:::readable Fir.find?_of_nodup Fir.Func.typeOf_of_mem (pin := Fir.Func.typeOf) (fingerprint := "12310842176801363216")
*Theorem: in a list of pairs whose first parts are distinct, a key's
first pair is the pair the list holds for it; so in a function whose
value names are distinct, a name has the type of its definition.* Let the names of the definitions
$`\mathrm{defs}(f)` of a function $`f` be distinct, and let $`x : t` be one
of them. Then $`\mathrm{type}_f(x) = t`.

Here $`\mathrm{defs}(f)` is the
{ref "The-fir-specification--Validation--Scope-and-symbols"}[definitions]
of $`f`, each a value name with its type, and $`\mathrm{type}_f(x)` is the
type of the first definition of $`x` among them. The second fact rests on
the first: in a list of pairs whose first parts are distinct, the first
pair whose first part is $`x` is the pair $`(x, t)` that the list holds.
A
{ref "The-fir-specification--Validation--The-general-rules"}[valid function]
has distinct names, so the type it gives a name is the type of the name's
only definition.
:::

:::readable Fir.lookup_of_mem Fir.lookup_append_of_not_mem (fingerprint := "14449396384479537477")
*Lemmas: looking a name up in a list of pairs.* If $`x` is the first part
of some pair of a list, looking $`x` up in the list gives a value $`v`, and
$`(x, v)` is a pair of the list. If no pair of $`l` has the first part
$`x`, looking $`x` up in $`l` followed by $`r` is looking it up in $`r`.
The proofs below use them to look a name up in an environment, whose
latest bindings come first.
:::

:::readable Fir.HVector.toDVals_types (pin := Fir.HVector.toDVals) (fingerprint := "14977757874954030664")
*Theorem: the typed values of a vector have the vector's types.* For
values $`v_1, \dots, v_n` of the types $`t_1, \dots, t_n`, the typed values
$`(t_1, v_1), \dots, (t_n, v_n)` have the types $`t_1, \dots, t_n`. The
interpreter turns an op's results into
{ref "The-fir-specification--Execution--Values-and-refinement"}[typed values]
this way before it binds them, and this says that their types are the
op's result types.
:::

:::readable Fir.Env.Holds (pin := Fir.Env) (fingerprint := "13649076270396545226")
*Definition: an environment holds a list of names.* An
{ref "The-fir-specification--Execution--The-interpreter"}[environment]
$`E` binds names to typed values, the latest first, and $`E(x)` is the
typed value of the latest binding of $`x` in $`E`, when there is one. For
a function $`f`, $`E` _holds_ the names $`X` when it binds each name of
$`X` to a value of the type that $`f` gives it:

$$`\begin{aligned} & \mathrm{holds}_f(E, X) \\ \iff\ & \forall x \in X. \\ & \quad \exists v.\ E(x) = (\mathrm{type}_f(x), v) \end{aligned}`

So $`f` gives $`x` a type, and $`E` binds $`x` to a value of it. This is
the invariant of a run that the next sections keep: before an op, the
environment holds every name the run has defined so far, so the op's
operands are found, with the types that validation checked.
:::

:::readable Fir.Env.bind_ok (pin := Fir.Env.bind) (fingerprint := "17627944006949166810")
*Theorem: binding as many names as values succeeds.* For every environment
$`E`, names $`x_1, \dots, x_n`, typed values $`w_1, \dots, w_n`, as many as
the names, and reason $`s`, binding the names to the values gives

$$`[x_1 \mapsto w_1, \dots, x_n \mapsto w_n] \cdot E`

Binding puts the new pairs in front of $`E`, and is stuck, for the
reason $`s` that its caller gives, only when the numbers of names and
values differ.
:::

:::readable Fir.mem_zip_types Fir.Env.holds_bind (fingerprint := "11346792559097344601")
*Theorem: pairing names with values of their types, and binding them,
keeps what an environment holds.* Let $`p^* = (x_1 : t_1) \dots (x_n : t_n)`
be names with types, and $`w_1, \dots, w_n` typed values of the types
$`t_1, \dots, t_n`.

* Each pair $`(x, w)` of the pairing
  $`(x_1, w_1), \dots, (x_n, w_n)` gives $`x : t` in $`p^*`, where $`t` is
  the type of $`w`.
* Let the function $`f` give each $`x_i` the type $`t_i`, let
  $`\mathrm{holds}_f(E, X)`, and let no name of $`X` be one of
  $`x_1, \dots, x_n`. Then the environment
  $`E' = [x_1 \mapsto w_1, \dots, x_n \mapsto w_n] \cdot E` holds $`X`
  followed by $`x_1, \dots, x_n`.

A run binds an op's results this way: the new names are found with
their types, and the names it held before are still found as they were.
:::

:::readable Fir.Env.operands_ok (pin := Fir.Env.operands) (fingerprint := "18266545032337680460")
*Theorem: an op's operands are found with their types.* For types
$`t_1, \dots, t_n` and names $`x_1, \dots, x_k`, let the function $`f` give
the names the types $`t_1, \dots, t_n`: $`k = n` and
$`\mathrm{type}_f(x_i) = t_i` for each $`i`. If
$`\mathrm{holds}_f(E, x_1 \dots x_k)`, then looking the operands up in
$`E` succeeds, with values $`v_1, \dots, v_n` of the types
$`t_1, \dots, t_n`.

Looking the operands $`x_1, \dots, x_k` up for the operand types
$`t_1, \dots, t_n` takes $`E(x_i)` for each $`i`, from the first, and
checks, with the dialect's test of equality of types, that its type is
$`t_i`. It is stuck when a name is not bound, when a type differs, or
when there are more names than types or fewer. The theorem says none of
these happens where the run's invariant holds and validation has checked
the operand types.
:::
