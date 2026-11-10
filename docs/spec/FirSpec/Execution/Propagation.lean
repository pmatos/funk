import VersoManual
import Fir.Execution.Propagation
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on poison classes, which renders
`Fir.Execution.Propagation` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Poison classes: readable blocks" =>

:::moduleDocs (fingerprint := "1793719121250415061")
:::

:::readable Fir.TyPoison (fingerprint := "4292109808732388566")
*Definition: the poison values of a dialect.* Each dialect says which
values of each of its types are poison. A type may have no poison at all.
Each op's poison class, $`\mathrm{class}(o)`, comes from the dialect's
{ref "The-fir-specification--Execution--Effect-sets"}[effect class].
:::

:::readable Fir.HVector.Any Fir.HVector.All Fir.HVector.Forall₂ Fir.HVector.forall₂_refl (fingerprint := "6154170390044616023")
*Definition: some, every, and position by position, for vectors of
values.* An op takes a vector of operand values
$`\vec{v} = (v_1, \dots, v_n)`, one of each operand type, and gives a
vector of result values. For a property $`P` of values and a relation
$`\mathrel{R}` between two values of one type:

* _some_ element of $`\vec{v}` has $`P` when $`\exists i.\ P(v_i)`; the
  empty vector has none;
* _every_ element of $`\vec{v}` has $`P` when $`\forall i.\ P(v_i)`; the
  empty vector has it;
* $`\vec{v}` and $`\vec{w}`, of the same types, are related _position by
  position_ when $`\forall i.\ v_i \mathrel{R} w_i`.

*Theorem: a relation that holds of every value with itself holds of every
vector with itself, position by position.* If $`x \mathrel{R} x` for every
value $`x`, then $`\vec{v}` and $`\vec{v}` are related by $`\mathrel{R}`
position by position, for every vector $`\vec{v}`. The proofs of
monotonicity, below, use it to show that a vector of results refines
itself, as for $`\mathsf{const}`, which has no operands.
:::

:::readable Fir.HVector.IsFilledBy Fir.PoisonOut Fir.UBByOwnRules Fir.PropagatesPoison (pin := Fir.HVector.Any) (pin := Fir.HVector.All) (pin := Fir.HVector.Forall₂) (fingerprint := "5327225852687059508")
*Definition: the obligation of an op that propagates poison.* Below,
$`\mathrm{denote}_o(\vec{v})` is the
{ref "The-fir-specification--Execution--Effects-and-op-semantics"}[meaning]
of the op $`o` on the operands $`\vec{v}`, read as the
{ref "The-fir-specification--Execution--Outcomes-and-behaviours"}[set]
of the ways it may end: $`\mathsf{ok}~\vec{w}`, with results $`\vec{w}`,
or $`\mathsf{ub}~r`.

A vector $`\vec{v}'` _fills_ $`\vec{v}` when it puts a defined value in
place of each poison of $`\vec{v}`: no element of $`\vec{v}'` is poison,
and $`v'_i = v_i` wherever $`v_i` is not poison.

An op $`o` _propagates poison_ when it meets two clauses, for every
operand vector $`\vec{v}` some element of which is poison:

* _Poison out_: whenever $`\mathsf{ok}~\vec{w} \in \mathrm{denote}_o(\vec{v})`,
  every element of $`\vec{w}` is poison.
* _UB only by the op's own rules_: whenever
  $`\mathsf{ub}~r \in \mathrm{denote}_o(\vec{v})`, some $`\vec{v}'` that
  fills $`\vec{v}` has
  $`\mathsf{ub}~r' \in \mathrm{denote}_o(\vec{v}')` for some $`r'`.

The second clause is LLVM's principle: a poison operand is immediate UB
only where some value it could take would be UB. A poison divisor may be
UB, since it could be zero; a poison operand of $`\mathsf{add}` may not,
since no value makes $`\mathsf{add}` UB. Without the clause, an op could
turn every poison into UB, and the deferral that poison exists for would
be lost
({ref "The-fir-specification--Execution--Poison-and-immediate-UB"}[poison and immediate UB]).
:::

:::readable Fir.Ev.IsRefinedBy Fir.SetM.IsRefinedBy Fir.SetM.isRefinedBy_refl (fingerprint := "16996066690332990826")
*Definition: one computation refines another.* Let $`\mathrel{R}` be a
relation on the values that two computations end with. One way to end,
$`e`, allows another, $`e'`, when

$$`\mathsf{ub}~r \text{ allows every } e'`

$$`\mathsf{ok}~a \text{ allows } \mathsf{ok}~b \iff a \mathrel{R} b`

and in no other case: $`\mathsf{ok}~a` never allows UB. A computation
$`y` refines a computation $`x` by $`\mathrel{R}` when every way $`y` may
end is allowed by some way $`x` may end. This is the
{ref "The-fir-specification--Execution--Refinement"}[refinement of behaviours],
for a single op instead of a whole run.

*Theorem: a computation refines itself when the relation is reflexive.* If
$`a \mathrel{R} a` for every $`a`, then every computation $`x` refines
$`x` by $`\mathrel{R}`. Monotonicity, below, comes down to this for an op
with no operands, whose only operand vector is the empty one.
:::

:::readable Fir.OpTotal (fingerprint := "146139999336173069")
*Definition: totality.* An op $`o` is _total_ when, on every operand vector
$`\vec{v}`, it has some outcome: if $`o` is not a terminator,
$`\mathrm{denote}_o(\vec{v})` is not empty, and if it is a terminator,
$`\mathrm{exit}_o(\vec{v})` is not empty.

An op that maps some operands to the empty set would drop that path from
every run that reaches it, and a run with fewer outcomes refines more
sources.
:::

:::readable Fir.ReturnsOnDefined (pin := Fir.HVector.Any) (fingerprint := "9248791201291918091")
*Definition: a result on defined operands.* An op $`o` _returns a result on
defined operands_ when some operand vector $`\vec{v}` with no poison
element has a result: $`\mathsf{ok}~\vec{w} \in \mathrm{denote}_o(\vec{v})`
for some $`\vec{w}`.

Without it, an op that is UB on every operand vector, the defined ones
included, would meet the clauses of propagation: for it, UB is the op's own
rule, so UB on a poison operand is too.
:::

:::readable Fir.OpMonotone (pin := Fir.Ev.IsRefinedBy) (pin := Fir.SetM.IsRefinedBy) (pin := Fir.HVector.Forall₂) (fingerprint := "673055495252104851")
*Definition: monotonicity.* An op $`o` is _monotone_ when refining its
operands refines what it does. For all operand vectors $`\vec{v}` and
$`\vec{v}'` such that each $`v'_i` refines $`v_i`, by the dialect's
{ref "The-fir-specification--Execution--Values-and-refinement"}[refinement of values]:

* if $`o` is not a terminator, $`\mathrm{denote}_o(\vec{v}')` refines
  $`\mathrm{denote}_o(\vec{v})` by refinement of the results position by
  position;
* if $`o` is a terminator, $`\mathrm{exit}_o(\vec{v}')` refines
  $`\mathrm{exit}_o(\vec{v})` by equality: where it goes may only be the
  same.

Refinement of computations is the one defined above: UB allows anything,
and a result allows the results that refine it. Monotonicity is what makes
refinement compositional: a pass that replaces a value by one that refines
it refines every op that uses it, and so the whole function.
:::

:::readable Fir.LawfulDialectPoison (pin := Fir.TypesValid) (fingerprint := "4142040794794364572")
*Definition: a lawful dialect.* A dialect is _lawful_ when it meets every
poison obligation on its valid op instances. An op instance is _valid_
when validation accepts its operand and result types
({ref "The-fir-specification--Validation--The-general-rules"}[the general rules]).
A lawful dialect meets five clauses:

* a poison value of a valid type is {ref "The-fir-specification--Execution--Values-and-refinement"}[refined] by every value of that
  type;
* every valid op instance $`o` whose class is $`\mathsf{propagates}`
  propagates poison;
* every such instance returns a result on defined operands;
* every valid op instance that runs by its own rule, that is, a
  terminator, or an op with no callee, is total;
* every such instance is monotone.

An op with a callee is left out of the last two: it runs its callee, never
a rule of its own, and its counterparts hold at function level. An
instance that validation rejects may break an obligation without harm,
since no valid program runs it. The core dialect is lawful, as the section
on
{ref "The-fir-specification--Execution--The-core-dialect___s-poison-obligations"}[the core dialect's poison obligations]
proves; from that, refinement through calls follows.
:::
