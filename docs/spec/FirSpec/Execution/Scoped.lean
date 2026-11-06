import VersoManual
import Fir.Execution.Scoped
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on scope along a run, which renders
`Fir.Execution.Scoped` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Scope along a run: readable blocks" =>

:::readable Fir.eq_of_nodup_map (fingerprint := "17771416556615606785")
*Lemma: two members of a list are one when a key that is distinct on the
list agrees on them.* If $`g` gives the members of a list distinct values,
and $`a` and $`b` are members with $`g(a) = g(b)`, then $`a = b`. The
proofs below use it to show that two blocks with one label are one block.
:::

:::readable Fir.Block.mem_allBlocks Fir.Func.mem_defs_arg Fir.Func.mem_defs_result (fingerprint := "13843914713198665285")
*Theorem: a block of a list is among its blocks at any depth, and the
arguments of a block and the results of its ops are definitions of the
function.*

* Each block of a list of blocks is among the blocks of the list at any
  depth, $`\mathrm{allblocks}`.
* For each block $`b` of $`\mathrm{blocks}(f)`, each argument $`y : t` of
  $`b` is in $`\mathrm{defs}(f)`.
* For each block $`b` of $`\mathrm{blocks}(f)` and each op $`o` of $`b`,
  each result $`y : t` of $`o` is in $`\mathrm{defs}(f)`.

$`\mathrm{blocks}(f)` is the top-level blocks of $`f`, and
$`\mathrm{allblocks}` and $`\mathrm{defs}(f)` are as in
{ref "The-fir-specification--Validation--Scope-and-symbols"}[scope and symbols].
With them, the type that $`f` gives a value bound by a jump or by an op
is the type the value is declared with.
:::

:::readable Fir.Func.block?_some (pin := Fir.Func.block?) (fingerprint := "18231392564545971550")
*Theorem: the block that a function finds by a label is one of its
blocks, with that label.* If $`\mathrm{block}_f(l) = b`, then $`b` is in
$`\mathrm{blocks}(f)` and its label is $`l`. Here $`\mathrm{block}_f(l)`
is the first block of $`\mathrm{blocks}(f)` whose label is $`l`, the
block that a jump to $`l` goes to.
:::

:::readable Fir.Func.dominates_of_edge (pin := Fir.Func.Dominates) (fingerprint := "6661983799789299018")
*Theorem: a block that dominates a block other than itself dominates
every block that jumps to it.* If $`a \mathrel{\mathrm{dom}_f} l'`,
$`a \neq l'` and $`l \to_f l'` is an edge, then
$`a \mathrel{\mathrm{dom}_f} l`.

$`a` {ref "The-fir-specification--Validation--Dominance"}[dominates] $`l`
when $`a = l`, or when no path from the entry reaches $`l` without passing
through $`a`. If some path reached $`l` around $`a`, it would go on along
the edge to $`l' \neq a`, still around $`a`. So a value defined in a
block that dominates the target of a jump, other than the target, is
also defined on the way to the jump.
:::

:::readable Fir.Func.Valid.block_eq (fingerprint := "1920285065544485871")
*Theorem: in a valid function, two of its blocks with one label are one
block.* Let $`f` be
{ref "The-fir-specification--Validation--The-general-rules"}[valid] in a
module context, and $`b` and $`b'` blocks of $`\mathrm{blocks}(f)` with
the same label. Then $`b = b'`. Validation asks the labels of the
top-level blocks to be distinct, and this is that rule put to use.
:::

:::readable Fir.Func.mem_params_of_inScope (fingerprint := "14275585149735458276")
*Theorem: only the parameters are in scope at the first op of the entry
block.* Let $`f` be valid in a module context, and $`e` its entry block,
which declares no arguments. If
$`\mathrm{inscope}_f(x, \mathrm{label}(e), 0)`, then $`x` is the name of a
parameter of $`f`.

$`\mathrm{inscope}_f(x, l, i)` says that the use of $`x` by the op at
index $`i` of the block labelled $`l` is
{ref "The-fir-specification--Validation--Dominance"}[in scope]. No block
but the entry dominates the entry, and no op comes before its first, so a
run that starts with only the parameters bound has every value in scope
there.
:::

:::readable Fir.Func.inScope_of_next (fingerprint := "6275212579330648413")
*Theorem: a value in scope at the next op is a result of this op, or was
in scope at this op.* Let $`f` be valid in a module context, $`b` a block
of $`\mathrm{blocks}(f)`, and $`i` less than the number of ops of $`b`.
If $`\mathrm{inscope}_f(x, \mathrm{label}(b), i + 1)` and $`x` is not the
name of a result of the op at index $`i`, then
$`\mathrm{inscope}_f(x, \mathrm{label}(b), i)`.

So a run that binds the results of an op keeps every value in scope at
the next op.
:::

:::readable Fir.Func.inScope_of_jump (fingerprint := "16213543251456165821")
*Theorem: a value in scope at the first op of a jump's target is an
argument of the target, or was in scope at the op that jumps, when that
op has no results.* Let $`f` be valid in a module context, and let:

* $`b` be a block of $`\mathrm{blocks}(f)`;
* $`b'` be a block of $`\mathrm{blocks}(f)`;
* $`o` be the op at index $`i` of $`b`;
* $`o` be the last op of $`b`: $`i + 1` is the number of its ops;
* $`o` have no results;
* $`s` be a successor of $`o`;
* the label of $`b'` be the label that $`s` names;
* $`\mathrm{inscope}_f(x, \mathrm{label}(b'), 0)`;
* $`x` not be the name of an argument of $`b'`.

Then $`\mathrm{inscope}_f(x, \mathrm{label}(b), i)`. A value in scope at
the target is defined in a block that dominates it. When that block is
not the target, it dominates $`b` too, and the value was in scope at the
jump, unless it is a result of the jump itself, which the interpreter
never binds; hence the condition that $`o` has none.
:::

:::readable Fir.Env.Scoped (fingerprint := "7193735154363532024")
*Definition: an environment holds every value in scope at an op.* For a
function $`f`, a label $`l` and an index $`i`, the environment $`E`
_holds every value in scope_ at the op at index $`i` of the block
labelled $`l` when it binds each value in scope there to a value of the
type that $`f` gives it:

$$`\begin{aligned} & \mathrm{scoped}_f(E, l, i) \\ \iff\ & \forall x.\ \mathrm{inscope}_f(x, l, i) \\ & \quad \implies \exists v.\ E(x) = (\mathrm{type}_f(x), v) \end{aligned}`

Here $`E(x)` is the typed value of the latest binding of $`x` in $`E`.
This is the invariant of a run that jumps: before each op, the run holds
every value in scope there. Every operand of the op, and every value that
it passes to a successor, is in scope, so the run finds each of them,
with its type.
:::

:::readable Fir.Env.scoped_bind (pin := Fir.Env.Scoped) (fingerprint := "4915632581719082868")
*Theorem: binding names to values of their types gives an environment
that holds every value in scope, when the old one held the others.* Let
$`p^* = (x_1 : t_1) \dots (x_n : t_n)` be names with types, and
$`w_1, \dots, w_n` typed values of the types $`t_1, \dots, t_n`. Let the
function $`f` give each $`x_i` the type $`t_i`, and let $`E` bind each
value in scope at the op at index $`i` of the block labelled $`l` that
is not one of $`x_1, \dots, x_n` to a value of the type $`f` gives it.
Then

$$`\mathrm{scoped}_f([x_1 \mapsto w_1, \dots, x_n \mapsto w_n] \cdot E, l, i)`

A lookup of a name that the binding binds finds the new value, and a
lookup of any other name finds what it found before, so the proof needs
no fact that the new names are new.
:::

:::readable Fir.Env.Scoped.holds (pin := Fir.Env.Holds) (fingerprint := "6921116275317150023")
*Theorem: an environment that holds every value in scope holds any names
in scope.* If $`\mathrm{scoped}_f(E, l, i)` and every name of $`X` is in
scope at the op at index $`i` of the block labelled $`l`, then
$`\mathrm{holds}_f(E, X)`: $`E` binds each name of $`X` to a value of the
type that $`f` gives it. So an op's operands are found where the
invariant holds.
:::

:::readable Fir.Env.scoped_params (fingerprint := "2848974677664751258")
*Theorem: a run starts holding every value in scope at its first op.* Let
$`f` be valid in a module context, $`e` its entry block, which declares
no arguments, and $`v_1, \dots, v_n` values of the types
$`t_1, \dots, t_n` of the parameters $`p_1, \dots, p_n` of $`f`. The
environment $`E = [p_1 \mapsto (t_1, v_1), \dots, p_n \mapsto (t_n, v_n)]`
holds every value in scope at the first op of $`e`:

$$`\mathrm{scoped}_f(E, \mathrm{label}(e), 0)`

$`E` is the environment where a run of $`f` on these values starts.
:::
