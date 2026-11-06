import VersoManual
import Fir.Validation.CheckOps
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on checking ops, which renders
`Fir.Validation.CheckOps` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Checking ops: readable blocks" =>

:::readable Fir.FuncTables Fir.Func.defSites Fir.Func.tables (fingerprint := "10369497456229509283")
*Definition: the tables of a function.* Before it checks the ops of a
function $`f`, the check builds five tables, once, from $`f` and a list
$`\mathit{all}` of its blocks at any depth:

* $`\mathrm{scope}`: for each value name, the type of its first definition
  among the parameters of $`f` and the definitions of the blocks of
  $`\mathit{all}`;
* $`\mathrm{sites}`: for each value name, every site where a top-level
  block of $`f`, or its parameter list, defines it;
* $`\mathrm{blocks}`: for each label, the first block of
  $`\mathrm{blocks}(f)` with that label;
* the function's graph, $`\mathrm{graph}(f)`;
* where its paths start, $`\mathrm{start}(f)`.

They are built as
{ref "The-fir-specification--Validation--Tables"}[tables of first values and of every value],
and a site is a
{ref "The-fir-specification--Validation--Dominance"}[definition site]. Only
the scope reaches into regions, as $`\mathrm{type}_f` does. The caller gives
$`\mathit{all}`, which is $`\mathrm{allblocks}(f)` unless a tool lists the
blocks its own way.
:::

:::readable Fir.Func.scope_eq Fir.Func.scope_fun Fir.Func.blocks_eq Fir.Func.start_head? Fir.Func.mem_sites (fingerprint := "7023703154083806816")
*Theorems: each table holds what the rules define.* For every function
$`f`, with the tables built from $`\mathit{all}`:

* when $`\mathit{all}` is $`\mathrm{allblocks}(f)`, the scope gives every
  name $`x` the type $`\mathrm{type}_f(x)`, and is undefined where
  $`\mathrm{type}_f` is;
* for every list $`\mathit{all}` and label $`l`, the blocks table gives
  $`l` the block $`\mathrm{block}_f(l)`, and is undefined where it is;
* for every list $`\mathit{all}`, the first label of the start is
  $`\mathrm{entry}(f)`, and there is none when $`f` has no entry;
* for every list $`\mathit{all}`, name $`x` and site $`s`, $`s` is among the
  sites of $`x` exactly when $`\mathrm{defines}_f(x, s)`.

So each later check can look a fact up in a table and still be read as the
rule that speaks of it.
:::

:::readable Fir.siteDominates Fir.siteDominates_iff (pin := Fir.Func.DominatesUse) (fingerprint := "5706251795073232108")
*Definition and theorem: whether a definition dominates a use, by search.*
$`\mathrm{sitedom}(g, S, s, l, i)` is
{ref "The-fir-specification--Validation--Dominance"}[dominance of a use]
with the search's
{ref "The-fir-specification--Validation--Reachability-and-dominance___-decided"}[dominates]
in place of $`\mathrm{dom}_f`: true for $`\mathsf{param}`; for
$`\mathsf{arg}~a`, $`\mathrm{dominates}(g, S, a, l)`; and for
$`\mathsf{result}~a~j`, either $`a = l` and $`j < i`, or $`a \neq l` and
$`\mathrm{dominates}(g, S, a, l)`.

*Theorem:* for every function $`f`, site $`s`, index $`i`, and label $`l`
of a block of $`\mathrm{blocks}(f)`:

$$`\begin{aligned} & \mathrm{sitedom}(\mathrm{graph}(f), \mathrm{start}(f), s, l, i) \\ \iff\ & s \mathrel{\mathrm{dom}_f} (l, i) \end{aligned}`
:::

:::readable Fir.DefSite.why (fingerprint := "6121637131070496736")
*Definition: why a definition does not dominate a use.* When the
definition of $`x` at a site does not dominate its use in the block
labelled $`l`, the problem says why, writing values and labels as the text
does:

* at $`\mathsf{arg}~a`: "`%x` is an argument of `^a`, which does not
  dominate `^l`";
* at $`\mathsf{result}~a~j` with $`a = l`: "`%x` is used before it is
  defined";
* at $`\mathsf{result}~a~j` with $`a \neq l`: "`%x` is defined in `^a`,
  which does not dominate `^l`".

A parameter dominates every use, so its message, "`%x` is a parameter", is
never given.
:::

:::readable Fir.useProblems Fir.useProblems_eq_nil (fingerprint := "14704668241507228120")
*Definition and theorem: the check of a use.* The check of a use of $`x` by
the op at index $`i` of the block labelled $`l` looks $`x` up in the sites
table:

* when $`x` has no site, it gives one problem: "`%x` is defined inside a
  region, and is not in scope here" when the scope has $`x`, and "`%x` is
  not defined in the function" otherwise;
* otherwise it gives one problem for each site of $`x` that does not
  dominate the use, saying why.

The check takes a function that turns a message into a problem placed at
the op: its function, block, index and location. A _way of placing a
problem_ is such a function, and the theorem holds for every one.

*Theorem:* for every function $`f`, every way of placing a problem at the
op, every index $`i`, name $`x`, and label $`l` of a block of
$`\mathrm{blocks}(f)`, with the tables built from $`\mathrm{allblocks}(f)`,
the check of the use gives no problem exactly when the use is
{ref "The-fir-specification--Validation--Dominance"}[in scope]:

$$`\begin{aligned} & \mathrm{useproblems}(x, l, i) = \epsilon \\ \iff\ & \mathrm{inscope}_f(x, l, i) \end{aligned}`
:::

:::readable Fir.succProblems Fir.succProblems_eq_nil (fingerprint := "14498177447669405208")
*Definition and theorem: the check of a successor.* The check of a
successor $`l(x_1, \dots, x_n)` gives:

* "no branch may go to the entry block `^l`" when $`l` is the first label
  of the start;
* "successor `^l` is not a block of the function" when the blocks table has
  no $`l`;
* otherwise, "successor `^l` does not pass one value of the right type for
  each argument of the block" unless the scope gives
  $`x_1, \dots, x_n` exactly the types of the arguments of that block.

Like the check of a use, it takes a way of placing a problem at the op,
and the theorem holds for every one.

*Theorem:* for every function $`f` whose dialect's types can be compared,
every way of placing a problem and every successor, with the tables built
from $`\mathrm{allblocks}(f)`, the check gives no problem exactly when the
successor is
{ref "The-fir-specification--Validation--The-general-rules"}[valid]:

$$`\begin{aligned} & \mathrm{succproblems}(l(x_1, \dots, x_n)) = \epsilon \\ \iff\ & f \vdash l(x_1, \dots, x_n)~\text{valid} \end{aligned}`
:::

:::readable Fir.ite_nil_eq_nil Fir.ite_none_eq_none (fingerprint := "4077244502137022509")
*Theorems: a check that gives something unless a condition holds gives
nothing exactly when it holds.* For every proposition $`c` that can be
decided and every value $`p`, of any type, the list that is empty when
$`c` holds and holds $`p` otherwise is empty exactly when $`c` holds. The
same goes for the choice between nothing, when $`c` holds, and $`p`. The
proofs of this chapter use them to read each
line of a check as the premise it tests.
:::

:::readable Fir.opProblems Fir.opProblems_eq_nil (fingerprint := "8802023847365866800")
*Definition and theorem: the check of an op.* The check of the op $`o` at
index $`i` of the block $`b` of $`f`, given the number $`n` of ops of
$`b`, tests the premises of the
{ref "The-fir-specification--Validation--The-general-rules"}[rule of a valid op]
in their order and gives a problem for each one that fails, placed at the
op: its function, block, index and location reference. For example, it says
"the op owns a region: no op may own one yet", "block `^l` does not end
with a terminator", or "the op has 2 operands, and its op instance takes 3".
It checks each successor and each use as the blocks above say. It reads the
symbol table and the location table through a
{ref "The-fir-specification--Validation--The-validation-check"}[lookup].

*Theorem:* for every dialect whose types can be compared and whose own
rules can be decided, every lookup that agrees with the module context
$`C`, every function $`f`, every block $`b` of $`\mathrm{blocks}(f)`, every index
$`i` and op $`o`, with the tables built from $`\mathrm{allblocks}(f)` and
$`n = |\mathrm{body}(b)|`, the check gives no problem exactly when the op
is valid:

$$`\begin{aligned} & \mathrm{opproblems}(o) = \epsilon \\ \iff\ & C, f, b, i \vdash o~\text{valid} \end{aligned}`
:::

:::readable Fir.eq_beq_iff Fir.or_isEmpty_eq_true (fingerprint := "9153842687865872429")
*Theorems: two facts about truth values.* For every truth value $`a` and
numbers $`n` and $`m`, $`a` is the truth value of the test $`n = m`
exactly when this holds: $`a` is true if and only if $`n = m`. For every truth value $`a` and list $`l`
of successors, "$`a` or $`l` is empty" is true exactly when $`l` is empty
whenever $`a` is false. The proof that the check of an op decides its rule
uses them for the premises about terminators and successors.
:::
