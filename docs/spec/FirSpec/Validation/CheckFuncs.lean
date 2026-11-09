import VersoManual
import Fir.Validation.CheckFuncs
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on checking functions, which renders
`Fir.Validation.CheckFuncs` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Checking functions: readable blocks" =>

:::moduleDocs (fingerprint := "11396718151567096626")
:::

:::readable Fir.Func.problem Fir.Func.blockProblem (fingerprint := "495569798519738376")
*Definition: a problem about a function, and about a block.* A
{ref "The-fir-specification--Validation--The-validation-check"}[problem]
about the function $`f` is placed at the symbol of $`f`. A problem about
its block $`b` is placed at the symbol of $`f`, the label of $`b`, and the
location reference of the first op of $`b`, when $`b` has an op.
:::

:::readable Fir.Func.entryProblems Fir.Func.entryProblems_eq_nil (fingerprint := "6428048307201822305")
*Definition and theorem: the check of the entry block.* The check of the
entry block gives "the function has no entry block" when the body has no
block, and "the entry block `^e` declares arguments: its arguments are the
function's parameters" when its entry block $`e` declares any.

*Theorem:* for every function $`f`, the check of its entry block gives no
problem exactly when $`\mathrm{blocks}(f) = e~b^*` for some block $`e`
that declares no arguments, the first premise of the
{ref "The-fir-specification--Validation--The-general-rules"}[rule of a valid function].
:::

:::readable Fir.Func.ruleProblem (fingerprint := "11410949032950985230")
*Definition: the problem of a broken function rule.* A function has no
location of its own. So when a function breaks its dialect's own rule over a
whole function, the problem "the function breaks a rule of its dialect"
names the function and its entry block, and has the location reference of
that block's first op. A function with no blocks has only its symbol.
:::

:::readable Fir.Func.problemsIn Fir.Func.problems (fingerprint := "2404998429050274037")
*Definition: the check of a function.* Given a
{ref "The-fir-specification--Validation--The-validation-check"}[lookup] and
a list of the function's blocks at any depth, the check of the function
$`f` builds its
{ref "The-fir-specification--Validation--Checking-ops"}[tables] once, and
gives, in this order:

* the problems of the entry block;
* "block `^l` is not reachable from the entry" for each top-level block
  that the
  {ref "The-fir-specification--Validation--Reachability-and-dominance___-decided"}[search]
  from the entry does not find;
* "label `^l` names more than one block" for each label that repeats one
  before it;
* "value `%x` is defined more than once" for each name that repeats one
  before it among the parameters and the definitions of the blocks;
* a problem for each value name and each label that is not spelled with
  name characters;
* "a result type of the function is not valid" for each result type that
  its dialect rejects, and a problem for each definition whose type it
  rejects;
* "block `^l` holds no ops" for each top-level block without ops;
* the problems of each op of each top-level block, in order;
* "the function breaks a rule of its dialect" when the function breaks its
  dialect's own rule over a whole function, at its entry block.

The check of $`f` in its module, $`\mathrm{problems}(f)`, runs this with
the list $`\mathrm{allblocks}(f)`.
:::

:::readable Fir.Func.valid_iff Fir.Func.reached_all Fir.Func.ops_all Fir.Func.types_all (fingerprint := "16203153610006954786")
*Theorems: the rule of a valid function, taken apart.* For every function
$`f`, module context $`C` and lookup:

* $`C \vdash f~\text{valid}` holds exactly when all of its premises hold,
  so the check can test them one by one;
* the search from the entry finds every top-level block exactly when every
  top-level block is reachable;
* when the lookup agrees with $`C`, the check of every op of every
  top-level block gives no problem exactly when every such op is valid;
* every type in $`\mathrm{types}(f)` is valid exactly when every result
  type of $`f` is valid and the type of every definition in
  $`\mathrm{defs}(f)` is valid.

Each turns one premise of the rule into the shape of a line of the check.
:::

:::readable Fir.Func.problems_eq_nil (fingerprint := "16442461881730532285")
*Theorem: the check of a function decides its validity.* For every dialect
whose types can be compared and whose own rules can be decided, every
module context $`C`, every lookup that agrees with $`C`, and every
function $`f`, the check of $`f` gives no problem exactly when $`f` is
valid in $`C`:

$$`\mathrm{problems}(f) = \epsilon \iff C \vdash f~\text{valid}`

So the check never rejects a valid function, and never accepts one that
breaks a rule.
:::
