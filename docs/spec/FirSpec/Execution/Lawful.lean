import VersoManual
import Fir.Execution.Lawful
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on what the lawful class gives, which
renders `Fir.Execution.Lawful` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "What the lawful class gives: readable blocks" =>

:::moduleDocs (fingerprint := "2582150824750587004")
:::

:::readable Fir.Func.Valid.typesValid (pin := Fir.TypesValid) (pin := Fir.Func.Valid) (pin := Fir.Func.OpValid) (fingerprint := "17332324743421552018")
*Theorem: every op of a valid function is a valid op instance.* In every
dialect with its validation rules, let the function $`f` be
{ref "The-fir-specification--Validation--The-general-rules"}[valid]
in a context $`C`. Then every op of every block of $`f` has an
{ref "The-fir-specification--Abstract-syntax--Dialects"}[op instance]
{ref "The-fir-specification--Validation--The-general-rules"}[whose types validation accepts]:
each of its operand types and each of its
result types is a valid type of the dialect.

Validation checks each operand's type against the type of the value it
names, gives each result the type of a value that $`f` defines, and
accepts only valid types among the types that $`f` states. The poison
obligations speak only of such op instances (ADR-2026-11-02-1515), so
this is what lets them speak for every op of a valid module.
:::

:::readable Fir.Func.Valid.opsMonotone (pin := Fir.Func.OpsMonotone) (pin := Fir.TypesValid) (fingerprint := "3009843287580231830")
*Theorem: in a dialect monotone at valid op instances, a valid function
has monotone ops.* In every dialect with its validation rules and a
refinement of its values, suppose that every op instance whose types
validation accepts, and that is a terminator or has no callee, is
{ref "The-fir-specification--Execution--Poison-classes"}[monotone]. Then
every function that is valid in some context has
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops].

The general refinement theorems ask monotonicity only of the ops that a
run can reach (ADR-2026-11-05-1715), and those are valid op instances in
a valid module, by the previous theorem.
:::

:::readable Fir.Func.progress_of_lawful (pin := Fir.LawfulDialectPoison) (pin := Fir.Progress) (fingerprint := "9879526906783345535")
*Theorem: in a lawful dialect, a function of a module whose functions are
valid and run within it has progress.* Let the dialect be
{ref "The-fir-specification--Execution--Poison-classes"}[lawful]: its
valid op instances meet the poison obligations, among them that each one
that is a terminator or has no callee is total. Let every function of the
module $`M` be valid in a context $`C`, and run within $`M`, as the
section on
{ref "The-fir-specification--Execution--Progress-with-calls"}[progress with calls]
asks. Then for every function $`f` of $`M` and every argument vector $`a`
of its parameter types, the runs of $`f` on $`a` have
{ref "The-fir-specification--Execution--Fuel-and-progress"}[progress]:
an outcome at every budget. Calls and recursion are included.

Progress with calls asks totality of every terminator and every op with
no callee of the module, and the class gives it, since each is a valid op
instance. No path of such a run is stuck either, whatever its ops do, as
that section proves.
:::

:::readable Fir.Func.runs_args_isRefinedBy_of_lawful (pin := Fir.LawfulDialectPoison) (fingerprint := "12246780387192884151")
*Theorem: refined arguments, by the lawful class alone.* In every
{ref "The-fir-specification--Execution--Poison-classes"}[lawful] dialect, let every function of the module $`M` be valid in a context
$`C`. Then for every function $`f` of $`M` and all argument vectors $`a`
and $`a'` of its parameter types with $`a_i \sqsubseteq a'_i` for each
$`i`, a poison replaced by any value for example:

$$`\mathrm{obs}(F_M(a)) \sqsubseteq \mathrm{obs}(F_M(a'))`

where $`F_M(a)` is the runs of $`f` in $`M` on $`a`. Calls and recursion
are included. The class makes every terminator and every op with no
callee monotone at valid op instances, so every function of $`M` has
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops], and the theorem of
{ref "The-fir-specification--Execution--Refined-arguments"}[refined arguments]
applies.
:::

:::readable Fir.Func.runs_replaceBody_isRefinedBy_of_lawful (pin := Fir.LawfulDialectPoison) (pin := Fir.FuncRuns.IsRefinedBy) (fingerprint := "2470441501711249044")
*Theorem: congruence in the callee, by the lawful class alone.* In every
{ref "The-fir-specification--Execution--Poison-classes"}[lawful] dialect whose refinement of values is reflexive and transitive,
let $`M` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid module],
$`g` a function of $`M` with the symbol $`s` whose parameter types have
finitely many argument vectors, and $`b` a region. Let the runs of
$`g[s \leftarrow b]` in $`M[s \leftarrow b]` refine the runs of $`g` in
$`M`. Then for every function $`f` of $`M`, the runs of
$`f[s \leftarrow b]` in $`M[s \leftarrow b]` refine the runs of $`f` in
$`M`, whatever the new body. Calls and recursion are included.

Here $`M[s \leftarrow b]` is $`M` with the body $`b` in place of the body
of its function $`s`, as in the section on
{ref "The-fir-specification--Execution--Replacing-a-callee"}[replacing a callee].
That section asks monotone ops only of the old module's functions, which
are valid, so the class gives them, and the new body need not be valid.
:::
