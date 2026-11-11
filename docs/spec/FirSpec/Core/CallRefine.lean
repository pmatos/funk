import VersoManual
import Fir.Core.CallRefine
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on refinement through core calls, which
renders `Fir.Core.CallRefine` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Refinement through core calls: readable blocks" =>

:::moduleDocs (fingerprint := "16259356870740253104")
:::

:::readable Fir.Core.Op.monotone_all Fir.Core.opsMonotone_all (fingerprint := "17589815968064864618")
*Theorems: every core op that runs by its own rule is monotone, and so
every core function has monotone ops.* For every
{ref "The-fir-specification--Abstract-syntax--Core-ops"}[core op] $`o`,
at every width, if $`o` is a terminator or has no callee, then $`o` is
{ref "The-fir-specification--Execution--Poison-classes"}[monotone]. That
is every core op but $`\mathsf{call}`, and each is monotone by the
obligation that its family proves. So every core function, valid or not,
has
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops],
which is what the general refinement theorems ask.

The width $`0` is included, which validation rejects. So the theorems
below hold for every core module, valid or not, where the
{ref "The-fir-specification--Execution--What-the-lawful-class-gives"}[lawful class]
would give them only for valid modules.
:::

:::readable Fir.Core.Ty.Finite Fir.Core.Ty.values Fir.Core.Ty.mem_values Fir.Core.argVectors Fir.Core.mem_argVectors (pin := Fir.ChoiceTree.allBits) (pin := Fir.Core.Ty.toType) (pin := Fir.Core.floatWidth) (fingerprint := "4362277538974857739")
*Definitions and theorems: every value of a core type with finitely many
values, and every argument vector.* An integer and a float type have
finitely many values; a pointer type has infinitely many, one for every
allocation and offset. The values of a
{ref "The-fir-specification--Execution--Core-values"}[core type] with
finitely many values are listed:

* the values of $`\mathsf{i}N` are poison and the $`2^N` vectors of $`N`
  bits, in order from $`0` to $`2^N - 1`;
* the values of $`\mathsf{float}\langle e,m \rangle` are poison and the
  vectors of $`1 + e + m` bits, in the same order.

No list holds the values of $`\mathsf{ptr}\langle N \rangle`, which lists
none. The argument vectors of a list of types $`t_1, \dots, t_n` are
listed too: every choice of a value of $`t_1`, then of $`t_2`, up to
$`t_n`, and the one empty vector when $`n = 0`.

*Theorems:* every value of a core type $`t` with finitely many values is
in the list of values of $`t`, and when each of the types $`t^*` has
finitely many values, every vector of values of $`t^*` is in the list of
argument vectors of $`t^*`. So the parameter types of a core function with
no pointer parameter have finitely many argument vectors, which
{ref "The-fir-specification--Execution--Replacing-a-callee"}[congruence in the callee]
asks.
:::

:::readable Fir.Core.args_isRefinedBy (pin := Fir.Core.funcRuns) (fingerprint := "16784468175903825772")
*Theorem: refined arguments, for core functions.* For every core module
$`M`, every core function $`f`, of $`M` or not, valid or not, run in
$`M`, and all argument vectors
$`a` and $`a'` of the parameter types of $`f` with $`a_i \sqsubseteq a'_i`
for each $`i`:

$$`\mathrm{obs}(F_M(a)) \sqsubseteq \mathrm{obs}(F_M(a'))`

where $`F_M(a)` is the runs of $`f` in $`M` on $`a`, poison included,
and $`\mathrm{obs}` their observable behaviour. Calls and recursion are
included. So a call on arguments that refine others, a poison replaced by
any value, refines the call on those others: its callee runs on them. It
is the general theorem of
{ref "The-fir-specification--Execution--Refined-arguments"}[refined arguments],
with the monotone ops of the core dialect.

It needs no validity. For a function of a
{ref "The-fir-specification--Validation--The-general-rules"}[valid module],
no path of either run is stuck and both have an outcome at every budget,
as the section on
{ref "The-fir-specification--Execution--Core-functions-with-calls"}[core functions with calls]
proves, so the theorem compares real behaviours.
:::

:::readable Fir.Core.replaceBody_isRefinedBy (pin := Fir.Core.funcRuns) (pin := Fir.FuncRuns.IsRefinedBy) (fingerprint := "8597197980571865364")
*Theorem: congruence in the callee, for core functions.* Let $`M` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid]
core module, $`g` a function of $`M` with the symbol $`s` and no pointer
parameter, and $`b` a region. Let the runs of $`g[s \leftarrow b]` in
$`M[s \leftarrow b]` refine the runs of $`g` in $`M`: on every argument
vector, its observable behaviour in the new module refines that of $`g`
in the old. Then for every function $`f` of $`M`, the runs of
$`f[s \leftarrow b]` in $`M[s \leftarrow b]` refine the runs of $`f` in
$`M`. Calls and recursion are included.

Here $`M[s \leftarrow b]` is $`M` with the body $`b` in place of the body
of its function $`s`, as in the section on
{ref "The-fir-specification--Execution--Replacing-a-callee"}[replacing a callee],
whose general theorem this is. The core dialect meets its hypotheses:
every core function has
{ref "The-fir-specification--Execution--Returns-and-UB___-followed-back"}[monotone ops], the refinement of core values is
reflexive and transitive, the parameter types of $`g` have finitely many
values, and the symbols of a valid module are unique. A callee with a
pointer parameter has infinitely many argument vectors, and congruence for
it waits for the general theorem over such types (#214).

The comparison is between real behaviours when the new function is valid
in the old module's context: then the new module is valid, and neither
module's runs have a stuck path. A body that is stuck at once, such as
one whose entry block declares arguments, meets the hypothesis with an
empty behaviour, which refines every source.
:::

:::readable Fir.Core.caller_isRefinedBy (pin := Fir.Core.funcRuns) (pin := Fir.FuncRuns.IsRefinedBy) (fingerprint := "16463603510413641815")
*Theorem: every other function, a caller or not, is refined by itself.*
Under the hypotheses of the previous theorem, for every function $`f` of
$`M` whose symbol is not $`s`, the runs of $`f` itself in
$`M[s \leftarrow b]` refine its runs in $`M`.

This is the case that an optimizer meets: it rewrites one function, and
every other function, unchanged, must still be correct in the module
that holds the new one, whether it calls the rewritten function, directly
or not, or does not.
:::
