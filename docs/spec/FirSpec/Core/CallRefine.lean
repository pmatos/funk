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

:::moduleDocs (fingerprint := "8510722386506462294")
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
below, and refined arguments with memory, hold for every core module, valid
or not, where the
{ref "The-fir-specification--Execution--What-the-lawful-class-gives"}[lawful class]
would give them only for valid modules.
:::

:::readable Fir.Core.Ty.Finite Fir.Core.Ty.values Fir.Core.Ty.mem_values Fir.Core.argVectors Fir.Core.mem_argVectors (pin := Fir.ChoiceTree.allBits) (pin := Fir.Core.Ty.toType) (pin := Fir.Core.floatWidth) (fingerprint := "1998525394283694137")
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

No list holds the values of $`\mathsf{ptr}\langle N \rangle`, so the
list takes the proof that its type has finitely many values. The argument
vectors of a list of types $`t_1, \dots, t_n` are
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

:::readable Fir.Core.replaceBody_isRefinedBy (pin := Fir.Func.runs) (pin := Fir.FuncRuns.IsRefinedBy) (fingerprint := "9393836866542943365")
*Theorem: congruence in the callee, for core functions.* Let $`M` be a
{ref "The-fir-specification--Validation--The-general-rules"}[valid]
core module, $`g` a function of $`M` with the symbol $`s` and no pointer
parameter, and $`b` a region. Let the runs in the set monad of $`g[s \leftarrow b]` in
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

The theorem is stated over the runs in the set monad, not over the runs of
core functions, which are their runs with memory. Congruence with memory,
{ref "The-fir-specification--Memory--Core-functions-with-memory"}[with a bound on the new callee's runs],
stands beside it; whether this form goes waits for the human's ruling on
#373.

The comparison is between real behaviours when the new function is valid
in the old module's context: then the new module is valid, and neither
module's runs have a stuck path. A body that is stuck at once, such as
one whose entry block declares arguments, meets the hypothesis with an
empty behaviour, which refines every source.
:::

:::readable Fir.Core.caller_isRefinedBy (pin := Fir.Func.runs) (pin := Fir.FuncRuns.IsRefinedBy) (fingerprint := "8806947217049377994")
*Theorem: every other function, a caller or not, is refined by itself.*
Under the hypotheses of the previous theorem, for every function $`f` of
$`M` whose symbol is not $`s`, the runs of $`f` itself in
$`M[s \leftarrow b]` refine its runs in $`M`.

This is the case that an optimizer meets: it rewrites one function, and
every other function, unchanged, must still be correct in the module
that holds the new one, whether it calls the rewritten function, directly
or not, or does not.
:::
