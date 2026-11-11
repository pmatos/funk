import VersoManual
import Fir.Execution.Summary
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on function summaries, which renders
`Fir.Execution.Summary` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "Function summaries: readable blocks" =>

:::moduleDocs (fingerprint := "6840252830234289169")
:::

:::readable Fir.MemSet.Sub Fir.Effects.Le (pin := Fir.MemSet.Has) (pin := Fir.instLEEffects) (fingerprint := "16971465220419375714")
*Definition: one effect set below another.* A set of memories $`M` is
_below_ $`N`, $`M \subseteq N`, when $`N` holds every memory that $`M`
holds. An effect set $`e` is below $`e'`, $`e \le e'`, when
$`\mathsf{reads}~e \subseteq \mathsf{reads}~e'`, and so for writes and
allocation, and each other effect of $`e` is an effect of $`e'`: $`e'`
has every effect that $`e` has.
:::

:::readable Fir.Effects.callerView (fingerprint := "4105496384024923075")
*Definition: what a caller sees.* $`\mathrm{caller}(e)` is $`e` without
$`\mathsf{control}`. A terminator of a callee ends a block of the callee,
so a call of it is not a terminator for its caller.
:::

:::readable Fir.MemSet.join Fir.Effects.join Fir.Effects.joinAll (fingerprint := "1628758086418682847")
*Definition: the join of effect sets.* The join of two sets of memories
is $`\top` when either is, and otherwise lists the memories of both. The
join $`e \sqcup e'` of two effect sets joins their sets of memories for
reads, writes and allocation, and has each other effect that either has.
The join of a list, $`\bigsqcup_i e_i`, joins its sets from the left,
from the empty set $`\emptyset`.
:::

:::readable Fir.Operation.call? Fir.SymbolTable.func? (fingerprint := "12311835251930273476")
*Definition: the call of an op, and the function of a symbol.* An op in
place $`o` _calls_ $`s`, $`\mathrm{call}(o) = s`, when it is not a
terminator and its dialect gives it the callee $`s`: the interpreter runs
a terminator by its exit, whatever its callee. The function of a symbol
table $`t` that $`s` names, $`t(s)`, is its first function with that
symbol, as the interpreter finds a callee.
:::

:::readable Fir.SymbolTable.callees (fingerprint := "12280298044229246773")
*Definition: the callees of a function.* The callees of a function $`f`
in a table $`t` are the symbols that the ops of $`f`, at any depth, call
and that name a function of $`t`, in order.
:::

:::readable Fir.SymbolTable.unseen Fir.countP_lt_of_mem Fir.SymbolTable.unseen_lt (fingerprint := "11354094714899778214")
*Definition and theorems: the functions left to see.* For a list of
symbols $`S`, $`\mathrm{unseen}_t(S)` counts the functions of $`t` whose
symbol is not in $`S`. A test that holds of no more elements than another,
and fails of an element of a list that the other holds of, counts fewer
elements of the list. So adding to $`S` a symbol not in it that names a
function of $`t` leaves fewer unseen.
:::

:::readable Fir.SymbolTable.reach (fingerprint := "3096077643177783369")
*Definition: the functions that a call may reach.* From a list of work
$`W` and a list of seen symbols $`S`, the walk $`\mathrm{reach}_t(W, S)`
takes the first symbol $`s` of $`W`:

* if $`s \in S`, or $`s` names no function of $`t`, it goes on with the
  rest of $`W`;
* otherwise it goes on with the callees of $`t(s)` before the rest of
  $`W`, and with $`s` seen, after $`S`.

When $`W` is empty it gives $`S`. Each step leaves one more function seen,
or shortens $`W`, so the walk ends, and it keeps its work in two lists,
so it needs no stack per call. $`\mathrm{reach}_t([s], [])` are the
functions that a call of $`s` may run: $`s`, and every function that a
function it reaches calls.
:::

:::readable Fir.SymbolTable.opOwn Fir.SymbolTable.funcOwn (fingerprint := "15048537052711931646")
*Definition: what a caller sees of an op and of a function's ops.* For an
op $`o` of a function of $`t`, $`\mathrm{own}_t(o)` is
$`\mathrm{caller}(\mathrm{eff}(o))`, or
$`\mathrm{caller}(\mathrm{eff}(o) \sqcup \top_{\mathit{eff}})` when $`o`
calls a symbol that names no function of $`t`: nothing narrower is known
of such a call. For a function $`f`,
$`\mathrm{own}_t(f) = \bigsqcup_{o} \mathrm{own}_t(o)` over the ops of
$`f` at any depth.
:::

:::readable Fir.SymbolTable.summary (fingerprint := "17621088214722189450")
*Definition: the summary of a function.* The summary of the function of
$`t` that $`s` names is the join of what a caller sees of the ops of every
function that it reaches:

$$`\mathrm{sum}_t(s) = \bigsqcup_{g \in \mathrm{reach}_t([s], [])} \mathrm{own}_t(t(g))`

A symbol that names no function has the empty summary. Recursion adds
nothing: a function that a walk has seen is not seen again.
:::

:::readable Fir.SymbolTable.opEffects (fingerprint := "14975733603493052991")
*Definition: the effects of an op in place.* An op $`o` of a function of
$`t` has $`\mathrm{eff}_t(o) = \mathrm{eff}(o)` when it calls nothing,
$`\mathrm{eff}(o) \sqcup \mathrm{sum}_t(s)` when it calls a function
$`s` of $`t`, and
$`\mathrm{eff}(o) \sqcup \mathrm{caller}(\top_{\mathit{eff}})` when it
calls a symbol that names no function of $`t`. So a call carries its
callee's effects (ADR-2026-11-10-2108).
:::
