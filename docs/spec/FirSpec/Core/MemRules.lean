import VersoManual
import Fir.Core.MemRules
import FirSpecSite.ReadableElab

open Verso.Genre Manual
open FirSpecSite

/-!
The readable blocks of the section on the core's rules with memory, which
renders `Fir.Core.MemRules` (ADR-2026-11-05-2012). Each block explains
declarations of that module and pins their fingerprint; the build fails
when the Lean changes under it.
-/

#doc (Manual) "The core's rules with memory: readable blocks" =>

:::moduleDocs (fingerprint := "7897766060644813517")
:::

:::readable Fir.Core.freezeValue_map Fir.Core.ruleOfEv_map Fir.Core.exitOfEv_map (pin := Fir.MonadMorphism.KeepsChoiceUB) (pin := Fir.Core.freezeValue) (pin := Fir.Core.ruleOfEv) (pin := Fir.Core.exitOfEv) (fingerprint := "17668704330183444261")
*Theorem: the rules of `freeze`, the divisions and the terminators mean the
same in both monads.* For every monad morphism $`\varphi` that
{ref "The-fir-specification--Execution--Monad-morphisms"}[keeps choice and UB],
$`\varphi` maps $`\mathsf{freeze}`'s rule on $`a` in $`m` to its rule on
$`a` in $`n`: $`a` itself, or bits chosen once when $`a` is poison. It maps
a {ref "The-fir-specification--Execution--Division-rules"}[division rule]
made from a function $`g` to a way to end, on every two operands of
$`\mathsf{i}w`, to the same rule in $`n`, and a
{ref "The-fir-specification--Execution--Branch-rules"}[terminator rule]
made from a way to end, such as $`\mathsf{cond\_br}`'s or
$`\mathsf{unreachable}`'s, to the same rule in $`n`: a result maps to the
same result, and UB to UB for the same reason.
:::

:::readable Fir.Core.denoteIn_mapsDenote (pin := Fir.Core.denoteIn) (pin := Fir.MonadMorphism.MapsDenote) (fingerprint := "2231277382733149318")
*Theorem: every core op means the same in both monads.* Let $`\varphi` be
a monad morphism from $`m` to $`n` that keeps choice and UB, and let
$`z_m` and $`z_n` say what an op with no rule does in $`m` and in $`n`, with
$`\varphi(z_m(p)) = z_n(p)` for every op $`p`. Then $`\varphi`
{ref "The-fir-specification--Execution--Monad-morphisms"}[maps] the core's
semantics in $`m` with $`z_m` to its semantics in $`n` with $`z_n`: for
every core op $`p` and operand vector $`\vec{v}`, it maps
$`\mathrm{denote}_p(\vec{v})` and $`\mathrm{exit}_p(\vec{v})` in $`m` to
those in $`n`.

The proof goes op by op. An op whose rule gives its result at once maps by
$`\varphi(\mathsf{pure}~r) = \mathsf{pure}~r`. $`\mathsf{freeze}`, the
float arithmetic and the conversions map by the theorems on their rules,
since $`\varphi` keeps a choice of bits; the divisions, $`\mathsf{cond\_br}`
and $`\mathsf{unreachable}` map by the theorems above, since $`\varphi`
keeps UB; and an op with no rule, as $`\mathsf{call}`, maps by the
hypothesis on $`z_m` and $`z_n`.
:::

:::readable Fir.Core.Op.memDenote? Fir.Core.Op.memExit? Fir.Core.memDenoteIn (pin := Fir.Core.denoteWith) (pin := Fir.MonadMemory) (pin := Fir.Core.allocaRule) (fingerprint := "3039986533218946549")
*Definition: the core's rules with memory.* Let $`m` be a monad with
choice, UB and the
{ref "The-fir-specification--Memory--The-memory-effect"}[memory effect] on
the memories of a run, where each memory $`y` of the run has the layout
entry $`\ell(y)` and the run names the core's memory $`x` as $`\rho(x)`.
The core's rules with memory are its rules in $`m`, at $`\ell` and
$`\rho`: an op that accesses the core's memory $`x` accesses the run's
memory $`\rho(x)` and reads its unit, byte order and pointer width from the
entry $`\ell(\rho(x))` (ADR-2026-11-13-0906). The rule with memory of
$`\mathsf{alloca}`, the one core op that touches memory, is its
{ref "The-fir-specification--Memory--Stack-allocation-rules"}[stack allocation rule],
which allocates in the memory $`\rho(N)` of its result $`\mathsf{ptr}\langle N \rangle`;
it has no rule without memory. Every other op touches no memory, so its
rule with memory, as an op that is not a terminator and as a terminator,
is its
{ref "The-fir-specification--Execution--Core-op-semantics"}[rule].

The core's semantics in $`m` at $`\ell` and $`\rho`, with $`z` for an op
with no rule, gives each op its rule with memory, and $`z(p)` to an op
$`p` that has none.
:::

:::readable Fir.Core.memDenoteIn_mapsDenote (fingerprint := "5332513432139245988")
*Theorem: the core's rules with memory mean the same in both monads.* For
monads $`m` and $`n` with choice, UB and the memory effect, a morphism
$`\varphi` from $`m` to $`n` that keeps choice, UB and allocation maps the
core's semantics with memory in $`m` at $`\ell` and $`\rho` to its
semantics with memory in $`n`, op by op, when it maps what an op with no
rule does. Every op but $`\mathsf{alloca}` follows from the theorem
above; $`\mathsf{alloca}` maps because $`\varphi` maps its allocation to
the same allocation in $`n`, and mapping the pointer to the result comes
after it in both. The
{ref "The-fir-specification--Memory--The-state-layer"}[translation through the layer]
keeps allocation.
:::

:::readable Fir.Core.memDenoteAt Fir.Core.instDialectMemDenote (pin := Fir.DialectMemDenote) (fingerprint := "718340430128983195")
*Definition: the core's semantics with memory.* At the layout entries
$`\ell` and the naming $`\rho`, the core's
{ref "The-fir-specification--Memory--Memory-obligations"}[semantics with memory]
runs each op by its rule with memory in the
{ref "The-fir-specification--Memory--The-state-layer"}[state layer] over
the set monad; an op with no rule has no way to end, as in the set monad.
It is given op by op, not by lifting the core's semantics in the set
monad, so an op that touches memory joins it with its own rule, as
$`\mathsf{alloca}` does.
:::

:::readable Fir.Core.Op.liftsSetM (pin := Fir.OpLiftsSetM) (fingerprint := "5082191809985086959")
*Theorem: every core op that touches no memory is tied.* For every core op
$`p` but $`\mathsf{alloca}`, at every layout
$`\ell` and naming $`\rho`, on every operand vector, $`p`'s meaning with
memory is its meaning in the set monad, lifted into the state layer: it
keeps the memories. Lifting
{ref "The-fir-specification--Memory--Runs-with-memory"}[keeps choice and UB],
and maps an op with no rule, which has no way to end in the set monad, to
one with no way to end in the layer, so the theorem above maps the core's
semantics in the set monad to its semantics with memory, op by op. The
core's obligations with memory follow from each op's own tie
({ref "The-fir-specification--Memory--Core-functions-with-memory"}[core functions with memory]).
$`\mathsf{alloca}` is not tied: it has no rule in the set monad, and
meets each obligation with memory by
{ref "The-fir-specification--Memory--Stack-allocation-obligations"}[its own rule].
:::
