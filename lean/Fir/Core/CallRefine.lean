import Fir.Core.ValidRuns
import Fir.Execution.Modes
import Fir.Execution.Replace

/-!
# Calls refine as their arguments and callees do

`call` is a poison exception, and its op-level obligations look only at a
stand-in, which says nothing about calls (ADR-2026-11-02-1156). Their real
counterparts hold at function level, for the functions of every core
module, calls and recursion included:

* _Refined arguments_ (`Core.args_isRefinedBy`). On arguments that refine
  others, a poison by any value, a function's observable behaviour
  refines its behaviour on those others. So a call on arguments that
  refine others refines the call on those others: its callee runs on
  them.
* _Congruence in the callee_ (`Core.replaceBody_isRefinedBy`). In a valid
  module, replacing the body of a function `@g` with one under which
  `@g`, run in the new module, refines `@g` in the old, as
  `FuncRuns.IsRefinedBy` asks of two `Core.FuncRuns`, refines every
  function of the module. A function other than `@g`, a caller of it or
  not, is refined by itself in the new module
  (`Core.caller_isRefinedBy`).

They follow from the general theorems of the sections on refined
arguments and on congruence in the callee, whose hypotheses the core
dialect meets:

* every core op is monotone (`Core.Op.monotone_all`), each by the
  obligation that its family proves, and `call` by its stand-in, which
  the interpreter never runs;
* the refinement of core values is reflexive and transitive
  (`Core.Ty.isRefinedBy_refl`, `Core.Ty.isRefinedBy_trans`);
* every core type has finitely many values: poison and the `2 ^ N` bit
  vectors of `iN`, and none of `ptr`. So every list of types has finitely
  many argument vectors (`Core.mem_argVectors`);
* the symbols of a valid module are unique.

Refined arguments need no validity: the theorem holds for every function
of every core module. For a function of a valid module, no path of either
run is stuck and both have an outcome at every budget (`Core.neverStuck`,
`Core.progress`), so the theorem compares real behaviours. Congruence in
the callee compares real behaviours when the new function is valid in
the old module's context: then the new module is valid
(`Module.valid_replaceBody`), and neither module's runs have a stuck
path. A body that gets stuck at once, such as one whose entry block
declares arguments, meets the hypothesis with an empty behaviour, which
refines every source.
-/

namespace Fir.Core

/-- Every core op is monotone, `call` by its stand-in, which the
interpreter never runs. -/
theorem Op.monotone_all : (op : Op) → OpMonotone (d := CoreDialect) op
  | .const w v => const_monotone w v
  | .add w f => add_monotone w f
  | .sub w f => sub_monotone w f
  | .mul w f => mul_monotone w f
  | .sdiv w x => sdiv_monotone w x
  | .udiv w x => udiv_monotone w x
  | .srem w => srem_monotone w
  | .urem w => urem_monotone w
  | .and w => and_monotone w
  | .or w => or_monotone w
  | .xor w => xor_monotone w
  | .shl w => shl_monotone w
  | .lshr w => lshr_monotone w
  | .ashr w => ashr_monotone w
  | .icmp p w => icmp_monotone p w
  | .select w => select_monotone w
  | .zext m n => zext_monotone m n
  | .sext m n => sext_monotone m n
  | .trunc m n => trunc_monotone m n
  | .freeze w => freeze_monotone w
  | .br => br_monotone
  | .condBr => condBr_monotone
  | .ret ts => ret_monotone ts
  | .call g ts rs => call_monotone g ts rs

/-- Every value of a core type: poison and each bit vector of `iN`, and
none of `ptr`. -/
def Ty.values : (t : Ty) → List ⟦t⟧
  | .int w => .poison :: (ChoiceTree.allBits w).map .value
  | .ptr => []

/-- Every value of a core type is one of its values. -/
theorem Ty.mem_values : ∀ {t : Ty} (v : ⟦t⟧), v ∈ t.values
  | .int _, .poison => List.mem_cons_self
  | .int _, .value b => List.mem_cons_of_mem _ (List.mem_map_of_mem (ChoiceTree.mem_allBits b))
  | .ptr, v => nomatch (v : Empty)

/-- Every argument vector of the types `ts`. -/
def argVectors : (ts : List Ty) → List (HVector toType ts)
  | [] => [.nil]
  | t :: ts => t.values.flatMap fun v => (argVectors ts).map (.cons v)

/-- Every argument vector of the types `ts` is one of them. -/
theorem mem_argVectors : ∀ {ts : List Ty} (a : HVector toType ts), a ∈ argVectors ts
  | [], .nil => List.mem_singleton_self _
  | _ :: _, .cons v a => List.mem_flatMap.2 ⟨v, Ty.mem_values v,
      List.mem_map_of_mem (mem_argVectors a)⟩

/-- Refined arguments: on arguments that refine others, a poison by any
value, the observable behaviour of every function of every core module
refines its behaviour on those others, calls and recursion included. -/
theorem args_isRefinedBy (M : Module CoreDialect) (f : Func CoreDialect)
    {a a' : HVector toType (f.params.map (·.2))} (h : a.Forall₂ TyRefinement.IsRefinedBy a') :
    observable (funcRuns M f a) ⊑ observable (funcRuns M f a') :=
  Func.runs_args_isRefinedBy Op.monotone_all M f h

variable {M : Module CoreDialect}

/-- Congruence in the callee: replacing the body of a function `@g` of a
valid core module with one under which `@g`, run in the new module,
refines `@g` in the old, refines every function of the module, calls and
recursion included. -/
theorem replaceBody_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (b : Region CoreDialect)
    (h : funcRuns M g ⊑ funcRuns (M.replaceBody g.name b) (g.replaceBody g.name b))
    {f : Func CoreDialect} (hf : f ∈ M.funcs) :
    funcRuns M f ⊑ funcRuns (M.replaceBody g.name b) (f.replaceBody g.name b) :=
  Func.runs_replaceBody_isRefinedBy Op.monotone_all Ty.isRefinedBy_refl Ty.isRefinedBy_trans
    hM.symbolsUnique hg b ⟨argVectors _, mem_argVectors⟩ h hf

/-- Every function of the module other than `@g`, a caller of it or not,
is refined by itself in the module with `@g`'s new body. -/
theorem caller_isRefinedBy (hM : M.Valid) {g : Func CoreDialect} (hg : g ∈ M.funcs)
    (b : Region CoreDialect)
    (h : funcRuns M g ⊑ funcRuns (M.replaceBody g.name b) (g.replaceBody g.name b))
    {f : Func CoreDialect} (hf : f ∈ M.funcs) (hfg : f.name ≠ g.name) :
    funcRuns M f ⊑ funcRuns (M.replaceBody g.name b) f := by
  have := replaceBody_isRefinedBy hM hg b h hf
  change funcRuns M f ⊑ funcRuns _ { f with body := if f.name = g.name then b else f.body } at this
  rwa [ite_eq_right hfg] at this

end Fir.Core
