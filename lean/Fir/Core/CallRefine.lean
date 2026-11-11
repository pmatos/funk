import Fir.Core.ValidRuns
import Fir.Execution.Modes
import Fir.Execution.Replace

/-!
# Calls refine as their arguments and callees do

`call` is a poison exception with no rule of its own, and no obligation
of its own (ADR-2026-11-02-1514). The obligations' counterparts for calls
hold for whole functions, for the functions of every core module, calls
and recursion included:

* _Refined arguments._ On arguments that refine others, such as a poison
  replaced by any value of its type, a function's observable behaviour
  refines its behaviour on those others. So a call on arguments that
  refine others refines the call on those others: its callee runs on
  them.
* _Congruence in the callee._ In a valid module, replacing the body of a
  function `@g` with one under which `@g`, run in the new module, refines
  `@g` in the old, refines every function of the module. A function other
  than `@g`, a caller of it or not, is refined by itself in the new
  module.

They follow from the general theorems of the sections on refined
arguments and on replacing a callee, whose hypotheses the core dialect
meets:

* every core terminator and every core op with no callee is monotone,
  each by the obligation that its family proves, at every width: every
  core op but `call`, whose way to go on is its callee's run;
* every core type has finitely many values: poison and the 2^N bit
  vectors of `iN`, poison and the bit vectors of `1 + e + m` bits of
  `float<e,m>`, and none of `ptr`. So every list of types has finitely
  many argument vectors;
* the refinement of core values is reflexive and transitive;
* the symbols of a valid module are unique.

The general theorems ask monotonicity of every terminator and every op
with no callee among the ops of the modules' functions and of the
function that runs (ADR-2026-11-05-1715). The core dialect meets it with
its ops' own obligations, which hold at every width, `i0` included, so
for every function of every module, valid or not. The lawful class covers
only the instances that validation accepts (ADR-2026-11-02-1515), so it
gives it only for the functions of valid modules (the section on what the
lawful class gives); these theorems ask for no valid module, so they use
the ops' own obligations.

Refined arguments need no validity: the theorem holds for every function
of every core module. For a function of a valid module, no path of either
run is stuck and both have an outcome at every budget (the section on
core functions with calls), so the theorem compares real behaviours.
Congruence in the callee compares real behaviours when the new function
is valid in the old module's context: then the new module is valid, and
neither module's runs have a stuck path. A body that gets stuck at once,
such as one whose entry block declares arguments, meets the hypothesis
with an empty behaviour, which refines every source.
-/

namespace Fir.Core

/-- Every core terminator and every core op with no callee is monotone, at
every width: every core op but `call`. -/
theorem Op.monotone_all : (op : Op) →
    Fir.isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none →
    OpMonotone (d := CoreDialect) op
  | .const w v, _ => const_monotone w v
  | .fconst e m v, _ => fconst_monotone e m v
  | .add w f, _ => add_monotone w f
  | .sub w f, _ => sub_monotone w f
  | .mul w f, _ => mul_monotone w f
  | .sdiv w x, _ => sdiv_monotone w x
  | .udiv w x, _ => udiv_monotone w x
  | .srem w, _ => srem_monotone w
  | .urem w, _ => urem_monotone w
  | .and w, _ => and_monotone w
  | .or w, _ => or_monotone w
  | .xor w, _ => xor_monotone w
  | .shl w, _ => shl_monotone w
  | .lshr w, _ => lshr_monotone w
  | .ashr w, _ => ashr_monotone w
  | .icmp p w, _ => icmp_monotone p w
  | .fcmp p e m, _ => fcmp_monotone p e m
  | .fbin o e m, _ => fbin_monotone o e m
  | .funary o e m, _ => funary_monotone o e m
  | .fma e m, _ => fma_monotone e m
  | .select w, _ => select_monotone w
  | .zext m n, _ => zext_monotone m n
  | .sext m n, _ => sext_monotone m n
  | .trunc m n, _ => trunc_monotone m n
  | .freeze w, _ => freeze_monotone w
  | .poison w, _ => poison_monotone w
  | .br, _ => br_monotone
  | .condBr, _ => condBr_monotone
  | .ret ts, _ => ret_monotone ts
  | .unreachable, _ => unreachable_monotone
  | .call .., h => by rcases h with h | h <;> cases h

/-- Every terminator and every op with no callee of every core function is
monotone, valid or not. -/
theorem opsMonotone_all (f : Func CoreDialect) : f.OpsMonotone :=
  fun _ _ o _ h => Op.monotone_all o.op h

/-- Every value of a core type: poison and each bit vector of `iN` or of a
float type, and none of `ptr`. -/
def Ty.values : (t : Ty) → List ⟦t⟧
  | .int w => .poison :: (ChoiceTree.allBits w).map .value
  | .float e m => .poison :: (ChoiceTree.allBits (floatWidth e m)).map .value
  | .ptr => []

/-- Every value of a core type is one of its values. -/
theorem Ty.mem_values : ∀ {t : Ty} (v : ⟦t⟧), v ∈ t.values
  | .int _, .poison => List.mem_cons_self
  | .int _, .value b => List.mem_cons_of_mem _ (List.mem_map_of_mem (ChoiceTree.mem_allBits b))
  | .float _ _, .poison => List.mem_cons_self
  | .float _ _, .value b =>
    List.mem_cons_of_mem _ (List.mem_map_of_mem (ChoiceTree.mem_allBits b))
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
  Func.runs_args_isRefinedBy M (fun g _ => opsMonotone_all g) f (opsMonotone_all f) h

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
  Func.runs_replaceBody_isRefinedBy (fun g _ => opsMonotone_all g) Ty.isRefinedBy_refl
    Ty.isRefinedBy_trans hM.symbolsUnique hg b ⟨argVectors _, mem_argVectors⟩ h hf

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
