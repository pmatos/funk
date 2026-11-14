import Fir.Core.ValidRuns
import Fir.Execution.Modes
import Fir.Execution.Replace

/-!
# Calls refine as their arguments and callees do

`call` is a poison exception with no rule of its own, and no obligation
of its own (ADR-2026-10-29-2006). The obligations' counterparts for calls
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

Both are stated over the runs of core functions, which are their runs with
memory (the sections on core functions with memory and on congruence in a
core callee). They follow from the general theorems,
whose hypotheses the core dialect meets, and this section gives what they
ask that needs no memory: every core terminator and every core op with no
callee is monotone, each by the obligation that its family proves, at every
width. That is every core op but `call`, whose way to go on is its callee's
run. The core's congruence asks for no finitely many argument vectors, in
either form, since every core op has finitely many outcomes (#214).

The section also lists the argument vectors of a callee whose parameter
types have finitely many values, which the general forms of congruence with
finitely many argument vectors ask for. An integer or float type has
finitely many values: poison and the 2^N bit vectors of `iN`, poison and the
bit vectors of `1 + e + m` bits of `float<e,m>`. A pointer type has
infinitely many: poison and a pointer for every allocation and every
offset.

The general theorems ask monotonicity of every terminator and every op
with no callee among the ops of the modules' functions and of the
function that runs
(`docs/decisions/semantics-refinement.md#the-ops-a-run-reaches`). The core dialect meets it with
its ops' own obligations, which hold at every width, `i0` included, so
for every function of every module, valid or not, and refined arguments
use them, so they ask for no valid module. The lawful class covers only the
instances that validation accepts (ADR-2026-10-29-2006), so it gives
monotonicity only for the functions of valid modules (the section on what
the lawful class gives); congruence with memory goes through it, so it asks
for a valid module.
-/

namespace Fir.Core

/-- Every core terminator and every core op with no callee is monotone, at
every width: every core op but `call`. `alloca` has no rule in the set
monad, so no outcome there, and is monotone in it at once; it is monotone
with memory by its own rule. -/
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
  | .fcmp p fl e m, _ => fcmp_monotone p fl e m
  | .fbin o fl e m, _ => fbin_monotone o fl e m
  | .funary o fl e m, _ => funary_monotone o fl e m
  | .fma fl e m, _ => fma_monotone fl e m
  | .select w, _ => select_monotone w
  | .zext m n, _ => zext_monotone m n
  | .sext m n, _ => sext_monotone m n
  | .trunc m n, _ => trunc_monotone m n
  | .toBits e m, _ => toBits_monotone e m
  | .ofBits e m, _ => ofBits_monotone e m
  | .sitofp n e m, _ => intToFloat_monotone n e m true
  | .uitofp n e m, _ => intToFloat_monotone n e m false
  | .fpext e m e' m', _ => convertFloat_monotone e m e' m' true
  | .fptrunc e m e' m', _ => convertFloat_monotone e m e' m' false
  | .ptradd n w, _ => ptradd_monotone n w
  | .fptosi e m n, _ => floatToInt_monotone e m n true
  | .fptoui e m n, _ => floatToInt_monotone e m n false
  | .freeze w, _ => freeze_monotone w
  | .poison w, _ => poison_monotone w
  | .br, _ => br_monotone
  | .condBr, _ => condBr_monotone
  | .ret ts, _ => ret_monotone ts
  | .unreachable, _ => unreachable_monotone
  | .call .., h => by rcases h with h | h <;> cases h
  | .alloca .., _ => fun _ _ _ => ⟨fun _ _ he => he.elim, fun h => nomatch h⟩

/-- Every terminator and every op with no callee of every core function is
monotone, valid or not. -/
theorem opsMonotone_all (f : Func CoreDialect) : f.OpsMonotone :=
  fun _ _ o _ h => Op.monotone_all o.op h

/-- A core type has finitely many values when it is an integer or a float
type. A pointer type has infinitely many. -/
def Ty.Finite : Ty → Prop
  | .int _ | .float _ _ => True
  | .ptr _ => False

/-- Every value of a core type with finitely many values, an integer or a
float type: poison and each bit vector of its width. A pointer type's values
are infinitely many, so no list holds them, and the proof that the type is
finite rules it out. -/
def Ty.values : (t : Ty) → t.Finite → List ⟦t⟧
  | .int w, _ => .poison :: (ChoiceTree.allBits w).map .value
  | .float e m, _ => .poison :: (ChoiceTree.allBits (floatWidth e m)).map .value
  | .ptr _, h => (h : False).elim

/-- Every value of a core type with finitely many values is one of its
values. -/
theorem Ty.mem_values : ∀ {t : Ty} (h : t.Finite) (v : ⟦t⟧), v ∈ t.values h
  | .int _, _, .poison => List.mem_cons_self
  | .int _, _, .value b =>
    List.mem_cons_of_mem _ (List.mem_map_of_mem (ChoiceTree.mem_allBits b))
  | .float _ _, _, .poison => List.mem_cons_self
  | .float _ _, _, .value b =>
    List.mem_cons_of_mem _ (List.mem_map_of_mem (ChoiceTree.mem_allBits b))
  | .ptr _, h, _ => (h : False).elim

/-- Every argument vector of the types `ts`, each with finitely many
values. -/
def argVectors : (ts : List Ty) → (∀ t ∈ ts, t.Finite) → List (HVector toType ts)
  | [], _ => [.nil]
  | t :: ts, h => (t.values (h t List.mem_cons_self)).flatMap fun v =>
    (argVectors ts fun u hu => h u (List.mem_cons_of_mem _ hu)).map (.cons v)

/-- Every argument vector of the types `ts`, each with finitely many
values, is one of them. -/
theorem mem_argVectors : ∀ {ts : List Ty} (h : ∀ t ∈ ts, t.Finite)
    (a : HVector toType ts), a ∈ argVectors ts h
  | [], _, .nil => List.mem_singleton_self _
  | _ :: _, _, .cons v a => List.mem_flatMap.2 ⟨v, Ty.mem_values _ v,
      List.mem_map_of_mem (mem_argVectors _ a)⟩

end Fir.Core
