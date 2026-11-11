import Fir.Core.ArithLaws
import Fir.Core.WrapLaws
import Fir.Core.ControlLaws
import Fir.Core.Validation
import Fir.Execution.Progress

/-!
# The tracer subset's three obligations

The runs of a function of a core module are its runs in the set monad on
each argument vector of its parameter types, poison included, at each
budget. They are the runs of a core function in the sense of refinement,
so the refinement of core functions is about them.

The three obligations of the section on fuel and progress hold for every
valid function whose ops are in the tracer subset, on every argument
vector. The tracer subset is the ops of the roadmap's tracer bullet, the
one tiny program that went first through every layer: `const`, `add`
without flags and `ret`.

The proofs are the general theorems of the previous sections, applied to
the core dialect. Fuel monotonicity holds for every function of every
module. Progress and no stuck path hold for every valid function whose
ops run straight to a return and are total. A valid function of the
tracer subset runs straight: no op of the subset calls a function,
`const` and `add` are not terminators, and `ret` returns its operands,
which its validation rule makes values of the function's result types.
Each of the three ops is total.

Every valid core function without a `call` op meets the three obligations
too, branches and loops included, as the section on core functions
without calls proves, and so does every function of every valid core
module, calls and recursion included, as the section on core functions
with calls proves.
-/

namespace Fir.Core

/-- The runs of the function `f` of the core module `M`: its run on each
argument vector of its parameter types, poison included, at each budget. -/
def funcRuns (M : Module CoreDialect) (f : Func CoreDialect) : FuncRuns (f.params.map (·.2)) :=
  f.runs M

/-- An op of the tracer subset of #10: `const`, `add` without flags, or
`ret`. -/
def Op.InTracer : Op → Prop
  | .const _ _ => True
  | .add _ f => f = {}
  | .ret _ => True
  | _ => False

/-- Every op of the function is in the tracer subset. -/
def InTracer (f : Func CoreDialect) : Prop :=
  ∀ b ∈ f.blocks, ∀ o ∈ b.body, o.op.InTracer

/-- A valid function of the tracer subset runs straight to a return. -/
theorem straight_of_tracer {ctx : ModuleContext CoreDialect} {f : Func CoreDialect}
    (hv : f.Valid ctx) (ht : InTracer f) : f.Straight where
  noCall b hb o ho := by
    have hop := ht b hb o ho
    revert hop
    match o.op with
    | .const _ _ | .add _ _ | .ret _ => intro _; rfl
    | .sub .. | .mul .. | .sdiv .. | .udiv .. | .srem _ | .urem _ | .and _ | .or _ | .xor _
    | .shl _ | .lshr _ | .ashr _ | .icmp .. | .select _ | .zext .. | .sext .. | .trunc ..
    | .freeze _ | .poison _ | .br | .condBr | .unreachable | .call .. | .fconst .. | .fcmp .. =>
      intro h; exact False.elim h
  noJump b hb o ho args i h := by
    have hop := ht b hb o ho
    revert args h
    match o.op, hop with
    | .const _ _, _ | .add _ _, _ => intro _ h; exact h
    | .ret _, _ => intro _ h; cases h
  returns b hb o ho hT := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hov := hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)
    have hvalid : validOp ⟨ctx.symbols, f.results⟩ b.body[i].op := hov.2.2.2.2.2.2.2.2.2.1
    have hop := ht b hb _ ho
    revert hT hvalid
    match b.body[i].op, hop with
    | .const _ _, _ | .add _ _, _ => intro hT; cases hT
    | .ret _, _ => intro _ hvalid; exact hvalid

/-- Every op of the tracer subset is total. -/
theorem total_of_tracer {f : Func CoreDialect} (ht : InTracer f) :
    ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpTotal o.op := by
  intro b hb o ho
  have hop := ht b hb o ho
  revert hop
  match o.op with
  | .const w v => intro _; exact const_total w v
  | .add w f => intro _; exact add_total w f
  | .ret ts => intro _; exact ret_total ts
  | .sub .. | .mul .. | .sdiv .. | .udiv .. | .srem _ | .urem _ | .and _ | .or _ | .xor _
  | .shl _ | .lshr _ | .ashr _ | .icmp .. | .select _ | .zext .. | .sext .. | .trunc ..
  | .freeze _ | .poison _ | .br | .condBr | .unreachable | .call .. | .fconst .. | .fcmp .. =>
    intro h; exact False.elim h

variable {M : Module CoreDialect} {f : Func CoreDialect}

/-- The three obligations of the section on fuel and progress, for the
runs of one function on one argument vector. -/
structure RunsWell (run : Nat → Run Obs) : Prop where
  fuelMonotone : FuelMonotone run
  progress : Progress run
  neverStuck : NeverStuck run

/-- Every valid function of the tracer subset runs well on every argument
vector. -/
theorem tracer_runsWell (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (funcRuns M f args) :=
  have hv := hM.funcs f hf
  ⟨Func.fuelMonotone M f args, Func.progress hv (straight_of_tracer hv ht) (total_of_tracer ht) M args,
    Func.neverStuck hv (straight_of_tracer hv ht) M args⟩

/-- More fuel never changes how a run of a valid function of the tracer
subset returns or hits UB. -/
theorem tracer_fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (funcRuns M f args) :=
  (tracer_runsWell hM hf ht args).fuelMonotone

/-- A run of a valid function of the tracer subset has an outcome at every
budget. -/
theorem tracer_progress (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : Progress (funcRuns M f args) :=
  (tracer_runsWell hM hf ht args).progress

/-- No path of a run of a valid function of the tracer subset is stuck. -/
theorem tracer_neverStuck (hM : M.Valid) (hf : f ∈ M.funcs) (ht : InTracer f)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (funcRuns M f args) :=
  (tracer_runsWell hM hf ht args).neverStuck

end Fir.Core
