import Fir.Core.ArithLaws
import Fir.Core.WrapLaws
import Fir.Core.ControlLaws
import Fir.Core.Validation
import Fir.Execution.Progress

/-!
# The tracer subset

The runs of a function of a core module, in the set monad, are its runs on
each argument vector of its parameter types, poison included, at each
budget. The refinement of core functions in the set monad is about them,
and the equivalence experiment of #282 compares them.

The tracer subset is the ops of the roadmap's tracer bullet, the one tiny
program that went first through every layer: `const`, `add` without flags
and `ret`. A valid function of the tracer subset runs straight: no op of
the subset calls a function, `const` and `add` are not terminators, and
`ret` returns its operands, which its validation rule makes values of the
function's result types.

A function's runs on one argument vector _run well_ when they meet the
three obligations of the section on fuel and progress. The section on core
functions with memory proves that the runs with memory of every valid
function of the tracer subset run well: it runs straight, so it runs within
itself, and the core dialect is lawful in its totality. So do those of every
valid core function without a `call` op, and of every function of every
valid core module, calls and recursion included.
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
    | .freeze _ | .poison _ | .br | .condBr | .unreachable | .call .. | .fconst .. | .fcmp ..
    | .fbin .. | .funary .. | .fma .. | .toBits .. | .ofBits .. | .sitofp .. | .uitofp ..
    | .fpext .. | .fptrunc .. | .ptradd .. | .fptosi .. | .fptoui .. =>
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

/-- The three obligations of the section on fuel and progress, for the
runs of one function on one argument vector. -/
structure RunsWell (run : Nat → Run Obs) : Prop where
  fuelMonotone : FuelMonotone run
  progress : Progress run
  neverStuck : NeverStuck run

end Fir.Core
