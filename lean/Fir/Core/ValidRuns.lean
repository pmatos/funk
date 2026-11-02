import Fir.Core.CallFree
import Fir.Execution.Calls

/-!
# Every valid core function

The three obligations of the section on fuel and progress hold for every
function of every valid core module, on every argument vector of its
parameter types, poison included, calls and recursion included:
`Core.fuelMonotone`, `Core.progress` and `Core.neverStuck`. A function may
call itself, or another function that calls it back, and branches and
loops are included. They follow from the general theorems of the previous
sections:

* fuel monotonicity holds for every function of every module
  (`Func.fuelMonotone`);
* every function of a valid core module runs within the module
  (`Core.inModule_of_valid`). Validation's rule for `call @g` asks that
  the module's symbol table give `@g` the type of the call, its operand
  types and its result types, which is what a call needs; `br`,
  `cond_br` and `ret` keep to the rules of their terminators, as for a
  function without calls. So no path of its run is stuck
  (`Func.neverStuck_of_inModule`);
* every core terminator and every core op with no callee is total
  (`Core.Op.total_all`), by the obligations of its family: every core op
  but `call`. So its run has an outcome at every budget
  (`Func.progress_of_inModule`). `call` needs no rule of its own: its way
  to go on is its callee's run, which the induction on the budget in the
  section on progress with calls covers (`Module.calls_hasPath`).

The theorems for core functions without calls (`Core.callFree_fuelMonotone`,
`Core.callFree_progress`, `Core.callFree_neverStuck`) keep their
statements. A function without calls runs within itself, so they need
only its own validity, in any context, where these need the validity of
its whole module, whose functions it may call.
-/

namespace Fir.Core

/-- A core op that calls a function is `call`, of that function. -/
theorem Op.eq_call_of_callee {op : Op} {s : Name} (h : callee? (d := CoreDialect) op = some s) :
    ∃ ts rs, op = .call s ts rs := by
  cases op <;> (cases h; try exact ⟨_, _, rfl⟩)

/-- Every core terminator and every core op with no callee is total: every
core op but `call`. -/
theorem Op.total_all (op : Op)
    (h : Fir.isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none) :
    OpTotal (d := CoreDialect) op := by
  cases hc : op.isCall with
  | false => exact op.total hc
  | true =>
    cases op <;> try cases hc
    all_goals rcases h with h | h <;> cases h

/-- Every function of a valid core module runs within the module: each
`call` names a function of the module of its type, by its validation rule,
and its terminators keep to their rules. -/
theorem inModule_of_valid {M : Module CoreDialect} {f : Func CoreDialect}
    (hv : f.Valid M.context) : f.InModule M where
  calls b hb o ho _ s h := by
    obtain ⟨ts, rs, hop⟩ := Op.eq_call_of_callee h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hvalid : validOp ⟨M.context.symbols, f.results⟩ b.body[i].op :=
      (hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)).2.2.2.2.2.2.2.2.2.1
    rw [hop] at hvalid ⊢
    exact hvalid
  jumps _ _ o _ hT args _ h := Op.exit_goto o.op args hT h
  returns b hb o ho _ args h := by
    obtain ⟨ts, hts⟩ := Op.exit_ret o.op args h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hvalid : validOp ⟨M.context.symbols, f.results⟩ b.body[i].op :=
      (hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)).2.2.2.2.2.2.2.2.2.1
    rw [hts] at hvalid ⊢
    exact hvalid

variable {M : Module CoreDialect} {f : Func CoreDialect}

/-- Every function of a valid core module runs well on every argument
vector, calls and recursion included. -/
theorem runsWell (hM : M.Valid) (hf : f ∈ M.funcs) (args : HVector toType (f.params.map (·.2))) :
    RunsWell (funcRuns M f args) :=
  have hm := fun g hg => inModule_of_valid (hM.funcs g hg)
  ⟨Func.fuelMonotone M f args,
    Func.progress_of_inModule hM.funcs hm (fun _ _ _ _ o _ hc => o.op.total_all hc) hf args,
    Func.neverStuck_of_inModule hM.funcs hm hf args⟩

/-- More fuel never changes how a run of a function of a valid core module
returns or hits UB. -/
theorem fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (funcRuns M f args) :=
  (runsWell hM hf args).fuelMonotone

/-- A run of a function of a valid core module has an outcome at every
budget, calls and recursion included. -/
theorem progress (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : Progress (funcRuns M f args) :=
  (runsWell hM hf args).progress

/-- No path of a run of a function of a valid core module is stuck, calls
and recursion included. -/
theorem neverStuck (hM : M.Valid) (hf : f ∈ M.funcs)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (funcRuns M f args) :=
  (runsWell hM hf args).neverStuck

end Fir.Core
