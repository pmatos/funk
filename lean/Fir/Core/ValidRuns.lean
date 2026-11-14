import Fir.Core.CallFree
import Fir.Execution.Calls

/-!
# Every valid core function

Two facts about the ops of a valid core module give the three obligations
of the section on fuel and progress for the runs with memory of every
function of the module, on every argument vector of its parameter types,
poison included, calls and recursion included (the section on core
functions with memory). A function may call itself, or another function
that calls it back, and branches and loops are included.

* _Every core terminator and every core op with no callee is total_:
  these are every core op but `call`, each total by the obligations of its
  family, and `alloca` total with memory by its own rule. `call` needs no
  rule of its own: its way to go on is its callee's run, which the
  induction on the budget in the section on progress with calls covers.
* _Every core function valid in the context of a module runs within that
  module_. Validation's rule for `call @g` asks that the module's symbol
  table give `@g` the type of the call, its operand types and its result
  types, which is what a call needs; `br`, `cond_br`, `ret` and
  `unreachable` keep to the rules of their terminators, as for a function
  without calls.

The facts for core functions without calls need only the function's own
validity, in any context. These need the validity of its whole module,
whose functions it may call.
-/

namespace Fir.Core

/-- A core op that calls a function is `call`, of that function. -/
theorem Op.eq_call_of_callee {op : Op} {s : Name} (h : callee? (d := CoreDialect) op = some s) :
    ∃ ts rs, op = .call s ts rs := by
  cases op <;> (cases h; try exact ⟨_, _, rfl⟩)

/-- Every core terminator and every core op with no callee that touches no
memory is total in the set monad: every core op but `call` and `alloca`. -/
theorem Op.total_all (op : Op)
    (h : Fir.isTerminator (d := CoreDialect) op = true ∨ callee? (d := CoreDialect) op = none)
    (hm : op.touchesMemory = false) : OpTotal (d := CoreDialect) op := by
  cases hc : op.isCall with
  | false => exact op.total hc hm
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

end Fir.Core
