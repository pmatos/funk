import Fir.Core.Runs
import Fir.Core.BitwiseLaws
import Fir.Core.FreezeLaws
import Fir.Core.WidthLaws
import Fir.Core.DivLaws
import Fir.Core.CompareLaws
import Fir.Core.BranchLaws
import Fir.Execution.Jumps

/-!
# Every core function without calls

The three obligations of the section on fuel and progress hold for every
valid function of the core dialect that has no `call` op (`CallFree`), on
every argument vector of its parameter types, poison included:
`Core.callFree_fuelMonotone`, `Core.callFree_progress` and
`Core.callFree_neverStuck`. Branches and loops are included. They follow
from the general theorems of the previous sections:

* fuel monotonicity holds for every function of every module
  (`Func.fuelMonotone`);
* every valid core function runs within itself (`Core.local_of_valid`): no
  core op calls a function yet; `br` and `cond_br` go only to successors
  they have (`Core.br_goto_lt`, `Core.condBr_goto_lt`) and give no
  results; and `ret`, the only core op whose exit returns, returns values
  of the function's result types, by its validation rule. So no path of
  its run is stuck (`Func.neverStuck_of_local`);
* every core op but `call` is total, by the obligations that each family
  proves of its ops (`Core.Op.total`). So such a function's run has an
  outcome at every budget (`Func.progress_of_local`).

`call` is left out. It has no rules until #20 names its callee, and an op
without rules has no outcome (ADR-2026-10-30-1855). So no claim is made
here of a function that has a `call` op, though `NeverStuck` would hold of
it only vacuously, on the paths that reach the call. #20 extends these
theorems to calls and recursion.
-/

namespace Fir.Core

/-- The op is a `call`. -/
def Op.isCall : Op → Bool
  | .call .. => true
  | _ => false

/-- No op of the function is a `call`. -/
def CallFree (f : Func CoreDialect) : Prop :=
  ∀ b ∈ f.blocks, ∀ o ∈ b.body, o.op.isCall = false

instance (f : Func CoreDialect) : Decidable (CallFree f) :=
  inferInstanceAs (Decidable (∀ b ∈ f.blocks, ∀ o ∈ b.body, o.op.isCall = false))

/-- Every core op but `call` is total. -/
theorem Op.total : (op : Op) → op.isCall = false → OpTotal (d := CoreDialect) op
  | .const w v, _ => const_total w v
  | .add w f, _ => add_total w f
  | .sub w f, _ => sub_total w f
  | .mul w f, _ => mul_total w f
  | .sdiv w x, _ => sdiv_total w x
  | .udiv w x, _ => udiv_total w x
  | .srem w, _ => srem_total w
  | .urem w, _ => urem_total w
  | .and w, _ => and_total w
  | .or w, _ => or_total w
  | .xor w, _ => xor_total w
  | .shl w, _ => shl_total w
  | .lshr w, _ => lshr_total w
  | .ashr w, _ => ashr_total w
  | .icmp p w, _ => icmp_total p w
  | .select w, _ => select_total w
  | .zext m n, _ => zext_total m n
  | .sext m n, _ => sext_total m n
  | .trunc m n, _ => trunc_total m n
  | .freeze w, _ => freeze_total w
  | .br, _ => br_total
  | .condBr, _ => condBr_total
  | .ret ts, _ => ret_total ts
  | .call .., h => nomatch h

/-- A core terminator that jumps goes to a successor that it has, and gives
no results. -/
theorem Op.exit_goto (op : Op) (args : HVector toType (Fir.sig (d := CoreDialect) op)) {i : Nat}
    (hT : Fir.isTerminator (d := CoreDialect) op = true)
    (h : DialectDenote.exit (m := SetM) (d := CoreDialect) op args (.ok (.goto i))) :
    i < Fir.succCount (d := CoreDialect) op ∧ Fir.returnTypes (d := CoreDialect) op = [] := by
  cases op with
  | br => exact ⟨br_goto_lt args h, rfl⟩
  | condBr => exact ⟨condBr_goto_lt args h, rfl⟩
  | ret _ => cases h
  | _ => cases hT

/-- The only core op whose exit returns is `ret`. -/
theorem Op.exit_ret (op : Op) (args : HVector toType (Fir.sig (d := CoreDialect) op))
    (h : DialectDenote.exit (m := SetM) (d := CoreDialect) op args (.ok .ret)) :
    ∃ ts, op = .ret ts := by
  cases op with
  | ret ts => exact ⟨ts, rfl⟩
  | br => cases h
  | condBr =>
    match args, h with
    | .cons c .nil, h =>
      have h' := (condBr_exit c _).1 h
      cases c with
      | poison => cases h'
      | value x =>
        simp only [condBrExit] at h'
        split at h' <;> cases h'
  | _ => cases h

/-- Every valid core function runs within itself. -/
theorem local_of_valid {ctx : ModuleContext CoreDialect} {f : Func CoreDialect}
    (hv : f.Valid ctx) : f.Local where
  noCall _ _ _ _ := rfl
  jumps _ _ o _ hT args _ h := Op.exit_goto o.op args hT h
  returns b hb o ho _ args h := by
    obtain ⟨ts, hts⟩ := Op.exit_ret o.op args h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    have hvalid : validOp ⟨ctx.symbols, f.results⟩ b.body[i].op :=
      (hv.ops b hb i b.body[i] (List.getElem?_eq_getElem hi)).2.2.2.2.2.2.2.2.2.1
    rw [hts] at hvalid ⊢
    exact hvalid

/-- Every op of a function without calls is total. -/
theorem total_of_callFree {f : Func CoreDialect} (hc : CallFree f) :
    ∀ b ∈ f.blocks, ∀ o ∈ b.body, OpTotal o.op :=
  fun b hb o ho => o.op.total (hc b hb o ho)

variable {M : Module CoreDialect} {f : Func CoreDialect}

/-- A function without calls that is valid in its module runs well on
every argument vector, jumps and loops included. -/
theorem callFree_runsWell (hv : f.Valid M.context) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : RunsWell (funcRuns M f args) :=
  ⟨Func.fuelMonotone M f args,
    Func.progress_of_local hv (local_of_valid hv) (total_of_callFree hc) M args,
    Func.neverStuck_of_local hv (local_of_valid hv) M args⟩

/-- More fuel never changes how a run of a valid core function without
calls returns or hits UB. -/
theorem callFree_fuelMonotone (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : FuelMonotone (funcRuns M f args) :=
  (callFree_runsWell (hM.funcs f hf) hc args).fuelMonotone

/-- A run of a valid core function without calls has an outcome at every
budget. -/
theorem callFree_progress (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : Progress (funcRuns M f args) :=
  (callFree_runsWell (hM.funcs f hf) hc args).progress

/-- No path of a run of a valid core function without calls is stuck. -/
theorem callFree_neverStuck (hM : M.Valid) (hf : f ∈ M.funcs) (hc : CallFree f)
    (args : HVector toType (f.params.map (·.2))) : NeverStuck (funcRuns M f args) :=
  (callFree_runsWell (hM.funcs f hf) hc args).neverStuck

end Fir.Core
