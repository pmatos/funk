import Fir.Core.Runs
import Fir.Core.BitwiseLaws
import Fir.Core.FreezeLaws
import Fir.Core.WidthLaws
import Fir.Core.DivLaws
import Fir.Core.CompareLaws
import Fir.Core.FloatCompareLaws
import Fir.Core.FloatArithLaws
import Fir.Core.BranchLaws
import Fir.Execution.Jumps

/-!
# Every core function without calls

The three obligations of the section on fuel and progress hold for every
valid function of the core dialect that has no `call` op, on every
argument vector of its parameter types, poison included. Branches and
loops are included. They follow from the general theorems of the previous
sections:

* fuel monotonicity holds for every function of every module;
* _every core op but `call` is total_, by the obligations that each family
  proves of its ops;
* _every valid core function without calls runs within itself_: none of
  its ops calls a function; `br` and `cond_br` go only to successors they
  have and give no results; and `ret`, the only core op whose exit
  returns, returns values of the function's result types, by its
  validation rule. So no path of its run is stuck, and, its ops being
  total, its run has an outcome at every budget.

A function with a `call` op is left out here: its run runs other functions of
its module, so these theorems, which ask only that the function itself be
valid, cannot cover it. They came first, while `call` had no rules
(`docs/decisions/fir-ref.md#an-op-without-rules`). The section on core
functions with calls extends them to calls and recursion, for every function of
a valid module.
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
  | .fconst e m v, _ => fconst_total e m v
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
  | .fcmp p fl e m, _ => fcmp_total p fl e m
  | .fbin o fl e m, _ => fbin_total o fl e m
  | .funary o fl e m, _ => funary_total o fl e m
  | .fma fl e m, _ => fma_total fl e m
  | .select w, _ => select_total w
  | .zext m n, _ => zext_total m n
  | .sext m n, _ => sext_total m n
  | .trunc m n, _ => trunc_total m n
  | .freeze w, _ => freeze_total w
  | .poison w, _ => poison_total w
  | .br, _ => br_total
  | .condBr, _ => condBr_total
  | .ret ts, _ => ret_total ts
  | .unreachable, _ => unreachable_total
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
  | unreachable => cases (unreachable_exit args _).1 h
  | _ => cases hT

/-- The only core op whose exit returns is `ret`. -/
theorem Op.exit_ret (op : Op) (args : HVector toType (Fir.sig (d := CoreDialect) op))
    (h : DialectDenote.exit (m := SetM) (d := CoreDialect) op args (.ok .ret)) :
    ∃ ts, op = .ret ts := by
  cases op with
  | ret ts => exact ⟨ts, rfl⟩
  | br => cases h
  | unreachable => cases (unreachable_exit args _).1 h
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

/-- A core op other than `call` calls no function. -/
theorem Op.callee_none : (op : Op) → op.isCall = false → callee? (d := CoreDialect) op = none := by
  intro op h
  cases op <;> first | rfl | cases h

/-- Every valid core function without a `call` op runs within itself. -/
theorem local_of_valid {ctx : ModuleContext CoreDialect} {f : Func CoreDialect}
    (hv : f.Valid ctx) (hc : CallFree f) : f.Local where
  noCall b hb o ho := o.op.callee_none (hc b hb o ho)
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
    Func.progress_of_local hv (local_of_valid hv hc) (total_of_callFree hc) M args,
    Func.neverStuck_of_local hv (local_of_valid hv hc) M args⟩

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
