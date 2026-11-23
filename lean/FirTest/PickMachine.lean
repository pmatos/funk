import FirTest.PickDialect
import FirRef.MachineModes

/-!
`fir-ref`'s machine on the picking dialect of `FirTest.PickDialect` (#235):
the runs of `@main` that pick their callee, run by `FirRef.Machine` in
exhaustive mode, end as the spec's interpreter ends them. The machine's
states for a rule that picks a callee and for a call (`Cur.pk`,
`Cur.call`) run here, and `Machine.exhaustive_eq` proves that the machine
computes the spec's tree for every dialect, this one included.

Every function of the module runs within it: in particular the rule of
`toy.pcall` picks only symbols that the module can call, which is what the
interpreter's progress asks of an op whose callee is picked.
-/

namespace FirTest.Pick

open Fir Memory FirRef

/-- How the machine's one path of a run ends, for the checks below. -/
def leafOutcome : Option (List (Machine.Leaf PickDialect Empty × Nat)) → String
  | some [(.ok (.ok (.ret [⟨.inl (.int 8), .value v⟩])), _)] => s!"ret {v.toNat}"
  | some [(.ok (.ok .fuelExhausted), _)] => "fuel"
  | some [(.ok (.error _), _)] => "stuck"
  | some [(.ub _, _)] => "ub"
  | _ => "other"

/-- The machine's run of `@main` at the selector `t`, on `%x = 5`, with
`fuel` steps, from the empty memories. -/
def machineMain (t : BitVec 8) (fuel : Nat) : String :=
  leafOutcome (Machine.exhaustive (ε := Empty) (N := Unit) (unit := fun _ => 0) (pickModule t)
    Memories.empty (main t) (.cons (.value 5) .nil) fuel 16)

#guard machineMain 0 10 == "ret 6"
#guard machineMain 1 10 == "ret 5"
#guard machineMain 2 10 == "ub"
#guard machineMain 3 10 == "ub"
#guard machineMain 4 10 == "ub"
#guard machineMain 9 10 == "ub"
#guard machineMain 0 6 == "ret 6"
#guard machineMain 0 5 == "fuel"
#guard machineMain 1 2 == "fuel"
-- The machine and the spec's interpreter agree on each of these runs.
#guard [0, 1, 2, 3, 4, 9].all fun t => [2, 5, 6, 10].all fun n => machineMain t n == runMain t n

/-- The rule of `toy.pcall` picks only symbols that the run can call. -/
theorem pickIn_ok {w : Nat} {table : List Name} {ok : Name → Bool} {t : PoisonOr (BitVec w)}
    {s : Name} (h : pickIn (m := SetM) table ok t (.ok s)) : ok s = true := by
  cases t with
  | poison => cases h
  | value v =>
    cases hs : table[v.toNat]? with
    | none => simp only [pickIn, hs] at h; cases h
    | some x =>
      simp only [pickIn, hs] at h
      by_cases hx : ok x = true
      · simp only [hx, ↓reduceIte] at h
        cases h
        exact hx
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
        cases h

/-- The rule of a picking op picks only symbols that the run can call. -/
theorem pick_ok (op : Op) (ok : Name → Bool) (args : HVector toType (Fir.sig (d := PickDialect) op))
    {s : Name} (h : DialectDenote.pick (d := PickDialect) (m := SetM) op ok args (.ok s)) :
    ok s = true := by
  cases op with
  | pcall w table =>
    match args, h with
    | .cons _ (.cons _ .nil), h => exact pickIn_ok h
  | _ => cases h

/-- No picking op names its callee. -/
theorem callee_ne_fixed (op : Op) (s : Name) : callee? (d := PickDialect) op ≠ some (.fixed s) := by
  cases op <;> simp [callee?]

/-- No exit of a picking op jumps. -/
theorem exit_ne_goto (op : Op) (args : HVector toType (Fir.sig (d := PickDialect) op)) (i : Nat) :
    ¬ DialectDenote.exit (d := PickDialect) (m := SetM) op args (.ok (.goto i)) := by
  cases op <;> intro h <;> cases h

/-- An op whose exit returns is `toy.ret`. -/
theorem exit_ret {op : Op} {args : HVector toType (Fir.sig (d := PickDialect) op)}
    (h : DialectDenote.exit (d := PickDialect) (m := SetM) op args (.ok .ret)) :
    ∃ w, op = .ret w := by
  cases op with
  | ret w => exact ⟨w, rfl⟩
  | _ => cases h

/-- Every function of the module runs within it: no op names a callee,
`toy.pcall` picks only symbols the module can call, no exit jumps, and
each `toy.ret` returns an `i8`, the result of its function. -/
theorem pickModule_inModule (t : BitVec 8) :
    ∀ g ∈ (pickModule t).funcs, g.InModule (pickModule t) := by
  intro g hg
  refine ⟨fun _ _ o _ _ s hc => absurd hc (callee_ne_fixed o.op s),
    fun _ _ o _ _ _ args s h => pick_ok o.op _ args h,
    fun _ _ o _ _ args i h => absurd h (exit_ne_goto o.op args i), ?_⟩
  intro b hb o ho _ args hx
  obtain ⟨w, hw⟩ := exit_ret hx
  simp only [pickModule, Module.funcs, List.filterMap, Item.func?, List.mem_cons,
    List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;>
    simp [Func.blocks, f, g, Pick.h, main, fn, mk] at hb <;>
    subst hb <;> dsimp only at ho <;> simp at ho <;>
    rcases ho with rfl | rfl | rfl <;> cases hw <;> rfl

end FirTest.Pick
