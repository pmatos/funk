import Fir.Execution.SummaryLaws

/-!
# The summary is the least fixpoint of the calls

The summary of each function of a symbol table is a solution of the
inequalities that the calls between its functions set, and the least one
(ADR-2026-11-09-1541). An assignment of an effect set to each symbol of a
table is _closed_ when, for each function and each op of it at any depth:

* what a caller sees of the op's own effects is below the function's set,
  with every effect but control when the op calls a symbol that names no
  function of the table;
* and when the op calls a function of the table, that function's set is
  below the caller's.

The summary is closed, so the effects of every op in place, its callee's
included, are below its function's summary: a call carries its callee's
effects, and those of every function that the callee calls in turn,
recursion included. And the summary is below every closed assignment, so
it is the least fixpoint of the calls: it claims no effect that no op a
call may run declares.
-/

namespace Fir

variable {d : Dialect} [DialectSignature d] [DialectCall d] [DialectEffects d]
  {t : SymbolTable d}

/-- An assignment `T` of an effect set to each symbol of `t` is closed under
the calls of `t`: what a caller sees of each op of each function is below
the function's set, and so is the set of each function of `t` that the op
calls. -/
structure SymbolTable.Closed (t : SymbolTable d) (T : Name → Effects (DialectEffects.Mem d)) :
    Prop where
  own : ∀ s f, t.func? s = some f → ∀ o ∈ f.allOps, t.opOwn o ≤ T s
  calls : ∀ s f, t.func? s = some f → ∀ o ∈ f.allOps, ∀ c, o.call? = some c →
    (t.func? c).isSome → T c ≤ T s

/-- What a caller sees of a function's own ops is below the set of its
symbol in a closed assignment. -/
theorem SymbolTable.funcOwn_le {T : Name → Effects (DialectEffects.Mem d)} (hT : t.Closed T)
    {s : Name} {f : Func d} (hf : t.func? s = some f) : t.funcOwn f ≤ T s :=
  Effects.joinAll_le fun e he => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
    exact hT.own s f hf o ho

/-- The summary of a symbol is below its set in every closed assignment: the
summary is the least closed assignment. -/
theorem SymbolTable.summary_le {T : Name → Effects (DialectEffects.Mem d)} (hT : t.Closed T)
    (s : Name) : t.summary s ≤ T s := by
  have hreach : ∀ g ∈ t.reach [s] [], T g ≤ T s :=
    SymbolTable.reach_sub (C := fun g => T g ≤ T s)
      (fun g f hg hf c hc => by
        obtain ⟨hcs, o, ho, hoc⟩ := SymbolTable.mem_callees.1 hc
        exact Effects.le_trans (hT.calls g f hf o ho c hoc hcs) hg)
      (fun _ h => nomatch h) fun g hg => by
        rcases List.mem_singleton.1 hg with rfl
        exact Effects.le_refl _
  refine Effects.joinAll_le fun e he => ?_
  obtain ⟨g, hg, he⟩ := List.mem_filterMap.1 he
  obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.1 he
  exact Effects.le_trans (t.funcOwn_le hT hf) (hreach g hg)

/-- A function's own ops are below its summary. -/
theorem SymbolTable.funcOwn_le_summary {s : Name} {f : Func d} (hf : t.func? s = some f) :
    t.funcOwn f ≤ t.summary s :=
  Effects.le_joinAll (List.mem_filterMap.2 ⟨s,
    SymbolTable.mem_reach (.inr ⟨List.mem_singleton_self _, by simp [hf]⟩), by simp [hf]⟩)

omit [DialectEffects d] in
/-- A function that a function calls reaches nothing that its caller does
not. -/
theorem SymbolTable.reach_of_callee {s c : Name} {f : Func d} (hf : t.func? s = some f)
    (hc : c ∈ t.callees f) : ∀ g ∈ t.reach [c] [], g ∈ t.reach [s] [] := by
  have hclosed := SymbolTable.reach_closed (t := t) (work := [s]) (seen := [])
    (fun _ h => nomatch h)
  have hs : s ∈ t.reach [s] [] :=
    SymbolTable.mem_reach (.inr ⟨List.mem_singleton_self _, by simp [hf]⟩)
  exact SymbolTable.reach_sub (C := (· ∈ t.reach [s] []))
    (fun g f hg hf c hc => hclosed g hg f hf c hc) (fun _ h => nomatch h) fun g hg => by
      rcases List.mem_singleton.1 hg with rfl
      exact hclosed s hs f hf g hc

/-- The summary of a function that a function calls is below the caller's:
the callee reaches nothing that the caller does not. -/
theorem SymbolTable.summary_le_of_callee {s c : Name} {f : Func d} (hf : t.func? s = some f)
    (hc : c ∈ t.callees f) : t.summary c ≤ t.summary s := by
  have hsub := t.reach_of_callee hf hc
  refine Effects.joinAll_le fun e he => ?_
  obtain ⟨g, hg, he⟩ := List.mem_filterMap.1 he
  exact Effects.le_joinAll (List.mem_filterMap.2 ⟨g, hsub g hg, he⟩)

/-- The summary is closed under the calls of its table. -/
theorem SymbolTable.summary_closed : t.Closed t.summary where
  own _ _ hf o ho := Effects.le_trans
    (Effects.le_joinAll (List.mem_map.2 ⟨o, ho, rfl⟩)) (t.funcOwn_le_summary hf)
  calls _ _ hf o ho _ hoc hcs :=
    t.summary_le_of_callee hf (SymbolTable.mem_callees.2 ⟨hcs, o, ho, hoc⟩)

/-- What a caller sees of an op is below every effect but control. -/
theorem SymbolTable.opOwn_le (o : Operation d) : t.opOwn o ≤ Effects.all.callerView := by
  unfold SymbolTable.opOwn
  split
  · split <;> exact Effects.callerView_mono (Effects.le_all _)
  · exact Effects.callerView_mono (Effects.le_all _)

/-- The summary has no control: what a caller sees of each op has none. -/
theorem SymbolTable.summary_control (s : Name) : (t.summary s).control = false := by
  have hle := t.summary_le (T := fun _ => Effects.all.callerView)
    ⟨fun _ _ _ o _ => t.opOwn_le o, fun _ _ _ _ _ _ _ _ => Effects.le_refl _⟩ s
  cases h : (t.summary s).control
  · rfl
  · exact absurd (hle.control h) Bool.false_ne_true

/-- What a caller sees of the own effects of an op is below what it sees of
the op. -/
theorem SymbolTable.effects_le_opOwn (o : Operation d) : (effects o.op).callerView ≤ t.opOwn o := by
  unfold SymbolTable.opOwn
  split
  · split
    · exact Effects.le_refl _
    · exact Effects.callerView_mono (Effects.le_join_left _ _)
  · exact Effects.le_refl _

/-- What a caller sees of the own effects of each op of a function is below
the function's summary. -/
theorem SymbolTable.effects_le_summary {s : Name} {f : Func d} (hf : t.func? s = some f)
    {o : Operation d} (ho : o ∈ f.allOps) : (effects o.op).callerView ≤ t.summary s :=
  Effects.le_trans (t.effects_le_opOwn o) (t.summary_closed.own s f hf o ho)

/-- The effects of each op in place in a function, its callee's summary
included, are below the function's summary, but for control: a call
carries its callee's effects, and its callee's callees', recursion
included. -/
theorem SymbolTable.opEffects_le_summary {s : Name} {f : Func d} (hf : t.func? s = some f)
    {o : Operation d} (ho : o ∈ f.allOps) : (t.opEffects o).callerView ≤ t.summary s := by
  have hown := t.summary_closed.own s f hf o ho
  unfold SymbolTable.opEffects
  unfold SymbolTable.opOwn at hown
  split
  · rename_i c hc
    rw [hc] at hown
    dsimp only at hown
    split
    · rename_i hcs
      rw [ite_eq_left hcs] at hown
      exact Effects.callerView_join_le hown (Effects.le_trans (Effects.callerView_le _)
        (t.summary_closed.calls s f hf o ho c hc hcs))
    · rename_i hcs
      rw [ite_eq_right hcs] at hown
      exact Effects.callerView_join_le
        (Effects.le_trans (Effects.callerView_mono (Effects.le_join_left _ _)) hown)
        (Effects.le_trans (Effects.callerView_mono (Effects.le_trans (Effects.callerView_le _)
          (Effects.le_join_right _ _))) hown)
  · rename_i hc
    rw [hc] at hown
    exact hown

end Fir
