import Fir.Execution.Summary

/-!
# The laws of function summaries

The summary of each function of a symbol table is a solution of the
inequalities that the calls between its functions set, and the least one
(ADR-2026-11-10-2108). An assignment of an effect set to each symbol of a
table is _closed_ when, for each function and each op of it at any depth:

* what a caller sees of the op's own effects is below the function's set,
  every effect but control when it calls a symbol that names no function;
* and when the op calls a function of the table, that function's set is
  below the caller's.

The summary is closed, so the effects of every op in place, its callee's
included, are below its function's summary: a call carries its callee's
effects, and those of every function the callee calls in turn, recursion
included. And the summary is below every closed assignment, so it is the
least fixpoint of the calls: it claims no effect that some op that a call
may run does not declare.

The proofs rest on three facts of the walk that finds the functions a call
reaches: it reaches every function of its work and keeps what it has seen;
what it reaches is closed under calls; and it reaches nothing outside a set
that is closed under calls and holds its work.
-/

namespace Fir

/-! # Joins -/

section Join

variable {Mem : Type}

/-- Every set of memories is below itself. -/
theorem MemSet.Sub.refl (a : MemSet Mem) : a.Sub a := fun _ h => h

/-- Every effect set is below itself. -/
theorem Effects.le_refl (a : Effects Mem) : a ≤ a :=
  ⟨MemSet.Sub.refl _, MemSet.Sub.refl _, MemSet.Sub.refl _, id, id, id, id⟩

/-- Below is transitive. -/
theorem Effects.le_trans {a b c : Effects Mem} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  ⟨fun m h => h₂.reads m (h₁.reads m h), fun m h => h₂.writes m (h₁.writes m h),
    fun m h => h₂.allocates m (h₁.allocates m h), h₂.mayUB ∘ h₁.mayUB,
    h₂.mayPoison ∘ h₁.mayPoison, h₂.observable ∘ h₁.observable, h₂.control ∘ h₁.control⟩

/-- The empty set is below every set. -/
theorem Effects.empty_le (a : Effects Mem) : ({} : Effects Mem) ≤ a :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ h => (nomatch h),
    fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h), fun h => (nomatch h)⟩

/-- What a caller sees of a set is below the set. -/
theorem Effects.callerView_le (a : Effects Mem) : a.callerView ≤ a :=
  ⟨MemSet.Sub.refl _, MemSet.Sub.refl _, MemSet.Sub.refl _, id, id, id, fun h => (nomatch h)⟩

/-- What a caller sees of a set below another is below what it sees of the
other. -/
theorem Effects.callerView_mono {a b : Effects Mem} (h : a ≤ b) : a.callerView ≤ b.callerView :=
  ⟨h.reads, h.writes, h.allocates, h.mayUB, h.mayPoison, h.observable, fun h => (nomatch h)⟩

/-- A set without control is below what a caller sees of a set above it. -/
theorem Effects.le_callerView {a b : Effects Mem} (h : a ≤ b) (hc : a.control = false) :
    a ≤ b.callerView :=
  ⟨h.reads, h.writes, h.allocates, h.mayUB, h.mayPoison, h.observable,
    fun h' => absurd (hc ▸ h' : false = true) (by simp)⟩

/-- Every set is below every effect. -/
theorem Effects.le_all (a : Effects Mem) : a ≤ Effects.all :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

/-- The join of two sets of memories holds a memory when either does. -/
theorem MemSet.has_join {m : Mem} : ∀ {a b : MemSet Mem}, (a.join b).Has m ↔ a.Has m ∨ b.Has m
  | .every, _ => by simp [MemSet.join, MemSet.Has]
  | .these _, .every => by simp [MemSet.join, MemSet.Has]
  | .these _, .these _ => List.mem_append

/-- A set is below its join with another. -/
theorem Effects.le_join_left (a b : Effects Mem) : a ≤ a.join b :=
  ⟨fun _ h => MemSet.has_join.2 (.inl h), fun _ h => MemSet.has_join.2 (.inl h),
    fun _ h => MemSet.has_join.2 (.inl h), fun h => by simp [Effects.join, h],
    fun h => by simp [Effects.join, h], fun h => by simp [Effects.join, h],
    fun h => by simp [Effects.join, h]⟩

/-- A set is below the join of another with it. -/
theorem Effects.le_join_right (a b : Effects Mem) : b ≤ a.join b :=
  ⟨fun _ h => MemSet.has_join.2 (.inr h), fun _ h => MemSet.has_join.2 (.inr h),
    fun _ h => MemSet.has_join.2 (.inr h), fun h => by simp [Effects.join, h],
    fun h => by simp [Effects.join, h], fun h => by simp [Effects.join, h],
    fun h => by simp [Effects.join, h]⟩

/-- The join of two sets below a third is below it. -/
theorem Effects.join_le {a b c : Effects Mem} (ha : a ≤ c) (hb : b ≤ c) : a.join b ≤ c := by
  refine ⟨fun m h => ?_, fun m h => ?_, fun m h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · exact (MemSet.has_join.1 h).elim (ha.reads m) (hb.reads m)
  · exact (MemSet.has_join.1 h).elim (ha.writes m) (hb.writes m)
  · exact (MemSet.has_join.1 h).elim (ha.allocates m) (hb.allocates m)
  · simp only [Effects.join, Bool.or_eq_true] at h; exact h.elim ha.mayUB hb.mayUB
  · simp only [Effects.join, Bool.or_eq_true] at h; exact h.elim ha.mayPoison hb.mayPoison
  · simp only [Effects.join, Bool.or_eq_true] at h; exact h.elim ha.observable hb.observable
  · simp only [Effects.join, Bool.or_eq_true] at h; exact h.elim ha.control hb.control

/-- What a caller sees of a join is below a set above what it sees of
each side. -/
theorem Effects.callerView_join_le {a b c : Effects Mem} (ha : a.callerView ≤ c)
    (hb : b.callerView ≤ c) : (a.join b).callerView ≤ c := by
  refine ⟨fun m h => ?_, fun m h => ?_, fun m h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => (nomatch h)⟩
  · exact (MemSet.has_join.1 h).elim (ha.reads m) (hb.reads m)
  · exact (MemSet.has_join.1 h).elim (ha.writes m) (hb.writes m)
  · exact (MemSet.has_join.1 h).elim (ha.allocates m) (hb.allocates m)
  · simp only [Effects.callerView, Effects.join, Bool.or_eq_true] at h
    exact h.elim ha.mayUB hb.mayUB
  · simp only [Effects.callerView, Effects.join, Bool.or_eq_true] at h
    exact h.elim ha.mayPoison hb.mayPoison
  · simp only [Effects.callerView, Effects.join, Bool.or_eq_true] at h
    exact h.elim ha.observable hb.observable

/-- A join from the left, from `init`, is above `init` and above each set it
joins, and below every set above them all. -/
theorem Effects.foldl_join {c : Effects Mem} : ∀ {es : List (Effects Mem)} {init : Effects Mem},
    (init ≤ es.foldl Effects.join init ∧ ∀ e ∈ es, e ≤ es.foldl Effects.join init) ∧
      (init ≤ c → (∀ e ∈ es, e ≤ c) → es.foldl Effects.join init ≤ c)
  | [], _ => ⟨⟨Effects.le_refl _, fun _ h => nomatch h⟩, fun h _ => h⟩
  | e :: es, init => by
    obtain ⟨⟨hi, hm⟩, hle⟩ := Effects.foldl_join (c := c) (es := es) (init := init.join e)
    refine ⟨⟨Effects.le_trans (Effects.le_join_left _ _) hi, fun x hx => ?_⟩, fun hc hes => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact Effects.le_trans (Effects.le_join_right _ _) hi
      · exact hm x hx
    · exact hle (Effects.join_le hc (hes e List.mem_cons_self))
        fun x hx => hes x (List.mem_cons_of_mem _ hx)

/-- Each set of a list is below the list's join. -/
theorem Effects.le_joinAll {es : List (Effects Mem)} {e : Effects Mem} (he : e ∈ es) :
    e ≤ Effects.joinAll es :=
  (Effects.foldl_join (c := {})).1.2 e he

/-- The join of a list of sets below a set is below it. -/
theorem Effects.joinAll_le {es : List (Effects Mem)} {c : Effects Mem} (h : ∀ e ∈ es, e ≤ c) :
    Effects.joinAll es ≤ c :=
  Effects.foldl_join.2 (Effects.empty_le c) h

end Join

/-! # The walk -/

variable {d : Dialect} [DialectSignature d] [DialectCall d] {t : SymbolTable d}

/-- A callee of a function names a function of the table, and some op of
the function calls it. -/
theorem SymbolTable.mem_callees {f : Func d} {c : Name} :
    c ∈ t.callees f ↔ (t.func? c).isSome ∧ ∃ o ∈ f.allOps, o.call? = some c := by
  simp only [SymbolTable.callees, List.mem_filter, List.mem_filterMap]
  exact ⟨fun ⟨h, hs⟩ => ⟨hs, h⟩, fun ⟨hs, h⟩ => ⟨h, hs⟩⟩

/-- The walk keeps what it has seen, and reaches every function of its
work. -/
theorem SymbolTable.mem_reach {s : Name} {work seen : List Name}
    (h : s ∈ seen ∨ (s ∈ work ∧ (t.func? s).isSome)) : s ∈ t.reach work seen := by
  induction work, seen using SymbolTable.reach.induct (t := t) with
  | case1 seen =>
    rw [SymbolTable.reach]
    rcases h with h | ⟨h, _⟩
    · exact h
    · cases h
  | case2 seen x work hx ih =>
    rw [SymbolTable.reach, dite_eq_left hx]
    refine ih ?_
    rcases h with h | ⟨h, hs⟩
    · exact .inl h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl hx
      · exact .inr ⟨h, hs⟩
  | case3 seen x work hx f hf ih =>
    rw [SymbolTable.reach, dite_eq_right hx]
    split
    · rename_i f' hf'
      rw [hf] at hf'
      cases hf'
      refine ih ?_
      rcases h with h | ⟨h, hs⟩
      · exact .inl (List.mem_append_left _ h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact .inl (List.mem_append_right _ List.mem_cons_self)
        · exact .inr ⟨List.mem_append_right _ h, hs⟩
    · rename_i hf'
      rw [hf] at hf'
      cases hf'
  | case4 seen x work hx hf ih =>
    rw [SymbolTable.reach, dite_eq_right hx]
    split
    · rename_i f' hf'
      rw [hf] at hf'
      cases hf'
    · refine ih ?_
      rcases h with h | ⟨h, hs⟩
      · exact .inl h
      · rcases List.mem_cons.1 h with rfl | h
        · rw [hf] at hs; cases hs
        · exact .inr ⟨h, hs⟩

/-- What the walk reaches is closed under calls, when each function it has
seen has its callees seen or in its work. -/
theorem SymbolTable.reach_closed {work seen : List Name}
    (hinv : ∀ g ∈ seen, ∀ f, t.func? g = some f → ∀ c ∈ t.callees f, c ∈ seen ∨ c ∈ work) :
    ∀ g ∈ t.reach work seen, ∀ f, t.func? g = some f → ∀ c ∈ t.callees f,
      c ∈ t.reach work seen := by
  induction work, seen using SymbolTable.reach.induct (t := t) with
  | case1 seen =>
    rw [SymbolTable.reach]
    intro g hg f hf c hc
    exact (hinv g hg f hf c hc).resolve_right (by simp)
  | case2 seen x work hx ih =>
    rw [SymbolTable.reach, dite_eq_left hx]
    refine ih fun g hg f hf c hc => ?_
    rcases hinv g hg f hf c hc with h | h
    · exact .inl h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl hx
      · exact .inr h
  | case3 seen x work hx f hf ih =>
    rw [SymbolTable.reach, dite_eq_right hx]
    split
    · rename_i f' hf'
      rw [hf] at hf'
      cases hf'
      refine ih fun g hg f₁ hf₁ c hc => ?_
      rcases List.mem_append.1 hg with hg | hg
      · rcases hinv g hg f₁ hf₁ c hc with h | h
        · exact .inl (List.mem_append_left _ h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl (List.mem_append_right _ List.mem_cons_self)
          · exact .inr (List.mem_append_right _ h)
      · rcases List.mem_singleton.1 hg with rfl
        rw [hf] at hf₁
        cases hf₁
        exact .inr (List.mem_append_left _ hc)
    · rename_i hf'
      rw [hf] at hf'
      cases hf'
  | case4 seen x work hx hf ih =>
    rw [SymbolTable.reach, dite_eq_right hx]
    split
    · rename_i f' hf'
      rw [hf] at hf'
      cases hf'
    · refine ih fun g hg f₁ hf₁ c hc => ?_
      rcases hinv g hg f₁ hf₁ c hc with h | h
      · exact .inl h
      · rcases List.mem_cons.1 h with rfl | h
        · have := (SymbolTable.mem_callees.1 hc).1
          rw [hf] at this
          cases this
        · exact .inr h

/-- The walk reaches nothing outside a set that is closed under calls and
holds its work and what it has seen. -/
theorem SymbolTable.reach_sub {C : Name → Prop}
    (hC : ∀ g f, C g → t.func? g = some f → ∀ c ∈ t.callees f, C c) {work seen : List Name}
    (hseen : ∀ s ∈ seen, C s) (hwork : ∀ s ∈ work, C s) : ∀ s ∈ t.reach work seen, C s := by
  induction work, seen using SymbolTable.reach.induct (t := t) with
  | case1 seen => rw [SymbolTable.reach]; exact hseen
  | case2 seen x work hx ih =>
    rw [SymbolTable.reach, dite_eq_left hx]
    exact ih hseen fun s hs => hwork s (List.mem_cons_of_mem _ hs)
  | case3 seen x work hx f hf ih =>
    rw [SymbolTable.reach, dite_eq_right hx]
    split
    · rename_i f' hf'
      rw [hf] at hf'
      cases hf'
      have hxC := hwork x List.mem_cons_self
      refine ih (fun s hs => ?_) fun s hs => ?_
      · rcases List.mem_append.1 hs with hs | hs
        · exact hseen s hs
        · rcases List.mem_singleton.1 hs with rfl
          exact hxC
      · rcases List.mem_append.1 hs with hs | hs
        · exact hC x f hxC hf s hs
        · exact hwork s (List.mem_cons_of_mem _ hs)
    · rename_i hf'
      rw [hf] at hf'
      cases hf'
  | case4 seen x work hx hf ih =>
    rw [SymbolTable.reach, dite_eq_right hx]
    split
    · rename_i f' hf'
      rw [hf] at hf'
      cases hf'
    · exact ih hseen fun s hs => hwork s (List.mem_cons_of_mem _ hs)

end Fir
