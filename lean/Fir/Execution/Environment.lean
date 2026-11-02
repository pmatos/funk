import Fir.Execution.Interpreter

/-!
# The environment of a run

A run looks each operand up in its environment, by name, and checks its
type. The lemmas below say when those lookups and checks succeed: when the
environment holds, for each name that the run has defined, a value of the
type that the function gives the name. The next section keeps that
invariant along a run. Names are unique in a valid function, so the type
that a function gives a name is the one of its only definition.
-/

namespace Fir

variable {d : Dialect}

/-- A list whose keys are unique gives each key the value it pairs it
with. -/
theorem find?_of_nodup {T : Type} {x : Name} {t : T} :
    ∀ {l : List (Name × T)}, (l.map (·.1)).Nodup → (x, t) ∈ l →
      (l.find? (·.1 == x)).map (·.2) = some t
  | (y, u) :: l, hnd, hm => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hy : y = x
    · subst hy
      rcases List.mem_cons.1 hm with h | h
      · cases h; simp
      · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hnd.1
    · have hm' : (x, t) ∈ l := by
        rcases List.mem_cons.1 hm with h | h
        · cases h; exact absurd rfl hy
        · exact h
      have hb : (y == x) = false := beq_false_of_ne hy
      simp only [List.find?_cons, hb]
      exact find?_of_nodup hnd.2 hm'

/-- In a function whose names are unique, a name has the type of its
definition. -/
theorem Func.typeOf_of_mem {f : Func d} {x : Name} {t : d.Ty} (hnd : (f.defs.map (·.1)).Nodup)
    (h : (x, t) ∈ f.defs) : f.typeOf x = some t :=
  find?_of_nodup hnd h

/-- A name of a list has a value in it: the first value paired with it. -/
theorem lookup_of_mem {β : Type} {x : Name} :
    ∀ {l : List (Name × β)}, x ∈ l.map (·.1) → ∃ v, l.lookup x = some v ∧ (x, v) ∈ l
  | (y, u) :: l, h => by
    by_cases hy : x = y
    · subst hy
      exact ⟨u, by simp [List.lookup], List.mem_cons_self⟩
    · have h' : x ∈ l.map (·.1) := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h hy
        · exact h
      obtain ⟨v, hv, hm⟩ := lookup_of_mem h'
      have hb : (x == y) = false := beq_false_of_ne hy
      exact ⟨v, by simp only [List.lookup, hb, hv], List.mem_cons_of_mem _ hm⟩

/-- A name that a list does not have is looked up past it. -/
theorem lookup_append_of_not_mem {β : Type} {x : Name} {r : List (Name × β)} :
    ∀ {l : List (Name × β)}, x ∉ l.map (·.1) → (l ++ r).lookup x = r.lookup x
  | [], _ => rfl
  | (y, _) :: l, h => by
    have hy : x ≠ y := fun e => h (List.mem_cons.2 (.inl e))
    have h' : x ∉ l.map (·.1) := fun e => h (List.mem_cons_of_mem _ e)
    have hb : (x == y) = false := beq_false_of_ne hy
    simp only [List.cons_append, List.lookup, hb, lookup_append_of_not_mem h']

/-- The values of a vector have the vector's types. -/
theorem HVector.toDVals_types {Ty : Type} [TyDenote Ty] :
    ∀ {ts : List Ty} (vs : HVector toType ts), (HVector.toDVals vs).map (·.1) = ts
  | [], .nil => rfl
  | _ :: _, .cons _ vs => by simp [HVector.toDVals, HVector.toDVals_types vs]

variable [TyDenote d.Ty]

/-- The environment holds a value for each of the names `xs`, of the type
that the function `f` gives it. -/
def Env.Holds (env : Env d) (f : Func d) (xs : List Name) : Prop :=
  ∀ x ∈ xs, ∃ dv, env.lookup x = some dv ∧ f.typeOf x = some dv.1

/-- Binding as many names as values succeeds. -/
theorem Env.bind_ok (env : Env d) {xs : List Name} {vs : List (DVal d)} (why : String)
    (h : xs.length = vs.length) : env.bind xs vs why = .ok (xs.zip vs ++ env) := by
  simp [Env.bind, h]; rfl

/-- Pairing the names of `ps` with values of their types pairs each name
with a value of its own type. -/
theorem mem_zip_types {x : Name} {dv : DVal d} :
    ∀ {ps : List (Name × d.Ty)} {dvs : List (DVal d)}, dvs.map (·.1) = ps.map (·.2) →
      (x, dv) ∈ (ps.map (·.1)).zip dvs → (x, dv.1) ∈ ps
  | [], [], _, h => nomatch h
  | (y, t) :: ps, dv' :: dvs, ht, h => by
    simp only [List.map_cons, List.cons.injEq] at ht
    rcases List.mem_cons.1 h with h | h
    · cases h; exact List.mem_cons.2 (.inl (by rw [ht.1]))
    · exact List.mem_cons_of_mem _ (mem_zip_types ht.2 h)

/-- Binding the names of `ps` to values of their types: the environment
then holds them, where `f` gives each its type, and still holds every
other name it held. -/
theorem Env.holds_bind {env : Env d} {f : Func d} {xs : List Name} {ps : List (Name × d.Ty)}
    {dvs : List (DVal d)} (hold : env.Holds f xs) (ht : dvs.map (·.1) = ps.map (·.2))
    (hdef : ∀ p ∈ ps, f.typeOf p.1 = some p.2) (hfresh : ∀ x ∈ xs, x ∉ ps.map (·.1)) :
    Env.Holds ((ps.map (·.1)).zip dvs ++ env) f (xs ++ ps.map (·.1)) := by
  have hlen : (ps.map (·.1)).length = dvs.length := by
    rw [List.length_map, ← List.length_map (f := (·.2)), ← ht, List.length_map]
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨dv, hl, hty⟩ := hold x hx
    have hz : x ∉ ((ps.map (·.1)).zip dvs).map (·.1) := by
      rw [List.map_fst_zip (Nat.le_of_eq hlen)]
      exact hfresh x hx
    exact ⟨dv, by rw [lookup_append_of_not_mem hz, hl], hty⟩
  · have hz : x ∈ ((ps.map (·.1)).zip dvs).map (·.1) := by
      rw [List.map_fst_zip (Nat.le_of_eq hlen)]
      exact hx
    obtain ⟨dv, hl, hm⟩ := lookup_of_mem hz
    refine ⟨dv, by rw [List.lookup_append, hl]; rfl, ?_⟩
    exact hdef _ (mem_zip_types ht hm)

variable [DecidableEq d.Ty]

/-- The operands of an op are found, with their types, when the
environment holds each of them and the function gives each the type of
its operand. -/
theorem Env.operands_ok {env : Env d} {f : Func d} :
    ∀ (ts : List d.Ty) (xs : List Name), xs.map f.typeOf = ts.map some → env.Holds f xs →
      ∃ vs, env.operands ts xs = .ok vs
  | [], [], _, _ => ⟨.nil, rfl⟩
  | t :: ts, x :: xs, ht, hold => by
    simp only [List.map_cons, List.cons.injEq] at ht
    obtain ⟨⟨t', v⟩, hl, hty⟩ := hold x (List.mem_cons_self)
    have htt : t' = t := Option.some.inj (hty.symm.trans ht.1)
    subst htt
    obtain ⟨vs, hvs⟩ := Env.operands_ok ts xs ht.2 (fun y hy => hold y (List.mem_cons_of_mem _ hy))
    exact ⟨.cons v vs, by simp [Env.operands, Env.value, hl, hvs]; rfl⟩
  | [], _ :: _, ht, _ | _ :: _, [], ht, _ => nomatch ht

end Fir
