import Fir.Execution.EnvRefine
import Fir.Execution.Propagation

/-!
# Values with no poison

The proof that function summaries are sound keeps track of poison in a
run's environment (the section on sound function summaries). A list of
values is _clean_ when no value of it is poison, and an environment is clean
when no value it binds is. A clean environment gives clean values and clean
operands, and binding clean values in it, such as parameters bound to
arguments with no poison, leaves it clean.
-/

namespace Fir

section Clean

variable {d : Dialect} [TyDenote d.Ty] [TyPoison d.Ty]

/-- No value of a list is poison. -/
def DVals.Clean (vs : List (DVal d)) : Prop := ∀ v ∈ vs, ¬ TyPoison.IsPoison v.2

/-- No value that an environment binds is poison. -/
def Env.Clean (env : Env d) : Prop := ∀ p ∈ env, ¬ TyPoison.IsPoison p.2.2

/-- The values of a vector have no poison when no element of it is poison. -/
theorem HVector.clean_toDVals : ∀ {ts : List d.Ty} (xs : HVector toType ts),
    DVals.Clean xs.toDVals ↔ ¬ xs.Any TyPoison.IsPoison
  | [], .nil => ⟨fun _ h => h, fun _ _ h => nomatch h⟩
  | _ :: _, .cons x xs => by
    simp only [DVals.Clean, HVector.toDVals, List.mem_cons, forall_eq_or_imp, HVector.Any,
      not_or]
    exact and_congr Iff.rfl (HVector.clean_toDVals xs)

/-- A name that a list looks up is bound in it. -/
theorem mem_of_lookup {β : Type} {x : Name} {v : β} :
    ∀ {l : List (Name × β)}, l.lookup x = some v → (x, v) ∈ l
  | (y, u) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hxy
      cases h
      rw [beq_iff_eq.1 hxy]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- A value that an environment with no poison binds is not poison. -/
theorem Env.Clean.value {env : Env d} (h : env.Clean) {x : Name} {v : DVal d}
    (hv : env.value x = .ok v) : ¬ TyPoison.IsPoison v.2 := by
  simp only [Env.value] at hv
  split at hv
  · rename_i v' hl
    cases hv
    exact h _ (mem_of_lookup hl)
  · cases hv

/-- Binding values with no poison in an environment with none leaves none. -/
theorem Env.Clean.bind {env : Env d} (h : env.Clean) (names : List Name) {vs : List (DVal d)}
    (hvs : DVals.Clean vs) : Env.Clean (names.zip vs ++ env) := fun p hp => by
  rcases List.mem_append.1 hp with hp | hp
  · exact hvs _ (List.of_mem_zip hp).2
  · exact h p hp

/-- Parameters bound to arguments with no poison make an environment with
none. -/
theorem Env.Clean.params {ts : List d.Ty} (names : List Name) (args : HVector toType ts)
    (h : ¬ args.Any TyPoison.IsPoison) : Env.Clean (names.zip args.toDVals) := by
  simpa using (show Env.Clean ([] : Env d) from fun _ h => nomatch h).bind names
    ((HVector.clean_toDVals args).2 h)

/-- The values found in an environment with no poison have none. -/
theorem Env.Clean.mapM_value {env : Env d} (h : env.Clean) :
    ∀ {xs : List Name} {vs : List (DVal d)}, xs.mapM env.value = .ok vs → DVals.Clean vs
  | [], _, hm => by cases hm; exact fun _ h => nomatch h
  | x :: xs, vs, hm => by
    simp only [List.mapM_cons] at hm
    cases hx : env.value x with
    | error e => rw [hx] at hm; cases hm
    | ok v =>
      cases hxs : xs.mapM env.value with
      | error e => rw [hx, hxs] at hm; cases hm
      | ok vs' =>
        rw [hx, hxs] at hm
        cases hm
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact h.value hx
        · exact h.mapM_value hxs w hw

variable [DecidableEq d.Ty]

/-- The operands found in an environment with no poison have none. -/
theorem Env.Clean.operands {env : Env d} (h : env.Clean) :
    ∀ {ts : List d.Ty} {xs : List Name} {args : HVector toType ts},
      env.operands ts xs = .ok args → ¬ args.Any TyPoison.IsPoison
  | [], [], .nil, _ => fun h => h
  | t :: ts, x :: xs, _, hm => by
    obtain ⟨v, as, hx, hxs, rfl⟩ := Env.operands_cons_ok.1 hm
    rintro (hp | hp)
    · exact h.value hx hp
    · exact h.operands hxs hp
  | [], _ :: _, _, hm | _ :: _, [], _, hm => by cases hm

end Clean

end Fir
