import Fir.Execution.RunPaths

/-!
# A run that runs out of fuel, with less fuel

A run of ops that runs out of fuel with more fuel runs out of fuel with
less: it takes the same path and runs out sooner, by the ways a step goes
on (`Fir.Execution.RunPaths`). A call whose callee is picked (#235) and has
no step left for the call runs out of fuel after its rule.
-/

namespace Fir

open SetM

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d SetM]

/-- A run that runs out of fuel with `j` more steps runs out of fuel with
fewer: it takes the same path, and runs out sooner. -/
theorem Func.runOps_exhausted_down (M : Module d) (n : Nat) :
    ∀ (j : Nat) (f : Func d) (env : Env d) (os : List (Operation d)),
      (Func.runOps (m := SetM) M (n + j) f env os).run (.ok (.ok .fuelExhausted)) →
      (Func.runOps (m := SetM) M n f env os).run (.ok (.ok .fuelExhausted)) := by
  have hne : Ev.NotStuck
      (.ok (.ok .fuelExhausted) : Ev (Except Stuck (Result (List (DVal d) × Nat)))) :=
    fun _ h => nomatch h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j f env os h
    match n, os with
    | 0, _ => exact Func.run_runOps_zero.2 rfl
    | k + 1, [] => rw [Nat.add_right_comm] at h; exact absurd h (Func.run_runOps_nil hne)
    | k + 1, o :: os =>
      rw [Nat.add_right_comm] at h
      refine (Func.stepPath_iff hne).2 ?_
      cases (Func.stepPath_iff hne).1 h with
      | goto hreg hargs hT hos hx hj h =>
        exact .goto hreg hargs hT hos hx hj (ih k (Nat.lt_succ_self k) j _ _ _ h)
      | denote hreg hargs hT hc hx hlen h =>
        exact .denote hreg hargs hT hc hx hlen (ih k (Nat.lt_succ_self k) j _ _ _ h)
      | callExh hreg hargs hT hc hg hen hx =>
        rcases hc.down with ⟨n'', rfl, hc'⟩ | ⟨rfl, hpc, hs⟩
        · exact .callExh hreg hargs hT hc' hg hen (ih n'' (Nat.lt_succ_of_le hc'.le.1) j _ _ _ hx)
        · exact .pickExh hreg hargs hT hpc hs rfl
      | callRet hreg hargs hT hc hg hen hx hty hlen h =>
        rename_i vs kk
        rcases hc.down with ⟨n'', rfl, hc'⟩ | ⟨rfl, hpc, hs⟩
        · rcases (Func.runOps_ahead M n'' j _ _ _).down_ret _ kk hx with ⟨hj, hx'⟩ | hx'
          · have hle : kk - j ≤ n'' := by
              have := Func.runOps_left_le M (n'' + j) _ _ _ _ _ hx
              omega
            have hmin : min kk (n'' + j) = (kk - j) + j := by
              have := Func.runOps_left_le M (n'' + j) _ _ _ _ _ hx
              omega
            rw [hmin] at h
            have h' := ih (kk - j) (Nat.lt_succ_of_le (Nat.le_trans hle hc'.le.1)) j _ _ _ h
            refine .callRet hreg hargs hT hc' hg hen hx' hty hlen ?_
            rwa [Nat.min_eq_left hle]
          · exact .callExh hreg hargs hT hc' hg hen hx'
        · exact .pickExh hreg hargs hT hpc hs rfl
      | pickExh hreg hargs hT hc hs hn =>
        exact .pickExh hreg hargs hT hc hs (by omega)

end Fir
