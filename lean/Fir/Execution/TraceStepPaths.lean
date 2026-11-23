import Fir.Execution.TraceStepWays

/-!
# A traced run of ops, one step at a time

The refinement proofs over traced runs compare two runs path by path, as the
proofs with memory do (`Fir.Execution.MemoryStepPaths`). This section says,
once, every way in which a path of a run of ops in the traced layer goes on
from its first op, from a given traced state:

* A path that does not end stuck, with fuel left and an op to run, takes
  one of twelve ways (`Func.TStepPath`). A terminator's exit, an op's rule
  or the external-call rule ends from the traced state, in UB after the
  acts it showed, or with the acts it showed and the traced state after it,
  from which the run goes on, after those acts. A call runs its callee in a
  frame: from the traced state with a new frame entered, and each return
  leaves the frame. When the callee returns, the caller goes on, with the
  steps that the callee leaves, from the traced state that the callee's
  return ends with, after the acts the callee showed. An op whose callee is
  picked (#235) first runs the rule that picks it, which may hit UB, and
  then calls the symbol it picks, after the rule's acts and one more step;
  with no step left for the call, it runs out of fuel after those acts.
* A run with no fuel runs out of fuel, and a block with no op left is
  stuck.
-/

namespace Fir

open Memory

variable {B α ε : Type}

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM B (TraceState Mem unit))]
  [DialectExtCall d (TraceM B (TraceState Mem unit))]

/-- A path of a traced run of ops that is not stuck, from `s`, is a path that
the first op goes on by, and every such path is a path of the run. -/
theorem Func.tStepPath_iff {M : Module d} {n : Nat} {f : Func d} {env : Env d}
    {o : Operation d} {os : List (Operation d)} {s : TraceState Mem unit}
    {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))}
    (hne : TraceEnd.NotStuck e) :
    Func.traceOps B M (n + 1) f env (o :: os) s e ↔ Func.TStepPath M n f env o os s e := by
  have fx : ∀ {e : TraceEnd B (TraceState Mem unit) (Except Stuck (Result (List (DVal d) × Nat)))},
      Func.TStepPath M n f env o os s (e.after []) → Func.TStepPath M n f env o os s e :=
    fun h => by rwa [TraceEnd.after_nil] at h
  constructor
  · intro h
    simp only [Func.traceOps, Func.runOps] at h
    split at h
    · obtain ⟨_, h, _⟩ := (TraceM.run_liftExcept_bind hne).1 h
      cases h
    rename_i hreg
    have hreg' : o.ownsCoreRegion = false := by simpa using hreg
    obtain ⟨args, hargs, h⟩ := (TraceM.run_liftExcept_bind hne).1 h
    split at h
    · rename_i hT
      split at h
      · obtain ⟨_, h, _⟩ := (TraceM.run_liftExcept_bind hne).1 h
        cases h
      rename_i hos
      have hos' : os = [] := by simpa using hos
      rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨x, t, s', e', hx, h, he⟩ | ⟨r, t, hr, he⟩ <;>
        rw [he]
      · cases x with
        | ret =>
          dsimp only at h
          split at h
          · have h : e' = _ := h
            subst h
            simp only [TraceEnd.after, List.append_nil]
            exact .ret hreg' hargs hT hos' hx (by assumption)
          · exact absurd h (TraceM.run_stuck (he ▸ hne).of_after)
        | goto i =>
          dsimp only at h
          obtain ⟨⟨b, env₁⟩, hj, h⟩ :=
            (TraceM.run_liftExcept_bind (he ▸ hne).of_after).1 h
          exact .goto hreg' hargs hT hos' hx hj h
      · exact .exitUB hreg' hargs hT hos' hr
    · rename_i hT
      have hT' : isTerminator o.op = false := by simpa using hT
      split at h
      · rename_i hc
        rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨rs, t, s', e', hrs, h, he⟩ | ⟨r, t, hr, he⟩ <;>
          rw [he]
        · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind (he ▸ hne).of_after).1 h
          simp only [Env.bind] at hb
          split at hb
          · cases hb
            exact .denote hreg' hargs hT' hc hrs (by assumption) h
          · cases hb
        · exact .denoteUB hreg' hargs hT' hc hr
      · rename_i sym hc
        refine fx ?_
        split at h
        · rename_i g hg
          obtain ⟨⟨body, genv⟩, hen, h⟩ := (TraceM.run_liftExcept_bind hne).1 h
          rcases (TraceM.run_except_bind _ _ _ _).1 h with
            ⟨x, t, s', e', hx, h, he⟩ | ⟨st, t, s', _, he⟩ | ⟨r, t, hr, he⟩ <;> rw [he]
          · have hne' := TraceEnd.NotStuck.of_after (he ▸ hne)
            rcases x with ⟨vs, k⟩ | _
            · dsimp only at h
              split at h
              · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind hne').1 h
                simp only [Env.bind] at hb
                split at hb
                · cases hb
                  exact .callRet hreg' hargs hT' (.fixed hc) hg hen hx (by assumption)
                    (by assumption) h
                · cases hb
              · exact absurd h (TraceM.run_stuck hne')
            · have h : e' = _ := h
              subst h
              simp only [TraceEnd.after, List.append_nil]
              exact .callExh hreg' hargs hT' (.fixed hc) hg hen hx
          · exact absurd he (hne st t s')
          · exact .callUB hreg' hargs hT' (.fixed hc) hg hen hr
        · rename_i hg
          split at h
          · rename_i hd
            rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨vs, t, s', e', hvs, h, he⟩ |
              ⟨r, t, hr, he⟩ <;> rw [he]
            · have hne' := TraceEnd.NotStuck.of_after (he ▸ hne)
              split at h
              · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind hne').1 h
                simp only [Env.bind] at hb
                split at hb
                · cases hb
                  exact .ext hreg' hargs hT' (.fixed hc) hg hd hvs (by assumption)
                    (by assumption) h
                · cases hb
              · exact absurd h (TraceM.run_stuck hne')
            · exact .extUB hreg' hargs hT' (.fixed hc) hg hd hr
          · exact absurd h (TraceM.run_stuck hne)
      · rename_i hc
        rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨sym, t₀, s₁, e₀, hs, h, he₀⟩ |
          ⟨r, t, hr, he₀⟩ <;> rw [he₀]
        · have hne₀ := TraceEnd.NotStuck.of_after (he₀ ▸ hne)
          cases n with
          | zero =>
            have h : e₀ = _ := h
            subst h
            simp only [TraceEnd.after, List.append_nil]
            exact .pickExh hreg' hargs hT' hc hs rfl
          | succ n =>
            dsimp only at h
            split at h
            · rename_i g hg
              obtain ⟨⟨body, genv⟩, hen, h⟩ := (TraceM.run_liftExcept_bind hne₀).1 h
              rcases (TraceM.run_except_bind _ _ _ _).1 h with
                ⟨x, t, s', e', hx, h, he⟩ | ⟨st, t, s', _, he⟩ | ⟨r, t, hr, he⟩ <;> rw [he]
              · have hne' := TraceEnd.NotStuck.of_after (he ▸ hne₀)
                rcases x with ⟨vs, k⟩ | _
                · dsimp only at h
                  split at h
                  · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind hne').1 h
                    simp only [Env.bind] at hb
                    split at hb
                    · cases hb
                      exact .callRet hreg' hargs hT' (.picked hc hs) hg hen hx (by assumption)
                        (by assumption) h
                    · cases hb
                  · exact absurd h (TraceM.run_stuck hne')
                · have h : e' = _ := h
                  subst h
                  simp only [TraceEnd.after, List.append_nil]
                  exact .callExh hreg' hargs hT' (.picked hc hs) hg hen hx
              · exact absurd he (hne₀ st t s')
              · exact .callUB hreg' hargs hT' (.picked hc hs) hg hen hr
            · rename_i hg
              split at h
              · rename_i hd
                rcases (TraceM.run_lift_bind _ _ _ _).1 h with ⟨vs, t, s', e', hvs, h, he⟩ |
                  ⟨r, t, hr, he⟩ <;> rw [he]
                · have hne' := TraceEnd.NotStuck.of_after (he ▸ hne₀)
                  split at h
                  · obtain ⟨env₁, hb, h⟩ := (TraceM.run_liftExcept_bind hne').1 h
                    simp only [Env.bind] at hb
                    split at hb
                    · cases hb
                      exact .ext hreg' hargs hT' (.picked hc hs) hg hd hvs (by assumption)
                        (by assumption) h
                    · cases hb
                  · exact absurd h (TraceM.run_stuck hne')
                · exact .extUB hreg' hargs hT' (.picked hc hs) hg hd hr
              · exact absurd h (TraceM.run_stuck hne₀)
        · exact .pickUB hreg' hargs hT' hc hr
  · intro h
    simp only [Func.traceOps, Func.runOps]
    cases h with
    | exitUB hreg hargs hT hos hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
    | ret hreg hargs hT hos hx hs =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx,
        by dsimp only; rw [ite_eq_left hs]; rfl, by simp [TraceEnd.after]⟩)
    | goto hreg hargs hT hos hx hj h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_left hT, ite_eq_right (by simp [hos])]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx,
        (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2 ⟨_, hj, h⟩, rfl⟩)
    | denoteUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
    | denote hreg hargs hT hc hx hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx,
        (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2
          ⟨_, Env.bind_ok _ _ hlen, h⟩, rfl⟩)
    | callUB hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        exact (TraceM.run_liftExcept_bind hne).2 ⟨_, hen,
          (TraceM.run_except_bind _ _ _ _).2 (.inr (.inr ⟨_, _, hx, rfl⟩))⟩
      | picked hc hs =>
        simp only [hc]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hs, ?_, rfl⟩)
        simp only [hg]
        exact (TraceM.run_liftExcept_bind (TraceEnd.notStuck_error _ _)).2 ⟨_, hen,
          (TraceM.run_except_bind _ _ _ _).2 (.inr (.inr ⟨_, _, hx, rfl⟩))⟩
    | callExh hreg hargs hT hc hg hen hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        exact (TraceM.run_liftExcept_bind hne).2 ⟨_, hen, (TraceM.run_except_bind _ _ _ _).2
          (.inl ⟨_, _, _, _, hx, rfl, by simp [TraceEnd.after]⟩)⟩
      | picked hc hs =>
        simp only [hc]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hs, ?_, rfl⟩)
        simp only [hg]
        exact (TraceM.run_liftExcept_bind (TraceEnd.notStuck_ok _ _ _)).2 ⟨_, hen,
          (TraceM.run_except_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, rfl, by simp [TraceEnd.after]⟩)⟩
    | callRet hreg hargs hT hc hg hen hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [TraceEnd.after_nil] at hne ⊢
        simp only [hc, hg]
        refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hen,
          (TraceM.run_except_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, ?_, rfl⟩)⟩
        dsimp only
        rw [ite_eq_left hty]
        exact (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2
          ⟨_, Env.bind_ok _ _ hlen, h⟩
      | picked hc hs =>
        simp only [hc]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hs, ?_, rfl⟩)
        simp only [hg]
        have hne₀ := TraceEnd.NotStuck.of_after hne
        refine (TraceM.run_liftExcept_bind hne₀).2 ⟨_, hen,
          (TraceM.run_except_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, ?_, rfl⟩)⟩
        dsimp only
        rw [ite_eq_left hty]
        exact (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne₀)).2
          ⟨_, Env.bind_ok _ _ hlen, h⟩
    | extUB hreg hargs hT hc hg hd hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [hc, hg]
        simp only [hd, ↓reduceIte]
        exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
      | picked hc hs =>
        simp only [hc]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hs, ?_, rfl⟩)
        simp only [hg, hd, ↓reduceIte]
        exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
    | ext hreg hargs hT hc hg hd hx hty hlen h =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      cases hc with
      | fixed hc =>
        simp only [TraceEnd.after_nil] at hne ⊢
        simp only [hc, hg]
        simp only [hd, ↓reduceIte]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, ?_, rfl⟩)
        rw [ite_eq_left hty]
        exact (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after hne)).2
          ⟨_, Env.bind_ok _ _ hlen, h⟩
      | picked hc hs =>
        simp only [hc]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hs, ?_, rfl⟩)
        simp only [hg, hd, ↓reduceIte]
        refine (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hx, ?_, rfl⟩)
        rw [ite_eq_left hty]
        exact (TraceM.run_liftExcept_bind (TraceEnd.NotStuck.of_after
          (TraceEnd.NotStuck.of_after hne))).2 ⟨_, Env.bind_ok _ _ hlen, h⟩
    | pickUB hreg hargs hT hc hx =>
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩)
    | pickExh hreg hargs hT hc hs hn =>
      subst hn
      rw [ite_eq_right (by simp [hreg])]
      refine (TraceM.run_liftExcept_bind hne).2 ⟨_, hargs, ?_⟩
      rw [ite_eq_right (by simp [hT])]
      simp only [hc]
      exact (TraceM.run_lift_bind _ _ _ _).2 (.inl ⟨_, _, _, _, hs, rfl,
        by simp [TraceEnd.after]⟩)

end Fir
