import Fir.Execution.TraceFollowStep

/-!
# Divergence across black boxes

A target configuration that shows a closed stream at every budget, diverging
silently or with acts forever, is allowed by every source configuration that
follows it (`TCfg.Follows.allows`): the source hits UB after acts that the
stream first shows, refined, or shows at every budget a stream that the target's
refines. The two runs need not go in step: a black box's two callees may take
different numbers of steps.

The proof follows the target move by move, under the hypothesis that the human
ruled on 2026-11-20, on #233: every op that runs by its own rule has finitely
many outcomes, given the world's answers.

* _The target's branch._ The target goes on by a move that infinitely many of
  its paths take, again and again (`TGood.branch`). Each configuration of the
  branch shows the stream after the moves before it (`TBranchT.tShows`).
* _The source follows._ Suppose the source did not allow the stream. At each
  move of the target, a source that follows and does not allow the stream
  after the moves so far follows with a move of its own, whose acts the
  target's refine (`TCfg.Follows.step`), and does not allow the stream after
  that move either, since it would then allow the stream before it
  (`TCfg.Allows.lift`). So, by dependent choice, the source has a branch of its
  own, move for move.
* _The source's branch shows a stream that the target's refines_
  (`TBranch.tShows`): its moves' acts are refined by the target's, and the
  target's moves show all of the target's stream. So the source allows the
  stream after all, a contradiction.
-/

namespace Fir

open Memory

variable {A : Type}

/-- A stream that a trace's acts start is that trace, then the stream after
it. -/
theorem Stream.eq_cat {S : Nat → Option A} {l : List A} (h : Stream.Cons S l) :
    S = Stream.cat l (Stream.drop S l.length) := by
  funext i
  unfold Stream.cat Stream.drop
  by_cases hi : i < l.length
  · rw [ite_eq_left hi]
    exact (h i _ (List.getElem?_eq_getElem hi)).trans (List.getElem?_eq_getElem hi).symm
  · rw [ite_eq_right hi, Nat.sub_add_cancel (by omega)]

/-- The acts of the moves of two branches, each move's refined by the other's,
are streams that refine each other. -/
theorem TBranch.acts_isRefinedBy [HRefinement A A] {t t' : Nat → List (Step A)}
    (h : ∀ i, Step.actsOf (t i) ⊑ Step.actsOf (t' i)) (i : Nat) :
    Stream.IsRefinedBy (TBranch.acts t i) (TBranch.acts t' i) := by
  have hpre : ∀ j i, Step.actsOf (TBranch.pre t i j) ⊑ Step.actsOf (TBranch.pre t' i j) := by
    intro j
    induction j with
    | zero => intro i; exact trivial
    | succ j ih =>
      intro i
      simp only [TBranch.pre, Step.actsOf_append]
      exact List.IsRefinedBy.append (h i) (ih (i + 1))
  intro p
  refine ⟨⟨fun hn => ?_, fun hn => ?_⟩, fun a b ha hb => ?_⟩
  · cases hs : TBranch.acts t' i p with
    | none => rfl
    | some b =>
      obtain ⟨j, hj⟩ := TBranch.acts_some hs
      rcases List.IsRefinedBy.getElem? (hpre j i) p with ⟨-, h₂⟩ | ⟨a, b', h₁, -, -⟩
      · rw [h₂] at hj
        cases hj
      · rw [TBranch.acts_eq h₁] at hn
        cases hn
  · cases hs : TBranch.acts t i p with
    | none => rfl
    | some a =>
      obtain ⟨j, hj⟩ := TBranch.acts_some hs
      obtain ⟨b, hb, -⟩ := List.IsRefinedBy.getElem?_some (hpre j i) p a hj
      rw [TBranch.acts_eq hb] at hn
      cases hn
  · obtain ⟨j, hj⟩ := TBranch.acts_some ha
    obtain ⟨b', hb', hab⟩ := List.IsRefinedBy.getElem?_some (hpre j i) p a hj
    rw [TBranch.acts_eq hb'] at hb
    cases hb
    exact hab

variable {E Ans : Type} [HRefinement E E] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step (Act E Ans)) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step (Act E Ans)) (TraceState Mem unit))] [TyRefinement d.Ty]
  {M M' : Module d}

/-- A target configuration that shows a closed stream at every budget is
allowed by every source configuration that follows it: the source hits UB
after acts that the stream first shows, refined, or shows at every budget a
stream that the target's refines. It asks that every call name the same
function in both modules or a traced black box, that the ops of the source
module's functions that run by their own rule be monotone, that every path of
every op show exactly one step, and that every op that runs by its own rule
have finitely many outcomes, given the world's answers. -/
theorem TCfg.Follows.allows (hone : OpsOneStep d (Act E Ans) (TraceState Mem unit))
    (hfin : OpsStepFinite d E Ans (TraceState Mem unit))
    (hmono : ∀ g ∈ M.funcs, g.TraceOpsMonotone (Step (Act E Ans)) (TraceState Mem unit))
    (hcalls : TraceCallsRefined (Act E Ans) Mem unit M M') {c c' : TCfg d Mem unit}
    (hc : c.Follows (Act E Ans) c') {T : Nat → Option (Act E Ans)} {K : Nat → Nat}
    (hcl : Stream.Closed T) (h : TShows (c'.exh (Act E Ans) M') T K) : c.Allows M T := by
  classical
  obtain ⟨cs, ts, Fs, Ts, Ks, hc0, hT0, -, hb⟩ := TGood.branch hone hfin (TGood.ofShows h)
  have hcl' : ∀ i, Stream.Closed (Ts i) := fun i => by
    have := hb.stream_eq 0 i
    rw [Nat.zero_add] at this
    rw [this, hT0]
    exact hcl.drop _
  have hcat : ∀ i, Ts i = Stream.cat (Step.actsOf (ts i)) (Ts (i + 1)) := fun i => by
    rw [hb.stream i]
    exact Stream.eq_cat (hb.cons i)
  refine Classical.byContradiction fun hno => ?_
  obtain ⟨sq, hsq0, hsq⟩ := exists_seq_of_step
    (α := TCfg d Mem unit × List (Step (Act E Ans)) × Nat) (a₀ := (c, [], 0))
    (P := fun i a => a.1.Follows (Act E Ans) (cs i) ∧ ¬ a.1.Allows M (Ts i))
    (R := fun i a b => TCfg.Move (Act E Ans) M a.1 b.1 b.2.1 b.2.2 ∧
      Step.actsOf b.2.1 ⊑ Step.actsOf (ts i))
    ⟨hc0 ▸ hc, hT0 ▸ hno⟩ fun i a ⟨hf, hna⟩ => by
      rcases hf.step hone hmono hcalls (hb.move i) (hb.tShows hone (i + 1) (hcl' (i + 1)))
          (hcl' (i + 1)) with hal | ⟨c₁, t, F, hmv, hf₁, ht⟩
      · exact absurd (hcat i ▸ hal) hna
      · refine ⟨(c₁, t, F), ⟨hf₁, fun hal₁ => hna ?_⟩, hmv, ht⟩
        rw [hcat i]
        exact TCfg.Allows.lift hone hmv ht hal₁
  have hsh := TBranch.tShows (R := fun i => (sq i).1.exh (Act E Ans) M)
    (t := fun i => (sq (i + 1)).2.1) (F := fun i => (sq (i + 1)).2.2)
    (fun i => (hsq i).2.1.tStep hone) 0
  simp only [hsq0] at hsh
  refine hno (.inr ⟨_, _, hsh, ?_⟩)
  rw [← hT0, ← hb.acts_eq hone 0 (hT0 ▸ hcl)]
  exact TBranch.acts_isRefinedBy (fun i => (hsq i).2.2) 0

end Fir
