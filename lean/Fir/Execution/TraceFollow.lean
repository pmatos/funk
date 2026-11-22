import Fir.Execution.TraceShowsObs
import Fir.Execution.TraceCallsAllowed

/-!
# The source follows the target's moves

Congruence in the callee compares a source module with a target module that
runs each call as the source does, or as a black box (`TraceCallsRefined`).
A source configuration _follows_ a target configuration when both run the same
ops of the same function, from an environment and a traced state that the
target's refine, and the source's ops that run by their own rule are monotone
(`TCfg.Follows`).

The source _allows_ a stream from a configuration when it hits UB after acts
that the stream first shows, refined, or shows, at every budget, a stream
that the given one refines (`TCfg.Allows`). This is what divergence of the
target asks of the source.

For each move of the target (`TCfg.Follows.step`), the source allows the
stream that the move puts before what the target shows after it, or follows
with a move whose acts the target's refine:

* an op that runs by its own rule: the source's op, monotone, allows the
  target's outcome by UB after acts that the target's first refine, or by an
  outcome whose results, acts and traced state the target's refine;
* a call of the same function in both: the source enters it too;
* a call whose callee returns: the source's callee allows the return by UB, or
  returns at some budget (`TraceCallsRefined.callee_allowed`);
* a call of a black box whose callee diverges in the target: the black box
  gives the source's callee UB, or divergence that the target's refines, at
  which the source's call diverges too.

A source that allows the stream after a move allows the stream with the move's
acts before it (`TCfg.Allows.lift`).
-/

namespace Fir

open Memory

variable {A : Type} [HRefinement A A] {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]
  {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d (TraceM (Step A) (TraceState Mem unit))]
  [DialectExtCall d (TraceM (Step A) (TraceState Mem unit))] {M M' : Module d}

/-- The source allows the stream `T` from the configuration `c`: it hits UB
after acts that `T` first shows, refined, or shows at every budget a stream
that `T` refines. -/
def TCfg.Allows (M : Module d) (c : TCfg d Mem unit) (T : Nat → Option A) : Prop :=
  (∃ n r mt, c.ub A M n r mt ∧ Stream.ShowsRefined (Step.actsOf mt) T) ∨
    ∃ S K, TShows (c.exh A M) S K ∧ Stream.IsRefinedBy S T

variable [TyRefinement d.Ty]

variable (A) in
/-- The source configuration `c` follows the target configuration `c'`: the same
ops of the same function, from an environment and a traced state that the
target's refine, the function's and the ops' that run by their own rule
monotone. -/
structure TCfg.Follows (c c' : TCfg d Mem unit) : Prop where
  f : c.f = c'.f
  os : c.os = c'.os
  env : c.env.IsRefinedBy c'.env
  s : c.s ⊑ c'.s
  mono : c.f.TraceOpsMonotone (Step A) (TraceState Mem unit)
  ops : TraceMonotoneOps (Step A) (TraceState Mem unit) c.os

omit [TyRefinement d.Ty] in
/-- UB after acts that a trace first shows, refined, allows the stream of that
trace, then any stream. -/
theorem Stream.ShowsRefined.of_prefix {l l' : List A} (h : List.IsRefinedPrefix l l')
    (T : Nat → Option A) : Stream.ShowsRefined l (Stream.cat l' T) := fun i a ha => by
  obtain ⟨b, hb, hab⟩ := List.IsRefinedPrefix.getElem? h i a ha
  refine ⟨b, ?_, hab⟩
  unfold Stream.cat
  rw [ite_eq_left (List.getElem?_eq_some_iff.1 hb).1]
  exact hb

omit [HRefinement A A] [TyRefinement d.Ty] in
/-- The stream of no acts, then a stream, is that stream. -/
theorem Stream.cat_nil (T : Nat → Option A) : Stream.cat [] T = T := by
  funext i
  simp [Stream.cat]

omit [TyRefinement d.Ty] in
/-- A source that allows the stream after a move allows it with the move's
acts before it, when the move's acts are refined by the target's. -/
theorem TCfg.Allows.lift (hone : OpsOneStep d A (TraceState Mem unit)) {c c₁ : TCfg d Mem unit}
    {t t' : List (Step A)} {F : Nat} (hmv : TCfg.Move A M c c₁ t F)
    (ht : Step.actsOf t ⊑ Step.actsOf t') {T₁ : Nat → Option A} (h : c₁.Allows M T₁) :
    c.Allows M (Stream.cat (Step.actsOf t') T₁) := by
  rcases h with ⟨n, r, mt₁, hu, hs⟩ | ⟨S, K, hS, hr⟩
  · obtain ⟨n', hu'⟩ := hmv.ub hu
    refine .inl ⟨n', r, t ++ mt₁, hu', ?_⟩
    rw [Step.actsOf_append]
    exact hs.cat ht
  · exact .inr ⟨_, _, TShows.step (hmv.tStep hone) hS, hr.cat ht⟩

omit [HRefinement A A] [TyRefinement d.Ty] in
/-- The paths of a callee's entry block, from the traced state with a frame
entered, that run out of fuel are those of its traced runs from the traced
state. -/
theorem TCfg.exh_iff_traceFrom {g : Func d} {a : HVector toType (g.params.map (·.2))}
    {s : TraceState Mem unit} {body : List (Operation d)} {genv : Env d}
    (hen : g.enter a.toDVals = .ok (body, genv)) (n : Nat) (mt : List (Step A)) :
    TCfg.exh A M ⟨g, genv, body, { s with mem := s.mem.enter }⟩ n mt ↔
      TRun.exh (g.traceFrom (A := A) M (a, s)) n mt := by
  constructor
  · rintro ⟨s₂, h⟩
    exact Func.traceFrom_exhausted_iff.2 ⟨body, genv, _, hen, (TraceM.run_inFrame _ _ _).2 ⟨_, h, rfl⟩⟩
  · intro h
    obtain ⟨body', genv', s₁, hen', h₁⟩ := Func.traceFrom_exhausted_iff.1 h
    rw [hen] at hen'
    cases hen'
    obtain ⟨e₁, h₁', he₁⟩ := (TraceM.run_inFrame _ _ _).1 h₁
    rcases e₁ with ⟨_, _⟩ | ⟨y, t₁, s₂⟩
    · cases he₁
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at he₁
    obtain ⟨rfl, rfl, -⟩ := he₁
    exact ⟨s₂, h₁'⟩

omit [HRefinement A A] [TyRefinement d.Ty] in
/-- A run that shows a stream shows it from paths that are those of another. -/
theorem TShows.congr {R R' : Nat → List (Step A) → Prop} {S : Nat → Option A} {K : Nat → Nat}
    (h : ∀ n mt, R n mt ↔ R' n mt) (hs : TShows R S K) : TShows R' S K := fun n => by
  obtain ⟨mt, hmt, hc, hk⟩ := hs n
  exact ⟨mt, (h n mt).1 hmt, hc, hk⟩

end Fir
