import Fir.Execution.TraceDialect
import Fir.Execution.ObserveEndLaws
import Fir.Execution.MemoryCalls

/-!
# Traced runs of a dialect with no event

A dialect whose ops show no event has a traced semantics of its own: its
semantics with memory, lifted onto the memories of the traced state. It has
no event, and the world's one answer is never asked for. Such a dialect
lifts its semantics with memory (`LiftsMem`) by construction, so its traced
runs show no act, nothing escapes, and they end as its runs with memory,
each return seen at its end (`Fir.Execution.TraceDialect`).

The end of a return relates what a run with memory ends with. Returned
values that refine others, and memories that refine others, with the same
allocations escaped, give ends of returns that refine each other: the
renaming of every allocation to itself shows the first in the second. The
two memories have the same allocations, each of the same kind, alignment,
liveness, size and address, and a live allocation's units refine the
other's; a dangling pointer, seen as poison, is refined by any value.

So what holds of runs with memory holds of traced runs. When a function's
runs from the empty memories refine another's, the memories they end with
included, its traced runs refine the other's, and so they do at every
world. Refined arguments and congruence in the callee then hold over the
traced runs of every dialect whose ops show no event, from the theorems with
memory (`Fir.Execution.TraceRefine`).
-/

namespace Fir

open Memory

/-! # The lifted traced semantics -/

section

variable (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] [DialectMemDenote d]

/-- The traced semantics of a dialect whose ops show no event: no event, one
answer, and each op's semantics with memory, lifted onto the memories of
the traced state, wherever a run names the dialect's memories and whatever
items it gives each op. -/
@[instance_reducible] def DialectTrace.ofMem : DialectTrace d where
  Event := Empty
  Answer := Unit
  IsRefinedBy := Eq
  traceAt := fun lay ρ L =>
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    { denote op args := TraceM.liftMem (DialectDenote.denote op args)
      exit op args := TraceM.liftMem (DialectDenote.exit op args) }

/-- A dialect whose traced semantics is its semantics with memory, lifted,
lifts its semantics with memory. -/
theorem DialectTrace.ofMem_liftsMem [DecidableEq d.Ty] [DialectCall d] :
    @LiftsMem d _ _ _ _ _ _ (DialectTrace.ofMem d) :=
  letI := DialectTrace.ofMem d
  ⟨fun lay ρ L => by
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    letI := DialectTrace.traceAt (d := d) lay ρ L
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩

end

/-! # The end of a return, from memories that refine others -/

namespace End

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] {μ : Nat → Mem} {ar : AddrRule}
  {V : Type} [HRefinement V V] [HasPtrs V]

/-- Returned values that refine others and memories that refine others, with
the same allocations escaped, give ends of returns that refine each other:
the renaming of every allocation to itself shows the first in the second,
when refinement of the returned values is transitive. -/
theorem isRefinedBy_of_mem (hV : ∀ {a b c : V}, a ⊑ b → b ⊑ c → a ⊑ c) {v v' : V}
    {S S' : Memories Mem unit} (es : List (Mem × AllocId)) (hv : v ⊑ v') (hS : S ⊑ S') :
    (⟨v, S, es⟩ : End unit μ ar V) ⊑ (⟨v', S', es⟩ : End unit μ ar V) := by
  have hle : ∀ {W : Type} [HRefinement W W] [HasPtrs W] (w : W),
      HasPtrs.map (Renaming.id.ptr μ S) w ⊑ w := fun w => by
    have := HasPtrs.map_le (Renaming.id.ptr μ S) (fun _ p => some p) w
      fun n p _ => Renaming.ptr_id S n p
    rwa [HasPtrs.map_some] at this
  refine ⟨Renaming.id, Renaming.id_injective, rfl, fun i e he => ⟨e, he, rfl, rfl⟩,
    fun n p _ => Renaming.id_covers _ n p, hV (hle v) hv, fun x a a' ha => ?_⟩
  cases ha
  refine ⟨?_, fun _ _ _ n p _ => Renaming.id_covers _ n p⟩
  rcases List.IsRefinedBy.getElem? (hS.2.1 x) a with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂, hb⟩
  · show Block.OptSeenIn ar _ ((S.mem x).blocks[a]?) ((S'.mem x).blocks[a]?)
    rw [h₁, h₂]
    exact trivial
  · show Block.OptSeenIn ar _ ((S.mem x).blocks[a]?) ((S'.mem x).blocks[a]?)
    rw [h₁, h₂]
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1 ▸ ar.refl _, fun hl =>
      List.isRefinedBy_trans MemUnit.isRefinedBy_trans (hle b.units) (hb.2.2.2.2.2 hl)⟩

end End

/-! # Runs with memory, seen at the end of each return -/

section

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectEffects d] [DialectMemDenote d] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems) (μ : Nat → N) (ar : AddrRule)

/-- How a path of a run from given memories ends, seen at the end of a
return with nothing escaped. -/
def Result.memEnd {V : Type} :
    Except Stuck (Result (V × Memories N (unitsOf lay))) →
      Except Stuck (Result (End (unitsOf lay) μ ar V))
  | .ok (.ret (v, S)) => .ok (.ret ⟨v, S, []⟩)
  | .ok .fuelExhausted => .ok .fuelExhausted
  | .error e => .error e

/-- The runs with memory of a function, each return seen at its end, are its
runs from the empty memories, each return seen at its end with nothing
escaped. -/
theorem Func.memEndRuns_eq (M : Module d) (f : Func d) (a : HVector toType (f.params.map (·.2)))
    (n : Nat) :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    f.memEndRuns lay ρ L μ ar M a n =
      Functor.map (f := SetM) (Result.memEnd lay μ ar)
        (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay))) n) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  simp only [Func.memEndRuns, Func.memRunsFrom, fromState]
  show _ = Result.memEnd lay μ ar <$> ExceptT.run (Result.withMem <$> ExceptT.mk _)
  rw [ExceptT.run_map, ExceptT.run_mk, Functor.map_map, Functor.map_map]
  refine congrArg (· <$> _) (funext fun p => ?_)
  obtain ⟨r, S⟩ := p
  rcases r with e | (v | _) <;> rfl

/-- The ways a computation of the set monad, its results mapped, may end. -/
theorem SetM.map_iff {α β : Type} (g : α → β) (s : SetM α) (e : Ev β) :
    (g <$> s) e ↔ (∃ a, s (.ok a) ∧ e = .ok (g a)) ∨ ∃ r, s (.ub r) ∧ e = .ub r :=
  Iff.rfl

variable {M : Module d} {f : Func d} {a : HVector toType (f.params.map (·.2))} {n : Nat}

/-- A run with memory returns, seen at its end, what the run from the empty
memories returns, with the memories it ends with and nothing escaped. -/
theorem Func.memEndRuns_ret_iff {o : End (unitsOf lay) μ ar (List (DVal d))} :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    (f.memEndRuns lay ρ L μ ar M a n).outcomes (.ret o) ↔
      o.escaped = [] ∧ (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay))) n).outcomes
        (.ret (o.vals, o.mem)) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  simp only [Run.outcomes, Func.memEndRuns_eq, SetM.map_iff]
  constructor
  · rintro (⟨x, hx, he⟩ | ⟨_, _, he⟩)
    · rcases x with _ | (⟨v, S⟩ | _) <;> cases he
      exact ⟨rfl, hx⟩
    · cases he
  · obtain ⟨v, S, es⟩ := o
    rintro ⟨rfl, h⟩
    exact .inl ⟨_, h, rfl⟩

/-- A run with memory, each return seen at its end, hits UB exactly when the
run from the empty memories does. -/
theorem Func.memEndRuns_ub_iff {r : String} :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    (f.memEndRuns lay ρ L μ ar M a n).outcomes (.ub r) ↔
      (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay))) n).outcomes (.ub r) := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  simp only [Run.outcomes, Func.memEndRuns_eq, SetM.map_iff]
  constructor
  · rintro (⟨_, _, he⟩ | ⟨_, h, he⟩) <;> cases he
    exact h
  · exact fun h => .inr ⟨r, h, rfl⟩

/-- A run with memory, each return seen at its end, runs out of fuel exactly
when the run from the empty memories does. -/
theorem Func.memEndRuns_exhausted_iff :
    letI := DialectMemDenote.denoteAt (d := d) lay ρ L
    (f.memEndRuns lay ρ L μ ar M a n).outcomes .fuelExhausted ↔
      (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay))) n).outcomes
        .fuelExhausted := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  simp only [Run.outcomes, Func.memEndRuns_eq, SetM.map_iff]
  constructor
  · rintro (⟨x, hx, he⟩ | ⟨_, _, he⟩)
    · rcases x with _ | (_ | _) <;> cases he
      exact hx
    · cases he
  · exact fun h => .inl ⟨_, h, rfl⟩

variable [TyRefinement d.Ty] [TyPointers d.Ty]

/-- When a function's runs from the empty memories refine another's, the
memories they end with included, its runs with memory, each return seen at
its end, refine the other's, when the refinement of values is transitive. -/
theorem Func.memEndRuns_isRefinedBy_of_from
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M' : Module d} {f' : Func d} {a' : HVector toType (f'.params.map (·.2))}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      observable (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay)))) ⊑
        observable (f'.memRunsFrom M' (a', (Memories.empty : Memories N (unitsOf lay))))) :
    observable (f.memEndRuns lay ρ L μ ar M a) ⊑ observable (f'.memEndRuns lay ρ L μ ar M' a') := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  have hV : ∀ {a b c : List (DVal d)}, a ⊑ b → b ⊑ c → a ⊑ c :=
    List.isRefinedBy_trans (DVal.isRefinedBy_trans htrans)
  have hub : ∀ {r : String}, observable (f.memRunsFrom M (a, Memories.empty)) (.ub r) →
      observable (f.memEndRuns lay ρ L μ ar M a) (.ub r) :=
    fun ⟨m, hm⟩ => ⟨m, (Func.memEndRuns_ub_iff lay ρ L μ ar).2 hm⟩
  intro t ht
  match t, ht with
  | .ret ⟨v', S', es⟩, ⟨n, hn⟩ =>
    obtain ⟨rfl, hn⟩ := (Func.memEndRuns_ret_iff lay ρ L μ ar).1 hn
    obtain ⟨s, hs, hst⟩ := h (.ret (v', S')) ⟨n, hn⟩
    match s, hs, hst with
    | .ub _, hs, _ => exact ⟨_, hub hs, trivial⟩
    | .ret (v, S), ⟨m, hm⟩, hle =>
      exact ⟨.ret ⟨v, S, []⟩, ⟨m, (Func.memEndRuns_ret_iff lay ρ L μ ar).2 ⟨rfl, hm⟩⟩,
        End.isRefinedBy_of_mem hV [] hle.1 hle.2⟩
  | .ub r, ⟨n, hn⟩ =>
    obtain ⟨s, hs, hst⟩ := h (.ub r) ⟨n, (Func.memEndRuns_ub_iff lay ρ L μ ar).1 hn⟩
    match s, hs, hst with
    | .ub _, hs, _ => exact ⟨_, hub hs, trivial⟩
  | .fuelExhausted, ht =>
    obtain ⟨s, hs, hst⟩ :=
      h .fuelExhausted fun n => (Func.memEndRuns_exhausted_iff lay ρ L μ ar).1 (ht n)
    match s, hs, hst with
    | .ub _, hs, _ => exact ⟨_, hub hs, trivial⟩
    | .fuelExhausted, hs, _ =>
      exact ⟨.fuelExhausted, fun n => (Func.memEndRuns_exhausted_iff lay ρ L μ ar).2 (hs n),
        trivial⟩

variable [DialectTrace d] [LiftsMem d]

/-- When a function's runs from the empty memories refine another's, the
memories they end with included, its traced runs refine the other's, for a
dialect whose ops show no event, when the refinement of values is
transitive. -/
theorem Func.traceRuns_isRefinedBy_of_from
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    {M' : Module d} {f' : Func d} {a' : HVector toType (f'.params.map (·.2))}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      observable (f.memRunsFrom M (a, (Memories.empty : Memories N (unitsOf lay)))) ⊑
        observable (f'.memRunsFrom M' (a', (Memories.empty : Memories N (unitsOf lay))))) :
    traceObservable (f.traceRuns lay ρ L μ ar M a) ⊑
      traceObservable (f'.traceRuns lay ρ L μ ar M' a') := by
  rw [Func.traceObservable_traceRuns, Func.traceObservable_traceRuns]
  exact TBehaviour.ofBehaviour_isRefinedBy_iff.2
    (Func.memEndRuns_isRefinedBy_of_from lay ρ L μ ar htrans h)

end

end Fir
