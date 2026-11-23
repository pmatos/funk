import Fir.Execution.TraceLift
import Fir.Execution.TraceObligations
import Fir.Execution.MemoryRefineUp

/-!
# Ops monotone in the traced layer

Two ways of building an op's semantics in the traced layer keep its
monotonicity:

* _The step before an op._ The traced layer of marked traces runs an op by
  its dialect's rule after a step, each act of its traces an act of the
  marked trace (`DialectTrace.stepAt`). A step refines a step, and mapping
  acts keeps their refinement, and UB after the acts _t_ becomes UB after
  the step and _t_. So an op monotone by its dialect's rule in the traced
  layer is monotone in the traced layer of marked traces.
* _The lift of the semantics with memory._ An op may run, in a dialect's
  traced semantics, by its rule with memory, on the memories of the traced
  state (`OpLiftsMem`), as every op of a dialect whose ops show no event
  does (`DialectTrace.ofMem`), and every op of the core, whose events come
  from external calls, not from its ops. The lift shows nothing and keeps
  what escaped, so results and memories that refine others, and UB, stay
  so. An op monotone with memory is then monotone in the traced layer.
-/

namespace Fir

open Memory

variable {A σ α β : Type}

/-! # Mapping each act to an act of a marked trace -/

/-- The trace of a way of ending, its acts mapped. -/
theorem TraceEnd.trace_mapActs {B : Type} (g : A → List B) (e : TraceEnd A σ α) :
    (e.mapActs g).trace = e.trace.flatMap g := by
  cases e <;> rfl

section

variable [HRefinement A A] [HRefinement σ σ]

/-- Mapping each act to the act of a marked trace keeps a way of ending
allowing another. -/
theorem TraceEnd.Allows.mapActs {r : α → β → Prop} :
    ∀ {e : TraceEnd A σ α} {e' : TraceEnd A σ β}, TraceEnd.Allows r e e' →
      TraceEnd.Allows r (e.mapActs fun a => [Step.act a]) (e'.mapActs fun a => [Step.act a])
  | .ok _, .ok _, h => ⟨h.1, Step.flatMap_act_isRefinedBy h.2.1, h.2.2⟩
  | .error _, e', h => by
    show List.IsRefinedPrefix _ (e'.mapActs _).trace
    rw [TraceEnd.trace_mapActs]
    exact Step.flatMap_act_isRefinedPrefix h
  | .ok _, .error _, h => h.elim

/-- A computation that refines another still does after a step, each act of
its traces an act of the marked trace. -/
theorem TraceRefinedBy.step {r : α → β → Prop} {c : TraceM A σ α} {c' : TraceM A σ β}
    (h : TraceRefinedBy r c c') :
    TraceRefinedBy r (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [Step.act a]) c)
      (TraceM.tick >>= fun _ => TraceM.mapActs (fun a => [Step.act a]) c') := by
  intro s s' hs e' he'
  rcases (TraceM.bind_apply _ _ _ _).1 he' with ⟨_, t, s₁, e₁, ht, ⟨e₀', hc, rfl⟩, rfl⟩ | ⟨_, _, ht, _⟩
  · have ht : (Except.ok ((), t, s₁) : TraceEnd (Step A) σ Unit) = .ok ((), [.tick], s') := ht
    cases ht
    obtain ⟨e₀, hc₀, hle⟩ := h s s' hs e₀' hc
    exact ⟨_, (TraceM.bind_apply _ _ _ _).2 (.inl ⟨(), [.tick], s, _, rfl, ⟨e₀, hc₀, rfl⟩, rfl⟩),
      hle.mapActs.after (show ([Step.tick] : List (Step A)) ⊑ [Step.tick] from ⟨trivial, trivial⟩)⟩
  · cases ht

end

/-! # The step before each op -/

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] [DialectTrace d]
  [TyRefinement d.Ty] {N : Type} [DecidableEq N] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N) (L : RunItems)

/-- An op monotone by its dialect's rule in the traced layer is monotone in
the traced layer of marked traces, where it runs after a step. -/
theorem OpTraceMonotone.stepAt {op : d.Op}
    (h : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpTraceMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) op) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    OpTraceMonotone (B := Step (DialectTrace.Acts d)) (σ := TraceState N (unitsOf lay)) op :=
  fun args args' hr => ⟨fun hT => ((h args args' hr).1 hT).step,
    fun hT => ((h args args' hr).2 hT).step⟩

/-- A rule that picks a callee monotonically in the traced layer does so in
the traced layer of marked traces, where it runs after a step. -/
theorem OpTracePickMonotone.stepAt {op : d.Op}
    (h : letI := DialectTrace.traceAt (d := d) lay ρ L
      OpTracePickMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) op) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    OpTracePickMonotone (B := Step (DialectTrace.Acts d)) (σ := TraceState N (unitsOf lay)) op :=
  fun ok ok' hok args args' hr => (h ok ok' hok args args' hr).step

/-- An external-call rule monotone in the traced layer is monotone in the
traced layer of marked traces, where it runs after a step. -/
theorem ExtTraceMonotone.stepAt {g : Name} {ts rs : List d.Ty}
    (h : letI := DialectTrace.traceAt (d := d) lay ρ L
      ExtTraceMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) g ts rs) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    ExtTraceMonotone (B := Step (DialectTrace.Acts d)) (σ := TraceState N (unitsOf lay)) g ts rs :=
  fun args args' hr => (h args args' hr).step

variable [DialectCall d]

/-- A function whose ops are monotone by its dialect's rule in the traced
layer has ops monotone in the traced layer of marked traces. -/
theorem Func.TraceOpsMonotone.stepAt {f : Func d}
    (h : letI := DialectTrace.traceAt (d := d) lay ρ L
      f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay))) :
    letI := DialectTrace.stepAt (d := d) lay ρ L
    f.TraceOpsMonotone (Step (DialectTrace.Acts d)) (TraceState N (unitsOf lay)) :=
  fun b hb o ho => ⟨fun hc => OpTraceMonotone.stepAt lay ρ L ((h b hb o ho).1 hc),
    fun hT g hc => ExtTraceMonotone.stepAt lay ρ L ((h b hb o ho).2.1 hT g hc),
    fun hT hc => ⟨OpTracePickMonotone.stepAt lay ρ L ((h b hb o ho).2.2 hT hc).1,
      fun g => ExtTraceMonotone.stepAt lay ρ L (((h b hb o ho).2.2 hT hc).2 g)⟩⟩

end

/-! # The lift of the semantics with memory -/

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem] [HRefinement A A]

/-- Computations of the state layer that refine each other, lifted onto the
memories of the traced state, refine each other in the traced layer: the
lift shows nothing and keeps what escaped. -/
theorem TraceRefinedBy.liftMem {r : α → α → Prop} {c c' : StateT (Memories Mem unit) SetM α}
    (h : StateRefinedBy r c c') :
    TraceRefinedBy (A := A) r (TraceM.liftMem c) (TraceM.liftMem c') := by
  intro s s' hs e' he'
  rcases he' with ⟨a', S', hc', rfl⟩ | ⟨r', hc', rfl⟩
  · obtain ⟨e₀, he₀, hle⟩ := h s.mem s'.mem hs.1 _ hc'
    cases e₀ with
    | ok p => exact ⟨.ok (p.1, [], { s with mem := p.2 }), .inl ⟨p.1, p.2, he₀, rfl⟩,
        hle.1, trivial, hle.2, hs.2⟩
    | ub r₀ => exact ⟨.error (r₀, []), .inr ⟨r₀, he₀, rfl⟩, TraceEnd.Allows.of_ub _ _⟩
  · obtain ⟨e₀, he₀, hle⟩ := h s.mem s'.mem hs.1 _ hc'
    cases e₀ with
    | ok _ => exact hle.elim
    | ub r₀ => exact ⟨.error (r₀, []), .inr ⟨r₀, he₀, rfl⟩, TraceEnd.Allows.of_ub _ _⟩

end

section

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectEffects d] [DialectMemDenote d]
  {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N) (L : RunItems)

/-- The op `op` runs, in a dialect's traced semantics, by its rule with
memory, lifted onto the memories of the traced state, wherever a run names
the dialect's memories by `ρ` and gives each op the items `L`: it shows no
event and keeps what escaped. A dialect may show events by other rules,
such as the core's external calls, while each of its ops lifts its rule with
memory. -/
def OpLiftsMem [DialectTrace d] (op : d.Op) : Prop :=
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  ∀ args : HVector toType (sig op),
    TraceM.liftMem (DialectDenote.denote (m := StateT (Memories N (unitsOf lay)) SetM) op args) =
        DialectDenote.denote (m := TraceM (DialectTrace.Acts d) (TraceState N (unitsOf lay))) op args ∧
      TraceM.liftMem (DialectDenote.exit (m := StateT (Memories N (unitsOf lay)) SetM) op args) =
        DialectDenote.exit (m := TraceM (DialectTrace.Acts d) (TraceState N (unitsOf lay))) op args ∧
      ∀ ok, TraceM.liftMem
          (DialectDenote.pick (m := StateT (Memories N (unitsOf lay)) SetM) op ok args) =
        DialectDenote.pick (m := TraceM (DialectTrace.Acts d) (TraceState N (unitsOf lay))) op ok args

/-- In the lifted traced semantics of a dialect whose ops show no event,
each op lifts its rule with memory. -/
theorem OpLiftsMem.ofMem (op : d.Op) :
    letI := DialectTrace.ofMem d
    OpLiftsMem lay ρ L op :=
  fun _ => ⟨rfl, rfl, fun _ => rfl⟩

/-- In a dialect whose traced semantics lifts its semantics with memory,
each op lifts its rule with memory. -/
theorem LiftsMem.opLiftsMem [DecidableEq d.Ty] [DialectCall d] [DialectTrace d] [LiftsMem d]
    (op : d.Op) : OpLiftsMem lay ρ L op := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  exact fun args => ⟨(LiftsMem.lifts lay ρ L).denote op args, (LiftsMem.lifts lay ρ L).exit op args,
    fun ok => (LiftsMem.lifts lay ρ L).pick op ok args⟩

variable [TyRefinement d.Ty]

/-- An op that lifts its rule with memory in a dialect's traced semantics,
and is monotone with memory, is monotone in the traced layer. -/
theorem OpTraceMonotone.ofLift [DialectTrace d] {op : d.Op} (hl : OpLiftsMem lay ρ L op)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      OpMemMonotone (σ := Memories N (unitsOf lay)) op) :
    letI := DialectTrace.traceAt (d := d) lay ρ L
    OpTraceMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) op := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  intro args args' hr
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · rw [← (hl args).1, ← (hl args').1]
    exact TraceRefinedBy.liftMem ((h args args' hr).1 hT)
  · rw [← (hl args).2.1, ← (hl args').2.1]
    exact TraceRefinedBy.liftMem ((h args args' hr).2 hT)

/-- A rule that lifts its rule with memory in a dialect's traced semantics,
and picks a callee monotonically with memory, picks it monotonically in the
traced layer. -/
theorem OpTracePickMonotone.ofLift [DialectTrace d] {op : d.Op} (hl : OpLiftsMem lay ρ L op)
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      OpMemPickMonotone (σ := Memories N (unitsOf lay)) op) :
    letI := DialectTrace.traceAt (d := d) lay ρ L
    OpTracePickMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) op := by
  letI := DialectMemDenote.denoteAt (d := d) lay ρ L
  letI := DialectTrace.traceAt (d := d) lay ρ L
  intro ok ok' hok args args' hr
  rw [← (hl args).2.2 ok, ← (hl args').2.2 ok']
  exact TraceRefinedBy.liftMem (h ok ok' hok args args' hr)

/-- In the traced semantics of a dialect whose ops show no event, an op
monotone with memory is monotone in the traced layer. -/
theorem OpTraceMonotone.ofMem {op : d.Op}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      OpMemMonotone (σ := Memories N (unitsOf lay)) op) :
    letI := DialectTrace.ofMem d
    letI := DialectTrace.traceAt (d := d) lay ρ L
    OpTraceMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) op :=
  letI := DialectTrace.ofMem d
  OpTraceMonotone.ofLift lay ρ L (OpLiftsMem.ofMem lay ρ L op) h

omit [DialectMemDenote d] in
/-- An external-call rule that lifts the rule with memory, UB, is monotone
in the traced layer: it ends only in UB that shows no act, which allows
every way of ending. -/
theorem ExtTraceMonotone.ofLift [DialectTrace d]
    (hl : letI := DialectTrace.traceAt (d := d) lay ρ L
      (MonadMorphism.traceMem N (unitsOf lay) (DialectTrace.Acts d)).MapsExtCall (d := d))
    (g : Name) (ts rs : List d.Ty) :
    letI := DialectTrace.traceAt (d := d) lay ρ L
    ExtTraceMonotone (B := DialectTrace.Acts d) (σ := TraceState N (unitsOf lay)) g ts rs :=
  letI := DialectTrace.traceAt (d := d) lay ρ L
  ExtTraceMonotone.of_ub
    (fun g args rs => (hl g args rs).symm.trans (TraceM.liftMem_extCall g args rs)) g ts rs

variable [DialectCall d]

/-- In a dialect's traced semantics where each op lifts its rule with
memory, and so does the external-call rule, a function whose ops are
monotone with memory has ops monotone in the traced layer. -/
theorem Func.TraceOpsMonotone.ofLift [DialectTrace d] {f : Func d}
    (hl : ∀ op : d.Op, OpLiftsMem lay ρ L op)
    (hlx : letI := DialectTrace.traceAt (d := d) lay ρ L
      (MonadMorphism.traceMem N (unitsOf lay) (DialectTrace.Acts d)).MapsExtCall (d := d))
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      f.MemOpsMonotone N (unitsOf lay)) :
    letI := DialectTrace.traceAt (d := d) lay ρ L
    f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)) :=
  fun b hb o ho => ⟨fun hc => OpTraceMonotone.ofLift lay ρ L (hl o.op) ((h b hb o ho).1 hc),
    fun _ g _ => ExtTraceMonotone.ofLift lay ρ L hlx g _ _,
    fun _ hc => ⟨OpTracePickMonotone.ofLift lay ρ L (hl o.op) ((h b hb o ho).2 hc),
      fun g => ExtTraceMonotone.ofLift lay ρ L hlx g _ _⟩⟩

/-- In the traced semantics of a dialect whose ops show no event, a function
whose ops are monotone with memory has ops monotone in the traced layer. -/
theorem Func.TraceOpsMonotone.ofMem {f : Func d}
    (h : letI := DialectMemDenote.denoteAt (d := d) lay ρ L
      f.MemOpsMonotone N (unitsOf lay)) :
    letI := DialectTrace.ofMem d
    letI := DialectTrace.traceAt (d := d) lay ρ L
    f.TraceOpsMonotone (DialectTrace.Acts d) (TraceState N (unitsOf lay)) :=
  letI := DialectTrace.ofMem d
  Func.TraceOpsMonotone.ofLift lay ρ L (OpLiftsMem.ofMem lay ρ L) (fun _ _ _ => rfl) h

end

end Fir
