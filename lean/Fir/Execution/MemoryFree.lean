import Fir.Execution.SummaryFixpoint
import Fir.Execution.MemoryObligationLaws
import Fir.Execution.Monotone

/-!
# Touching no memory

A callee whose effects include no memory read, write or allocation runs the
same from any memories (the section on runs that touch no memory). Touching
no memory is a property of two things:

* of a set of effects: it reads, writes and allocates in no memory. A
  function _reaches no memory_ when every function that its run may reach,
  itself included, declares no memory effect for any of its ops. A function
  whose summary touches no memory reaches none, since its summary holds the
  effects of every function it reaches. A call that names no function of
  the table adds every effect to a summary, but nothing to what a function
  reaches, since a run is stuck there;
* of a computation in the state layer: it _ignores the memories_. From any
  memories it ends in UB for the reasons it does from any others, and each
  way it ends with results, it ends with the memories it started with, and
  from any others with the same results and those others. A computation of
  the set monad run in the state layer does, and mapping its results keeps
  it.

The effect obligations do not give the second from the first: they compare
runs from memories with the same allocations, and say nothing of the frames
or of memories with other allocations. So the theorems on runs ask the
dialect for it, of each op that runs by its own rule, a terminator or an op
with no callee, and declares no memory effect: its ops _ignore the memories
where they touch none_. The core dialect meets it, since none of its ops
touches memory.

A path of a run is compared with the path of another run that returns the
same values with other memories, so a path can have the memories it returns
replaced.
-/

namespace Fir

open SetM Memory

/-! # Effects that touch no memory -/

section

variable {Mem : Type}

/-- A set of effects touches no memory: it reads, writes and allocates in
none. -/
def Effects.TouchesNoMemory (e : Effects Mem) : Prop :=
  ∀ x, ¬ e.reads.Has x ∧ ¬ e.writes.Has x ∧ ¬ e.allocates.Has x

/-- A set of effects below one that touches no memory touches none. -/
theorem Effects.TouchesNoMemory.of_le {a b : Effects Mem} (h : a ≤ b)
    (hb : b.TouchesNoMemory) : a.TouchesNoMemory := fun x =>
  ⟨fun hr => (hb x).1 (h.reads x hr), fun hw => (hb x).2.1 (h.writes x hw),
    fun ha => (hb x).2.2 (h.allocates x ha)⟩

end

variable {d : Dialect} [DialectSignature d] [DialectCall d] [DialectEffects d]

/-- The function of the table `t` that the symbol `s` names reaches no
memory: each function that its run may reach, itself included, declares no
memory effect for any of its ops. A call that names no function of `t` adds
nothing: its run is stuck there. -/
def SymbolTable.ReachesNoMemory (t : SymbolTable d) (s : Name) : Prop :=
  ∀ g ∈ t.reach [s] [], ∀ f, t.func? g = some f → ∀ o ∈ f.allOps, (effects o.op).TouchesNoMemory

variable {t : SymbolTable d} {s : Name} {f : Func d} {o : Operation d}

/-- A function whose summary touches no memory reaches no memory. -/
theorem SymbolTable.ReachesNoMemory.of_summary (h : (t.summary s).TouchesNoMemory) :
    t.ReachesNoMemory s := fun g hg f hf o ho => by
  have hown : (effects o.op).callerView ≤ t.opOwn o := by
    unfold SymbolTable.opOwn
    split
    · split
      · exact Effects.le_refl _
      · exact Effects.callerView_mono (Effects.le_join_left _ _)
    · exact Effects.le_refl _
  have hfs : t.funcOwn f ≤ t.summary s :=
    Effects.le_joinAll (List.mem_filterMap.2 ⟨g, hg, by simp [hf]⟩)
  exact Effects.TouchesNoMemory.of_le (a := (effects o.op).callerView) (Effects.le_trans hown
    (Effects.le_trans (Effects.le_joinAll (List.mem_map.2 ⟨o, ho, rfl⟩)) hfs)) h

/-- Each op of a function that reaches no memory declares no memory
effect. -/
theorem SymbolTable.ReachesNoMemory.own (h : t.ReachesNoMemory s) (hf : t.func? s = some f)
    (ho : o ∈ f.allOps) : (effects o.op).TouchesNoMemory :=
  h s (SymbolTable.mem_reach (.inr ⟨List.mem_singleton_self _, by simp [hf]⟩)) f hf o ho

/-- Each function that a function that reaches no memory calls reaches no
memory: it reaches nothing that its caller does not. -/
theorem SymbolTable.ReachesNoMemory.callee (h : t.ReachesNoMemory s) (hf : t.func? s = some f)
    (ho : o ∈ f.allOps) {c : Name} (hc : o.call? = some c) (hcs : (t.func? c).isSome) :
    t.ReachesNoMemory c := by
  have hclosed := SymbolTable.reach_closed (t := t) (work := [s]) (seen := [])
    (fun _ h => nomatch h)
  have hs : s ∈ t.reach [s] [] :=
    SymbolTable.mem_reach (.inr ⟨List.mem_singleton_self _, by simp [hf]⟩)
  have hcc : c ∈ t.callees f := SymbolTable.mem_callees.2 ⟨hcs, o, ho, hc⟩
  have hsub : ∀ g ∈ t.reach [c] [], g ∈ t.reach [s] [] :=
    SymbolTable.reach_sub (C := (· ∈ t.reach [s] [])) (fun g f hg hf c hc => hclosed g hg f hf c hc)
      (fun _ h => nomatch h) fun g hg => by
        rcases List.mem_singleton.1 hg with rfl
        exact hclosed s hs f hf g hcc
  exact fun g hg => h g (hsub g hg)

/-! # Computations that ignore the memories -/

section

variable {σ α β : Type}

/-- The computation `c` ignores the memories: from any memories it ends in
UB for the reasons it does from any others, and each way it ends with
results ends with the memories it started with, and from any others with
the same results and those others. -/
def IgnoresMemory (c : StateT σ SetM α) : Prop :=
  (∀ S r, c S (.ub r) → ∀ T, c T (.ub r)) ∧
    ∀ S a S', c S (.ok (a, S')) → S' = S ∧ ∀ T, c T (.ok (a, T))

/-- A computation of the set monad, run in the state layer, ignores the
memories. -/
theorem IgnoresMemory.lift (x : SetM α) : IgnoresMemory (σ := σ) (StateT.lift x) := by
  refine ⟨fun S r h T => ?_, fun S a S' h => ?_⟩
  · rcases (SetM.lift_apply x S _).1 h with ⟨_, -, he⟩ | ⟨_, hr, he⟩
    · cases he
    · cases he
      exact (SetM.lift_apply x T _).2 (.inr ⟨_, hr, rfl⟩)
  · rcases (SetM.lift_apply x S _).1 h with ⟨_, ha, he⟩ | ⟨_, -, he⟩
    · cases he
      exact ⟨rfl, fun T => (SetM.lift_apply x T _).2 (.inl ⟨_, ha, rfl⟩)⟩
    · cases he

/-- Mapping the results keeps a computation that ignores the memories. -/
theorem IgnoresMemory.map {c : StateT σ SetM α} (f : α → β) (h : IgnoresMemory c) :
    IgnoresMemory (f <$> c) := by
  refine ⟨fun S r hc T => ?_, fun S b S' hc => ?_⟩
  · rcases (SetM.stateMap_apply f c S _).1 hc with ⟨_, _, -, he⟩ | ⟨_, hr, he⟩
    · cases he
    · cases he
      exact (SetM.stateMap_apply f c T _).2 (.inr ⟨_, h.1 S _ hr T, rfl⟩)
  · rcases (SetM.stateMap_apply f c S _).1 hc with ⟨a, S'', ha, he⟩ | ⟨_, -, he⟩
    · cases he
      obtain ⟨rfl, hT⟩ := h.2 S a _ ha
      exact ⟨rfl, fun T => (SetM.stateMap_apply f c T _).2 (.inl ⟨a, T, hT T, rfl⟩)⟩
    · cases he

end

/-- The ops of `d` ignore the memories where they touch none, in a semantics
with the memories named by `Mem`: each op that runs by its own rule, a
terminator or an op with no callee, and declares no memory effect, ignores
the memories, as an op that is not a terminator and as a terminator. -/
def OpsIgnoreMemory (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectCall d]
    [DialectEffects d] (Mem : Type) (unit : Mem → Nat)
    [DialectDenote d (StateT (Memory.Memories Mem unit) SetM)] : Prop :=
  ∀ op : d.Op, isTerminator op = true ∨ callee? op = none → (effects op).TouchesNoMemory →
    ∀ args : HVector toType (sig op),
      (isTerminator op = false →
        IgnoresMemory (DialectDenote.denote (m := StateT (Memory.Memories Mem unit) SetM) op args)) ∧
      (isTerminator op = true →
        IgnoresMemory (DialectDenote.exit (m := StateT (Memory.Memories Mem unit) SetM) op args))

/-- A path of a run with its returned memories replaced by `g` of them. -/
def Ev.mapRet {β : Type} (g : β → β) : Ev (Except Stuck (Result β)) → Ev (Except Stuck (Result β))
  | .ok (.ok (.ret b)) => .ok (.ok (.ret (g b)))
  | .ok (.ok .fuelExhausted) => .ok (.ok .fuelExhausted)
  | .ok (.error st) => .ok (.error st)
  | .ub r => .ub r

/-- The values a run of ops returns, with the memories `T` and the steps it
leaves. -/
abbrev atMemSteps {α σ : Type} (T : σ) : (α × σ) × Nat → (α × σ) × Nat := fun p => ((p.1.1, T), p.2)

/-- The values a run of a function returns, with the memories `T`. -/
abbrev atMem {α σ : Type} (T : σ) : α × σ → α × σ := fun p => (p.1, T)

/-- A path that ends with a result is not stuck. -/
theorem Ev.notStuck_ok {α : Type} (r : α) : Ev.NotStuck (.ok (.ok r) : Ev (Except Stuck α)) :=
  fun _ h => nomatch h

/-- A path that ends in UB is not stuck. -/
theorem Ev.notStuck_ub {α : Type} (r : String) : Ev.NotStuck (.ub r : Ev (Except Stuck α)) :=
  fun _ h => nomatch h

/-- A path that is not stuck is not stuck with its memories replaced. -/
theorem Ev.NotStuck.mapRet {β : Type} {g : β → β} :
    ∀ {e : Ev (Except Stuck (Result β))}, Ev.NotStuck e → Ev.NotStuck (e.mapRet g)
  | .ok (.ok (.ret _)), _ | .ok (.ok .fuelExhausted), _ | .ub _, _ => fun _ h => nomatch h
  | .ok (.error st), h => absurd rfl (h st)

/-- Dropping the steps a run leaves and replacing its memories commute. -/
theorem Ev.dropLeft_mapRet {α σ : Type} (T : σ) :
    ∀ e : Ev (Except Stuck (Result ((α × σ) × Nat))),
      (e.mapRet (atMemSteps T)).dropLeft = e.dropLeft.mapRet (atMem T)
  | .ok (.ok (.ret _)) | .ok (.ok .fuelExhausted) | .ok (.error _) | .ub _ => rfl

end Fir
