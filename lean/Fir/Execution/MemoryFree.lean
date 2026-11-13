import Fir.Execution.SummaryFixpoint
import Fir.Execution.MemoryObligationLaws
import Fir.Execution.Monotone

/-!
# Touching no memory

A callee whose effects include no memory read, write or allocation runs the
same from any memories (the section on runs that touch no memory). Touching
no memory is a property of two things:

* of a set of effects: it reads, writes and allocates in no memory. A
  function's effects are its summary, which holds the effects of every
  function it reaches. A function of a table whose ops all declare no
  memory effect, and whose calls each name a function of the table, has a
  summary that touches no memory;
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

/-- The summary of every function of a table touches no memory when each op
of each of its functions declares no memory effect and each of their calls
names a function of the table. -/
theorem SymbolTable.summary_touchesNoMemory {t : SymbolTable d}
    (hops : ∀ s f, t.func? s = some f → ∀ o ∈ f.allOps, (effects o.op).TouchesNoMemory)
    (hcalls : ∀ s f, t.func? s = some f → ∀ o ∈ f.allOps, ∀ c, o.call? = some c →
      (t.func? c).isSome)
    (s : Name) : (t.summary s).TouchesNoMemory := by
  let E : Effects (DialectEffects.Mem d) := { mayUB := true, mayPoison := true, observable := true }
  have hle : ∀ {e : Effects (DialectEffects.Mem d)}, e.TouchesNoMemory → e.callerView ≤ E :=
    fun h => ⟨fun x hx => ((h x).1 hx).elim, fun x hx => ((h x).2.1 hx).elim,
      fun x hx => ((h x).2.2 hx).elim, fun _ => rfl, fun _ => rfl, fun _ => rfl,
      fun hc => nomatch hc⟩
  have hE : E.TouchesNoMemory := fun _ => ⟨nofun, nofun, nofun⟩
  refine Effects.TouchesNoMemory.of_le (t.summary_le (T := fun _ => E) ⟨?_, ?_⟩ s) hE
  · intro s f hf o ho
    unfold SymbolTable.opOwn
    split
    · rename_i c hc
      rw [ite_eq_left (hcalls s f hf o ho c hc)]
      exact hle (hops s f hf o ho)
    · exact hle (hops s f hf o ho)
  · exact fun _ _ _ _ _ _ _ _ => Effects.le_refl _

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
