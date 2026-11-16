import Fir.Execution.Trace
import Fir.Execution.MemoryState

/-!
# The traced layer

A run with memory runs in the state layer over the set monad. There, UB ends
a path and takes everything with it: the set monad's UB carries only its
reason. A traced run must keep the acts it showed before UB, since UB in
the source allows only a target that first shows them. So a traced run
runs in a layer of its own, the _traced layer_, in which UB carries the
trace shown so far.

A computation of the traced layer starts from the trace shown so far and
the memories, and each of its paths ends with a result, the trace and the
memories, or with UB, its reason and the trace. Its paths form a _set of
paths_, a set monad with no UB of its own, since UB is the layer's. The
layer is Lean's state and exception transformers over that set:

$$`\mathrm{TraceM}\,A\,\sigma\,\alpha = \mathrm{List}\,A \times \sigma \to
  \mathrm{Paths}(\mathrm{Except}\,(\mathrm{String} \times \mathrm{List}\,A)\,
    (\alpha \times (\mathrm{List}\,A \times \sigma)))`

It has the effects of the state layer: a choice of bits, UB, and frames,
which enter a call before its computation and leave it after. It adds the
_event effect_: `emit e` shows the event `e` to the world, and goes on with
the world's answer. Every world counts, so in the layer an event may get
any answer, and the act that holds the event and its answer joins the
trace.

A computation of the state layer runs in the traced layer by keeping the
trace: each path that ends with a result keeps the trace it started with,
and each path that ends in UB ends in UB after that trace. This _lift_ is a
monad morphism, keeps choice and UB, and keeps frames, so the interpreter's
run of a dialect whose ops show no event, in the traced layer, is its run
with memory, lifted (the section on the interpreter's morphism theorem).
-/

namespace Fir

open Memory

/-! # Sets of paths -/

/-- A set of the ways a computation may end, with no UB of its own. -/
def Paths (α : Type) : Type := α → Prop

namespace Paths

instance : Monad Paths where
  pure a := fun b => b = a
  bind s f := fun b => ∃ a, s a ∧ f a b

variable {α β γ : Type}

/-- `pure` then `f` is `f`. -/
theorem pure_bind (a : α) (f : α → Paths β) : (pure a >>= f) = f a := by
  funext b
  exact propext ⟨fun ⟨_, h, h'⟩ => h ▸ h', fun h => ⟨a, rfl, h⟩⟩

/-- `s` then `pure` is `s`. -/
theorem bind_pure (s : Paths α) : (s >>= pure) = s := by
  funext b
  exact propext ⟨fun ⟨_, h, h'⟩ => (h' : b = _) ▸ h, fun h => ⟨b, h, rfl⟩⟩

/-- Binds associate. -/
theorem bind_assoc (s : Paths α) (f : α → Paths β) (g : β → Paths γ) :
    (s >>= f >>= g) = s >>= fun a => f a >>= g := by
  funext c
  exact propext ⟨fun ⟨b, ⟨a, ha, hb⟩, hc⟩ => ⟨a, ha, b, hb, hc⟩,
    fun ⟨a, ha, b, hb, hc⟩ => ⟨b, ⟨a, ha, hb⟩, hc⟩⟩

/-- Sets of paths are a lawful monad. -/
instance : LawfulMonad Paths :=
  LawfulMonad.mk' Paths (fun s => bind_pure s) (fun a f => pure_bind a f)
    (fun s f g => bind_assoc s f g)

end Paths

/-! # The layer -/

/-- The traced layer, for acts of type `A` and a state of type `σ`: from the
trace shown so far and the state, the set of the ways a computation may
end, each with a result, the trace and the state, or with UB, its reason
and the trace. -/
abbrev TraceM (A σ : Type) : Type → Type :=
  StateT (List A × σ) (ExceptT (String × List A) Paths)

/-- The event effect: `emit e` shows the event `e` to the world, and goes on
with the world's answer. -/
class MonadEvent (E Ans : Type) (m : Type → Type) where
  emit : E → m Ans

variable {A σ : Type}

/-- UB in the traced layer ends the path after the trace shown so far. -/
instance : MonadUB (TraceM A σ) := ⟨fun r st => ExceptT.mk (pure (.error (r, st.1)))⟩

/-- In the traced layer, an event may get any answer, and the act joins the
trace. -/
instance {E Ans : Type} : MonadEvent E Ans (TraceM (Act E Ans) σ) :=
  ⟨fun e st => ExceptT.mk fun x => ∃ a, x = .ok (a, (st.1 ++ [⟨e, a⟩], st.2))⟩

/-! # The lift -/

/-- A computation of the state layer, run in the traced layer: it keeps the
trace, and its UB ends the path after the trace. -/
def TraceM.lift (x : StateT σ SetM α) : TraceM A σ α := fun st => ExceptT.mk fun e =>
  (∃ a s', x st.2 (.ok (a, s')) ∧ e = .ok (a, (st.1, s'))) ∨
    (∃ r, x st.2 (.ub r) ∧ e = .error (r, st.1))

/-- Lifting `pure` is `pure`. -/
theorem TraceM.lift_pure {α : Type} (a : α) : TraceM.lift (A := A) (pure a : StateT σ SetM α) = pure a := by
  funext st e
  show _ = (e = .ok (a, st))
  apply propext
  constructor
  · rintro (⟨a', s', h, rfl⟩ | ⟨r, h, rfl⟩)
    · cases h
      rfl
    · cases h
  · rintro rfl
    exact .inl ⟨a, st.2, rfl, rfl⟩

/-- Lifting a sequence is the sequence of the lifts. -/
theorem TraceM.lift_bind {α β : Type} (x : StateT σ SetM α) (f : α → StateT σ SetM β) :
    TraceM.lift (A := A) (x >>= f) = TraceM.lift x >>= fun a => TraceM.lift (f a) := by
  funext st e
  simp only [TraceM.lift, ExceptT.mk, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, pure]
  apply propext
  constructor
  · rintro (⟨b, s'', (⟨⟨a, s'⟩, hx, hf⟩ | ⟨_, _, h⟩), rfl⟩ | ⟨r, (⟨⟨a, s'⟩, hx, hf⟩ | ⟨r', hx, h⟩), rfl⟩)
    · exact ⟨.ok (a, (st.1, s')), .inl ⟨a, s', hx, rfl⟩, .inl ⟨b, s'', hf, rfl⟩⟩
    · cases h
    · exact ⟨.ok (a, (st.1, s')), .inl ⟨a, s', hx, rfl⟩, .inr ⟨r, hf, rfl⟩⟩
    · injection h with h
      subst h
      exact ⟨.error (r, st.1), .inr ⟨r, hx, rfl⟩, rfl⟩
  · rintro ⟨r, (⟨a, s', hx, rfl⟩ | ⟨r', hx, rfl⟩), hf⟩
    · rcases hf with ⟨b, s'', hf, rfl⟩ | ⟨r, hf, rfl⟩
      · exact .inl ⟨b, s'', .inl ⟨(a, s'), hx, hf⟩, rfl⟩
      · exact .inr ⟨r, .inl ⟨(a, s'), hx, hf⟩, rfl⟩
    · cases hf
      exact .inr ⟨r', .inr ⟨r', hx, rfl⟩, rfl⟩

variable (A σ) in
/-- The lift from the state layer over the set monad into the traced layer
is a monad morphism. -/
def MonadMorphism.trace : MonadMorphism (StateT σ SetM) (TraceM A σ) where
  map := TraceM.lift
  map_pure := TraceM.lift_pure
  map_bind := TraceM.lift_bind
  map_map g x := by
    rw [map_eq_pure_bind, TraceM.lift_bind, map_eq_pure_bind]
    simp only [TraceM.lift_pure]

/-- A choice in the traced layer is the lift of a choice. -/
instance : MonadChoice (TraceM A σ) :=
  ⟨fun w => TraceM.lift (MonadChoice.choose w : StateT σ SetM (BitVec w))⟩

/-- The lift keeps choice and UB. -/
theorem MonadMorphism.trace_keeps : (MonadMorphism.trace A σ).KeepsChoiceUB where
  choose _ := rfl
  ub r := by
    funext st e
    show _ = (e = .error (r, st.1))
    apply propext
    constructor
    · rintro (⟨_, _, h, _⟩ | ⟨r', h, rfl⟩) <;> cases h
      rfl
    · rintro rfl
      exact .inr ⟨r, rfl, rfl⟩

/-! # Frames -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A frame in the traced layer enters a call before its computation and
leaves the call after, and keeps the trace. -/
instance : MonadFrame (TraceM A (Memories Mem unit)) :=
  ⟨fun x st => (fun r => (r.1, (r.2.1, r.2.2.exit))) <$> x (st.1, st.2.enter)⟩

/-- The lift keeps frames. -/
theorem MonadMorphism.trace_mapsFrame :
    (MonadMorphism.trace A (Memories Mem unit)).MapsFrame := by
  intro α x
  funext st e
  simp only [MonadMorphism.trace, MonadFrame.frame, TraceM.lift, Functor.map, ExceptT.map, ExceptT.mk,
    bind, pure, Function.comp]
  apply propext
  constructor
  · rintro (⟨a, s', (⟨⟨a₀, s₀⟩, hx, h⟩ | ⟨_, _, h⟩), rfl⟩ | ⟨r, (⟨_, _, h⟩ | ⟨r', hx, h⟩), rfl⟩)
    · cases h
      exact ⟨.ok (a₀, (st.1, s₀)), .inl ⟨a₀, s₀, hx, rfl⟩, rfl⟩
    · cases h
    · cases h
    · injection h with h
      subst h
      exact ⟨.error (r, st.1), .inr ⟨r, hx, rfl⟩, rfl⟩
  · rintro ⟨r, (⟨a, s', hx, rfl⟩ | ⟨r', hx, rfl⟩), h⟩
    · cases h
      exact .inl ⟨a, s'.exit, .inl ⟨(a, s'), hx, rfl⟩, rfl⟩
    · cases h
      exact .inr ⟨r', .inr ⟨r', hx, rfl⟩, rfl⟩

end Fir
