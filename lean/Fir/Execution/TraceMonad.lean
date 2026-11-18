import Fir.Execution.Trace
import Fir.Execution.MemoryState

/-!
# The traced layer

A run with memory runs in the state layer over the set monad. There, UB ends
a path and takes everything with it: the set monad's UB carries only its
reason. A traced run must keep the acts it showed before UB, since UB in
the source allows only a target that first shows them. So a traced run
runs in a layer of its own, the _traced layer_, in which UB carries the
trace.

A computation of the traced layer starts from a state, the memories, and
each of its paths ends with a result, the trace that the computation showed
and the state, or with UB, its reason and the trace it showed:

$$`\mathrm{TraceM}\,A\,\sigma\,\alpha = \sigma \to
  \mathrm{Paths}(\mathrm{Except}\,(\mathrm{String} \times \mathrm{List}\,A)\,
    (\alpha \times \mathrm{List}\,A \times \sigma))`

where a set of paths is a set monad with no UB of its own. A sequence shows
the trace of its first computation, then that of the second: a computation
never reads the trace shown before it.

The layer has the effects of the state layer: a choice, of bits or of a
NaN, UB, and frames, which enter a call before its computation and leave it
after. It adds the _event effect_: `emit e` shows the event `e` to the
world, and goes on with the world's answer. Every world counts, so in the layer an event may
get any answer, and the computation shows the act that holds the event and
its answer.

A computation of the state layer runs in the traced layer by showing
nothing. This _lift_ is a monad morphism, keeps choice and UB, and keeps
frames. Mapping the acts of every trace, each act to a list of acts, is a
monad morphism too, since it maps a concatenation to the concatenation of
the images; it keeps choice, UB and frames.
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

/-- One way a traced computation may end, for acts of type `A`: with a
result, the trace it showed and the state, or with UB, its reason and the
trace it showed. -/
abbrev TraceEnd (A σ α : Type) : Type := Except (String × List A) (α × List A × σ)

/-- The traced layer, for acts of type `A` and a state of type `σ`: from the
state, the set of the ways a computation may end. -/
def TraceM (A σ α : Type) : Type := σ → Paths (TraceEnd A σ α)

variable {A B C σ α β γ : Type}

/-- The way a path ends, after the trace `t` shown before it. -/
def TraceEnd.after (t : List A) : TraceEnd A σ α → TraceEnd A σ α
  | .ok (a, t', s) => .ok (a, t ++ t', s)
  | .error (r, t') => .error (r, t ++ t')

/-- After no trace, a path ends as it did. -/
@[simp] theorem TraceEnd.after_nil (e : TraceEnd A σ α) : e.after [] = e := by
  cases e <;> rfl

/-- After two traces, a path ends as after their concatenation. -/
theorem TraceEnd.after_after (t t' : List A) (e : TraceEnd A σ α) :
    (e.after t').after t = e.after (t ++ t') := by
  cases e <;> simp [after, List.append_assoc]

namespace TraceM

instance : Monad (TraceM A σ) where
  pure a s := fun e => e = .ok (a, [], s)
  bind x f s := fun e => ∃ r, x s r ∧ match r with
    | .ok (a, t, s') => ∃ e', f a s' e' ∧ e = e'.after t
    | .error er => e = .error er

/-- The ways a sequence ends: each way its first computation ends with a
result, followed by a way its second ends, after the first's trace; and each
way its first ends in UB. -/
theorem bind_apply (x : TraceM A σ α) (f : α → TraceM A σ β) (s : σ) (e : TraceEnd A σ β) :
    (x >>= f) s e ↔ (∃ a t s' e', x s (.ok (a, t, s')) ∧ f a s' e' ∧ e = e'.after t) ∨
      ∃ r t, x s (.error (r, t)) ∧ e = .error (r, t) := by
  constructor
  · rintro ⟨(⟨r, t⟩ | ⟨a, t, s'⟩), h, he⟩
    · exact .inr ⟨r, t, h, he⟩
    · obtain ⟨e', hf, rfl⟩ := he
      exact .inl ⟨a, t, s', e', h, hf, rfl⟩
  · rintro (⟨a, t, s', e', h, hf, rfl⟩ | ⟨r, t, h, rfl⟩)
    · exact ⟨_, h, e', hf, rfl⟩
    · exact ⟨_, h, rfl⟩

/-- `pure` then `f` is `f`. -/
theorem pure_bind (a : α) (f : α → TraceM A σ β) : (pure a >>= f) = f a := by
  funext s e
  apply propext
  rw [bind_apply]
  constructor
  · rintro (⟨_, _, _, e', h, hf, rfl⟩ | ⟨_, _, h, _⟩) <;> cases (h : _ = _)
    simpa using hf
  · intro h
    exact .inl ⟨a, [], s, e, rfl, h, (TraceEnd.after_nil e).symm⟩

/-- `x` then `pure` is `x`. -/
theorem bind_pure (x : TraceM A σ α) : (x >>= pure) = x := by
  funext s e
  apply propext
  rw [bind_apply]
  constructor
  · rintro (⟨a, t, s', _, h, he, rfl⟩ | ⟨r, t, h, rfl⟩)
    · cases (he : _ = _)
      simpa [TraceEnd.after] using h
    · exact h
  · intro h
    rcases e with ⟨r, t⟩ | ⟨a, t, s'⟩
    · exact .inr ⟨r, t, h, rfl⟩
    · exact .inl ⟨a, t, s', _, h, rfl, by simp [TraceEnd.after]⟩

/-- Binds associate. -/
theorem bind_assoc (x : TraceM A σ α) (f : α → TraceM A σ β) (g : β → TraceM A σ γ) :
    (x >>= f >>= g) = x >>= fun a => f a >>= g := by
  funext s e
  apply propext
  simp only [bind_apply]
  constructor
  · rintro (⟨b, t₂, s₂, e₃, h₁₂, hg, rfl⟩ | ⟨r, t, h₁₂, rfl⟩)
    · rcases h₁₂ with ⟨a, t₁, s₁, e₂, hx, hf, he₂⟩ | ⟨_, _, _, he₂⟩
      · rcases e₂ with ⟨_, _⟩ | ⟨_, _, _⟩ <;> cases he₂
        exact .inl ⟨a, t₁, s₁, _, hx, .inl ⟨_, _, _, e₃, hf, hg, rfl⟩,
          by rw [TraceEnd.after_after]⟩
      · cases he₂
    · rcases h₁₂ with ⟨a, t₁, s₁, e₂, hx, hf, he₂⟩ | ⟨r', t', hx, he₂⟩
      · rcases e₂ with ⟨_, _⟩ | ⟨_, _, _⟩ <;> cases he₂
        exact .inl ⟨a, t₁, s₁, _, hx, .inr ⟨_, _, hf, rfl⟩, rfl⟩
      · cases he₂
        exact .inr ⟨_, _, hx, rfl⟩
  · rintro (⟨a, t₁, s₁, e', hx, h₂, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · rcases h₂ with ⟨b, t₂, s₂, e₃, hf, hg, rfl⟩ | ⟨r, t₂, hf, rfl⟩
      · exact .inl ⟨b, t₁ ++ t₂, s₂, e₃, .inl ⟨a, t₁, s₁, _, hx, hf, rfl⟩, hg,
          by rw [TraceEnd.after_after]⟩
      · exact .inr ⟨r, t₁ ++ t₂, .inl ⟨a, t₁, s₁, _, hx, hf, rfl⟩, rfl⟩
    · exact .inr ⟨r, t, .inr ⟨r, t, hx, rfl⟩, rfl⟩

/-- The traced layer is a lawful monad. -/
instance : LawfulMonad (TraceM A σ) :=
  LawfulMonad.mk' (TraceM A σ) (fun x => bind_pure x) (fun a f => pure_bind a f)
    (fun x f g => bind_assoc x f g)

end TraceM

/-- The event effect: `emit e` shows the event `e` to the world, and goes on
with the world's answer. -/
class MonadEvent (E Ans : outParam Type) (m : Type → Type) where
  emit : E → m Ans

/-- UB in the traced layer ends the path, showing nothing more. -/
instance : MonadUB (TraceM A σ) := ⟨fun r _ e => e = .error (r, [])⟩

/-- In the traced layer, an event may get any answer, and the computation
shows the act. -/
instance {E Ans : Type} : MonadEvent E Ans (TraceM (Act E Ans) σ) :=
  ⟨fun ev s e => ∃ a, e = .ok (a, [⟨ev, a⟩], s)⟩

/-! # The lift -/

/-- A computation of the state layer, run in the traced layer: it shows
nothing, and its UB ends the path. -/
def TraceM.lift (x : StateT σ SetM α) : TraceM A σ α := fun s e =>
  (∃ a s', x s (.ok (a, s')) ∧ e = .ok (a, [], s')) ∨ (∃ r, x s (.ub r) ∧ e = .error (r, []))

/-- Lifting `pure` is `pure`. -/
theorem TraceM.lift_pure (a : α) : TraceM.lift (A := A) (pure a : StateT σ SetM α) = pure a := by
  funext s e
  apply propext
  constructor
  · rintro (⟨_, _, h, rfl⟩ | ⟨_, h, _⟩) <;> cases h
    rfl
  · rintro rfl
    exact .inl ⟨a, s, rfl, rfl⟩

/-- Lifting a sequence is the sequence of the lifts. -/
theorem TraceM.lift_bind (x : StateT σ SetM α) (f : α → StateT σ SetM β) :
    TraceM.lift (A := A) (x >>= f) = TraceM.lift x >>= fun a => TraceM.lift (f a) := by
  funext s e
  apply propext
  rw [TraceM.bind_apply]
  constructor
  · rintro (⟨b, s'', (⟨⟨a, s'⟩, hx, hf⟩ | ⟨_, _, h⟩), rfl⟩ |
      ⟨r, (⟨⟨a, s'⟩, hx, hf⟩ | ⟨r', hx, h⟩), rfl⟩)
    · exact .inl ⟨a, [], s', _, .inl ⟨a, s', hx, rfl⟩, .inl ⟨b, s'', hf, rfl⟩, rfl⟩
    · cases h
    · exact .inl ⟨a, [], s', _, .inl ⟨a, s', hx, rfl⟩, .inr ⟨r, hf, rfl⟩, rfl⟩
    · injection h with h
      subst h
      exact .inr ⟨r, [], .inr ⟨r, hx, rfl⟩, rfl⟩
  · rintro (⟨a, t, s', e', hx, hf, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · rcases hx with ⟨_, _, hx, he⟩ | ⟨_, _, he⟩ <;> cases he
      rcases hf with ⟨b, s'', hf, rfl⟩ | ⟨r, hf, rfl⟩
      · exact .inl ⟨b, s'', .inl ⟨(_, _), hx, hf⟩, rfl⟩
      · exact .inr ⟨r, .inl ⟨(_, _), hx, hf⟩, rfl⟩
    · rcases hx with ⟨_, _, _, he⟩ | ⟨_, hx, he⟩ <;> cases he
      exact .inr ⟨_, .inr ⟨_, hx, rfl⟩, rfl⟩

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
instance : MonadChoice (TraceM A σ) where
  choose w := TraceM.lift (MonadChoice.choose w : StateT σ SetM (BitVec w))
  chooseNaN e mb := TraceM.lift (MonadChoice.chooseNaN e mb : StateT σ SetM (BitVec (mb + 1)))

/-- The lift keeps choice and UB. -/
theorem MonadMorphism.trace_keeps : (MonadMorphism.trace A σ).KeepsChoiceUB where
  choose _ := rfl
  chooseNaN _ _ := rfl
  ub r := by
    funext s e
    apply propext
    constructor
    · rintro (⟨_, _, h, _⟩ | ⟨r', h, rfl⟩) <;> cases h
      rfl
    · rintro rfl
      exact .inr ⟨r, rfl, rfl⟩

/-! # Mapping the acts of traces -/

/-- The way a path ends, with each act `a` of its trace replaced by the acts
`g a`. -/
def TraceEnd.mapActs (g : A → List B) : TraceEnd A σ α → TraceEnd B σ α
  | .ok (a, t, s) => .ok (a, t.flatMap g, s)
  | .error (r, t) => .error (r, t.flatMap g)

/-- Mapping acts after a trace maps the trace too. -/
theorem TraceEnd.mapActs_after (g : A → List B) (t : List A) (e : TraceEnd A σ α) :
    (e.after t).mapActs g = (e.mapActs g).after (t.flatMap g) := by
  cases e <;> simp [after, mapActs]

/-- A computation of the traced layer, with each act `a` of its traces
replaced by the acts `g a`. -/
def TraceM.mapActs (g : A → List B) (x : TraceM A σ α) : TraceM B σ α :=
  fun s e => ∃ e', x s e' ∧ e = e'.mapActs g

/-- Mapping the acts of `pure` is `pure`. -/
theorem TraceM.mapActs_pure (g : A → List B) (a : α) :
    TraceM.mapActs (σ := σ) g (pure a) = pure a := by
  funext s e
  exact propext ⟨fun ⟨_, h, he⟩ => by cases (h : _ = _); exact he, fun h => ⟨_, rfl, h⟩⟩

/-- Mapping the acts of a sequence is the sequence of the images. -/
theorem TraceM.mapActs_bind (g : A → List B) (x : TraceM A σ α) (f : α → TraceM A σ β) :
    TraceM.mapActs g (x >>= f) = TraceM.mapActs g x >>= fun a => TraceM.mapActs g (f a) := by
  funext s e
  apply propext
  rw [TraceM.bind_apply]
  constructor
  · rintro ⟨e₀, h, rfl⟩
    rcases (TraceM.bind_apply _ _ _ _).1 h with ⟨a, t, s', e', hx, hf, rfl⟩ | ⟨r, t, hx, rfl⟩
    · exact .inl ⟨a, t.flatMap g, s', _, ⟨_, hx, rfl⟩, ⟨e', hf, rfl⟩, TraceEnd.mapActs_after _ _ _⟩
    · exact .inr ⟨r, t.flatMap g, ⟨_, hx, rfl⟩, rfl⟩
  · rintro (⟨a, t, s', e', ⟨e₁, hx, he₁⟩, ⟨e₂, hf, rfl⟩, rfl⟩ | ⟨r, t, ⟨e₁, hx, he₁⟩, rfl⟩)
    · rcases e₁ with ⟨_, _⟩ | ⟨a₁, t₁, s₁⟩ <;> cases he₁
      exact ⟨_, (TraceM.bind_apply _ _ _ _).2 (.inl ⟨_, _, _, _, hx, hf, rfl⟩),
        (TraceEnd.mapActs_after _ _ _).symm⟩
    · rcases e₁ with ⟨r₁, t₁⟩ | ⟨_, _, _⟩ <;> cases he₁
      exact ⟨_, (TraceM.bind_apply _ _ _ _).2 (.inr ⟨_, _, hx, rfl⟩), rfl⟩

variable (σ) in
/-- Mapping the acts of traces is a monad morphism. -/
def MonadMorphism.mapActs (g : A → List B) : MonadMorphism (TraceM A σ) (TraceM B σ) where
  map := TraceM.mapActs g
  map_pure := TraceM.mapActs_pure g
  map_bind := TraceM.mapActs_bind g
  map_map h x := by
    rw [map_eq_pure_bind, TraceM.mapActs_bind, map_eq_pure_bind]
    simp only [TraceM.mapActs_pure]

/-- Mapping acts twice maps each act to the acts of the images of its
images. -/
theorem TraceM.mapActs_mapActs (g : B → List C) (h : A → List B) (x : TraceM A σ α) :
    TraceM.mapActs g (TraceM.mapActs h x) = TraceM.mapActs (fun a => (h a).flatMap g) x := by
  funext s e
  apply propext
  constructor
  · rintro ⟨_, ⟨e', hx, rfl⟩, rfl⟩
    refine ⟨e', hx, ?_⟩
    cases e' <;> simp [TraceEnd.mapActs, List.flatMap_assoc]
  · rintro ⟨e', hx, rfl⟩
    refine ⟨_, ⟨e', hx, rfl⟩, ?_⟩
    cases e' <;> simp [TraceEnd.mapActs, List.flatMap_assoc]

/-- Mapping each act to itself changes nothing. -/
theorem TraceM.mapActs_singleton (x : TraceM A σ α) : TraceM.mapActs (fun a => [a]) x = x := by
  funext s e
  apply propext
  constructor
  · rintro ⟨e', hx, rfl⟩
    cases e' <;> simpa [TraceEnd.mapActs] using hx
  · intro hx
    exact ⟨e, hx, by cases e <;> simp [TraceEnd.mapActs]⟩

/-- Mapping the acts of a lift changes nothing, since a lift shows nothing. -/
theorem TraceM.mapActs_lift (g : A → List B) (x : StateT σ SetM α) :
    TraceM.mapActs g (TraceM.lift x) = TraceM.lift x := by
  funext s e
  apply propext
  constructor
  · rintro ⟨_, (⟨a, s', h, rfl⟩ | ⟨r, h, rfl⟩), rfl⟩
    · exact .inl ⟨a, s', h, rfl⟩
    · exact .inr ⟨r, h, rfl⟩
  · rintro (⟨a, s', h, rfl⟩ | ⟨r, h, rfl⟩)
    · exact ⟨_, .inl ⟨a, s', h, rfl⟩, rfl⟩
    · exact ⟨_, .inr ⟨r, h, rfl⟩, rfl⟩

/-- Mapping acts keeps choice and UB, since a choice and UB show nothing. -/
theorem MonadMorphism.mapActs_keeps (g : A → List B) :
    (MonadMorphism.mapActs σ g).KeepsChoiceUB where
  choose _ := TraceM.mapActs_lift g _
  chooseNaN _ _ := TraceM.mapActs_lift g _
  ub r := by
    funext s e
    exact propext ⟨fun ⟨_, h, he⟩ => by cases (h : _ = _); exact he, fun h => ⟨_, rfl, h⟩⟩

/-! # Frames -/

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- A frame in the traced layer enters a call before its computation and
leaves the call after. -/
instance : MonadFrame (TraceM A (Memories Mem unit)) :=
  ⟨fun x S e => ∃ e', x S.enter e' ∧ e = e'.map fun r => (r.1, r.2.1, r.2.2.exit)⟩

/-- The lift keeps frames. -/
theorem MonadMorphism.trace_mapsFrame :
    (MonadMorphism.trace A (Memories Mem unit)).MapsFrame := by
  intro α x
  funext S e
  apply propext
  constructor
  · rintro (⟨a, s', ⟨⟨a₀, s₀⟩, hx, h⟩ | ⟨_, _, h⟩, rfl⟩ | ⟨r, ⟨_, _, h⟩ | ⟨r', hx, h⟩, rfl⟩)
    · cases h
      exact ⟨_, .inl ⟨a₀, s₀, hx, rfl⟩, rfl⟩
    · cases h
    · cases h
    · injection h with h
      subst h
      exact ⟨_, .inr ⟨r, hx, rfl⟩, rfl⟩
  · rintro ⟨_, (⟨a, s', hx, rfl⟩ | ⟨r', hx, rfl⟩), rfl⟩
    · exact .inl ⟨a, s'.exit, .inl ⟨(a, s'), hx, rfl⟩, rfl⟩
    · exact .inr ⟨r', .inr ⟨r', hx, rfl⟩, rfl⟩

/-- Mapping acts keeps frames. -/
theorem MonadMorphism.mapActs_mapsFrame (g : A → List B) :
    (MonadMorphism.mapActs (Memories Mem unit) g).MapsFrame := by
  intro α x
  funext S e
  apply propext
  constructor
  · rintro ⟨_, ⟨e', hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨e', hx, rfl⟩, by cases e' <;> rfl⟩
  · rintro ⟨_, ⟨e', hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨e', hx, rfl⟩, by cases e' <;> rfl⟩

end Fir
