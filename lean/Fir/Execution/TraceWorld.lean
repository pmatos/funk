import Fir.Execution.TraceMonad

/-!
# The world's view of memory

The world outside the program never sees the program's allocation ids
(ADR-2026-11-09-1540). It knows an allocation only once the allocation has
escaped to it, and it names it by its _handle_: its place in the list of
the allocations that escaped, in the order they escaped. The source and the
target of a pass number their allocations each in its own order, but the
world answers the same events with the same handles, so its answers can be
compared as they are.

So a traced run carries, beside its memories, the list of the allocations
that escaped, each by its memory: its _traced state_. A run starts with
nothing escaped.

* An op that hands an address to code outside the program _escapes_ its
  allocation: the allocation joins the list, if it is not in it, and the op
  gets its handle. Only a live allocation can escape: a dangling pointer
  is poison in the comparison of two runs, so it hands out nothing.
  Which ops escape what is theirs to say: an external call escapes each
  allocation that its pointer arguments, or the allocations that already
  escaped, reach when it is made, since a pointer stored into escaped
  memory is handed out too, as in LLVM's capture tracking; so the world
  can reach nothing that has not escaped. It escapes them in an order that
  depends on the arguments and on where each pointer is stored, never on
  allocation ids, so that a source and a target give the same allocations
  the same handles.
* An op shows an event, and the world answers it with a result and with
  _actions_ on escaped memory, taken in order: it may write units into an
  escaped live allocation, inside it; create a heap allocation in a memory,
  aligned to a power of two, which escapes from the start; and free an
  escaped live heap allocation. An event that hands control to code that
  may act on escaped memory, such as an external call, is shown by `ask`
  below, not by the bare event effect, which lets the world take no action.
  A unit the world writes may hold a fragment of a pointer, which names its
  allocation by its handle. The act records the event, the result and the
  actions, so the world's actions are part of its answer.

A computation of the state layer runs in the traced layer on the memories of
the traced state, showing nothing and keeping what escaped. That lift is a
monad morphism, keeps choice and UB, and keeps frames: a frame enters a call
on the memories, and leaves it, freeing its stack allocations, which may
have escaped. Mapping the acts of traces keeps frames too.
-/

namespace Fir

open Memory

variable {Mem : Type} {unit : Mem → Nat} {A B : Type}

/-- The state of a traced run: its memories, and the allocations that
escaped to the world, each by its memory, in the order they escaped. The
world names the allocation at place `k` of the list by the handle `k`. -/
structure TraceState (Mem : Type) (unit : Mem → Nat) where
  mem : Memories Mem unit
  escaped : List (Mem × AllocId)

/-- The traced state before anything runs: the memories `S` a run starts
with, which hold its starting allocations outside every call, and nothing
escaped. -/
def TraceState.init (S : Memories Mem unit) : TraceState Mem unit := ⟨S, []⟩

/-! # The lift -/

variable {α β : Type}

/-- A computation of the state layer, run in the traced layer on the
memories of the traced state: it shows nothing, keeps what escaped, and its
UB ends the path. -/
def TraceM.liftMem (x : StateT (Memories Mem unit) SetM α) : TraceM A (TraceState Mem unit) α :=
  fun s e => (∃ a S', x s.mem (.ok (a, S')) ∧ e = .ok (a, [], { s with mem := S' })) ∨
    (∃ r, x s.mem (.ub r) ∧ e = .error (r, []))

/-- Lifting `pure` is `pure`. -/
theorem TraceM.liftMem_pure (a : α) :
    TraceM.liftMem (A := A) (pure a : StateT (Memories Mem unit) SetM α) = pure a := by
  funext s e
  apply propext
  constructor
  · rintro (⟨_, _, h, rfl⟩ | ⟨_, h, _⟩) <;> cases h
    rfl
  · rintro rfl
    exact .inl ⟨a, s.mem, rfl, rfl⟩

/-- Lifting a sequence is the sequence of the lifts. -/
theorem TraceM.liftMem_bind (x : StateT (Memories Mem unit) SetM α)
    (f : α → StateT (Memories Mem unit) SetM β) :
    TraceM.liftMem (A := A) (x >>= f) = TraceM.liftMem x >>= fun a => TraceM.liftMem (f a) := by
  funext s e
  apply propext
  rw [TraceM.bind_apply]
  constructor
  · rintro (⟨b, S'', (⟨⟨a, S'⟩, hx, hf⟩ | ⟨_, _, h⟩), rfl⟩ |
      ⟨r, (⟨⟨a, S'⟩, hx, hf⟩ | ⟨r', hx, h⟩), rfl⟩)
    · exact .inl ⟨a, [], { s with mem := S' }, _, .inl ⟨a, S', hx, rfl⟩,
        .inl ⟨b, S'', hf, rfl⟩, rfl⟩
    · cases h
    · exact .inl ⟨a, [], { s with mem := S' }, _, .inl ⟨a, S', hx, rfl⟩, .inr ⟨r, hf, rfl⟩, rfl⟩
    · injection h with h
      subst h
      exact .inr ⟨r, [], .inr ⟨r, hx, rfl⟩, rfl⟩
  · rintro (⟨a, t, s', e', hx, hf, rfl⟩ | ⟨r, t, hx, rfl⟩)
    · rcases hx with ⟨_, S', hx, he⟩ | ⟨_, _, he⟩ <;> cases he
      rcases hf with ⟨b, S'', hf, rfl⟩ | ⟨r, hf, rfl⟩
      · exact .inl ⟨b, S'', .inl ⟨(_, _), hx, hf⟩, rfl⟩
      · exact .inr ⟨r, .inl ⟨(_, _), hx, hf⟩, rfl⟩
    · rcases hx with ⟨_, _, _, he⟩ | ⟨_, hx, he⟩ <;> cases he
      exact .inr ⟨_, .inr ⟨_, hx, rfl⟩, rfl⟩

variable (A Mem unit) in
/-- The lift from the state layer over the set monad into the traced layer,
on the memories of the traced state, is a monad morphism. -/
def MonadMorphism.traceMem : MonadMorphism (StateT (Memories Mem unit) SetM)
    (TraceM A (TraceState Mem unit)) where
  map := TraceM.liftMem
  map_pure := TraceM.liftMem_pure
  map_bind := TraceM.liftMem_bind
  map_map g x := by
    rw [map_eq_pure_bind, TraceM.liftMem_bind, map_eq_pure_bind]
    simp only [TraceM.liftMem_pure]

/-- Lifting a computation that keeps the memories, on the memories of the
traced state, is lifting it on the traced state. -/
theorem TraceM.liftMem_keep {γ : Type} (y : SetM γ) :
    TraceM.liftMem (A := A) (fun S => (fun c => (c, S)) <$> y : StateT (Memories Mem unit) SetM γ) =
      TraceM.lift (fun s => (fun c => (c, s)) <$> y : StateT (TraceState Mem unit) SetM γ) := by
  funext s e
  apply propext
  constructor
  · rintro (⟨c, S', (⟨a, ha, he⟩ | ⟨_, _, he⟩), rfl⟩ | ⟨r, (⟨_, _, he⟩ | ⟨r', hr, he⟩), rfl⟩) <;>
      cases he
    · exact .inl ⟨_, s, .inl ⟨_, ha, rfl⟩, rfl⟩
    · exact .inr ⟨_, .inr ⟨_, hr, rfl⟩, rfl⟩
  · rintro (⟨c, s', (⟨a, ha, he⟩ | ⟨_, _, he⟩), rfl⟩ | ⟨r, (⟨_, _, he⟩ | ⟨r', hr, he⟩), rfl⟩) <;>
      cases he
    · exact .inl ⟨_, s.mem, .inl ⟨_, ha, rfl⟩, rfl⟩
    · exact .inr ⟨_, .inr ⟨_, hr, rfl⟩, rfl⟩

/-- The lift keeps choice and UB. -/
theorem MonadMorphism.traceMem_keeps : (MonadMorphism.traceMem Mem unit A).KeepsChoiceUB := by
  refine ⟨fun w => TraceM.liftMem_keep _, fun e mb => TraceM.liftMem_keep _, fun r => ?_⟩
  · funext s e
    apply propext
    constructor
    · rintro (⟨_, _, h, _⟩ | ⟨r', h, rfl⟩) <;> cases h
      rfl
    · rintro rfl
      exact .inr ⟨r, rfl, rfl⟩

/-! # Frames -/

variable [DecidableEq Mem]

/-- A frame in the traced layer enters a call on the memories before its
computation and leaves the call after, freeing its stack allocations. What
escaped stays escaped. -/
instance : MonadFrame (TraceM A (TraceState Mem unit)) :=
  ⟨fun x s e => ∃ e', x { s with mem := s.mem.enter } e' ∧
    e = e'.map fun r => (r.1, r.2.1, { r.2.2 with mem := r.2.2.mem.exit })⟩

/-- The lift keeps frames. -/
theorem MonadMorphism.traceMem_mapsFrame : (MonadMorphism.traceMem Mem unit A).MapsFrame := by
  intro α x
  funext s e
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
    (MonadMorphism.mapActs (TraceState Mem unit) g).MapsFrame := by
  intro α x
  funext S e
  apply propext
  constructor
  · rintro ⟨_, ⟨e', hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨e', hx, rfl⟩, by cases e' <;> rfl⟩
  · rintro ⟨_, ⟨e', hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨e', hx, rfl⟩, by cases e' <;> rfl⟩

/-! # Escaping -/

/-- The allocation `a` of the memory `x` escapes: its handle, its place in
the list of escaped allocations, which it joins at the end when it is not
in it yet. Only a live allocation escapes: an id that the memory has not
allocated, or a freed allocation, which a dangling pointer points into and
which is poison in the comparison of two runs (ADR-2026-11-09-1540), has no
handle, and nothing escapes. -/
def TraceState.escape (s : TraceState Mem unit) (x : Mem) (a : AllocId) :
    Option Nat × TraceState Mem unit :=
  if ((s.mem.mem x).blocks[a]?.map (·.live)) = some true then
    match s.escaped.idxOf? (x, a) with
    | some k => (some k, s)
    | none => (some s.escaped.length, { s with escaped := s.escaped ++ [(x, a)] })
  else (none, s)

/-- The escape effect: `escape x a` lets the allocation `a` of the memory `x`
escape, and gives its handle, if it is live. -/
def TraceM.escape (x : Mem) (a : AllocId) : TraceM A (TraceState Mem unit) (Option Nat) :=
  fun s e => e = .ok ((s.escape x a).1, [], (s.escape x a).2)

/-- The allocation that the handle `k` names, if any. -/
def TraceM.handle (k : Nat) : TraceM A (TraceState Mem unit) (Option (Mem × AllocId)) :=
  fun s e => e = .ok (s.escaped[k]?, [], s)

/-! # The world's actions -/

/-- A unit that the world writes: bits, poison, or the fragment `i` of a
pointer of the memory numbered `m`, into the escaped allocation of handle
`h`, if any, at the offset `o`. -/
inductive WUnit where
  | bits (b : Nat)
  | poison
  | frag (m : Nat) (h : Option Nat) (o : Int) (i : Nat)
  deriving Repr, DecidableEq

/-- An action of the world on escaped memory: write units into the escaped
allocation of handle `h`, from the offset `o`; create a heap allocation of
`n` units aligned to `2 ^ k` in the memory numbered `m`, as every
allocation's alignment is a power of two (the human's ruling of 2026-11-11
on #231); or free the escaped allocation of handle `h`. -/
inductive WorldAct where
  | store (h o : Nat) (us : List WUnit)
  | alloc (m n k : Nat)
  | free (h : Nat)
  deriving Repr, DecidableEq

/-- A unit the world writes, as a unit of a memory whose units are `w` bits
wide, where the memory numbered `n` is `μ n` and the handles name the
allocations of `esc`: its bits, taken modulo `2 ^ w`, or a fragment of a
pointer into the allocation that its handle names, which must be in the
pointer's memory. -/
def WUnit.resolve (μ : Nat → Mem) (esc : List (Mem × AllocId)) (w : Nat) :
    WUnit → Option (MemUnit w)
  | .bits b => some (.bits (BitVec.ofNat w b))
  | .poison => some .poison
  | .frag m none o i => some (.frag m ⟨none, o⟩ i)
  | .frag m (some h) o i => match esc[h]? with
    | some (x, a) => if x = μ m then some (.frag m ⟨some a, o⟩ i) else none
    | none => none

/-- The world's action, on the traced state, where the memory numbered `n`
is `μ n`: the traced state after it, or none when the world cannot take it.
It writes only inside an escaped live allocation, and frees only an escaped
live heap allocation; an allocation it creates escapes at once. -/
def WorldAct.apply (μ : Nat → Mem) : WorldAct → TraceState Mem unit → Option (TraceState Mem unit)
  | .store h o us, s => do
    let (x, a) ← s.escaped[h]?
    let us' ← us.mapM (WUnit.resolve μ s.escaped (unit x))
    match s.mem.store x ⟨some a, o⟩ us' 1 with
    | .ok S => some { s with mem := S }
    | .error _ => none
  | .alloc m n k, s =>
    some ⟨(s.mem.alloc (μ m) .heap n (2 ^ k)).2,
      s.escaped ++ [(μ m, (s.mem.mem (μ m)).blocks.length)]⟩
  | .free h, s => do
    let (x, a) ← s.escaped[h]?
    let b ← (s.mem.mem x).blocks[a]?
    if b.kind = .heap ∧ b.live then some { s with mem := s.mem.free x a } else none

/-- The world's actions, in order. -/
def WorldAct.applyAll (μ : Nat → Mem) : List WorldAct → TraceState Mem unit →
    Option (TraceState Mem unit)
  | [], s => some s
  | w :: ws, s => (w.apply μ s).bind (applyAll μ ws)

/-- The event effect with the world's memory: `ask μ e` shows the event `e`,
and the world answers with a result and actions on escaped memory, which
it takes. Every world counts, so in the layer an event may get any result
and any actions the world can take, and the act records the event, the
result and the actions. -/
def TraceM.ask {E Ans : Type} (μ : Nat → Mem) (ev : E) :
    TraceM (Act E (Ans × List WorldAct)) (TraceState Mem unit) Ans :=
  fun s e => ∃ a ws s', WorldAct.applyAll μ ws s = some s' ∧ e = .ok (a, [⟨ev, (a, ws)⟩], s')

end Fir
