import Fir.Execution.MemoryObligations
import Fir.Memory.FrameLaws
import Fir.Execution.Lawful

/-!
# Runs with memory

A run with memory is a run of the interpreter in the state layer over the
set monad, by the dialect's semantics with memory at a naming of its
memories, each with its layout entry (the section on memory obligations):
it starts from the empty
memories of a run, outside every call, and each path that ends carries the
memories as they are at its end. Until observations at the end of a run
are designed ([#233](https://github.com/pmatos/funk/issues/233)), an
observer sees what the run returns and not its memories, so the runs with
memory of a function are runs in the sense of the outcomes, and fuel
monotonicity, progress and refinement speak of them as they speak of runs
in the set monad.

A dialect whose ops touch no memory runs in the state layer by its rules in
the monad below: each op runs by its rule and keeps the memories. That is a
monad morphism, Lean's `StateT.lift`, which keeps frames, since a call that
allocates nothing frees nothing when it returns. A dialect whose semantics
with memory is that lift, at every naming, _lifts the set monad_: this ties
its semantics in the set monad to its semantics with memory. The run with
memory of a function of such a dialect is then its run in the set monad,
with the memories it started from; its runs with memory are its runs, and
every theorem about its runs holds of them. The dialects of the tests and
their sums lift the set monad by their definition; the core dialect runs its
own rules with memory, and lifts the set monad by a theorem.

The tie also holds of one op: an op is _tied_ when it runs with memory by
its rule in the set monad and keeps the memories. A dialect lifts the set
monad exactly when every op is tied, so a dialect can tie each op on its
own, and an op that touches memory can sit beside tied ones. Lifting keeps
choice, and UB, which ends a path in the set monad whatever follows it, so
it maps a rule written once for any monad with those effects to the same
rule in the layer: the core dialect ties its ops so.
-/

namespace Fir

open Memory

/-! # Lifting a monad into the layer -/

variable {m : Type → Type} [Monad m] [LawfulMonad m]

variable (m) in
/-- A computation with no memory, in the state layer: it runs, and keeps the
state. This is a monad morphism, Lean's `StateT.lift`. -/
def MonadMorphism.liftState (σ : Type) :
    MonadMorphism m (StateT σ m) where
  map x := StateT.lift x
  map_pure a := by
    funext s
    simp [StateT.lift, pure, StateT.pure]
  map_bind x f := by
    funext s
    simp [StateT.lift, bind, StateT.bind]
  map_map g x := by
    funext s
    simp [StateT.lift, Functor.map, StateT.map]

/-- Lifting into the layer keeps choice, and keeps UB when UB in the monad
below ends a path whatever follows it. -/
theorem MonadMorphism.liftState_keeps [MonadChoice m] [MonadUB m] (σ : Type)
    (hub : ∀ {α β : Type} (r : String) (f : α → m β), MonadUB.ub r >>= f = MonadUB.ub r) :
    (MonadMorphism.liftState m σ).KeepsChoiceUB where
  choose w := by
    funext s
    show MonadChoice.choose w >>= (fun b => pure (b, s)) =
      (fun b => (b, s)) <$> MonadChoice.choose w
    rw [map_eq_pure_bind]
  ub r := by
    funext s
    exact hub r _

/-- UB in the set monad ends a path whatever follows it. -/
theorem SetM.ub_bind {α β : Type} (r : String) (f : α → SetM β) :
    (MonadUB.ub r : SetM α) >>= f = MonadUB.ub r := by
  funext e
  apply propext
  show ((∃ a, Ev.ok a = .ub r ∧ f a e) ∨ ∃ r', Ev.ub r' = .ub r ∧ e = .ub r') ↔ e = .ub r
  constructor
  · rintro (⟨_, h, _⟩ | ⟨_, h, rfl⟩) <;> cases h
    rfl
  · rintro rfl
    exact .inr ⟨r, rfl, rfl⟩

section

variable {Mem : Type} {unit : Mem → Nat} [DecidableEq Mem]

/-- Lifting into the layer keeps frames, when a frame of the monad below is
the computation itself: entering a call and leaving it at once changes no
memory. -/
theorem MonadMorphism.liftState_mapsFrame [MonadFrame m]
    (hid : ∀ {α : Type} (x : m α), MonadFrame.frame x = x) :
    (MonadMorphism.liftState m (Memories Mem unit)).MapsFrame := by
  intro α x
  funext S
  show StateT.lift (MonadFrame.frame x) S =
    (fun r => (r.1, r.2.exit)) <$> StateT.lift x S.enter
  simp [hid, StateT.lift, Memories.exit_enter]

end

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d]

/-- A dialect's semantics in a monad with no memory, in the state layer over
it: each op runs by its rule and keeps the state. -/
@[instance_reducible] def DialectDenote.liftState (σ : Type) [DialectDenote d m] :
    DialectDenote d (StateT σ m) where
  denote op args := StateT.lift (DialectDenote.denote op args)
  exit op args := StateT.lift (DialectDenote.exit op args)

attribute [local instance] DialectDenote.liftState

/-- Lifting into the layer maps each op's semantics to its lifted
semantics. -/
theorem DialectDenote.liftState_mapsDenote (σ : Type) [DialectDenote d m] :
    (MonadMorphism.liftState m σ).MapsDenote (d := d) (n := StateT σ m) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

omit [Monad m] [LawfulMonad m] in
/-- Two semantics of a dialect in one monad are the same when each op means
the same in both, and each terminator goes to the same places. -/
theorem DialectDenote.ext {a b : DialectDenote d m}
    (hd : ∀ op args, a.denote op args = b.denote op args)
    (he : ∀ op args, a.exit op args = b.exit op args) : a = b := by
  cases a
  cases b
  congr
  · funext op args
    exact hd op args
  · funext op args
    exact he op args

/-- A dialect's semantics with memory lifts its semantics in the set monad:
wherever a run names its memories, each op runs by its rule in the set
monad and keeps the memories. This ties the two semantics: its ops touch no
memory, and its runs with memory are its runs. -/
class LiftsSetM (d : Dialect) [TyDenote d.Ty] [DialectSignature d] [DialectEffects d]
    [DialectMemDenote d] [DialectDenote d SetM] : Prop where
  lifts : ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N),
    DialectMemDenote.denoteAt lay ρ =
      DialectDenote.liftState (m := SetM) (Memories N (unitsOf lay))

section

variable [DialectEffects d] [DialectMemDenote d] [DialectDenote d SetM]

/-- The op touches no memory: wherever a run names the dialect's memories,
whatever their entries, it runs with memory by its rule in the set monad
and keeps the memories, both as an op that is not a terminator and as a
terminator. The tie of one op, so that each op of a dialect can be tied on
its own, and an op that touches memory can sit beside tied ones. -/
def OpLiftsSetM (op : d.Op) : Prop :=
  ∀ {N : Type} [DecidableEq N] (lay : N → MemLayout) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) lay ρ
    ∀ args : HVector toType (sig op),
      DialectDenote.denote (m := StateT (Memories N (unitsOf lay)) SetM) op args =
          StateT.lift (DialectDenote.denote (m := SetM) op args) ∧
        DialectDenote.exit (m := StateT (Memories N (unitsOf lay)) SetM) op args =
          StateT.lift (DialectDenote.exit (m := SetM) op args)

/-- In a dialect that lifts the set monad, every op is tied. -/
theorem LiftsSetM.opLifts [LiftsSetM d] (op : d.Op) : OpLiftsSetM op := by
  intro N _ lay ρ args
  rw [LiftsSetM.lifts lay ρ]
  exact ⟨rfl, rfl⟩

/-- A dialect whose every op is tied lifts the set monad. -/
theorem LiftsSetM.ofOpLifts (h : ∀ op : d.Op, OpLiftsSetM op) : LiftsSetM d :=
  ⟨fun lay ρ => DialectDenote.ext (fun op args => (h op lay ρ args).1)
    (fun op args => (h op lay ρ args).2)⟩

end

/-! # The runs with memory of a function -/

variable [DecidableEq d.Ty] [DialectCall d] {N : Type} [DecidableEq N] (unit : N → Nat)

/-- The run with memory of a function of a dialect whose ops touch no
memory is its run in the set monad: it keeps the memories it starts with. -/
theorem Func.memRun_eq [DialectDenote d SetM] (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (S : Memories N unit) :
    (f.run M (m := StateT (Memories N unit) SetM) args fuel).run S =
      (fun r => (r, S)) <$> (f.run M (m := SetM) args fuel).run := by
  rw [← Func.run_map (DialectDenote.liftState_mapsDenote (Memories N unit))
    (MonadMorphism.liftState_mapsFrame (fun _ => rfl)) M f args fuel]
  simp [MonadMorphism.except, MonadMorphism.liftState, StateT.lift, ExceptT.run, ExceptT.mk]

variable [DialectEffects d] [DialectMemDenote d] (lay : N → MemLayout)
  (ρ : DialectEffects.Mem d → N)

/-- The runs with memory of the function `f` of the module `M`, where a run
names the dialect's memory `x` as `ρ x`, whose layout entry is `lay (ρ x)`:
its run in the state layer over the set monad, by the dialect's
semantics with memory at that naming, from the empty memories, at each
budget, on each argument vector of its parameter types. An observer sees
what it returns. -/
def Func.memRuns (M : Module d) (f : Func d) :
    FuncRuns (HVector toType (f.params.map (·.2))) (List (DVal d)) :=
  letI := DialectMemDenote.denoteAt (d := d) lay ρ
  fun args fuel => Functor.map (f := SetM) Prod.fst
    ((f.run M (m := StateT (Memories N (unitsOf lay)) SetM) args fuel).run Memories.empty)

variable [DialectDenote d SetM]

/-- The runs with memory of the functions of a dialect that lifts the set
monad are their runs, at every naming of its memories. -/
theorem Func.memRuns_eq [LiftsSetM d] (M : Module d) (f : Func d) :
    f.memRuns lay ρ M = f.runs M := by
  funext args fuel
  unfold Func.memRuns
  rw [LiftsSetM.lifts lay ρ, Func.memRun_eq]
  simp only [Functor.map_map, id_map']
  rfl

/-! # Refinement, with no memory touched -/

variable [LiftsSetM d] [DialectValidation d] [TyPoison d.Ty] [TyRefinement d.Ty]
  [LawfulDialectPoison d]
  {ctx : ModuleContext d} {M : Module d}

/-- Congruence in the callee, with memory: for a lawful dialect whose ops
touch no memory, in a valid module, replacing the body of its function `@g`
with one under which `@g` refines itself with memory refines every function
of the module with memory. It asks what the theorem on runs asks. -/
theorem Func.memRuns_replaceBody_isRefinedBy_of_lawful
    (hrefl : ∀ {t : d.Ty} (v : ⟦t⟧), TyRefinement.IsRefinedBy v v)
    (htrans : ∀ {t : d.Ty} {u v w : ⟦t⟧}, TyRefinement.IsRefinedBy u v →
      TyRefinement.IsRefinedBy v w → TyRefinement.IsRefinedBy u w)
    (hM : M.Valid) {g : Func d} (hg : g ∈ M.funcs) (b : Region d)
    (hfin : ∃ L : List (HVector toType (g.params.map (·.2))), ∀ a, a ∈ L)
    (h : g.memRuns lay ρ M ⊑
      (g.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b))
    {f : Func d} (hf : f ∈ M.funcs) :
    f.memRuns lay ρ M ⊑ (f.replaceBody g.name b).memRuns lay ρ (M.replaceBody g.name b) := by
  rw [Func.memRuns_eq, Func.memRuns_eq] at h ⊢
  exact Func.runs_replaceBody_isRefinedBy_of_lawful hrefl htrans hM hg b hfin h hf

end Fir
