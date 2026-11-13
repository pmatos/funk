import Fir.Execution.Interpreter

/-!
# Running the interpreter in another monad

The interpreter is written once, for any monad. Its meaning is the run in
the set monad, but `fir-ref` cannot compute a set: it runs the interpreter
in a monad whose computations it can walk (ADR-2026-10-29-2017). This
section ties the two. A _monad morphism_ maps the computations of one monad
to those of another, and keeps the steps that runs are built from: ending
at once with a value, running one computation then another, and applying
a function to a result. When it maps each op's computation in the first
monad to the op's computation in the second, and each call's frame to a
frame, it maps the interpreter's run in the first to its run in the
second. The interpreter is written against
an abstract monad, so it cannot tell the two apart: this is the last
theorem below.

`fir-ref`'s exhaustive, scripted and sampled modes rely on it: they run
the interpreter in the tree of choices of the next section, and the morphism
from that tree to the set monad carries their results to the spec's run.

A morphism that also keeps choice and UB maps each op rule written once for
any monad with those effects to the same rule in the other monad, so a
dialect whose rules are written that way meets the theorem's condition op
by op.
-/

namespace Fir

/-- A monad morphism from `m` to `n`: it maps each computation of `m` to one
of `n`, and keeps `pure`, `bind` and `map`. -/
structure MonadMorphism (m n : Type → Type) [Monad m] [Monad n] where
  /-- The computation of `n` that a computation of `m` maps to. -/
  map : {α : Type} → m α → n α
  map_pure : ∀ {α : Type} (a : α), map (pure a) = pure a
  map_bind : ∀ {α β : Type} (x : m α) (f : α → m β), map (x >>= f) = map x >>= fun a => map (f a)
  map_map : ∀ {α β : Type} (g : α → β) (x : m α), map (g <$> x) = g <$> map x

variable {m n : Type → Type} [Monad m] [Monad n] (φ : MonadMorphism m n)

/-- A monad morphism from `m` to `n` is one from `ExceptT ε m` to
`ExceptT ε n`, which keeps the error each path may end with. -/
def MonadMorphism.except (ε : Type) : MonadMorphism (ExceptT ε m) (ExceptT ε n) where
  map x := ExceptT.mk (φ.map x.run)
  map_pure a := by
    simp only [pure, ExceptT.pure, ExceptT.run, ExceptT.mk, φ.map_pure]
  map_bind x f := by
    simp only [bind, ExceptT.bind, ExceptT.run, ExceptT.mk, φ.map_bind]
    congr 1
    funext r
    cases r <;> simp [ExceptT.bindCont, φ.map_pure]
  map_map g x := by
    simp only [Functor.map, ExceptT.map, ExceptT.run, ExceptT.mk, φ.map_bind]
    congr 1
    funext r
    cases r <;> simp [φ.map_pure]

/-- A path that ends with an error, or goes on, ends so in both monads. -/
theorem MonadMorphism.except_liftExcept {ε α : Type} (e : Except ε α) :
    (φ.except ε).map (liftExcept e) = liftExcept e := by
  cases e <;> simp [MonadMorphism.except, liftExcept, ExceptT.run, throw, throwThe,
    MonadExceptOf.throw, ExceptT.mk, pure, ExceptT.pure, φ.map_pure]

/-- A computation of `m`, lifted to `ExceptT ε m`, maps to its image,
lifted. -/
theorem MonadMorphism.except_lift {ε α : Type} (x : m α) :
    (φ.except ε).map (ExceptT.lift x) = ExceptT.lift (φ.map x) := by
  simp only [MonadMorphism.except, ExceptT.lift, ExceptT.run, ExceptT.mk, φ.map_map]

/-- The morphism maps a computation that ends with a function of the result
of another as it maps the other. -/
theorem MonadMorphism.map_bind_pure {α β : Type} {x : m α} {y : n α} (h : φ.map x = y)
    (g : α → β) : φ.map (x >>= fun a => pure (g a)) = y >>= fun a => pure (g a) := by
  rw [φ.map_bind, h]
  simp only [φ.map_pure]

/-- The morphism keeps choice and UB: it maps a choice of `w` bits to a
choice of `w` bits, and UB to UB for the same reason. A rule written once
for any monad with these two effects then means in `n` what its image of
the rule in `m` means. -/
structure MonadMorphism.KeepsChoiceUB [MonadChoice m] [MonadChoice n] [MonadUB m] [MonadUB n] :
    Prop where
  /-- A choice of bits maps to a choice of bits. -/
  choose : ∀ w, φ.map (MonadChoice.choose w) = MonadChoice.choose w
  /-- UB maps to UB, for the same reason. -/
  ub : ∀ {α : Type} (r : String), φ.map (MonadUB.ub r : m α) = MonadUB.ub r

variable [MonadFrame m] [MonadFrame n]

/-- The morphism maps running a computation as a call's frame in `m` to
running its image as a call's frame in `n`. -/
def MonadMorphism.MapsFrame : Prop :=
  ∀ {α : Type} (x : m α), φ.map (MonadFrame.frame x) = MonadFrame.frame (φ.map x)

/-- A morphism that maps frames maps them in `ExceptT ε m` too. -/
theorem MonadMorphism.except_inFrame (hf : φ.MapsFrame) {ε α : Type} (x : ExceptT ε m α) :
    (φ.except ε).map (inFrame x) = inFrame ((φ.except ε).map x) := by
  simp only [MonadMorphism.except, inFrame, ExceptT.run, ExceptT.mk]
  exact hf _

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d] [DialectCall d]
  [DialectDenote d m] [DialectDenote d n]

/-- The morphism maps each op's semantics in `m` to its semantics in `n`:
both what an op that is not a terminator gives and where a terminator
goes. -/
structure MonadMorphism.MapsDenote : Prop where
  denote : ∀ (op : d.Op) (args : HVector toType (sig op)),
    φ.map (DialectDenote.denote (m := m) op args) = DialectDenote.denote (m := n) op args
  exit : ∀ (op : d.Op) (args : HVector toType (sig op)),
    φ.map (DialectDenote.exit (m := m) op args) = DialectDenote.exit (m := n) op args

variable {φ}

/-- Running ops maps to running them in the other monad, calls included,
when the morphism maps frames to frames. -/
theorem Func.runOps_map (h : φ.MapsDenote (d := d)) (hf : φ.MapsFrame) (M : Module d) (fuel : Nat) :
    ∀ (f : Func d) (env : Env d) (os : List (Operation d)),
      (φ.except Stuck).map (Func.runOps (m := m) M fuel f env os) =
        Func.runOps (m := n) M fuel f env os := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro f env os
    match fuel, os with
    | 0, _ => simp [Func.runOps, (φ.except Stuck).map_pure]
    | _ + 1, [] => simp [Func.runOps, φ.except_liftExcept]
    | k + 1, o :: os =>
      have ih₀ := ih k (Nat.lt_succ_self k)
      have ih₁ : ∀ j, _ := fun j => ih (min j k) (Nat.lt_succ_of_le (Nat.min_le_right j k))
      simp only [Func.runOps]
      all_goals repeat' (first
        | (apply bind_congr; intro _)
        | split
        | simp only [(φ.except Stuck).map_bind, (φ.except Stuck).map_pure, φ.except_liftExcept,
            φ.except_lift, φ.except_inFrame hf, h.denote, h.exit, ih₀, ih₁])

/-- The interpreter cannot tell monads apart: a morphism that maps each
op's semantics in `m` to its semantics in `n`, and frames to frames, maps a
function's run in `m` to its run in `n`. -/
theorem Func.run_map (h : φ.MapsDenote (d := d)) (hf : φ.MapsFrame) (M : Module d) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (φ.except Stuck).map (f.run M (m := m) args fuel) = f.run M (m := n) args fuel := by
  simp only [Func.run]
  all_goals repeat' (first
    | (apply bind_congr; intro _)
    | split
    | simp only [(φ.except Stuck).map_bind, (φ.except Stuck).map_pure, φ.except_liftExcept,
        φ.except_inFrame hf, Func.runOps_map h hf])

end Fir
