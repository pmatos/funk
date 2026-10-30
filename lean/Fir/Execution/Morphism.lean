import Fir.Execution.Interpreter

/-!
# Running the interpreter in another monad

The interpreter is written once, for any monad. Its meaning is the run in
the set monad, but `fir-ref` cannot compute a set: it runs the interpreter
in a monad whose computations it can walk (ADR-2026-10-29-2017). This
section ties the two. A _monad morphism_ maps the computations of one monad
to those of another, and keeps `pure`, `bind` and `map`. When it maps each
op's computation in the first monad to the op's computation in the second,
it maps the interpreter's run in the first to its run in the second. The
interpreter is written against an abstract monad, so it cannot tell the two
apart: this is the theorem `Func.run_map`.

`fir-ref`'s exhaustive and scripted modes rely on it: they run the
interpreter in the tree of choices of the next section, and the morphism
from that tree to the set monad carries their results to the spec's run.
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

variable {d : Dialect} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
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

/-- Running ops maps to running them in the other monad. -/
theorem Func.runOps_map (h : φ.MapsDenote (d := d)) (f : Func d) :
    ∀ (fuel : Nat) (env : Env d) (os : List (Operation d)),
      (φ.except Stuck).map (f.runOps (m := m) fuel env os) = f.runOps (m := n) fuel env os
  | 0, _, _ => by simp [Func.runOps, (φ.except Stuck).map_pure]
  | _ + 1, _, [] => by simp [Func.runOps, φ.except_liftExcept]
  | k + 1, env, o :: os => by
    have ih := Func.runOps_map h f k
    simp only [Func.runOps]
    simp only [apply_ite (φ.except Stuck).map, (φ.except Stuck).map_bind, φ.except_liftExcept,
      φ.except_lift, h.denote, h.exit, ih]
    all_goals repeat' (first | (apply bind_congr; intro _) | split)
    all_goals simp only [(φ.except Stuck).map_bind, φ.except_liftExcept,
      (φ.except Stuck).map_pure, ih]

/-- The interpreter cannot tell monads apart: a morphism that maps each
op's semantics in `m` to its semantics in `n` maps a function's run in `m`
to its run in `n`. -/
theorem Func.run_map (h : φ.MapsDenote (d := d)) (f : Func d)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) :
    (φ.except Stuck).map (f.run (m := m) args fuel) = f.run (m := n) args fuel := by
  simp only [Func.run]
  all_goals repeat' (first | (apply bind_congr; intro _) | split)
  all_goals simp only [(φ.except Stuck).map_bind, φ.except_liftExcept,
    Func.runOps_map h]

end Fir
