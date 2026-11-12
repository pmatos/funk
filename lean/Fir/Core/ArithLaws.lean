import Fir.Core.Semantics
import Fir.Core.Poison

/-!
# Constants are lawful

This section and the eight after it prove that each core op meets its
_obligations_: the conditions that the poison classes section asks of every
valid op of a lawful dialect. An op that propagates poison must give only poison
when an operand is poison, may be UB on a poison operand only where some
value in its place would be UB too, and must return a result on some
operands with no poison. Every op that runs by a rule of its own, which is
every core op but `call`, must also be total, with some outcome on every
operand vector, and monotone, so that refining its operands refines what it
does. With every obligation met, the core dialect is lawful, and refinement
is compositional: run on arguments that refine others, every function's
behaviour refines its behaviour on those others, calls and recursion
included, as the section on refinement through core calls proves. Each
proof is about fir's execution rules, read in the set monad.

`const` propagates poison (ADR-2026-10-29-2006), at an integer type and
at a float type alike. The core poison classes
section proves that it meets its poison clauses and is monotone whatever
its semantics. Below, its rule gives the rest: it returns a result on
operands with no poison, and it is total.

`poison` meets them the same way (ADR-2026-10-29-2006). Its one operand
vector is the empty one, which holds no poison, and on it `poison` returns
its result, the poison of its type: a result on defined operands, which is
all that obligation asks, and an outcome, which is all that totality asks.

Last, two facts of the sum without flags: it gives poison on a poison
operand, and on operands that refine others it gives a sum that refines
theirs. The next section proves `add`, with and without its flags, lawful,
with `sub` and `mul`.
-/

namespace Fir.Core

/-- `const` returns its value on its one operand vector, the empty one. -/
theorem const_returnsOnDefined (w : Nat) (v : BitVec w) :
    ReturnsOnDefined (d := CoreDialect) (.const w v) :=
  ⟨.nil, fun h => h, _, rfl⟩

/-- `const` has an outcome on its one operand vector. -/
theorem const_total (w : Nat) (v : BitVec w) : OpTotal (d := CoreDialect) (.const w v) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- A float `const` returns its value on its one operand vector, the empty
one. -/
theorem fconst_returnsOnDefined (e m : Nat) (v : BitVec (floatWidth e m)) :
    ReturnsOnDefined (d := CoreDialect) (.fconst e m v) :=
  ⟨.nil, fun h => h, _, rfl⟩

/-- A float `const` has an outcome on its one operand vector. -/
theorem fconst_total (e m : Nat) (v : BitVec (floatWidth e m)) :
    OpTotal (d := CoreDialect) (.fconst e m v) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- `poison` returns its result on its one operand vector, the empty one,
which holds no poison. -/
theorem poison_returnsOnDefined (w : Nat) : ReturnsOnDefined (d := CoreDialect) (.poison w) :=
  ⟨.nil, fun h => h, _, rfl⟩

/-- `poison` has an outcome on its one operand vector. -/
theorem poison_total (w : Nat) : OpTotal (d := CoreDialect) (.poison w) :=
  fun _ => ⟨fun _ => ⟨_, rfl⟩, fun h => nomatch h⟩

/-- In the set monad, `poison` returns the poison of its type, and nothing
else: no other value and no UB. -/
theorem poison_denote (w : Nat)
    (e : Ev (HVector toType (Fir.returnTypes (d := CoreDialect) (.poison w)))) :
    DialectDenote.denote (m := SetM) (d := CoreDialect) (.poison w) .nil e ↔
      e = .ok (.cons (PoisonOr.poison : PoisonOr (BitVec w)) .nil) :=
  Iff.rfl

/-- A poison operand of `add` gives poison. -/
theorem addValues_poison {a b : PoisonOr (BitVec w)} (h : a = .poison ∨ b = .poison) :
    addValues a b = .poison := by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

/-- `add` on operands that refine others gives a sum that refines theirs. -/
theorem addValues_isRefinedBy {a b a' b' : PoisonOr (BitVec w)} (ha : a ⊑ a') (hb : b ⊑ b') :
    addValues a b ⊑ addValues a' b' := by
  cases a with
  | poison => trivial
  | value x =>
    cases b with
    | poison => trivial
    | value y =>
      cases a' with
      | poison => exact ha.elim
      | value x' =>
        cases b' with
        | poison => exact hb.elim
        | value y' =>
          have hx : x = x' := ha
          have hy : y = y' := hb
          subst hx hy
          exact PoisonOr.isRefinedBy_refl _

end Fir.Core
