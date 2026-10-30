import Fir.Syntax.Dialect

/-!
Execution gives every valid module its meaning. Its definitions are the
reference interpreter, `fir-ref`: the only interpreter of fir, a test oracle
that never ships inside a compiler (S7, ADR-2026-10-29-2009). Its general
part, below, fixes what a run can end with, what a function shows to an
observer, and when one function correctly replaces another. The interpreter
itself, and the rules of each op, are written by #10 and #14 to #20.

# Poison

fir has one deferred-UB value, poison, and no `undef` (S1,
ADR-2026-10-29-2006). Some failures, such as an `add nsw` that overflows, do
not make the op undefined. They make its result poison instead. Using poison
is not UB in itself, but some uses are, such as branching on it. The next
section explains poison and immediate UB in plain words.
-/

namespace Fir

/--
A value that may be poison. The integer values of the core dialect are
`PoisonOr (BitVec N)`. The constructor names match LeanMLIR's
(ADR-2026-10-29-2030).
-/
inductive PoisonOr (α : Type) where
  | poison
  | value (a : α)
  deriving Repr, DecidableEq, Inhabited

/-!
# Refinement

Refinement is fir's correctness relation (S4, ADR-2026-10-29-2008): a target
is correct for a source when each of its observable behaviours is allowed by
the source. The relation is written `a ⊑ b`, read "`a` is refined by `b`":
`b` does nothing that `a` does not allow. It is defined level by level, from
values up to behaviours and functions, through one class whose shape
follows LeanMLIR's `HRefinement`.
-/

/-- Heterogeneous refinement: `a ⊑ b` says that `b` refines `a`. -/
class HRefinement (α β : Type) where
  /-- `a ⊑ b`: `b` refines `a`. -/
  IsRefinedBy : α → β → Prop

@[inherit_doc] infix:50 " ⊑ " => HRefinement.IsRefinedBy

/-- A poison value is refined by any value, and a value only by itself. -/
def PoisonOr.IsRefinedBy : PoisonOr α → PoisonOr α → Prop
  | .poison, _ => True
  | .value a, .value b => a = b
  | .value _, .poison => False

instance : HRefinement (PoisonOr α) (PoisonOr α) := ⟨PoisonOr.IsRefinedBy⟩

/--
How a dialect refines the values of each of its types. For the core
dialect it is the refinement of `PoisonOr` values.
-/
class TyRefinement (Ty : Type) [TyDenote Ty] where
  IsRefinedBy : {t : Ty} → ⟦t⟧ → ⟦t⟧ → Prop

/-- A value together with its type: what an op consumes or produces. -/
abbrev DVal (d : Dialect) [TyDenote d.Ty] := (t : d.Ty) × ⟦t⟧

/-- A typed value is refined by a value of the same type that refines it.
A dialect whose `DVal` instance search cannot find this one names it, as the
core dialect does. -/
instance instHRefinementDVal {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty] :
    HRefinement (DVal d) (DVal d) where
  IsRefinedBy a b := ∃ h : a.1 = b.1, TyRefinement.IsRefinedBy (h ▸ a.2) b.2

/-- Typed values refine transitively when the values of each type do. -/
theorem DVal.isRefinedBy_trans {d : Dialect} [TyDenote d.Ty] [TyRefinement d.Ty]
    (h : ∀ {t : d.Ty} {a b c : ⟦t⟧}, TyRefinement.IsRefinedBy a b →
      TyRefinement.IsRefinedBy b c → TyRefinement.IsRefinedBy a c)
    {x y z : DVal d} (hxy : x ⊑ y) (hyz : y ⊑ z) : x ⊑ z := by
  obtain ⟨tx, vx⟩ := x; obtain ⟨ty, vy⟩ := y; obtain ⟨tz, vz⟩ := z
  obtain ⟨h₁, hxy⟩ := hxy; obtain ⟨h₂, hyz⟩ := hyz
  cases h₁; cases h₂
  exact ⟨rfl, h hxy hyz⟩

/-- Lists are refined element by element. -/
def List.IsRefinedBy [HRefinement α β] : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => a ⊑ b ∧ List.IsRefinedBy as bs
  | _, _ => False

instance [HRefinement α β] : HRefinement (List α) (List β) := ⟨List.IsRefinedBy⟩

/-- A poison value is refined by any value: S4's second rule, for values. -/
theorem PoisonOr.poison_isRefinedBy (b : PoisonOr α) : (PoisonOr.poison : PoisonOr α) ⊑ b :=
  trivial

/-- Refinement of values is reflexive. -/
theorem PoisonOr.isRefinedBy_refl : ∀ a : PoisonOr α, a ⊑ a
  | .poison => trivial
  | .value _ => rfl

/-- Refinement of values is transitive. -/
theorem PoisonOr.isRefinedBy_trans : ∀ {a b c : PoisonOr α}, a ⊑ b → b ⊑ c → a ⊑ c
  | .poison, _, _, _, _ => trivial
  | .value _, .value _, .value _, hab, hbc => Eq.trans hab hbc
  | .value _, .value _, .poison, _, hbc => hbc.elim
  | .value _, .poison, _, hab, _ => hab.elim

/-- Lists refine element by element, so refinement of lists is transitive
when refinement of their elements is. -/
theorem List.isRefinedBy_trans [HRefinement α α] (h : ∀ {a b c : α}, a ⊑ b → b ⊑ c → a ⊑ c) :
    ∀ {as bs cs : List α}, as ⊑ bs → bs ⊑ cs → as ⊑ cs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨hab, habs⟩, ⟨hbc, hbcs⟩ => ⟨h hab hbc, List.isRefinedBy_trans h habs hbcs⟩
  | [], _ :: _, _, hab, _ | _ :: _, [], _, hab, _ => hab.elim
  | [], [], _ :: _, _, hbc | _ :: _, _ :: _, [], _, hbc => hbc.elim

end Fir
