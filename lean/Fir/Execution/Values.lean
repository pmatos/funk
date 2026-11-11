import Fir.Syntax.Dialect

/-!
Execution gives every valid module its meaning. Its definitions are the
reference interpreter, `fir-ref`: the only interpreter of fir, a test oracle
that never ships inside a compiler (ADR-2026-10-29-2009). Its general
part, below, fixes what a run can end with, what a function shows to an
observer, and when one function correctly replaces another. The interpreter
itself, and the rules of each op, come in the sections after it.

# Poison

fir has one deferred-UB value, poison, and no `undef`: that is the poison
semantics of ADR-2026-10-29-2006. Some failures, such as an `add nsw` that
overflows, do not make the op undefined. They make its result poison instead. Using poison
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

Refinement is fir's correctness relation (ADR-2026-10-29-2008), defined
below for values and lists of values, and in the section on refinement for
whole functions. Each level is defined from the one below it, in the same
shape as LeanMLIR's refinement (ADR-2026-10-29-2030).
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

/-- A pair refines another when each part refines the other's part. -/
instance instHRefinementProd [HRefinement α α] [HRefinement β β] : HRefinement (α × β) (α × β) :=
  ⟨fun p q => p.1 ⊑ q.1 ∧ p.2 ⊑ q.2⟩

/-! # Lists that refine element by element -/

section

variable {α : Type} [HRefinement α α]


/-- Lists that refine each other have the same length. -/
theorem List.IsRefinedBy.length_eq : ∀ {l l' : List α}, l ⊑ l' → l.length = l'.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => congrArg (· + 1) (List.IsRefinedBy.length_eq h.2)
  | [], _ :: _, h | _ :: _, [], h => (h : False).elim

/-- A list refines itself when each element does. -/
theorem List.isRefinedBy_refl (h : ∀ a : α, a ⊑ a) : ∀ l : List α, l ⊑ l
  | [] => trivial
  | a :: l => ⟨h a, List.isRefinedBy_refl h l⟩

/-- Refinement of lists keeps appending. -/
theorem List.IsRefinedBy.append : ∀ {l l' m m' : List α}, l ⊑ l' → m ⊑ m' → l ++ m ⊑ l' ++ m'
  | [], [], _, _, _, hm => hm
  | _ :: _, _ :: _, _, _, h, hm => ⟨h.1, List.IsRefinedBy.append h.2 hm⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => (h : False).elim

/-- Refinement of lists keeps dropping elements. -/
theorem List.IsRefinedBy.drop : ∀ (n : Nat) {l l' : List α}, l ⊑ l' → l.drop n ⊑ l'.drop n
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => List.IsRefinedBy.drop n h.2
  | _ + 1, [], _ :: _, h | _ + 1, _ :: _, [], h => (h : False).elim

/-- Refinement of lists keeps taking elements. -/
theorem List.IsRefinedBy.take : ∀ (n : Nat) {l l' : List α}, l ⊑ l' → l.take n ⊑ l'.take n
  | 0, _, _, _ => trivial
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, List.IsRefinedBy.take n h.2⟩
  | _ + 1, [], _ :: _, h | _ + 1, _ :: _, [], h => (h : False).elim

/-- Lists that refine each other hold elements that refine each other at
each index, or no element in both. -/
theorem List.IsRefinedBy.getElem? : ∀ {l l' : List α}, l ⊑ l' → ∀ i : Nat,
    (l[i]? = none ∧ l'[i]? = none) ∨ ∃ a a', l[i]? = some a ∧ l'[i]? = some a' ∧ a ⊑ a'
  | [], [], _, _ => .inl ⟨rfl, rfl⟩
  | _ :: _, _ :: _, h, 0 => .inr ⟨_, _, rfl, rfl, h.1⟩
  | _ :: _, _ :: _, h, i + 1 => List.IsRefinedBy.getElem? h.2 i
  | [], _ :: _, h, _ | _ :: _, [], h, _ => (h : False).elim

/-- Replacing the element at one index by one that refines it keeps
refinement. -/
theorem List.IsRefinedBy.set : ∀ {l l' : List α}, l ⊑ l' → ∀ (i : Nat) {a a' : α}, a ⊑ a' →
    l.set i a ⊑ l'.set i a'
  | [], [], _, _, _, _, _ => trivial
  | _ :: _, _ :: _, h, 0, _, _, ha => ⟨ha, h.2⟩
  | _ :: _, _ :: _, h, i + 1, _, _, ha => ⟨h.1, List.IsRefinedBy.set h.2 i ha⟩
  | [], _ :: _, h, _, _, _, _ | _ :: _, [], h, _, _, _, _ => (h : False).elim

/-- Changing the element at one index by a map that keeps refinement keeps
refinement. -/
theorem List.IsRefinedBy.modify {g : α → α} (hg : ∀ {a a' : α}, a ⊑ a' → g a ⊑ g a') :
    ∀ {l l' : List α}, l ⊑ l' → ∀ i : Nat, l.modify i g ⊑ l'.modify i g
  | [], [], _, i => by rw [List.modify_nil]; trivial
  | _ :: _, _ :: _, h, 0 => ⟨hg h.1, h.2⟩
  | _ :: _, _ :: _, h, i + 1 => ⟨h.1, List.IsRefinedBy.modify hg h.2 i⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => (h : False).elim

end

end Fir
