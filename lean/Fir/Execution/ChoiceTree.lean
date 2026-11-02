import Fir.Execution.Morphism

/-!
# The tree of choices

A computation of the set monad says which ways a run may end, but no
program can list them: a set is a proposition. `fir-ref` runs the
interpreter in a monad that it can walk instead, the _tree of choices_
(ADR-2026-10-29-2017, ADR-2026-10-30-2217). A computation in it is a tree. A leaf says how a
path ends: with a result, with immediate UB, or with no outcome at all,
the empty set that an op without execution rules has
(ADR-2026-10-30-1855). A node is a choice of `w` bits, with one subtree
for each value the bits may take.

The tree's meaning is a set: `ChoiceTree.toSet` maps each tree to the set
of the ways its paths end. That map is a monad morphism, so a run of the
interpreter in the tree maps to its run in the set monad, by the previous
section. `fir-ref`'s three modes walk the tree: exhaustive mode visits every
path, scripted mode follows the one path that a choice sequence names, and
sampled mode draws one.
-/

namespace Fir

/-- A computation as a tree of choices. `ε` says why a path may end with no
outcome. -/
inductive ChoiceTree (ε α : Type) where
  /-- The path ends with the result `a`. -/
  | pure (a : α)
  /-- The path ends with immediate UB. -/
  | ub (reason : String)
  /-- The path ends with no outcome, for the reason `e`. -/
  | noOutcome (e : ε)
  /-- A choice of `w` bits: the path goes on with `k b` for the bits `b`. -/
  | choose (w : Nat) (k : BitVec w → ChoiceTree ε α)

namespace ChoiceTree

variable {ε : Type}

/-- Runs `f` on the result of each path of `t`. -/
def bind : ChoiceTree ε α → (α → ChoiceTree ε β) → ChoiceTree ε β
  | .pure a, f => f a
  | .ub r, _ => .ub r
  | .noOutcome e, _ => .noOutcome e
  | .choose w k, f => .choose w fun b => (k b).bind f

instance : Monad (ChoiceTree ε) where
  pure := .pure
  bind := ChoiceTree.bind

instance : MonadChoice (ChoiceTree ε) := ⟨fun w => .choose w .pure⟩

instance : MonadUB (ChoiceTree ε) := ⟨.ub⟩

/-- The set of the ways a tree's paths end. A path with no outcome adds
nothing. -/
def toSet : ChoiceTree ε α → SetM α
  | .pure a => fun e => e = .ok a
  | .ub r => fun e => e = .ub r
  | .noOutcome _ => fun _ => False
  | .choose _ k => fun e => ∃ b, (k b).toSet e

/-- The set of a tree that runs `f` on each result is the set monad's bind. -/
theorem toSet_bind (t : ChoiceTree ε α) (f : α → ChoiceTree ε β) :
    (t.bind f).toSet = t.toSet >>= fun a => (f a).toSet := by
  induction t with
  | pure a =>
    funext e
    apply propext
    show (f a).toSet e ↔
      (∃ a', Ev.ok a' = .ok a ∧ (f a').toSet e) ∨ ∃ r, Ev.ub r = .ok a ∧ e = .ub r
    exact ⟨fun h => .inl ⟨a, rfl, h⟩, fun
      | .inl ⟨_, h, h'⟩ => by cases h; exact h'
      | .inr ⟨_, h, _⟩ => nomatch h⟩
  | ub r =>
    funext e
    apply propext
    show e = .ub r ↔
      (∃ a, Ev.ok a = .ub r ∧ (f a).toSet e) ∨ ∃ r', Ev.ub r' = .ub r ∧ e = .ub r'
    exact ⟨fun h => .inr ⟨r, rfl, h⟩, fun
      | .inl ⟨_, h, _⟩ => nomatch h
      | .inr ⟨_, h, he⟩ => by cases h; exact he⟩
  | noOutcome _ =>
    funext e
    apply propext
    show False ↔ (∃ a, False ∧ _) ∨ ∃ r, False ∧ e = .ub r
    exact ⟨False.elim, fun
      | .inl ⟨_, h, _⟩ => h
      | .inr ⟨_, h, _⟩ => h⟩
  | choose w k ih =>
    funext e
    apply propext
    show (∃ b, ((k b).bind f).toSet e) ↔
      (∃ a, (∃ b, (k b).toSet (.ok a)) ∧ (f a).toSet e) ∨
        ∃ r, (∃ b, (k b).toSet (.ub r)) ∧ e = .ub r
    constructor
    · rintro ⟨b, h⟩
      rw [ih b] at h
      rcases h with ⟨a, ha, h⟩ | ⟨r, hr, he⟩
      · exact .inl ⟨a, ⟨b, ha⟩, h⟩
      · exact .inr ⟨r, ⟨b, hr⟩, he⟩
    · rintro (⟨a, ⟨b, ha⟩, h⟩ | ⟨r, ⟨b, hr⟩, he⟩)
      · exact ⟨b, by rw [ih b]; exact .inl ⟨a, ha, h⟩⟩
      · exact ⟨b, by rw [ih b]; exact .inr ⟨r, hr, he⟩⟩

/-- `toSet` is a monad morphism from the tree of choices to the set monad. -/
def toSetMorphism : MonadMorphism (ChoiceTree ε) SetM where
  map := toSet
  map_pure _ := rfl
  map_bind := toSet_bind
  map_map g t := toSet_bind t (fun a => .pure (g a))

/-- A choice of `w` bits is the set monad's choice. -/
theorem toSet_choose (w : Nat) :
    (MonadChoice.choose w : ChoiceTree ε (BitVec w)).toSet = MonadChoice.choose w := rfl

/-- UB is the set monad's UB. -/
theorem toSet_ub (r : String) :
    (MonadUB.ub r : ChoiceTree ε α).toSet = (MonadUB.ub r : SetM α) := rfl

end ChoiceTree

end Fir
