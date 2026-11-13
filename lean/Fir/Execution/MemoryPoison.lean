import Fir.Execution.MemoryOpRefine

/-!
# Poison obligations with memory

An op that propagates poison carries two obligations, and so does each
valid instance of it, beside totality and monotonicity (the section on
poison classes): a poison operand gives only poison results, and UB only by
the op's own rules; and the op returns a result on some operand vector with
no poison. Those obligations speak of the op's semantics in the set monad.
An op that touches memory has none there, so these obligations speak of the
op's semantics with memory, as totality, monotonicity and the effect
obligations do (`docs/decisions/semantics-poison.md#the-obligations-with-memory`):

* _Poison out, with memory_: wherever a run names the dialect's memories,
  from any memories, on operands of which one is poison, every result
  vector the op returns is all poison.
* _UB only by the op's own rules, with memory_: wherever a run names the
  dialect's memories, if the op may hit UB from the memories `S` on
  operands of which one is poison, it may hit UB from `S` on some operands
  that fill each poison with a defined value. The memories stay the same:
  a load through a poison pointer may be UB because some pointer in its
  place faults on those memories.
* _A result on defined operands, with memory_: wherever a run names the
  dialect's memories, the op returns a result on some operand vector with
  no poison, from some memories inside a call: memories with a frame, as a
  run's are wherever an op runs, since the interpreter runs every function
  in a frame. A load returns one from memories that hold its allocation.
  Memories outside every call would not do: an op that returns only there
  is UB wherever a run reaches it, as an op that is always UB is.

They look only at what an op that is not a terminator runs by its own rule,
as the obligations in the set monad do: only such an op returns results, a
terminator's exit passes values on and is an exception, and an op with a
callee runs its callee. They speak only of valid op instances.

A computation of the set monad, run in the state layer, keeps the memories
and ends as it ends in the set monad. So in a dialect that lifts the set
monad, as every dialect whose ops touch no memory does, an op meets each
obligation with memory exactly when it meets it in the set monad, and a
lawful dialect is lawful in its poison with memory. A sum and a lift run an
op of a side by that side's rule with its results mapped (the section on
the poison of a sum and a lift, with memory).

A dialect meets them by being _lawful in its poison with memory_, the class
below, with the poison of every valid type refined by every value, as
`LawfulDialectPoison` asks. The class asks for no semantics in the set
monad, so a dialect whose ops touch memory can meet it. With
`LawfulDialectTotal` and `LawfulDialectMonotone` it holds every poison
obligation with memory: a dialect that meets the three is _lawful with
memory_.
-/

namespace Fir

open Memory

section

variable {d : Dialect} [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d] [DialectEffects d]
  [DialectMemDenote d]

/-- Poison out, with memory: wherever a run names the dialect's memories,
from any memories, on operands of which one is poison, every result vector
the op returns is all poison. -/
def MemPoisonOut (op : d.Op) : Prop :=
  ∀ {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) unit ρ
    ∀ args : HVector toType (sig op), args.Any TyPoison.IsPoison → ∀ S rs S',
      DialectDenote.denote (m := StateT (Memories N unit) SetM) op args S (.ok (rs, S')) →
        rs.All TyPoison.IsPoison

/-- UB only by the op's own rules, with memory: wherever a run names the
dialect's memories, if the op may hit UB from the memories `S` on operands
of which one is poison, it may hit UB from `S` on some operands that fill
each poison with a defined value. -/
def MemUBByOwnRules (op : d.Op) : Prop :=
  ∀ {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) unit ρ
    ∀ (args : HVector toType (sig op)) (S : Memories N unit) (r : String),
      args.Any TyPoison.IsPoison →
      DialectDenote.denote (m := StateT (Memories N unit) SetM) op args S (.ub r) →
      ∃ args', args.IsFilledBy args' ∧
        ∃ r', DialectDenote.denote (m := StateT (Memories N unit) SetM) op args' S (.ub r')

/-- The obligation, with memory, of an op that propagates poison. -/
structure MemPropagatesPoison (op : d.Op) : Prop where
  /-- A poison operand gives only poison results. -/
  poisonOut : MemPoisonOut op
  /-- A poison operand is UB only where a defined value in its place may be,
  from the same memories. -/
  ubByOwnRules : MemUBByOwnRules op

/-- A result on defined operands, with memory: wherever a run names the
dialect's memories, the op returns a result on some operand vector with no
poison, from some memories inside a call, which have a frame. -/
def MemReturnsOnDefined (op : d.Op) : Prop :=
  ∀ {N : Type} [DecidableEq N] (unit : N → Nat) (ρ : DialectEffects.Mem d → N),
    letI := DialectMemDenote.denoteAt (d := d) unit ρ
    ∃ args : HVector toType (sig op), ¬ args.Any TyPoison.IsPoison ∧
      ∃ S rs S', S.frames ≠ [] ∧
        DialectDenote.denote (m := StateT (Memories N unit) SetM) op args S (.ok (rs, S'))

/-- A dialect lawful in its poison with memory: a poison value of a valid
type is refined by every value of its type, and every valid instance that
propagates poison propagates it with memory and returns a result on some
defined operands from some memories. -/
class LawfulDialectMemPoison (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectValidation d] [DialectMemDenote d] : Prop where
  poison_isRefinedBy : ∀ {t : d.Ty}, validTy t → ∀ (p v : ⟦t⟧), TyPoison.IsPoison p →
    TyRefinement.IsRefinedBy p v
  propagates : ∀ op : d.Op, TypesValid op → poisonClass op = .propagates → MemPropagatesPoison op
  returnsOnDefined : ∀ op : d.Op, TypesValid op → poisonClass op = .propagates →
    MemReturnsOnDefined op

/-- A dialect lawful with memory: lawful in its poison, its totality and its
monotonicity with memory, so it meets every poison obligation over its
semantics with memory. -/
abbrev LawfulDialectMem (d : Dialect) [TyDenote d.Ty] [TyPoison d.Ty] [TyRefinement d.Ty]
    [DialectSignature d] [DialectEffects d] [DialectCall d] [DialectValidation d]
    [DialectMemDenote d] : Prop :=
  LawfulDialectMemPoison d ∧ LawfulDialectTotal d ∧ LawfulDialectMonotone d

end

/-! # Dialects whose ops touch no memory -/

variable {d : Dialect} [TyDenote d.Ty] [TyPoison d.Ty] [DialectSignature d] [DialectEffects d]
  [DialectDenote d SetM] [DialectMemDenote d] [LiftsSetM d]

/-- In a dialect that lifts the set monad, an op that propagates poison in
the set monad propagates it with memory. -/
theorem MemPropagatesPoison.ofLifts {op : d.Op} (h : PropagatesPoison op) :
    MemPropagatesPoison op where
  poisonOut unit ρ args hany S rs S' hden := by
    rw [LiftsSetM.lifts unit ρ] at hden
    rcases (SetM.lift_apply _ S _).1 hden with ⟨a, ha, he⟩ | ⟨_, -, he⟩
    · cases he
      exact h.poisonOut args hany rs ha
    · cases he
  ubByOwnRules unit ρ args S r hany hden := by
    rw [LiftsSetM.lifts unit ρ] at hden ⊢
    rcases (SetM.lift_apply _ S _).1 hden with ⟨_, -, he⟩ | ⟨r₀, hr, he⟩
    · cases he
    · cases he
      obtain ⟨args', hfill, r', hub⟩ := h.ubByOwnRules args r hany hr
      exact ⟨args', hfill, r', (SetM.lift_apply _ S _).2 (.inr ⟨r', hub, rfl⟩)⟩

/-- In a dialect that lifts the set monad, an op that propagates poison with
memory propagates it in the set monad. -/
theorem MemPropagatesPoison.setM {op : d.Op} (h : MemPropagatesPoison op) :
    PropagatesPoison op where
  poisonOut args hany rs hden := by
    have hp := h.poisonOut (N := Unit) (fun _ => 0) (fun _ => ()) args hany Memories.empty rs
      Memories.empty
    rw [LiftsSetM.lifts] at hp
    exact hp ((SetM.lift_apply _ _ _).2 (.inl ⟨rs, hden, rfl⟩))
  ubByOwnRules args r hany hden := by
    have hu := h.ubByOwnRules (N := Unit) (fun _ => 0) (fun _ => ()) args Memories.empty r hany
    rw [LiftsSetM.lifts] at hu
    obtain ⟨args', hfill, r', hub⟩ := hu ((SetM.lift_apply _ _ _).2 (.inr ⟨r, hden, rfl⟩))
    rcases (SetM.lift_apply _ _ _).1 hub with ⟨_, -, he⟩ | ⟨r₀, hr, he⟩
    · cases he
    · cases he
      exact ⟨args', hfill, r', hr⟩

/-- In a dialect that lifts the set monad, an op that returns a result on
defined operands in the set monad returns one with memory, from any
memories. -/
theorem MemReturnsOnDefined.ofLifts {op : d.Op} (h : ReturnsOnDefined op) :
    MemReturnsOnDefined op := by
  intro _ _ unit ρ
  rw [LiftsSetM.lifts unit ρ]
  obtain ⟨args, hnp, rs, hrs⟩ := h
  exact ⟨args, hnp, Memories.empty.enter, rs, Memories.empty.enter, List.cons_ne_nil _ _,
    (SetM.lift_apply _ _ _).2 (.inl ⟨rs, hrs, rfl⟩)⟩

/-- In a dialect that lifts the set monad, an op that returns a result on
defined operands with memory returns one in the set monad. -/
theorem MemReturnsOnDefined.setM {op : d.Op} (h : MemReturnsOnDefined op) :
    ReturnsOnDefined op := by
  have hu := h (N := Unit) (fun _ => 0) (fun _ => ())
  rw [LiftsSetM.lifts] at hu
  obtain ⟨args, hnp, S, rs, S', -, hden⟩ := hu
  rcases (SetM.lift_apply _ S _).1 hden with ⟨a, ha, he⟩ | ⟨_, -, he⟩
  · cases he
    exact ⟨args, hnp, rs, ha⟩
  · cases he

variable [TyRefinement d.Ty] [DialectCall d] [DialectValidation d]

/-- A lawful dialect that lifts the set monad is lawful in its poison with
memory: its poison obligations in the set monad hold with memory. -/
theorem LawfulDialectMemPoison.ofLawful [LawfulDialectPoison d] : LawfulDialectMemPoison d where
  poison_isRefinedBy := LawfulDialectPoison.poison_isRefinedBy
  propagates op hv hc := MemPropagatesPoison.ofLifts (LawfulDialectPoison.propagates op hv hc)
  returnsOnDefined op hv hc :=
    MemReturnsOnDefined.ofLifts (LawfulDialectPoison.returnsOnDefined op hv hc)

/-- A dialect that lifts the set monad and is lawful in its poison, its
totality and its monotonicity with memory is lawful: each obligation with
memory holds in the set monad. -/
theorem LawfulDialectPoison.ofMem [LawfulDialectMemPoison d] [LawfulDialectTotal d]
    [LawfulDialectMonotone d] : LawfulDialectPoison d where
  poison_isRefinedBy := LawfulDialectMemPoison.poison_isRefinedBy
  propagates op hv hc := (LawfulDialectMemPoison.propagates op hv hc).setM
  returnsOnDefined op hv hc := MemReturnsOnDefined.setM (LawfulDialectMemPoison.returnsOnDefined op hv hc)
  total op hv hc := MemTotal.setM (LawfulDialectTotal.total op hv hc)
  monotone op hv hc := MemMonotone.setM (LawfulDialectMonotone.monotone op hv hc)

/-- In a dialect that lifts the set monad, the poison obligations hold
exactly when the obligations with memory do: it is lawful exactly when it is
lawful with memory. So the obligations with memory
reject every semantics that the poison obligations reject. -/
theorem LawfulDialectPoison.iff_mem : LawfulDialectPoison d ↔ LawfulDialectMem d :=
  ⟨fun _ => ⟨.ofLawful, .ofLawful, .ofLawful⟩, fun ⟨_, _, _⟩ => .ofMem⟩

end Fir
