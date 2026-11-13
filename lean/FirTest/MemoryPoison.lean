import FirTest.Deps
import FirTest.LawfulRefine

/-!
Tests of the poison obligations with memory (`Fir.Execution.MemoryPoison`).

* The core dialect, the dialects of the tests and their sums are lawful in
  their poison with memory, and the class holds with the standard axioms
  alone.
* The peek dialect, written here for these tests, has one op that loads
  through a pointer, so it has no semantics in the set monad. Its op
  propagates poison: a poison pointer is UB, as a load through some
  defined pointer is, the one with no provenance. So it is lawful in its
  poison with memory.
* A peek that is UB on a poison pointer but never on a defined one, since a
  load that faults gives poison, is rejected by the clause "UB only by the
  op's own rules", from the very memories it ran from.
* `FirRef.coreUnit` gives each memory of a module the unit of its entry in
  the module's data layout.
-/

namespace FirTest.MemoryPoison

open Fir Fir.Memory

example : LawfulDialectMemPoison CoreDialect := inferInstance
example : LawfulDialectMemPoison CoreToy := inferInstance
example : LawfulDialectMemPoison CoreToyBit := inferInstance
example : LawfulDialectMemPoison CoreProbe := inferInstance

/-- info: 'Fir.Core.lawfulDialectMemPoison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.lawfulDialectMemPoison

/-- The ops of the peek dialect: `peek` loads an `i8` through a pointer. -/
inductive PeekOp where
  | peek
  deriving DecidableEq

/-- A dialect, for these tests, whose op loads from memory, over the core's
types. -/
abbrev PeekDialect : Dialect := ⟨PeekOp, Core.Ty⟩

instance : DialectSignature PeekDialect where
  sig _ := [.ptr 0]
  returnTypes _ := [.int 8]
  isTerminator _ := false
  succCount _ := 0

instance : DialectCall PeekDialect := ⟨fun _ => none⟩

/-- The peek dialect has one memory, `()`. `peek` propagates poison, reads
the memory, may hit UB and may produce poison. -/
instance : DialectEffects PeekDialect :=
  ⟨Unit, fun _ => .propagates,
    fun _ => { reads := .these [()], mayUB := true, mayPoison := true }⟩

instance : DialectValidation PeekDialect where
  validTy _ := True
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True

variable {N : Type} [DecidableEq N] (unit : N → Nat) (x : N)

/-- `peek` through the pointer `p` in the memory `x`: UB on a poison
pointer, else the `i8` that the one unit at `p` decodes to, in little-endian
order. A load that faults is UB. -/
def peekAt : PoisonOr Pointer → StateT (Memories N unit) SetM (HVector toType [Core.Ty.int 8])
  | .poison => MonadUB.ub "peek through a poison pointer"
  | .value p => (fun us => .cons (decodeInt (unit x) 8 .little us) .nil) <$>
      MonadMemory.load (m := StateT (Memories N unit) SetM) x p 1

/-- Wherever a run names the memory `()` as `ρ ()`, `peek` loads from it. -/
instance : DialectMemDenote PeekDialect where
  denoteAt unit ρ :=
    { denote := fun
        | .peek, .cons p .nil => peekAt unit (ρ ()) p
      exit := fun _ _ => MonadUB.ub "peek is not a terminator" }

/-- A load through the pointer with no provenance is UB, from any
memories. -/
theorem peekAt_none (S : Memories N unit) :
    peekAt unit x (.value ⟨none, 0⟩) S (.ub Fault.noProvenance.reason) :=
  (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, rfl, rfl⟩)

/-- The memories inside a call, with one unit allocated on its stack. -/
def oneUnit : Pointer × Memories N unit := (Memories.empty : Memories N unit).enter.alloc x .stack 1

/-- Those memories have a frame. -/
theorem oneUnit_frames : (oneUnit unit x).2.frames ≠ [] := by
  simp [oneUnit, Memories.alloc, Memories.record, Memories.enter, Memories.set]

/-- A load from a new allocation of one unit returns a result. -/
theorem peekAt_alloc :
    let r := oneUnit unit x
    peekAt unit x (.value r.1) r.2 (.ok (.cons (decodeInt (unit x) 8 .little [.poison]) .nil, r.2)) := by
  intro r
  have hl : r.2.load x r.1 1 = .ok [.poison] := by
    show ((Memories.empty.enter.alloc x .stack 1).2.mem x).load
      (Memories.empty.enter.alloc x .stack 1).1 1 = _
    rw [Memories.alloc_mem_self, Memories.alloc_fst]
    exact Memory.load_alloc _ _ (Int.le_refl 0) (by simp)
  refine (SetM.stateMap_apply _ _ _ _).2 (.inl ⟨[.poison], r.2, ?_, rfl⟩)
  show (match r.2.load x r.1 1 with
    | .ok us => pure (us, r.2)
    | .error f => MonadUB.ub f.reason : SetM _) _
  rw [hl]
  rfl

/-- `peek` propagates poison with memory, and returns a result on a defined
pointer from memories that hold its allocation: the peek dialect is lawful
in its poison with memory, with no semantics in the set monad. -/
instance : LawfulDialectMemPoison PeekDialect where
  poison_isRefinedBy _ := Core.Ty.poison_isRefinedBy
  propagates
    | .peek, _, _ => {
        poisonOut := by
          intro _ _ _ _ args hany S rs S' hden
          match args with
          | .cons p .nil =>
            cases p with
            | poison => cases hden
            | value _ => rcases hany with h | h <;> cases h
        ubByOwnRules := by
          intro _ _ unit ρ args S _ hany _
          match args with
          | .cons p .nil =>
            cases p with
            | poison =>
              refine ⟨.cons (.value ⟨none, 0⟩) .nil, ⟨?_, .inl rfl, trivial⟩, _,
                peekAt_none unit (ρ ()) S⟩
              rintro (h | h) <;> cases h
            | value _ => rcases hany with h | h <;> cases h }
  returnsOnDefined
    | .peek, _, _ => by
      intro unit ρ
      refine ⟨.cons (.value (oneUnit unit (ρ ())).1) .nil, ?_, _, _, _, oneUnit_frames unit (ρ ()),
        peekAt_alloc unit (ρ ())⟩
      rintro (h | h) <;> cases h

/-! # A peek that the obligations reject -/

/-- `peek` that is UB on a poison pointer, but gives poison where a load
through a defined pointer faults, so it is never UB on one. -/
def peekLax : PoisonOr Pointer → StateT (Memories N unit) SetM (HVector toType [Core.Ty.int 8])
  | .poison => MonadUB.ub "peek through a poison pointer"
  | .value p => fun S => match S.load x p 1 with
    | .ok us => pure (.cons (decodeInt (unit x) 8 .little us) .nil, S)
    | .error _ => pure (.cons .poison .nil, S)

omit [DecidableEq N] in
/-- `peekLax` through a defined pointer is never UB. -/
theorem peekLax_value_noUB (p : Pointer) (S : Memories N unit) (r : String) :
    ¬ peekLax unit x (.value p) S (.ub r) := by
  simp only [peekLax]
  cases S.load x p 1 <;> exact fun h => by cases h

/-- The peek dialect's semantics with memory by `peekLax`. -/
@[instance_reducible] def laxMemDenote : DialectMemDenote PeekDialect where
  denoteAt unit ρ :=
    { denote := fun
        | .peek, .cons p .nil => peekLax unit (ρ ()) p
      exit := fun _ _ => MonadUB.ub "peek is not a terminator" }

/-- The clause "UB only by the op's own rules" rejects `peekLax`: it is UB
on a poison pointer from the empty memories, but on no defined pointer. -/
theorem peekLax_unlawful : ¬ @LawfulDialectMemPoison PeekDialect _ _ _ _ _ _ laxMemDenote := by
  letI := laxMemDenote
  intro h
  obtain ⟨args', ⟨hn, -⟩, r', hub⟩ :=
    (h.propagates .peek ⟨fun _ _ => trivial, fun _ _ => trivial⟩ rfl).ubByOwnRules (N := Unit) (fun _ => 8) (fun _ => ())
      (.cons .poison .nil) Memories.empty "peek through a poison pointer" (.inl rfl) rfl
  match args' with
  | .cons p .nil =>
    cases p with
    | poison => exact hn (.inl rfl)
    | value p => exact peekLax_value_noUB _ () p _ _ hub

/-! # The units of a module's memories -/

/-- A layout that gives memory 0 16-bit units, and declares memory 1 with
12-bit units. -/
def layout : DataLayout :=
  [{ mem := 0, unit := 16, pointer := 32, order := .little },
    { mem := 1, unit := 12, pointer := 32, order := .little }]

#guard FirRef.coreUnit [] 0 == 8
#guard FirRef.coreUnit layout 0 == 16
#guard FirRef.coreUnit layout 1 == 12
#guard FirRef.coreUnit [] 1 == 8
#guard FirRef.coreUnit layout 2 == 8

end FirTest.MemoryPoison
