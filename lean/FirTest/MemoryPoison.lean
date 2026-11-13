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
* `peek` reads the unit and the byte order of the memory it loads from in
  that memory's layout entry: an `i8` takes two units of a memory with 4-bit
  units, and the same units give `0x12` at `big` and `0x21` at `little`.
* `DataLayout.entry` gives each memory of a module its entry in the module's
  data layout, and the default memory's to one that it does not declare.
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

variable {N : Type} [DecidableEq N] (lay : N → MemLayout) (x : N)

/-- The units that an `i8` takes in the memory `x`, by its entry. -/
abbrev peekUnits : Nat := unitsFor (lay x).unit 8

/-- `peek` through the pointer `p` in the memory `x`: UB on a poison
pointer, else the `i8` that the units at `p` decode to, as many as an `i8`
takes in `x`, in `x`'s byte order. Both come from `x`'s layout entry. A
load that faults is UB. -/
def peekAt : PoisonOr Pointer →
    StateT (Memories N (unitsOf lay)) SetM (HVector toType [Core.Ty.int 8])
  | .poison => MonadUB.ub "peek through a poison pointer"
  | .value p => (fun us => .cons (decodeInt (lay x).unit 8 (lay x).order us) .nil) <$>
      MonadMemory.load (m := StateT (Memories N (unitsOf lay)) SetM) x p (peekUnits lay x)

/-- Wherever a run names the memory `()` as `ρ ()`, `peek` loads from it,
by its entry `lay (ρ ())`. -/
instance : DialectMemDenote PeekDialect where
  denoteAt lay ρ :=
    { denote := fun
        | .peek, .cons p .nil => peekAt lay (ρ ()) p
      exit := fun _ _ => MonadUB.ub "peek is not a terminator" }

/-- A load through the pointer with no provenance is UB, from any
memories. -/
theorem peekAt_none (S : Memories N (unitsOf lay)) :
    peekAt lay x (.value ⟨none, 0⟩) S (.ub Fault.noProvenance.reason) :=
  (SetM.stateMap_apply _ _ S _).2 (.inr ⟨_, rfl, rfl⟩)

/-- A load that gives the units `us` gives the `i8` they decode to, at the
unit and the byte order of the memory's entry. -/
theorem peekAt_load {S : Memories N (unitsOf lay)} {p : Pointer} {us : List (MemUnit (lay x).unit)}
    (h : S.load x p (peekUnits lay x) = .ok us) :
    peekAt lay x (.value p) S (.ok (.cons (decodeInt (lay x).unit 8 (lay x).order us) .nil, S)) :=
        by
  refine (SetM.stateMap_apply _ _ _ _).2 (.inl ⟨us, S, ?_, rfl⟩)
  simp only [MonadMemory.load, h]
  rfl

/-- The memories inside a call, with an `i8`'s units allocated on its
stack. -/
def oneUnit : Pointer × Memories N (unitsOf lay) :=
  (Memories.empty : Memories N (unitsOf lay)).enter.alloc x .stack (peekUnits lay x)

/-- Those memories have a frame. -/
theorem oneUnit_frames : (oneUnit lay x).2.frames ≠ [] := by
  simp [oneUnit, Memories.alloc, Memories.record, Memories.enter, Memories.set]

/-- A load from a new allocation returns a result. -/
theorem peekAt_alloc :
    let r := oneUnit lay x
    peekAt lay x (.value r.1) r.2 (.ok (.cons (decodeInt (lay x).unit 8 (lay x).order
      (List.replicate (peekUnits lay x) .poison)) .nil, r.2)) := by
  intro r
  refine peekAt_load lay x ?_
  show ((Memories.empty.enter.alloc x .stack (peekUnits lay x)).2.mem x).load
    (Memories.empty.enter.alloc x .stack (peekUnits lay x)).1 (peekUnits lay x) = _
  rw [Memories.alloc_mem_self, Memories.alloc_fst]
  exact Memory.load_alloc _ _ (Int.le_refl 0) (by simp)

/-- An entry with 4-bit units, in the byte order `o`. -/
def nibbles (o : ByteOrder) : MemLayout := { mem := 0, unit := 4, pointer := 64, order := o }

/-- The same two units give `0x12` from a big-endian memory of 4-bit units,
and `0x21` from a little-endian one: `peek` reads the byte order from the
entry of the memory it loads from. -/
example {S : Memories Unit (unitsOf fun _ => nibbles .big)} {p : Pointer}
    (h : S.load () p 2 = .ok [.bits 1#4, .bits 2#4]) :
    peekAt (fun _ => nibbles .big) () (.value p) S (.ok (.cons (.value 0x12#8) .nil, S)) :=
  peekAt_load (fun _ => nibbles .big) () h

example {S : Memories Unit (unitsOf fun _ => nibbles .little)} {p : Pointer}
    (h : S.load () p 2 = .ok [.bits 1#4, .bits 2#4]) :
    peekAt (fun _ => nibbles .little) () (.value p) S (.ok (.cons (.value 0x21#8) .nil, S)) :=
  peekAt_load (fun _ => nibbles .little) () h

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
          intro _ _ lay ρ args S _ hany _
          match args with
          | .cons p .nil =>
            cases p with
            | poison =>
              refine ⟨.cons (.value ⟨none, 0⟩) .nil, ⟨?_, .inl rfl, trivial⟩, _,
                peekAt_none lay (ρ ()) S⟩
              rintro (h | h) <;> cases h
            | value _ => rcases hany with h | h <;> cases h }
  returnsOnDefined
    | .peek, _, _ => by
      intro lay ρ
      refine ⟨.cons (.value (oneUnit lay (ρ ())).1) .nil, ?_, _, _, _, oneUnit_frames lay (ρ ()),
        peekAt_alloc lay (ρ ())⟩
      rintro (h | h) <;> cases h

/-! # A peek that the obligations reject -/

/-- `peek` that is UB on a poison pointer, but gives poison where a load
through a defined pointer faults, so it is never UB on one. -/
def peekLax : PoisonOr Pointer →
    StateT (Memories N (unitsOf lay)) SetM (HVector toType [Core.Ty.int 8])
  | .poison => MonadUB.ub "peek through a poison pointer"
  | .value p => fun S => match S.load x p (peekUnits lay x) with
    | .ok us => pure (.cons (decodeInt (lay x).unit 8 (lay x).order us) .nil, S)
    | .error _ => pure (.cons .poison .nil, S)

/-- `peekLax` through a defined pointer is never UB. -/
theorem peekLax_value_noUB (p : Pointer) (S : Memories N (unitsOf lay)) (r : String) :
    ¬ peekLax lay x (.value p) S (.ub r) := by
  simp only [peekLax]
  cases S.load x p (peekUnits lay x) <;> exact fun h => by cases h

/-- The peek dialect's semantics with memory by `peekLax`. -/
@[instance_reducible] def laxMemDenote : DialectMemDenote PeekDialect where
  denoteAt lay ρ :=
    { denote := fun
        | .peek, .cons p .nil => peekLax lay (ρ ()) p
      exit := fun _ _ => MonadUB.ub "peek is not a terminator" }

/-- The clause "UB only by the op's own rules" rejects `peekLax`: it is UB
on a poison pointer from the empty memories, but on no defined pointer. -/
theorem peekLax_unlawful : ¬ @LawfulDialectMemPoison PeekDialect _ _ _ _ _ _ laxMemDenote := by
  letI := laxMemDenote
  intro h
  obtain ⟨args', ⟨hn, -⟩, r', hub⟩ :=
    (h.propagates .peek ⟨fun _ _ => trivial, fun _ _ => trivial⟩ rfl).ubByOwnRules (N := Unit)
      (fun _ => MemLayout.default) (fun _ => ())
      (.cons .poison .nil) Memories.empty "peek through a poison pointer" (.inl rfl) rfl
  match args' with
  | .cons p .nil =>
    cases p with
    | poison => exact hn (.inl rfl)
    | value p => exact peekLax_value_noUB _ () p _ _ hub

/-! # The entries of a module's memories -/

/-- A layout that gives memory 0 16-bit units, and declares memory 1 with
12-bit units and 32-bit pointers. -/
def layout : DataLayout :=
  [{ mem := 0, unit := 16, pointer := 32, order := .little },
    { mem := 1, unit := 12, pointer := 32, order := .little }]

#guard (DataLayout.entry [] 0).unit == 8
#guard (DataLayout.entry layout 0).unit == 16
#guard (DataLayout.entry layout 1).unit == 12
#guard (DataLayout.entry [] 1).unit == 8
#guard (DataLayout.entry layout 2).unit == 8
#guard (DataLayout.entry layout 1).pointer == 32

end FirTest.MemoryPoison
