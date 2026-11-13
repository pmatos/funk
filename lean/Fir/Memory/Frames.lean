import Fir.Memory.Model

/-!
A run has every memory of its module at once: the core's default memory and
any memory that a dialect adds (ADR-2026-11-09-1542, ADR-2026-10-29-2016).
This section gives them as one state, the _memories_ of a run, which the run
carries from op to op.

Each memory has a name, of a type that the dialects give, and its units have
the width that the module's data layout gives that memory. The memories are
written once, for any names `Mem` and any unit width `unit x` of each name
`x`, so that no width and no layout is fixed here. Each memory is a memory of
the model of the previous sections, with its own allocations: an allocation
id names an allocation of one memory alone.

A stack allocation lives until the call that made it returns
(ADR-2026-11-09-1548). So the memories also keep a stack of _frames_, one for
each call that has not yet returned, the innermost first. A frame lists the
stack allocations that its call made, each by its memory and its id:

* entering a call pushes an empty frame;
* allocating on the stack records the allocation in the innermost frame, and
  an allocation of another kind is in no frame;
* leaving a call frees every allocation of its frame, then pops it.

The interpreter enters a frame when it starts to run a function and leaves it
when the function returns (the section on the memory effect), so each call's
stack allocations are freed when it returns, and no other allocation is.
Freeing never faults, so leaving a frame never does either.

The memories are kept as a _table_: a list of memories, each with its name.
The memory of a name is the first one of that name in the table, and a name
that the table does not hold names the empty memory, which every memory is
before the run allocates in it. Replacing a memory puts the new one first and
drops the old one, so the table holds each name at most once, and grows only
when a memory that the run has not touched before changes. Finding a memory
then looks at no more entries than the run has memories, however many
stores, allocations and frees came before, and takes no stack for them
(`docs/decisions/fir-ref-memory.md`).
-/

namespace Fir.Memory

/-- The memories of a run, for memories named by `Mem` whose units are
`unit x` bits wide for the memory `x`: the table of the memories, each with
its name, and the frames of the calls that have not returned, the innermost
first. A frame lists the stack allocations its call made, each by its memory
and its id. -/
structure Memories (Mem : Type) (unit : Mem → Nat) where
  table : List (Σ x : Mem, Memory (unit x))
  frames : List (List (Mem × AllocId))

namespace Memories

variable {Mem : Type} {unit : Mem → Nat}

/-- The memories of a run before anything is allocated, outside every call:
no memory in the table, so each is empty. -/
def empty : Memories Mem unit := ⟨[], []⟩

/-- Enters a call: pushes an empty frame. -/
def enter (S : Memories Mem unit) : Memories Mem unit :=
  { S with frames := [] :: S.frames }

variable [DecidableEq Mem]

/-- The memory `x` of a table: the first one of its name, or the empty
memory when the table has none. -/
def lookup (x : Mem) : List (Σ y : Mem, Memory (unit y)) → Memory (unit x)
  | [] => .empty
  | ⟨y, m⟩ :: t => if h : y = x then h ▸ m else lookup x t

/-- The memory `x` of the memories of a run. -/
def mem (S : Memories Mem unit) (x : Mem) : Memory (unit x) :=
  lookup x S.table

/-- Loads `n` units of the memory `x` through `p`, or gives the fault that
makes the load UB. -/
def load (S : Memories Mem unit) (x : Mem) (p : Pointer) (n : Nat) :
    Except Fault (List (MemUnit (unit x))) :=
  (S.mem x).load p n

/-- The memories with the memory `x` replaced by `m`. -/
def set (S : Memories Mem unit) (x : Mem) (m : Memory (unit x)) : Memories Mem unit :=
  { S with table := ⟨x, m⟩ :: S.table.filter fun e => !decide (e.1 = x) }

/-- Records the stack allocation `a` of the memory `x` in the innermost
frame. Outside every call there is no frame, and nothing is recorded, so
such an allocation would never be freed. A run never allocates outside a
call: the interpreter runs the function that a run starts with in a frame
of its own, as it runs every callee. -/
def record (S : Memories Mem unit) (x : Mem) (a : AllocId) : Memories Mem unit :=
  match S.frames with
  | [] => S
  | fr :: frs => { S with frames := ((x, a) :: fr) :: frs }

/-- Allocates `n` units of kind `k` in the memory `x`, and gives the pointer
to the first one. A stack allocation is recorded in the innermost frame. -/
def alloc (S : Memories Mem unit) (x : Mem) (k : AllocKind) (n : Nat) :
    Pointer × Memories Mem unit :=
  let r := (S.mem x).alloc k n
  let S' := S.set x r.2
  (r.1, if k = .stack then S'.record x (S.mem x).blocks.length else S')

/-- Frees the allocation `a` of the memory `x`. -/
def free (S : Memories Mem unit) (x : Mem) (a : AllocId) : Memories Mem unit :=
  S.set x ((S.mem x).free a)

/-- Stores the units `us` to the memory `x` through `p`, or gives the fault
that makes the store UB. -/
def store (S : Memories Mem unit) (x : Mem) (p : Pointer) (us : List (MemUnit (unit x))) :
    Except Fault (Memories Mem unit) :=
  ((S.mem x).store p us).map (S.set x)

/-- Frees each allocation of the list, in order. -/
def freeAll (S : Memories Mem unit) : List (Mem × AllocId) → Memories Mem unit
  | [] => S
  | (x, a) :: as => (S.free x a).freeAll as

/-- Leaves a call: frees every allocation of the innermost frame, and pops
it. Outside every call it changes nothing. -/
def exit (S : Memories Mem unit) : Memories Mem unit :=
  match S.frames with
  | [] => S
  | fr :: frs => ({ S with frames := frs } : Memories Mem unit).freeAll fr

end Memories

end Fir.Memory
