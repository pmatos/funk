import Fir.Syntax.Dialect

/-!
# Effect sets

Each op declares a set of effects: what it may do beyond computing its
results from its operands (ADR-2026-11-09-1541). A pass may move, merge or
remove an op only as far as its effects allow, and it reads them from one
place, the dialect's effect class below. Every dialect declares its ops'
effects, including effects on memories of its own, so that a dialect added
for new hardware states them too (ADR-2026-10-29-2016).

An effect set is drawn from these effects:

* _reads memory m_, _writes memory m_, and _allocates or frees in memory m_:
  each names the memories it touches, or says that it may touch every
  memory, as an external call does;
* _may-UB_: the op may end in immediate UB;
* _may produce poison_: on operands with no poison, a result of the op may
  be poison;
* _observable_: the op adds an event to the trace of the run;
* _control_: the op is a terminator.

The empty set is _pure_. The memories are the dialect's own: each dialect
says what names its memories have. The memory-named effects are fixed here
in shape, and no op uses them yet: the core dialect has no memory, and
gains one with the memory model (ADR-2026-11-09-1542).

The effect class holds each op's poison class too, which says how the op
treats poison operands (the section on poison classes): the op's poison
behaviour is declared in one place, with its other effects. The poison
class and _may produce poison_ say different things: the class is about
poison operands, and the effect about operands with no poison
(ADR-2026-11-09-1541).

The effects of an op are those of its own rule. An op with a callee also
has its callee's, whose meaning is the callee's run (ADR-2026-10-29-2006):
the section on function summaries gives each function the effects that a
call of it may have, and each op in place its own effects with its
callee's (ADR-2026-11-09-1541). The spec proves each declaration sound in the section on effect
obligations: an effect that an op leaves out, it does not have.
-/

namespace Fir

/-- How an op treats poison operands. -/
inductive PoisonClass where
  /-- A poison operand makes every result the op returns poison. -/
  | propagates
  /-- The op states its own rule for poison operands. -/
  | exception
  deriving Repr, DecidableEq

/-- The memories an effect touches: the listed ones, or every memory. -/
inductive MemSet (Mem : Type) where
  /-- These memories, and no other. -/
  | these (ms : List Mem)
  /-- Every memory. -/
  | every
  deriving Repr, DecidableEq

/-- A set of memories holds a memory when it lists it, or is every memory. -/
def MemSet.Has {Mem : Type} : MemSet Mem → Mem → Prop
  | .these ms, m => m ∈ ms
  | .every, _ => True

/-- An op's set of effects. Each memory-named effect names the memories it
touches; each other effect is there or not. The default is the empty set:
the op is pure. -/
structure Effects (Mem : Type) where
  /-- The memories the op may read. -/
  reads : MemSet Mem := .these []
  /-- The memories the op may write. -/
  writes : MemSet Mem := .these []
  /-- The memories in which the op may allocate or free. -/
  allocates : MemSet Mem := .these []
  /-- The op may end in immediate UB. -/
  mayUB : Bool := false
  /-- On operands with no poison, a result of the op may be poison. -/
  mayPoison : Bool := false
  /-- The op may add an event to the trace of the run. -/
  observable : Bool := false
  /-- The op is a terminator. -/
  control : Bool := false
  deriving Repr, DecidableEq

/-- Every effect, on every memory: what an op declares when nothing narrower
is known of it, as of an external call (ADR-2026-11-09-1541). -/
def Effects.all {Mem : Type} : Effects Mem :=
  ⟨.every, .every, .every, true, true, true, true⟩

/-- Renames the memories of a set of memories. -/
def MemSet.map {Mem Mem' : Type} (f : Mem → Mem') : MemSet Mem → MemSet Mem'
  | .these ms => .these (ms.map f)
  | .every => .every

/-- Renames the memories of a set of effects, as when a dialect's ops are
seen in a larger dialect that holds its memories among others. -/
def Effects.map {Mem Mem' : Type} (f : Mem → Mem') (e : Effects Mem) : Effects Mem' :=
  { e with reads := e.reads.map f, writes := e.writes.map f, allocates := e.allocates.map f }

/-- Each op of a dialect declares its poison class and its set of effects,
over the dialect's memories `Mem`. -/
class DialectEffects (d : Dialect) where
  /-- The names of the dialect's memories. -/
  Mem : Type
  /-- How the op treats poison operands. -/
  poisonClass : d.Op → PoisonClass
  /-- The effects of the op's own rule. An op with a callee runs its callee
  and has its callee's effects too, which this set leaves out: the effects
  of an op in place, `SymbolTable.opEffects`, add its callee's summary. -/
  effects : d.Op → Effects Mem
export DialectEffects (poisonClass effects)

end Fir
