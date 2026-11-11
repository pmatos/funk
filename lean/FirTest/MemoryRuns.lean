import FirTest.Calls

/-!
Tests of runs with memory: the frame hook frees a call's stack allocations
when the call returns, and leaves every other allocation as it was
(ADR-2026-11-09-1548). No core op touches memory yet, so a semantics
written here for these tests, not fir's, gives `const` an allocation: it
allocates a unit of the given kind in the run's one memory, then gives its
constant by the core rule. The runs are those of the interpreter in the
state layer over the tree of choices, walked by exhaustive mode, from the
empty memories.
-/

namespace FirTest.MemoryRuns

open Fir Fir.Memory FirRef

/-- The memories of these runs: one memory, of 8-bit units. -/
abbrev Mems := Memories Unit (fun _ => 8)

/-- The state layer over the tree of choices that `fir-ref run` runs the
core dialect in. -/
abbrev MemTree := StateT Mems (ChoiceTree Core.Op)

/-- The tree of choices of `fir-ref run`. -/
abbrev Tree := ChoiceTree Core.Op

/-- A semantics, not fir's, in which `const` allocates one unit of kind `k`
before it gives its constant. Every other op keeps its core rule and the
memories. -/
@[instance_reducible] def constAllocates (k : AllocKind) : DialectDenote CoreDialect MemTree where
  denote
    | Core.Op.const w v, args => do
      let _ ← MonadMemory.alloc () k 1
      StateT.lift (DialectDenote.denote (m := Tree) (d := CoreDialect) (Core.Op.const w v) args)
    | op, args => StateT.lift (DialectDenote.denote (m := Tree) op args)
  exit op args := StateT.lift (DialectDenote.exit (m := Tree) op args)

/-- A semantics, not fir's, in which `const 3` loads a unit from the
allocation with id 1 and every other `const` allocates a unit on the stack,
before each gives its constant. -/
@[instance_reducible] def constThreeLoads : DialectDenote CoreDialect MemTree where
  denote
    | Core.Op.const w v, args => do
      if v.toNat = 3 then discard <| MonadMemory.load () ⟨some 1, 0⟩ 1
      else discard <| MonadMemory.alloc () .stack 1
      StateT.lift (DialectDenote.denote (m := Tree) (d := CoreDialect) (Core.Op.const w v) args)
    | op, args => StateT.lift (DialectDenote.denote (m := Tree) op args)
  exit op args := StateT.lift (DialectDenote.exit (m := Tree) op args)

/-- What a path of a run shows of its memories: the liveness of each
allocation of the one memory, in order, and the number of frames left. -/
def shown (S : Mems) : List Bool × Nat := ((S.mem ()).blocks.map (·.live), S.frames.length)

/-- Every way the run of the function `func` of the text `t` may end, with
the semantics `sem`, and what each path shows of its memories; a path that
ends in UB shows none. `none` when the text does not parse or a path
chooses. -/
def memRunWith (sem : DialectDenote CoreDialect MemTree) (t func : String) :
    Option (List (Bool × List Bool × Nat)) :=
  match parseCore t with
  | .error _ => none
  | .ok M => match M.funcs.find? (Text.printSymbol ·.name == func) with
    | none => none
    | some f => match readArgs (f.params.map (·.2)) [] with
      | .error _ => none
      | .ok args => letI := sem
        (ChoiceTree.explore ((f.run M (m := MemTree) args 1000).run Memories.empty) 0).map
          fun ls => ls.map fun
            | (.ok (.ok (.ret _), S), _) => (true, shown S)
            | (.ok (_, S), _) => (false, shown S)
            | _ => (false, [], 0)

/-- `memRunWith`, with `const` allocating on kind `k`. -/
def memRun (k : AllocKind) (t func : String) : Option (List (Bool × List Bool × Nat)) :=
  memRunWith (constAllocates k) t func

/-- `@inner` makes one constant; `@outer` makes one, then calls `@inner`,
then makes another. -/
def nested : String := withFuncs [
  "func @inner() -> i8 {\n^e:\n  %c: i8 = const 1 @0\n  ret %c @0\n}\n",
  "func @outer() -> i8 {\n^e:\n  %a: i8 = const 2 @0\n  %b: i8 = call @inner @0\n" ++
    "  %d: i8 = const 3 @0\n  ret %b @0\n}\n"]

-- A function's stack allocations are freed when it returns: `@inner`'s on
-- its return to `@outer`, and `@outer`'s when the run returns. No frame is
-- left.
#guard memRun .stack nested "@inner" == some [(true, [false], 0)]
#guard memRun .stack nested "@outer" == some [(true, [false, false, false], 0)]
-- An allocation of another kind is in no frame: it stays live.
#guard memRun .heap nested "@outer" == some [(true, [true, true, true], 0)]
#guard memRun .global nested "@inner" == some [(true, [true], 0)]
-- `@inner`'s allocation is freed on its return to `@outer`, before `@outer`
-- returns: `const 3` in `@outer` then loads from it, which is UB.
#guard memRunWith constThreeLoads nested "@outer" == some [(false, [], 0)]

/-! # A run with no allocation

The core dialect's own rules touch no memory: its runs with memory keep the
empty memories, and are its runs. -/

example (M : Module CoreDialect) (f : Func CoreDialect)
    (args : HVector toType (f.params.map (·.2))) :
    letI := DialectDenote.liftState (d := CoreDialect) (m := SetM) Mems
    f.memRuns Unit (fun _ => 8) M args = f.runs M args := by
  rw [Func.memRuns_eq]

end FirTest.MemoryRuns
