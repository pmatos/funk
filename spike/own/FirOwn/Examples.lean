import FirOwn.Interp
import FirOwn.Core

/-!
# Sample functions, run in both `fir-ref` modes

Each sample is written in fir text in its doc comment, then as the abstract
syntax that a parser would produce.
-/

namespace FirOwn.Examples

open Core (Ty Op)

/-- What a run shows to an observer: poison, or a value of some width. -/
inductive Obs where
  | poison
  | value (w : Nat) (n : Nat)
  deriving Repr, DecidableEq

def obs : DVal Core → Obs
  | ⟨.int w, v⟩ =>
    match (v : PoisonOr (BitVec w)) with
    | .poison => .poison
    | .value x => .value w x.toNat

deriving instance Repr, DecidableEq for Result

abbrev Outcome := Prog.Ev (Result Obs)

def toOutcome : Prog.Ev (Result (DVal Core)) → Outcome
  | .ok r => .ok (r.map obs)
  | .ub r => .ub r

/-- `fir-ref` exhaustive mode: the outcome set, and whether the budget ran out. -/
def runAll (f : Func Core) (args : List (DVal Core)) (fuel := 64) (budget := 16) :
    List Outcome × Bool :=
  let (es, over) := Prog.exhaustive (run f fuel args) budget
  (es.map toOutcome, over)

/-- `fir-ref` scripted mode: one outcome for one choice sequence. -/
def runScripted (f : Func Core) (args : List (DVal Core)) (script : List Nat)
    (fuel := 64) : Option (Outcome × Bool) :=
  (Prog.scripted (run f fuel args) script).map fun (e, u) => (toOutcome e, u)

def i (w : Nat) : Ty := .int w
def iv (w : Nat) (n : Int) : DVal Core := ⟨.int w, .value (BitVec.ofInt w n)⟩
def let1 (x : Name) (w : Nat) (op : Op) (args : List Name) (loc : Nat) : Inst Core :=
  { results := [(x, i w)], op, args, loc := .ref loc }

/-- The tracer subset.
```
func @add3(%x: i8) -> i8 {
entry(%x: i8):
  %c = const 3 : i8     @1
  %r = add %x, %c : i8  @1
  ret %r : i8           @2
}
``` -/
def add3 : Func Core where
  name := "add3"
  results := [i 8]
  blocks := [{ label := "entry", params := [("x", i 8)], body := [
    let1 "c" 8 (.const 8 3) [] 1,
    let1 "r" 8 (.add 8 false) ["x", "c"] 1,
    { results := [], op := .ret [i 8], args := ["r"], loc := .ref 2 }] }]

/-- Two blocks; the branch passes block arguments (H1).
```
func @twoBlocks(%a: i32, %b: i32) -> i32 {
entry(%a: i32, %b: i32):
  %s = add %a, %b : i32   @1
  br next(%s, %a)         @1
next(%p: i32, %q: i32):
  %r = add %p, %q : i32   @2
  ret %r : i32            @2
}
``` -/
def twoBlocks : Func Core where
  name := "twoBlocks"
  results := [i 32]
  blocks := [
    { label := "entry", params := [("a", i 32), ("b", i 32)], body := [
      let1 "s" 32 (.add 32 false) ["a", "b"] 1,
      { results := [], op := .br, args := [], succs := [⟨"next", ["s", "a"]⟩], loc := .ref 1 }] },
    { label := "next", params := [("p", i 32), ("q", i 32)], body := [
      let1 "r" 32 (.add 32 false) ["p", "q"] 2,
      { results := [], op := .ret [i 32], args := ["r"], loc := .ref 2 }] }]

/-- Poison from `add nsw`, then `freeze`. `frozen 8 127 true` is:
```
func @frozen() -> i8 {
entry:
  %m = const 127 : i8         @1
  %one = const 1 : i8         @1
  %p = add nsw %m, %one : i8  @1   -- overflows: poison
  %f = freeze %p : i8         @2
  %z = xor %f, %f : i8        @3
  ret %z : i8                 @4
}
```
`frozen 2 1 false` overflows at `i2` and returns `%f` itself. -/
def frozen (w : Nat) (big : Int) (useXor : Bool) : Func Core where
  name := "frozen"
  results := [i w]
  blocks := [{ label := "entry", params := [], body := [
    let1 "m" w (.const w big) [] 1,
    let1 "one" w (.const w 1) [] 1,
    let1 "p" w (.add w true) ["m", "one"] 1,
    let1 "f" w (.freeze w) ["p"] 2,
    let1 "z" w (.xor w) ["f", "f"] 3,
    { results := [], op := .ret [i w], args := [if useXor then "z" else "f"], loc := .ref 4 }] }]

/-- `poison` returned without `freeze`. -/
def retPoison : Func Core := { frozen 8 127 false with
  blocks := [{ label := "entry", params := [], body := [
    let1 "m" 8 (.const 8 127) [] 1,
    let1 "one" 8 (.const 8 1) [] 1,
    let1 "p" 8 (.add 8 true) ["m", "one"] 1,
    { results := [], op := .ret [i 8], args := ["p"], loc := .ref 2 }] }] }

/-- Branching on poison is immediate UB, not poison (S1). -/
def branchOnPoison : Func Core where
  name := "branchOnPoison"
  results := [i 8]
  blocks := [
    { label := "entry", params := [], body := [
      let1 "t" 1 (.const 1 1) [] 1,
      let1 "p" 1 (.add 1 true) ["t", "t"] 1,
      { results := [], op := .condBr, args := ["p"],
        succs := [⟨"a", []⟩, ⟨"a", []⟩], loc := .ref 2 }] },
    { label := "a", params := [], body := [
      let1 "r" 8 (.const 8 0) [] 3,
      { results := [], op := .ret [i 8], args := ["r"], loc := .ref 3 }] }]

/-- A loop that never ends runs out of fuel. -/
def spin : Func Core where
  name := "spin"
  results := []
  blocks := [{ label := "entry", params := [], body := [
    { results := [], op := .br, args := [], succs := [⟨"entry", []⟩] }] }]

/-! ## Runs -/

#guard runAll add3 [iv 8 40] == ([.ok (.ret [.value 8 43])], false)
#guard runAll add3 [iv 8 255] == ([.ok (.ret [.value 8 2])], false)
#guard runAll twoBlocks [iv 32 5, iv 32 7] == ([.ok (.ret [.value 32 17])], false)
#guard runAll retPoison [] == ([.ok (.ret [.poison])], false)
#guard runAll branchOnPoison [] == ([.ub "branch on poison"], false)
#guard runAll spin [] == ([.ok .fuelExhausted], false)
-- `freeze` of poison at i2: four outcomes, one per choice.
#guard runAll (frozen 2 1 false) [] ==
  ((List.range 4).map fun n => .ok (.ret [.value 2 n]), false)
-- At i8, `x xor x` after `freeze` is 0 on every one of the 256 choices.
#guard runAll (frozen 8 127 true) [] ==
  ((List.range 256).map fun _ => .ok (.ret [.value 8 0]), false)
-- Over budget: exhaustive mode says so instead of guessing.
#guard (runAll (frozen 8 127 true) [] (budget := 4)).2 == true
-- Scripted mode: the witness 3 gives 3, and reports that a choice was used.
#guard runScripted (frozen 2 1 false) [] [3] == some (.ok (.ret [.value 2 3]), true)
#guard runScripted add3 [iv 8 1] [] == some (.ok (.ret [.value 8 4]), false)

/-! ## Proofs about one sample -/

/-- The kernel checks the whole outcome set of a small sample. -/
theorem frozen_i2_outcomes :
    runAll (frozen 2 1 false) [] =
      ([.ok (.ret [.value 2 0]), .ok (.ret [.value 2 1]),
        .ok (.ret [.value 2 2]), .ok (.ret [.value 2 3])], false) := by
  decide

/-- The run of `frozen 8 127 true` is one choice of 8 bits followed by
`x xor x`, by evaluation alone. -/
theorem frozen_xor_run :
    run (m := Prog) (frozen 8 127 true) 64 [] =
      Prog.choose 8 fun b => .pure (.ret [⟨.int 8, .value (b ^^^ b)⟩]) := by
  rfl

/-- So every behaviour of `x xor x` after `freeze` returns 0, at any choice. -/
theorem frozen_xor_zero (e : Prog.Ev (Result (DVal Core))) :
    Prog.sem (run (frozen 8 127 true) 64 []) e ↔
      e = .ok (.ret [⟨.int 8, .value 0⟩]) := by
  rw [frozen_xor_run]
  simp [Prog.sem, BitVec.xor_self]

end FirOwn.Examples
