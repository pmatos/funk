import FirTest.TraceDialect
import FirRef.RunArgs

/-!
Tests of scripted worlds (#233, stage 4): the answers to each event in
order, and the world's writes into escaped memory, and what `fir-ref run
--world` reports. The core and `gpu` show no event yet, so the tests of a
script with answers use the emit dialect of `FirTest.TraceDialect` and a
computation of the traced layer that lets an allocation escape and asks
the world; `fir-ref run --world` is tested on what exists: an empty script
fits every run of the sum, a script with an answer fits none, and the end
of a return reports the memory an observer reaches.
-/

namespace FirTest.WorldScript

open Fir Fir.Memory FirRef

/-! # Answers in order -/

section Emit

open FirTest.TraceDialect

/-- The end of `emitMain`'s return: no value, empty memories, nothing
escaped. -/
abbrev emitEnd : ObservedEnd (unitsOf lay) (fun _ => ()) (List (DVal EmitDialect)) :=
  ⟨[], Memories.empty, []⟩

/-- At the script that answers its one event with `7`, `emitMain` returns
after the act of `emit` answered with `7`: that outcome follows the script,
is shown at its world, and is an outcome of the traced runs. -/
example : traceObservable (runs .nil) (.ret [(⟨0, 7⟩ : Act Nat Nat)] emitEnd) ∧
    (TOutcome.ret [(⟨0, 7⟩ : Act Nat Nat)] emitEnd).Follows [7] ∧
    (TOutcome.ret [(⟨0, 7⟩ : Act Nat Nat)] emitEnd).InWorld (WorldScript.world [7]) :=
  ⟨⟨2, _, emitMain_run 7, rfl⟩, rfl,
    ((TOutcome.follows_iff [7] (TOutcome.ret [(⟨0, 7⟩ : Act Nat Nat)] emitEnd) _ rfl).1 rfl).1⟩

/-- The outcome that answers `emit` with `6` does not follow that script, and
is not shown at its world. -/
example : ¬ (TOutcome.ret [(⟨0, 6⟩ : Act Nat Nat)] emitEnd).Follows [7] ∧
    ¬ (TOutcome.ret [(⟨0, 6⟩ : Act Nat Nat)] emitEnd).InWorld (WorldScript.world [7]) :=
  ⟨by simp [TOutcome.Follows], fun h => by
    simpa [WorldScript.world, TOutcome.before] using h 0 _ rfl⟩

/-- A script that answers no event, or two, fits no outcome of `emitMain`,
which shows one: an outcome shown at their worlds shows as many acts as
they have answers only when it follows them. -/
example : ¬ (TOutcome.ret [(⟨0, 7⟩ : Act Nat Nat)] emitEnd).Follows [] ∧
    ¬ (TOutcome.ret [(⟨0, 7⟩ : Act Nat Nat)] emitEnd).Follows [7, 7] := by
  simp [TOutcome.Follows]

end Emit

/-! # Writes into escaped memory -/

/-- Memories whose units are bytes. -/
abbrev w : Nat → Nat := fun _ => 8

/-- The acts of these tests: an event that is a number, answered by a number
and the world's actions. -/
abbrev A := Act Nat (Nat × List WorldAct)

/-- A traced state whose memory 0 holds one live allocation, a byte that
holds 5, of which nothing escaped. -/
def s0 : TraceState Nat w := ⟨Memories.empty.set 0 ⟨[⟨.global, 1, [.bits 5], true, none, false⟩]⟩, []⟩

/-- A computation that lets the allocation escape, then asks the world with
the event `3`, as an external call would. -/
def callOut : TraceM A (TraceState Nat w) Nat := do
  let _ ← TraceM.escape 0 0
  TraceM.ask id 3

/-- The script that answers the event with `9`, and writes `7` into the
escaped allocation of handle 0. -/
def script : WorldScript (Nat × List WorldAct) := [(9, [.store 0 0 [.bits 7]])]

/-- The traced state after the script's answer: the byte holds 7, and the
allocation escaped with the handle 0. -/
def s1 : TraceState Nat w := ⟨Memories.empty.set 0 ⟨[⟨.global, 1, [.bits 7], true, none, false⟩]⟩, [(0, 0)]⟩

/-- The world's action on `s0` after the escape is the write that leaves
`s1`. -/
theorem apply_script :
    WorldAct.applyAll id [.store 0 0 [.bits 7]] (s0.escape 0 0).2 = some s1 :=
  rfl

/-- `callOut` shows the act of its event with the script's answer, and
returns its result in the state that the script's write leaves. -/
theorem callOut_script : callOut s0 (.ok (9, [⟨3, (9, [.store 0 0 [.bits 7]])⟩], s1)) :=
  ⟨.ok ((s0.escape 0 0).1, [], (s0.escape 0 0).2), rfl,
    _, ⟨9, [.store 0 0 [.bits 7]], s1, apply_script, rfl⟩, rfl⟩

/-- Every path of `callOut` whose answers follow the script returns `9` in
the state `s1`: the script fixes the answers and the writes. -/
theorem callOut_follows {r : Nat} {t : List A} {s : TraceState Nat w}
    (h : callOut s0 (.ok (r, t, s))) (hf : t.map (·.answer) = script) : r = 9 ∧ s = s1 := by
  obtain ⟨_, rfl, e', ⟨a, ws, s', happ, rfl⟩, he⟩ := h
  simp only [TraceEnd.after, List.nil_append, Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  simp only [List.map_cons, List.map_nil, script, List.cons.injEq, Prod.mk.injEq, and_true] at hf
  obtain ⟨rfl, rfl⟩ := hf
  rw [apply_script] at happ
  exact ⟨rfl, (Option.some.inj happ).symm⟩

-- At the end of a return in `s1`, an observer reaches the escaped
-- allocation, and `fir-ref run --world` reports its byte as the world wrote
-- it.
#guard (endReach (⟨[], s1.mem, s1.escaped⟩ : ObservedEnd w id (List (DVal CoreDialect)))).map
      (·.map (allocJson s1.mem)) =
    some ["{\"memory\":0,\"alloc\":0,\"kind\":\"global\",\"align\":1,\"size\":1,\"live\":true," ++
      "\"units\":[\"0x07\"]}"]

/-! # `fir-ref run --world` -/

/-- A module of the sum whose kernel `@keep` stores its argument into
work-group memory, which outlives the call, through a pointer that it
stores in more work-group memory, and returns a pointer to that. -/
def kernels : String := "module @dev() {
  dialects gpu

  func @keep(%v: i8) -> ptr {
  ^e:
    %b: ptr = gpu.work_group_alloca i8 @0
    store nonatomic %v, %b @0
    %pp: ptr = gpu.work_group_alloca ptr @0
    store nonatomic %b, %pp @0
    %s: ptr = alloca stack i8 @0
    ret %pp @0
  }

  func @frame() -> ptr {
  ^e:
    %s: ptr = alloca stack i8 @0
    ret %s @0
  }
}

func @add(%a: i8, %b: i8) -> i8 {
^e:
  %s: i8 = add %a, %b @0
  ret %s @0
}

locs {
  @0 = unknown
}
"

/-- `fir-ref run` on `kernels`, with the scripted world `world`. -/
def runWorld (func : String) (args : List String) (world : Option (List WorldAnswer))
    (mode : Mode := .scripted []) : RunReport :=
  runBytes "t.fir" kernels.toUTF8 defaultFuel func args mode .single world

/-- Eight fragments of the pointer `p` of the memory 0, as units. -/
def frags (p : String) : String :=
  ",".intercalate ((List.range 8).map fun i => s!"\"frag(0, {p}, {i})\"")

-- Without a world, a run reports what it reported before.
#guard runWorld "@add" ["2", "3"] none == { out := "{\"kind\":\"return\",\"values\":[\"5\"],\"choices\":0}", status := 0 }
-- With the empty script, a run with no pointer reports an empty trace and
-- no memory.
#guard runWorld "@add" ["2", "3"] (some []) == { out := "{\"kind\":\"return\",\"values\":[\"5\"]," ++
  "\"trace\":[],\"escaped\":[],\"memory\":[],\"choices\":0}", status := 0 }
/-- The report of `@keep`: the pointer's allocation, then the one its units
point into. -/
def keepOut : String :=
  "{\"kind\":\"return\",\"values\":[\"ptr(1, 0)\"],\"trace\":[],\"escaped\":[]," ++
  "\"memory\":[{\"memory\":0,\"alloc\":1,\"kind\":\"global\",\"align\":8,\"size\":8," ++
  "\"live\":true,\"units\":[" ++ frags "ptr(0, 0)" ++ "]},{\"memory\":0,\"alloc\":0," ++
  "\"kind\":\"global\",\"align\":1,\"size\":1,\"live\":true,\"units\":[\"0xff\"]}]," ++
  "\"choices\":0}"

-- The end of a return reports the memory that an observer reaches from the
-- returned pointer. The stack allocation, freed at the return, is not
-- reached.
#guard runWorld "@dev::@keep" ["-1"] (some []) == { out := keepOut, status := 0 }
-- A returned stack pointer is dangling: it reaches nothing.
#guard (runWorld "@dev::@frame" [] (some [])).out == "{\"kind\":\"return\"," ++
  "\"values\":[\"ptr(0, 0)\"],\"trace\":[],\"escaped\":[],\"memory\":[],\"choices\":0}"
-- Every outcome of exhaustive mode carries its trace and its end.
#guard (runWorld "@add" ["poison", "1"] (some []) (.exhaustive 16)).out ==
  "{\"kind\":\"outcomes\",\"choices\":0,\"outcomes\":[{\"kind\":\"return\"," ++
  "\"values\":[\"poison\"],\"trace\":[],\"escaped\":[],\"memory\":[]}]}"
-- A script that answers an event fits no run of the sum, which shows none.
#guard (runWorld "@add" ["2", "3"] (some [⟨[], []⟩])).err == "fir-ref: @add: the world's " ++
  "script does not fit the run: the run shows no event, and the script answers 1"

/-! # Reading a script -/

/-- What a script reads as, or the error that reading it gives. -/
def read (t : String) : Option (List WorldAnswer) ⊕ String :=
  match readWorld t with
  | .ok ws => .inl (some ws)
  | .error e => .inr e

#guard read "" == .inl (some [])
#guard read "# no event\n\n" == .inl (some [])
#guard read "answer 5 poison\nstore 0 2 0x7f poison frag(0,1,-3,7)\nalloc 3 16 2\nanswer\nfree 1\n" ==
  .inl (some [⟨["5", "poison"], [.store 0 2 [.bits 0x7f, .poison, .frag 0 (some 1) (-3) 7], .alloc 3 16 2]⟩,
    ⟨[], [.free 1]⟩])
-- CRLF line ends and tabs read as LF and spaces.
#guard read "answer\t5\r\nfree 0\r\n" == .inl (some [⟨["5"], [.free 0]⟩])
#guard read "store 0 0 0x1" == .inr "line 1: an action of the world comes before any answer"
#guard read "answer\nfree x" == .inr "line 2: free x is not an answer or an action of the world"
#guard read "answer\nstore 0 0 frag(0,none,0)" ==
  .inr "line 2: store 0 0 frag(0,none,0) is not an answer or an action of the world"

end FirTest.WorldScript
