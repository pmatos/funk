import FirTest.FloatArith

/-!
Tests of `fir-ref run --exhaustive --nans` on `FirRef.runBytes`
(ADR-2026-11-16-0855, `docs/decisions/fir-ref-command-line.md#trying-a-few-nans`):
at a NaN choice it tries the positive quiet NaN and each NaN it is given,
in order, each once, and skips a pattern that is no NaN of the format; at any
other choice it tries every value; it says `complete` when no path made a NaN
choice; and it charges the budget the bits that count the NaNs it tries. The
machine's walk gives what the spec's walk of the run's tree gives, and the
theorems of the mode rest on the axioms that the build allows.
-/

namespace FirTest.NaNRuns

open Fir FirRef

/-- What the mode reports on `@f` of the text `t` with the NaNs `nans` and a
budget of `b` bits. -/
def nanRun (t : String) (args : List String) (nans : List Nat) (b : Nat := 16) : RunReport :=
  runText t "@f" args (mode := .exhaustiveNaN b nans)

/-- The report of the outcomes that return each of `vss`, with `c` choices
on the longest path, complete or not. -/
def nanOutcomes (vss : List (List String)) (c : Nat) (complete : Bool) : RunReport :=
  { out := "{\"kind\":\"outcomes\",\"choices\":" ++ toString c ++ ",\"complete\":" ++
      toString complete ++ ",\"outcomes\":[" ++
      ",".intercalate (vss.map fun vs => "{\"kind\":\"return\",\"values\":" ++ valuesJson vs ++ "}") ++
      "]}",
    status := 0 }

/-- `inf - inf` at `f32`, whose result is any NaN. -/
def infSub : String := floatOp "fsub" " round(rne)" "f32" 2

def inf32 : List String := ["0x7f800000", "0x7f800000"]

-- The positive quiet NaN, and no more with no NaNs given.
#guard nanRun infSub inf32 [] == nanOutcomes [["0x7fc00000"]] 1 false
-- The NaNs given come after them, each once; `1.0` and an `f64` NaN are no
-- NaNs of `f32` and are skipped.
#guard nanRun infSub inf32 [0x7fc00001, 0x3f800000, 0x7fc00000, 0xffffffff, 0x7fc00001,
    0x7ff8000000000000] ==
  nanOutcomes [["0x7fc00000"], ["0x7fc00001"], ["0xffffffff"]] 1 false
-- At `f64`, and at `float<2,1>`, whose quiet NaNs are its only NaNs.
#guard nanRun (floatOp "fsub" " round(rne)" "f64" 2) ["0x7ff0000000000000", "0x7ff0000000000000"]
    [0x7ff0000000000001] ==
  nanOutcomes [["0x7ff8000000000000"], ["0x7ff0000000000001"]] 1 false
#guard nanRun (floatOp "fsub" " round(rne)" "float(2, 1)" 2) ["0x6", "0x6"] [0xf] ==
  nanOutcomes [["0x7"], ["0xf"]] 1 false

-- A run that makes no NaN choice is complete: with no choice, and with
-- `freeze`'s, whose values it all tries.
#guard nanRun (floatOp "fadd" " round(rne)" "f32" 2) ["1.0", "2.0"] [0x7fc00000] ==
  nanOutcomes [["3.0"]] 0 true
#guard nanRun (frozen "i1") ["true"] [] == nanOutcomes [["false"], ["true"]] 1 true

/-- `inf - inf` at `f32`, as the integer of its bits. -/
def infSubBits : String :=
  body "func @f(%a: f32, %b: f32) -> i32"
    ["^e:", "  %r: f32 = fsub round(rne) %a, %b @0", "  %i: i32 = bitcast %r @0", "  ret %i @0"]

-- A NaN that a bit cast reads is tried as one that is returned.
#guard nanRun infSubBits inf32 [0x7fc00001] ==
  nanOutcomes [["2143289344"], ["2143289345"]] 1 false

/-- `inf - inf`, then `+ 1`: two NaN choices on one path. -/
def twoNaNs : String :=
  body "func @f(%a: f32, %b: f32) -> f32"
    ["^e:", "  %r: f32 = fsub round(rne) %a, %b @0", "  %o: f32 = const 1.0 @0",
     "  %s: f32 = fadd round(rne) %r, %o @0", "  ret %s @0"]

#guard nanRun twoNaNs inf32 [] == nanOutcomes [["0x7fc00000"]] 2 false
#guard nanRun twoNaNs inf32 [0xffc00000] == nanOutcomes [["0x7fc00000"], ["0xffc00000"]] 2 false

/-- `@f(%a: f32, %n: i32) -> f32`, which adds `%a` to itself `%n` times. -/
def sumLoop : String :=
  body "func @f(%a: f32, %n: i32) -> f32"
    ["^e:", "  %z: i32 = const 0 @0", "  br ^h(%a, %n) @0",
     "^h(%x: f32, %k: i32):", "  %d: i1 = icmp eq %k, %z @0", "  cond_br %d, ^x, ^b @0",
     "^b:", "  %y: f32 = fadd round(rne) %x, %a @0", "  %o: i32 = const 1 @0",
     "  %j: i32 = sub %k, %o @0", "  br ^h(%y, %j) @0", "^x:", "  ret %x @0"]

-- The quiet NaN alone takes no bit, so 1,000 NaN choices on a path fit any
-- budget; one NaN given takes 1 bit at each of them.
#guard nanRun sumLoop ["0x7fc00001", "1000"] [] 0 == nanOutcomes [["0x7fc00000"]] 1000 false
#guard nanRun sumLoop ["0x7fc00001", "16"] [0xffc00000] ==
  nanOutcomes [["0x7fc00000"], ["0xffc00000"]] 16 false
#guard nanRun sumLoop ["0x7fc00001", "17"] [0xffc00000] ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":16}", status := 0 }
-- Two NaNs to try take 1 bit, and three take 2.
#guard nanRun infSub inf32 [0x7fc00001] 0 ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":0}", status := 0 }
#guard nanRun infSub inf32 [0x7fc00001, 0xffc00000] 1 ==
  { out := "{\"kind\":\"choice-budget-exceeded\",\"budget\":1}", status := 0 }
#guard nanRun infSub inf32 [0x7fc00001, 0xffc00000] 2 ==
  nanOutcomes [["0x7fc00000"], ["0x7fc00001"], ["0xffc00000"]] 1 false
#guard ChoiceTree.bitsFor 1 = 0 && ChoiceTree.bitsFor 2 = 1 && ChoiceTree.bitsFor 3 = 2 &&
  ChoiceTree.bitsFor 4 = 2 && ChoiceTree.bitsFor 5 = 3

/-! # The machine against the spec -/

/-- The mode's report on `@f` of `t`, by the spec's walk of the run's tree
when `spec` is true, and by the machine otherwise. -/
def nanBy (spec : Bool) (t : String) (args : List String) (nans : List Nat) : RunReport :=
  letI : Gpu.WorkItem := .single
  match parseBytes (d := CoreGpu) t.toUTF8 with
  | .error _ => fails 1 "no parse"
  | .ok m => match findFunc m "@f" with
    | none => fails 2 "no function"
    | some (n, f) => match readGpuArgs (f.params.map (·.2)) args with
      | .error why => fails 2 why
      | .ok vs => exhaustiveNaNReport "@f" 16 <| if spec then
          (Gpu.modeTree n f vs defaultFuel).exploreNaN nans 16
        else Gpu.exhaustiveNaN n f vs defaultFuel 16 nans

#guard [(infSub, inf32), (twoNaNs, inf32), (infSubBits, inf32), (frozen "i2", ["1"])].all
  fun (t, args) => nanBy true t args [0x7fc00001] == nanBy false t args [0x7fc00001]

/-! # The command line -/

#guard modeLine ["--exhaustive", "--nans", "0x7fc00000,0xffc00000", "f.fir", "@f"] ==
  "exhaustive 16 nans [2143289344, 4290772992]"
#guard modeLine ["--exhaustive", "--nans", "0x7fc00000,0xFFC00000,0x1", "f.fir", "@f"] ==
  "error: --nans takes bit patterns, as 0x7fc00000,0xffc00000, not 0xFFC00000"
#guard modeLine ["--nans", "", "--exhaustive", "--choice-bits", "3", "f.fir", "@f"] ==
  "exhaustive 3 nans []"
#guard modeLine ["--exhaustive", "f.fir", "@f"] == "exhaustive 16"
#guard modeLine ["--nans", "0x1", "f.fir", "@f"] == "error: --nans needs --exhaustive"
#guard modeLine ["--exhaustive", "--nans", "7fc00000", "f.fir", "@f"] ==
  "error: --nans takes bit patterns, as 0x7fc00000,0xffc00000, not 7fc00000"
#guard modeLine ["--exhaustive", "--nans", "0x1,", "f.fir", "@f"] ==
  "error: --nans takes bit patterns, as 0x7fc00000,0xffc00000, not "
#guard modeLine ["--exhaustive", "--nans"] == "error: --nans takes a list of bit patterns"

/-! # Axioms -/

/-- info: 'Fir.Gpu.exhaustiveNaN_memOutcomes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.exhaustiveNaN_memOutcomes

/-- info: 'Fir.Gpu.exhaustiveNaN_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Fir.Gpu.exhaustiveNaN_exact

/-- info: 'FirRef.gpuExhaustiveNaN_eq_runGpuExhaustiveNaN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms FirRef.gpuExhaustiveNaN_eq_runGpuExhaustiveNaN

end FirTest.NaNRuns
