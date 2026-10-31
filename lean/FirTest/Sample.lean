import FirTest.Modes

/-!
Tests of `fir-ref run --seed`, sampled mode (ADR-2026-10-31-0002): its
generator, its command line, and its reports. Each value it draws is one
of the run's outcomes, as exhaustive mode lists them, and the sequence it
prints, given to `--choices`, follows the same path to the same report.
-/

namespace FirTest

open Fir FirRef

/-! # The generator

SplitMix64's first outputs from the state 0 are its published ones. -/

#guard (Seed.next ⟨0⟩).1 == 0xE220A8397B1DCDAF
#guard ((Seed.next ⟨0⟩).2.next).1 == 0x6E789E6AA1B965F4
#guard (Seed.words 0 ⟨0⟩).1 == 0
#guard (Seed.words 1 ⟨0⟩).1 == 0xE220A8397B1DCDAF
#guard (Seed.words 3 ⟨0⟩).1 ==
  0xE220A8397B1DCDAF <<< 128 ||| 0x6E789E6AA1B965F4 <<< 64 ||| 0x06C45D188009454F

/-- The values that `draw` gives at `w` bits for the seeds below `n`. -/
def draws (w n : Nat) : List (BitVec w) := (List.range n).map fun s => (draw w ⟨s.toUInt64⟩).1

-- One draw in four is a boundary bit pattern, so a hundred seeds meet each
-- one, at every width.
#guard [1, 2, 7, 8, 33, 64, 65, 128].all fun w => (boundaries w).all ((draws w 100).contains ·)
-- The other draws spread over the values, and a wide choice takes more
-- than one draw of 64 bits.
#guard (draws 64 100).eraseDups.length > 60
#guard (draws 128 100).any fun b => b.toNat ≥ 2 ^ 120

/-! # The command line -/

#guard modeLine ["--seed", "5", "f.fir", "@f"] == "sampled 5"
#guard modeLine ["--seed", "0", "f.fir", "@f"] == "sampled 0"
#guard modeLine ["--seed", "18446744073709551615", "f.fir", "@f"] == "sampled 18446744073709551615"
#guard modeLine ["--seed", "18446744073709551616", "f.fir", "@f"] ==
  "error: --seed takes a number below 2^64, not 18446744073709551616"
#guard modeLine ["--seed", "-1", "f.fir", "@f"] == "error: --seed takes a number below 2^64, not -1"
#guard modeLine ["f.fir", "@f", "--seed"] == "error: --seed takes a number below 2^64"
#guard modeLine ["--seed", "1", "--choices", "1", "f.fir", "@f"] ==
  "error: --seed does not go with --choices"
#guard modeLine ["--seed", "1", "--exhaustive", "f.fir", "@f"] ==
  "error: --seed does not go with --exhaustive"
#guard modeLine ["--seed", "1", "--choice-bits", "4", "f.fir", "@f"] ==
  "error: --choice-bits needs --exhaustive"
#guard modeLine ["--", "--seed", "1"] == "scripted []"

/-! # Reports -/

/-- What sampled mode reports on the text `t`, with the seed `s`. -/
def sampleRun (t : String) (args : List String) (s : Nat) : RunReport :=
  runText t "@f" args defaultFuel (.sampled s)

/-- The choices that a sampled report says it drew. -/
def sequenceOf (r : RunReport) : List String :=
  match r.out.splitOn ",\"sequence\":[" with
  | [_, rest] => match ((rest.splitOn "]").headD "").replace "\"" "" with
    | "" => []
    | inner => inner.splitOn ","
  | _ => ["no sequence"]

/-- A sampled report without the choices it drew: scripted mode's report
of the same path. -/
def withoutSequence (r : RunReport) : RunReport :=
  { r with out := (r.out.splitOn ",\"sequence\":[").headD "" ++ "}" }

/-- Scripted mode, on the choices that sampled mode drew with the seed `s`,
reports the same path. -/
def replays (t : String) (args : List String) (s : Nat) : Bool :=
  let r := sampleRun t args s
  runText t "@f" args defaultFuel (.scripted (sequenceOf r)) == withoutSequence r

/-- The outcome of a sampled report is one that exhaustive mode lists. -/
def listed (t : String) (args : List String) (s : Nat) : Bool :=
  let o := (((sampleRun t args s).out.splitOn ",\"choices\":").headD "") ++ "}"
  ((explore t args).out.splitOn o).length > 1

#guard sampleRun (frozen "i2") ["1"] 1 ==
  { out := "{\"kind\":\"return\",\"values\":[\"-1\"],\"choices\":1,\"sequence\":[\"-1\"]}",
    status := 0 }
#guard sampleRun (frozen "i2") ["0"] 7 ==
  { out := "{\"kind\":\"return\",\"values\":[\"1\"],\"choices\":0,\"sequence\":[]}", status := 0 }
#guard sampleRun (subSelf "i64") ["9223372036854775807"] 3 ==
  { out := "{\"kind\":\"return\",\"values\":[\"0\"],\"choices\":1,\"sequence\":[\"" ++
      (sequenceOf (sampleRun (subSelf "i64") ["9223372036854775807"] 3)).headD "" ++ "\"]}",
    status := 0 }
-- A seed draws the same values every time, and seeds differ.
#guard sampleRun (frozen "i64") ["9223372036854775807"] 1 ==
  sampleRun (frozen "i64") ["9223372036854775807"] 1
#guard sampleRun (frozen "i64") ["9223372036854775807"] 1 !=
  sampleRun (frozen "i64") ["9223372036854775807"] 2

-- Every sampled outcome is one of the run's.
#guard (List.range 64).all (listed (frozen "i2") ["1"])
#guard (List.range 64).all (listed (frozen "i1") ["true"])
#guard (List.range 64).all (listed twoFreezes ["true"])
#guard (List.range 64).all (listed (subSelf "i8") ["127"])

-- The sequence it prints fits the run, at every width: scripted mode on it
-- gives the same report.
#guard [("i1", "true"), ("i2", "1"), ("i7", "63"), ("i8", "127"), ("i33", "4294967295"),
    ("i64", "9223372036854775807"), ("i128", "170141183460469231731687303715884105727")].all
  fun (ty, a) => (List.range 32).all (replays (frozen ty) [a])
#guard (List.range 32).all (replays twoFreezes ["true"])
#guard (List.range 32).all (replays (subSelf "i64") ["9223372036854775807"])
#guard (List.range 4).all (replays (frozen "i2") ["0"])

-- A stuck path is reported with status 1, and an op without rules as an
-- error.
#guard sampleRun (body "func @f(%a: i1) -> i1"
    ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0"]) ["true"] 0 ==
  { out := "{\"kind\":\"stuck\",\"reason\":\"a block ends without a terminator\",\"choices\":1," ++
      "\"sequence\":[\"" ++ (sequenceOf (sampleRun (body "func @f(%a: i1) -> i1"
        ["^e:", "  %p: i1 = add nsw %a, %a @0", "  %f: i1 = freeze %p @0"]) ["true"] 0)).headD "" ++
      "\"]}", status := 1 }
#guard sampleRun (body "func @f()" ["^e:", "  br ^n @0", "^n:", "  ret @0"]) [] 0 ==
  fails 2 "fir-ref: @f: br has no execution rules yet"

/-! # The theorems' axioms -/

/-- info: 'Fir.ChoiceTree.sample_script' depends on axioms: [propext] -/
#guard_msgs in #print axioms Fir.ChoiceTree.sample_script

/-- info: 'Fir.Core.sampled_fits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sampled_fits

/-- info: 'Fir.Core.sampled_outcomes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sampled_outcomes

/-- info: 'Fir.Core.sampled_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Fir.Core.sampled_stuck

end FirTest
