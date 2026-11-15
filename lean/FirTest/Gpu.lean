import Fir

/-!
The second dialect in tree, `gpu` (ADR-2026-11-09-1545), on the cases of
`tests/dialects/gpu.cases`, which `crates/funk-ir/tests/gpu.rs` reads too,
so the two sides agree on each of them. Each case is read in the sum of the
core and `gpu`, `CoreGpu`, as `fir-ref fmt` and `fir-ref validate` read
it: an accepted case parses, prints as itself and has no problem; an
invalid one parses, prints as itself and has a problem; a malformed one
does not parse.
-/

namespace FirTest.GpuCases

open Fir

/-- What a case asks of the check. -/
inductive Verdict where
  | accept
  | invalid
  | malformed
  deriving DecidableEq

/-- One case of the shared file: its verdict, its name and its text. -/
structure Case where
  verdict : Verdict
  name : String
  text : String

/-- A case's verdict, from its word. -/
def verdict? : String → Option Verdict
  | "accept" => some .accept
  | "invalid" => some .invalid
  | "malformed" => some .malformed
  | _ => none

/-- The cases of the shared file. -/
def cases : List Case :=
  ((include_str "../../tests/dialects/gpu.cases").splitOn "=== ").tail.filterMap fun piece =>
    let lines := piece.splitOn "\n"
    match (lines.headD "").splitOn " " with
    | [w, name] => (verdict? w).map fun v => ⟨v, name, "\n".intercalate lines.tail⟩
    | _ => none

/-- Whether the check gives a case its verdict. -/
def Case.holds (c : Case) : Bool :=
  match (Fir.parse c.text : Except ParseError (Module CoreGpu)), c.verdict with
  | .ok m, .accept => m.print == c.text && m.allProblems.isEmpty
  | .ok m, .invalid => m.print == c.text && !m.allProblems.isEmpty
  | .error _, .malformed => true
  | _, _ => false

#guard cases.length == 8
#guard (cases.filter (·.verdict == .accept)).length == 2
#guard (cases.filter (·.verdict == .malformed)).length == 3
#guard (cases.filter (!·.holds)).map (·.name) == []

/-- The messages of a case's problems. -/
def messages (name : String) : List String :=
  match cases.find? (·.name == name) with
  | some c => match (Fir.parse c.text : Except ParseError (Module CoreGpu)) with
    | .ok m => m.allProblems.map (·.message)
    | .error _ => []
  | none => []

-- An id that is not an `i32` breaks the dialect's own rule; a word of `gpu`
-- outside a module whose set names it breaks the dialect-set rule; and a
-- device module's pointer types name the host's memories.
#guard messages "an-i64-id" == ["the op breaks its dialect's own rule"]
#guard messages "device-module-without-gpu" ==
  ["the function writes a word of the dialect gpu, which the module's dialect set does not name"]
#guard messages "device-memory-not-declared" ==
  ["a type names memory 3, which the data layout does not declare"]

-- The core alone reads no word of `gpu`.
#guard (cases.filter fun c => c.verdict == .accept &&
  (Fir.parse c.text : Except ParseError (Module CoreDialect)).toBool).isEmpty

-- The sum's dialect set is `gpu`'s name, and each op routes to `gpu`.
#guard names CoreGpu == ["gpu"]
#guard decodeOp (d := CoreGpu) "gpu.work_group_id" [.word "gpu.y"] [] [.inl (.int 32)] ==
  some (.inr (.query .workGroupId .y 32))

end FirTest.GpuCases
