import Fir
import FirTest.EffectCases

/-!
The effect summaries of functions, on the shared cases of
`tests/dialects/effect-summaries.cases`, which
`crates/funk-ir/tests/summaries.rs` reads too, so Rust's summaries are
`SymbolTable.summary` (ADR-2026-11-10-2108).

Each case gives the summary of every function of every symbol table of its
module, by the path of symbols that leads to it. A set is written as in
`effects.cases`, with each set of memories in sorted order, since a summary
is a set and the order in which a walk joins memories is not part of it.
The checks below also run the summary on a chain of calls and a recursion
that are deep, which the walk follows without a stack per call.
-/

namespace FirTest.SummaryCases

open Fir

/-- One case of the shared file: its name, the summary each path names,
and its text. -/
structure Case where
  name : String
  sums : List (List Name × String)
  text : String

/-- A line of summaries: the symbols of its path, then the set. -/
def parseSum (line : String) : Option (List Name × String) :=
  match (line.splitOn " ").reverse with
  | set :: path@(_ :: _) =>
    if path.all (·.startsWith "@") then some (path.reverse.map fun (p : String) => (p.drop 1).toString, set)
    else none
  | _ => none

/-- The cases of the shared file. -/
def cases : List Case :=
  ((include_str "../../tests/dialects/effect-summaries.cases").splitOn "=== ").tail.map fun piece =>
    let lines := piece.splitOn "\n"
    let body := lines.tail
    let sums := body.takeWhile (·.startsWith "@")
    ⟨lines.headD "", sums.filterMap parseSum, "\n".intercalate (body.drop sums.length)⟩

/-- The symbol table that a path of nested modules leads to, from the items
`items` and the dialect set `ds` of a table. -/
def tableAt (ds : List Name) (items : List (Item CoreDialect)) :
    List Name → Option (SymbolTable CoreDialect)
  | [] => some ⟨ds, items⟩
  | n :: ns => items.findSome? fun
    | .module n' ds' is => if n' == n then tableAt ds' is ns else none
    | .func _ => none

mutual
/-- The paths of the functions of every table under an item, behind
`pre`. -/
def funcPathsItem (pre : List Name) : Item CoreDialect → List (List Name)
  | .func f => [pre ++ [f.name]]
  | .module n _ is => funcPaths (pre ++ [n]) is

/-- The paths of every function of every table under `items`, behind
`pre`. -/
def funcPaths (pre : List Name) : List (Item CoreDialect) → List (List Name)
  | [] => []
  | i :: is => funcPathsItem pre i ++ funcPaths pre is
end

/-- A set of memories in sorted order, each once. -/
def sortMems : MemSet String → MemSet String
  | .these ms => .these (ms.eraseDups.mergeSort (· ≤ ·))
  | .every => .every

/-- A summary as the shared file writes it. The core has no memory, so its
memories are named by no string. -/
def renderSum (e : Effects (DialectEffects.Mem CoreDialect)) : String :=
  let named := e.map Empty.elim
  let sorted : Effects String :=
    { named with
      reads := sortMems named.reads
      writes := sortMems named.writes
      allocates := sortMems named.allocates }
  FirTest.EffectCases.render id sorted

/-- The summary that a case gives a path, as the shared file writes it. -/
def Case.summary? (m : Module CoreDialect) (path : List Name) : Option String := do
  let t ← tableAt m.dialects m.items path.dropLast
  let s ← path.getLast?
  t.func? s |>.map fun _ => renderSum (t.summary s)

/-- The paths of a case that do not have the summary that it names, or the
case's name when its text does not parse or it names other paths than
those of its functions. -/
def Case.failures (c : Case) : List String :=
  match (Fir.parse c.text : Except ParseError (Module CoreDialect)) with
  | .error _ => [c.name]
  | .ok m =>
    let wrong := c.sums.filterMap fun (p, set) =>
      if Case.summary? m p == some set then none else some (c.name ++ " " ++ " ".intercalate p)
    if funcPaths [] m.items == c.sums.map (·.1) then wrong else c.name :: wrong

#guard cases.length == 11
#guard (cases.flatMap Case.failures) == []

/-! # Deep chains -/

/-- The text of a module of `n + 1` functions, each of which calls the next,
and the last of which divides. -/
def chainText (n : Nat) : String :=
  let link (i : Nat) := s!"func @f{i}(%a: i8) -> i8 \{\n^entry:\n  %r: i8 = call @f{i + 1} %a @0\n  ret %r @0\n}\n\n"
  String.join ((List.range n).map link) ++
    s!"func @f{n}(%a: i8) -> i8 \{\n^entry:\n  %r: i8 = udiv %a, %a @0\n  ret %r @0\n}\n\nlocs \{\n  @0 = unknown\n}\n"

/-- The summary of the first function of a chain of `n + 1`. -/
def chainHead (n : Nat) : Option String :=
  match (Fir.parse (chainText n) : Except ParseError (Module CoreDialect)) with
  | .ok m => some (renderSum (m.table.summary "f0"))
  | .error _ => none

#guard chainHead 0 == some "may-ub"
#guard chainHead 2000 == some "may-ub"

/-- The text of a function that calls itself `n` times in a row. -/
def selfText (n : Nat) : String :=
  let call (i : Nat) := s!"  %r{i + 1}: i8 = call @f %r{i} @0\n"
  s!"func @f(%r0: i8) -> i8 \{\n^entry:\n" ++ String.join ((List.range n).map call) ++
    s!"  ret %r{n} @0\n}\n\nlocs \{\n  @0 = unknown\n}\n"

#guard (match (Fir.parse (selfText 2000) : Except ParseError (Module CoreDialect)) with
  | .ok m => renderSum (m.table.summary "f") == "pure"
  | .error _ => false)

/-! # The theorems apply to the core -/

/-- In a module of valid core functions, a function whose summary leaves out
may-UB never ends in UB. -/
example {ctx : ModuleContext CoreDialect} {M : Module CoreDialect}
    (hv : ∀ g ∈ M.funcs, g.Valid ctx) {s : Name} {f : Func CoreDialect}
    (hf : M.func? s = some f) (hs : (M.table.summary s).mayUB = false)
    (args : HVector toType (f.params.map (·.2))) (fuel : Nat) (r : String) :
    ¬ (f.run (m := SetM) M args fuel).run (.ub r) :=
  Module.summary_neverUB hv hf hs args fuel r

end FirTest.SummaryCases
