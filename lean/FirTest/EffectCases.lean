import Fir

/-!
The effects of each core op instance, on the shared cases of
`tests/dialects/effects.cases`, which `crates/funk-ir/tests/effects.rs`
reads too, so the Rust registry's sets are `Core.Op.effects`
(ADR-2026-11-09-1541).

Each case names the set of the first op of the entry block of `@f`. A set
is written `pure`, or as its effects joined by `,`, in the order of the
fields of `Effects`. The cases pin all 35 core op names, every flag set of `add`,
`sub` and `mul`, and `exact` on `sdiv` and `udiv`; the Rust test checks that
they cover each attribute that changes a set.
-/

namespace FirTest.EffectCases

open Fir

/-- The word of a memory-named effect: its name and its memories, or nothing
when it names none. -/
def memWord {Mem : Type} (memName : Mem → String) (name : String) : MemSet Mem → List String
  | .these [] => []
  | .these ms => [name ++ "(" ++ "+".intercalate (ms.map memName) ++ ")"]
  | .every => [name ++ "(*)"]

/-- A set of effects as the shared file writes it. -/
def render {Mem : Type} (memName : Mem → String) (e : Effects Mem) : String :=
  let words := memWord memName "reads" e.reads ++ memWord memName "writes" e.writes ++
    memWord memName "allocates" e.allocates ++
    [("may-ub", e.mayUB), ("may-poison", e.mayPoison), ("observable", e.observable),
      ("control", e.control)].filterMap fun (w, b) => if b then some w else none
  if words.isEmpty then "pure" else ",".intercalate words

#guard render (fun _ => "") ({} : Effects Empty) == "pure"
#guard render id (Effects.all : Effects String) ==
  "reads(*),writes(*),allocates(*),may-ub,may-poison,observable,control"
#guard render id ({ writes := .these ["a", "b"], mayUB := true } : Effects String) ==
  "writes(a+b),may-ub"

/-- One case of the shared file: its name, the set it names and its text. -/
structure Case where
  name : String
  set : String
  text : String

/-- The cases of the shared file. -/
def cases : List Case :=
  ((include_str "../../tests/dialects/effects.cases").splitOn "=== ").tail.filterMap fun piece =>
    let lines := piece.splitOn "\n"
    match (lines.headD "").splitOn " " with
    | [name, set] => some ⟨name, set, "\n".intercalate lines.tail⟩
    | _ => none

/-- The op that a case pins: the first op of the entry block of `@f`. -/
def Case.op (c : Case) : Option Core.Op :=
  match (Fir.parse c.text : Except ParseError (Module CoreDialect)) with
  | .ok m => m.items.findSome? fun
      | .func f => if f.name == "f" then f.body.blocks.head? >>= (·.body.head?) |>.map (·.op)
        else none
      | _ => none
  | .error _ => none

/-- Whether the pinned op parses and has, through the effect class, the set
that the case names. -/
def Case.holds (c : Case) : Bool :=
  match c.op with
  | some o => render Empty.elim (effects (d := CoreDialect) o) == c.set
  | none => false

#guard cases.length == 67
#guard (cases.filter (!·.holds)).map (·.name) == []
-- The cases pin every core op.
#guard ((cases.filterMap Case.op).map Core.Op.name).eraseDups.length == 35
#guard (Core.samples.map Core.Op.name).all fun n =>
  (cases.filterMap Case.op).any (·.name == n)

end FirTest.EffectCases
