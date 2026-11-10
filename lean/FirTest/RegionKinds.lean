import FirTest.Mixed
import FirTest.Bit

/-!
Region kinds that a dialect registers (#230). A test dialect named `toy`
registers the kind `toy.graph`, whose rule asks that a region hold exactly
one block, and has two ops: `toy.run`, which owns one region of the kind
`toy.graph`, and `toy.free`, which owns one region of the kind `toy.free`,
which no dialect registers.

The tests read texts with the spec's parser and check them with the spec's
validation check, in the sum of the core and the dialect, and in a sum of
three dialects where the dialect is lifted over the bit dialect. A region
goes to the rule of the dialect that registers its kind, through the sum
and the lift. The kind's word joins the module's dialect set. The
interpreter runs `toy.run` by the dialect's semantics and does not enter
its region, and is stuck on an op that owns a region of the core's kind.
-/

namespace FirTest.RegionKinds

/-- An op of the region dialect. -/
inductive Op where
  | run
  | free
  deriving Repr, DecidableEq

end FirTest.RegionKinds

namespace FirTest

open Fir FirRef

/-- The region dialect over the core. -/
abbrev RegionDialect : Dialect := OverCore RegionKinds.Op

/-- The sum of the core and the region dialect. -/
abbrev CoreRegion : Dialect := CoreSum RegionKinds.Op

namespace RegionKinds

instance : DialectSignature RegionDialect where
  sig _ := []
  returnTypes _ := []
  isTerminator _ := false
  succCount _ := 0
  regionKinds
    | .run => ["toy.graph"]
    | .free => ["toy.free"]

/-- The name of an op. -/
def Op.name : Op → String
  | .run => "toy.run"
  | .free => "toy.free"

/-- The op with this name, with no attributes, operands or results. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Empty)) : Option Op :=
  match as, ts, rs with
  | [], [], [] => if n = "toy.run" then some .run else if n = "toy.free" then some .free else none
  | _, _, _ => none

instance : DialectText RegionDialect where
  opName := Op.name
  opAttrs _ := []
  decodeOp := Op.decode
  tyAttr := OverCore.tyAttr
  decodeTy := OverCore.decodeTy

/-- The rule of the kind `toy.graph`: the region holds exactly one block. -/
def GraphValid {host : Dialect} (r : Region host) : Prop := r.blocks.length = 1

instance : DialectValidation RegionDialect where
  validTy := OverCore.ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True
  regionKindNames := ["toy.graph"]
  validRegion _ k _ _ r := k = "toy.graph" ∧ GraphValid r

instance : DecidableDialectValidation RegionDialect where
  decValidTy t := inferInstanceAs (Decidable (OverCore.ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)
  decValidRegion _ k _ _ r := inferInstanceAs (Decidable (k = "toy.graph" ∧ r.blocks.length = 1))

instance : DialectCall RegionDialect := ⟨fun _ => none⟩

/-- The region dialect's semantics: its ops give no results. -/
instance : DialectDenote RegionDialect Mix where
  denote _ _ := pure .nil
  exit op _ := .noOutcome op.name

/-! # Validation in the sum of the core and the dialect -/

/-- The messages of the problems of a text, and of its dialect set, in the
sum of the core and the region dialect, or the parse error's reason. -/
def messages (t : String) : List String :=
  match (Fir.parse t : Except ParseError (Module CoreRegion)) with
  | .ok m => m.allProblems.map (·.message)
  | .error e => ["parse: " ++ e.reason]

/-- A module that names the dialect `toy`, of one function whose entry
block holds `ops`, then `ret`. -/
def text (ops : List String) (set : Bool := true) : String :=
  (if set then "dialects toy\n\n" else "") ++ "func @f() {\n^entry:\n" ++
    String.join (ops.map (· ++ "\n")) ++ "  ret @0\n}\n\nlocs {\n  @0 = unknown\n}\n"

/-- An op that owns one region whose blocks are `blocks`, each one `ret`,
written with the kind word `kind`. -/
def owner (name kind : String) (blocks : List String) : String :=
  "  " ++ name ++ " {" ++ kind ++ "\n" ++
    String.join (blocks.map fun l => "    ^" ++ l ++ ":\n      ret @0\n") ++ "  } @0"

/-- The text parses in the sum and prints as itself. -/
def roundTrips (t : String) : Bool :=
  match (Fir.parse t : Except ParseError (Module CoreRegion)) with
  | .ok m => m.print == t
  | .error _ => false

#guard roundTrips (text [owner "toy.run" " toy.graph" ["g"]])
#guard roundTrips (text [owner "toy.run" " toy.graph" ["g", "h"]])
#guard messages (text [owner "toy.run" " toy.graph" ["g"]]) == []
#guard messages (text [owner "toy.run" "" ["g"]]) ==
  ["the op's regions are not of the kinds that its op instance states"]
#guard messages (text [owner "toy.run" " toy.graph" ["g", "h"]]) ==
  ["a region of the op breaks the rule of its kind toy.graph"]
#guard messages (text [owner "toy.run" " toy.free" ["g"]]) ==
  ["the op's regions are not of the kinds that its op instance states",
   "a region of the op is of kind toy.free, which no dialect registers"]
#guard messages (text [owner "toy.free" " toy.free" ["g"]]) ==
  ["a region of the op is of kind toy.free, which no dialect registers"]

-- An op inside a region obeys the general rules, which the region kind's
-- rule does not see: here a symbol that names no function, and a location
-- reference outside the table.
#guard messages (text ["  toy.run { toy.graph\n    ^g:\n      call @nope @0\n      ret @0\n  } @0"]) ==
  ["the op refers to @nope, which names no function", "the op breaks its dialect's own rule"]
#guard messages (text ["  toy.run { toy.graph\n    ^g:\n      ret @7\n  } @0"])
  == ["location reference @7 is not in the location table"]

-- A region kind's word joins the dialect set: without `dialects toy`, the
-- core's `br` whose only word of `toy` is its region's kind breaks the set.
#guard messages (text ["  br { toy.graph\n    ^g:\n      ret @0\n  } @0"] (set := false)) ==
  ["the op's regions are not of the kinds that its op instance states",
   "the op ends a block, and is not the last op of ^entry",
   "the op has 0 successors, and its op instance has 1",
   "the function writes a word of the dialect toy, which the module's dialect set does not name"]
#guard messages (text [owner "toy.run" " toy.graph" ["g"]] (set := false)) ==
  ["the function writes a word of the dialect toy, which the module's dialect set does not name"]

/-- The region dialect's name is new to the core. -/
theorem region_new : name (Ext Op) ∉ names CoreDialect := by decide

/-- The region dialect writes its ops and its kind under its name. -/
instance : LawfulDialectName CoreDialect (Ext Op) where
  opName_named
    | .run => (by decide : wordDialect "toy.run" = some "toy")
    | .free => (by decide : wordDialect "toy.free" = some "toy")
  opAttrs_mem _ _ h := nomatch h
  tyAttr_named t := t.elim
  tyAttr_mem t := t.elim
  kind_named k hk := by
    simp only [regionKindNames, List.mem_singleton] at hk
    subst hk
    decide

/-- The sum sends a region of the kind `toy.graph` to the dialect's rule. -/
example {host : Dialect} (v : DialectView CoreRegion host) (ctx : FuncContext host)
    (f : Func host) (r : Region host) :
    validRegion v "toy.graph" ctx f r ↔ "toy.graph" = "toy.graph" ∧ GraphValid r :=
  Dialect.sum.validRegion_ext region_new v (List.mem_singleton_self _) ctx f r

/-! # Through a lift, in a sum of three dialects -/

/-- The core's types, included in those of the sum of the core and the bit
dialect. -/
abbrev coreInBit : TyIncl CoreDialect.Ty (CoreDialect ⊞ BitExt).Ty := TyIncl.inl

/-- The region dialect, written over the core, lifted into the sum of the
core and the bit dialect. -/
abbrev RegionOverBit : Dialect := (Ext Op).lift CoreDialect coreInBit

/-- The sum of the core, the bit dialect and the region dialect. -/
abbrev CoreBitRegion : Dialect := CoreDialect ⊞ BitExt ⊞ RegionOverBit

/-- The sum of three registers the region dialect's kind, from the lift. -/
example : regionKindNames (d := CoreBitRegion) = ["toy.graph"] := rfl

/-- The messages of a text's problems in the sum of three dialects. -/
def threeMessages (t : String) : List String :=
  match (Fir.parse t : Except ParseError (Module CoreBitRegion)) with
  | .ok m => m.allProblems.map (·.message)
  | .error e => ["parse: " ++ e.reason]

/-- `text`, with the dialect set `toy, bit`. -/
def threeText (ops : List String) : String :=
  "dialects bit, toy\n\n" ++ (text ops).drop "dialects toy\n\n".length

#guard threeMessages (threeText [owner "toy.run" " toy.graph" ["g"]]) == []
#guard threeMessages (threeText [owner "toy.run" " toy.graph" ["g", "h"]]) ==
  ["a region of the op breaks the rule of its kind toy.graph"]
#guard threeMessages (threeText [owner "toy.run" " bit.graph" ["g"]]) ==
  ["the op's regions are not of the kinds that its op instance states",
   "a region of the op is of kind bit.graph, which no dialect registers"]

/-! # Running

The interpreter runs `toy.run` by the dialect's semantics, and does not
enter its region, whose block would return. An op that owns a region of the
core's kind leaves the run stuck. -/

/-- How the run of the first function of a text ends: `ret` with the number
of values it returns, `stuck` with the reason, or `none` when the text does
not parse or the run makes a choice. -/
def runEnd (t : String) : Option String :=
  match (Fir.parse t : Except ParseError (Module CoreRegion)) with
  | .error _ => none
  | .ok m => m.funcs.head?.bind fun f =>
    match readSumArgs (f.params.map (·.2)) [] with
    | .error _ => none
    | .ok vs =>
      match (f.run m (m := Mix) vs 10).run.script constOf [] 0 with
      | .ok (.ok (.ok (.ret vs)), _) => some s!"ret {vs.length}"
      | .ok (.ok (.ok .fuelExhausted), _) => some "fuel"
      | .ok (.ok (.error e), _) => some ("stuck: " ++ e.reason)
      | _ => none

#guard runEnd (text [owner "toy.run" " toy.graph" ["g"]]) == some "ret 0"
#guard runEnd (text [owner "toy.run" "" ["g"]]) ==
  some "stuck: an op owns a region of the core's kind, and no rule runs one"

end RegionKinds

end FirTest
