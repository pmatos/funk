import FirTest.Interpreter
import FirTest.OverCore

/-!
A test dialect with a type of its own, for the spec's sum of dialects
(ADR-2026-11-09-1543). The flag dialect extends the core dialect under the
test dialects' name `toy` (ADR-2026-10-30-1146). Its type `toy.flag` is its
own, and its two ops take and give the core's integers too:
`%f: toy.flag = toy.flag %x` says whether the integer `%x` is not zero, and
`%b: i1 = toy.test %f` reads the flag back as an `i1`.

In the sum of the core and the flag dialect, a type goes to the side its
head word names: `toy.flag` to the flag dialect and `i8` to the core. The
tests show that the sum reads and prints a module that mixes the two
dialects' types, validates it, and rejects a core op at the flag type.
-/

namespace FirTest.Flag

/-- The flag dialect's own types: one, `toy.flag`. -/
inductive Ty where
  | flag
  deriving Repr, DecidableEq

/-- An op of the flag dialect: `make w` makes a flag of an `iN` with
`N = w`, and `test` reads a flag as an `i1`. -/
inductive Op where
  | make (w : Nat)
  | test
  deriving Repr, DecidableEq

end FirTest.Flag

namespace FirTest

open Fir

/-- The flag dialect, before it is put over a base. -/
abbrev FlagExt : Dialect := ⟨Flag.Op, Flag.Ty⟩

instance : DialectName FlagExt := ⟨"toy"⟩

/-- The flag dialect over the core: its ops, at the core's types and its own. -/
abbrev FlagDialect : Dialect := CoreDialect.over FlagExt

/-- The sum of the core dialect and the flag dialect. -/
abbrev CoreFlag : Dialect := CoreDialect ⊞ FlagExt

namespace Flag

instance : DialectSignature FlagDialect where
  sig
    | .make w => [.inl (.int w)]
    | .test => [.inr .flag]
  returnTypes
    | .make _ => [.inr .flag]
    | .test => [.inl (.int 1)]
  isTerminator _ := false
  succCount _ := 0

/-- The name of a flag op. -/
def Op.name : Op → String
  | .make _ => "toy.flag"
  | .test => "toy.test"

/-- The flag op with this name, at these operand and result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List (Core.Ty ⊕ Ty)) : Option Op :=
  match as, ts, rs with
  | [], [.inl (.int w)], [.inr .flag] => if n = "toy.flag" then some (.make w) else none
  | [], [.inr .flag], [.inl (.int 1)] => if n = "toy.test" then some .test else none
  | _, _, _ => none

/-- Writes a type: the core's as the core does, and `toy.flag`. -/
def tyAttr : Core.Ty ⊕ Ty → Attr
  | .inl t => t.attr
  | .inr .flag => .word "toy.flag"

/-- Reads a type: a type of the toy dialect's name is `toy.flag` or none,
and every other type is the core's. -/
def decodeTy (a : Attr) : Option (Core.Ty ⊕ Ty) :=
  if a.dialect? = some "toy" then
    match a with
    | .word "toy.flag" => some (.inr .flag)
    | _ => none
  else (Core.Ty.decode a).map .inl

instance : DialectText FlagDialect where
  opName := Op.name
  opAttrs _ := []
  decodeOp := Op.decode
  tyAttr := tyAttr
  decodeTy := decodeTy

/-- The flag dialect accepts the core's valid types and its own. -/
def ValidTy : Core.Ty ⊕ Ty → Prop
  | .inl t => t.Valid
  | .inr _ => True

instance : DecidablePred ValidTy
  | .inl t => inferInstanceAs (Decidable t.Valid)
  | .inr _ => inferInstanceAs (Decidable True)

instance : DialectValidation FlagDialect where
  validTy := ValidTy
  symbolRefs _ := []
  validOp _ _ := True
  validFunc _ _ _ := True

instance : DecidableDialectValidation FlagDialect where
  decValidTy t := inferInstanceAs (Decidable (ValidTy t))
  decValidOp _ _ := inferInstanceAs (Decidable True)
  decValidFunc _ _ _ := inferInstanceAs (Decidable True)

/-! # The flag dialect's text is lawful -/

/-- A core type names no dialect. -/
theorem core_dialect? (t : Core.Ty) : t.attr.dialect? = none := by
  cases h : t.attr.dialect? with
  | none => rfl
  | some x =>
    have := Attr.dialect?_mem h
    rw [show t.attr = Fir.tyAttr (d := CoreDialect) t from rfl, Core.tyAttr_bare] at this
    cases this

/-- The flag dialect's text meets the seven laws. -/
theorem lawfulDialectText : LawfulDialectText FlagDialect where
  decodeOp_encode
    | .make _ => by simp [opName, opAttrs, decodeOp, Op.name, Op.decode, sig, returnTypes]
    | .test => by simp [opName, opAttrs, decodeOp, Op.name, Op.decode, sig, returnTypes]
  encode_decodeOp n as ts rs o h := by
    change Op.decode n as ts rs = some o at h
    unfold Op.decode at h
    split at h
    · split at h
      · rename_i hn
        cases h
        exact ⟨hn.symm, rfl, rfl, rfl⟩
      · cases h
    · split at h
      · rename_i hn
        cases h
        exact ⟨hn.symm, rfl, rfl, rfl⟩
      · cases h
    · cases h
  decodeTy_encode
    | .inl t, hv => by
      change decodeTy t.attr = _
      simp [decodeTy, core_dialect? t, Core.Ty.decode_attr t hv]
    | .inr .flag, _ => by decide
  encode_decodeTy a t h := by
    change decodeTy a = some t at h
    unfold decodeTy at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp h
      exact Core.Ty.attr_decode ht'
  opName_isWord
    | .make _ => (by decide : isWord "toy.flag")
    | .test => (by decide : isWord "toy.test")
  opAttrs_writable _ := trivial
  tyAttr_isType
    | .inl t, hv => Core.Ty.attr_isType t hv
    | .inr .flag, _ => (by decide : isWord "toy.flag")

instance : LawfulDialectText FlagDialect := lawfulDialectText

/-- The flag dialect writes its ops and its type under the name `toy`. -/
instance : LawfulDialectName CoreDialect FlagExt where
  opName_named
    | .make _ => (by decide : wordDialect "toy.flag" = some "toy")
    | .test => (by decide : wordDialect "toy.test" = some "toy")
  opAttrs_mem _ _ h := nomatch h
  tyAttr_named | .flag, _ => (by decide : wordDialect "toy.flag" = some "toy")
  tyAttr_mem
    | .flag, _, x, h => by
      have : x = "toy" := by simpa [tyAttr, Attr.dialects, DialectText.tyAttr, wordDialect] using h
      subst this
      exact List.mem_singleton_self _

end Flag

/-- The flag dialect's name is new to the core. -/
theorem flag_new : name FlagExt ∉ names CoreDialect := by simp [names, name]

instance : LawfulDialectText CoreFlag := Dialect.sum.lawful (Dialect.sum.routes_of_names flag_new)

/-- Every valid module of the sum is well formed. -/
theorem coreFlag_validIsWellFormed : ValidIsWellFormed (d := CoreFlag) :=
  Dialect.sum.validIsWellFormed flag_new

/-- The round trip of the sum. -/
theorem coreFlag_printThenParse : PrintThenParse (d := CoreFlag) Fir.parse :=
  Dialect.sum.printThenParse flag_new

/-! # Types routed by their head word -/

#guard decodeTy (d := CoreFlag) (.word "toy.flag") == some (.inr .flag)
#guard decodeTy (d := CoreFlag) (.word "i8") == some (.inl (.int 8))
#guard decodeTy (d := CoreFlag) (.word "toy.i8") == none
#guard decodeTy (d := CoreFlag) (.word "flag") == none

/-! # A module with a type of the flag dialect -/

/-- Parses with the sum of the core and the flag dialect. -/
def parseFlag (t : String) : Except ParseError (Module CoreFlag) := Fir.parse t

/-- `@f` makes a flag of `%a` and reads it back, and `@g` takes a flag. -/
def flagText : String :=
  "func @f(%a: i8) -> i1 {\n^entry:\n  %f: toy.flag = toy.flag %a @0\n" ++
  "  %b: i1 = toy.test %f @0\n  ret %b @0\n}\n\n" ++
  "func @g(%f: toy.flag) -> i1 {\n^entry:\n  %b: i1 = toy.test %f @0\n  ret %b @0\n}\n\n" ++
  "locs {\n  @0 = unknown\n}\n"

-- The sum reads the module, prints it as itself, and finds it valid.
#guard match parseFlag flagText with
  | .ok m => m.print == flagText && m.problems.isEmpty
  | .error _ => false
-- The core dialect alone does not read the flag type.
#guard (Fir.parse (d := CoreDialect) flagText).toBool == false
-- A core op does not decode at the flag type: `ret` of a flag is not a
-- core op instance.
#guard (parseFlag (flagText.replace "ret %b @0\n}\n\nfunc" "ret %f @0\n}\n\nfunc"
    |>.replace "func @f(%a: i8) -> i1" "func @f(%a: i8) -> toy.flag")).toBool == false
-- A function that returns a flag holds no valid core op, since the core
-- cannot write its result types: its `add` breaks the core's rule, and its
-- `toy.flag` does not.
#guard match parseFlag ("func @h(%a: i8) -> toy.flag {\n^entry:\n" ++
    "  %s: i8 = add %a, %a @0\n  %f: toy.flag = toy.flag %s @0\n  ret @0\n}\n\n" ++
    "locs {\n  @0 = unknown\n}\n") with
  | .ok m =>
    m.problems.any (fun p => p.op == some 0 && p.message == "the op breaks its dialect's own rule") &&
      !m.problems.any (·.op == some 1)
  | .error _ => false

/-! # Sums of more than two dialects

A sum is a dialect, so a third dialect over it nests: every class of the
spec's sum resolves for `base ⊞ e₁ ⊞ e₂` from the classes of its parts. -/

section
variable (base e₁ e₂ : Dialect)

example [DialectSignature base] [DialectSignature (base.over e₁)]
    [DialectSignature ((base ⊞ e₁).over e₂)] : DialectSignature (base ⊞ e₁ ⊞ e₂) :=
  inferInstance

example [DialectName e₁] [DialectName e₂] [DialectText base] [DialectText (base.over e₁)]
    [DialectText ((base ⊞ e₁).over e₂)] : DialectText (base ⊞ e₁ ⊞ e₂) :=
  inferInstance

example [DialectValidation base] [DialectValidation (base.over e₁)]
    [DialectValidation ((base ⊞ e₁).over e₂)] [DecidableDialectValidation base]
    [DecidableDialectValidation (base.over e₁)]
    [DecidableDialectValidation ((base ⊞ e₁).over e₂)] :
    DecidableDialectValidation (base ⊞ e₁ ⊞ e₂) :=
  inferInstance

example [TyDenote base.Ty] [TyDenote e₁.Ty] [TyDenote e₂.Ty] : TyDenote (base ⊞ e₁ ⊞ e₂).Ty :=
  inferInstance

example [DecidableEq base.Ty] [DecidableEq e₁.Ty] [DecidableEq e₂.Ty] :
    DecidableEq (base ⊞ e₁ ⊞ e₂).Ty :=
  inferInstance

example [DialectSet base] [DialectName e₁] [DialectName e₂] :
    names (base ⊞ e₁ ⊞ e₂) = names base ++ [name e₁] ++ [name e₂] :=
  rfl

end

-- The set of a nested sum lists each added dialect's name, in the order
-- they are added. Both test dialects are named `toy`, so this sum is not
-- lawful: a lawful sum of three dialects needs a dialect over the sum of
-- the other two, which stage 2 of #227 lifts into place.
#guard names (CoreDialect ⊞ Ext Empty ⊞ FlagExt) == [name (Ext Empty), name FlagExt]

end FirTest
