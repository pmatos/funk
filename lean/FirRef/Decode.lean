import FirRef.Decode.Tree

/-!
`fir-ref` decodes modules with `FirRef.decodeModule`, not with the spec's
`Text.decodeModule` (ADR-2026-10-30-1450). `decodeFunc` is the spec's
`decodeFunc` with its two passes replaced by the loops `defineFrames` and
`decodeFrames`, which take no stack per level of regions and none per block
or op, and with the copies of `decodeType`, `decodeDef` and `define`
compiled after `print_eq_printAttr`. `decodeFuncItem`, `decodeItem`,
`decodeItems` and `decodeModule` are the spec's, calling `decodeFunc`; they
recurse once per level of nested modules. The theorem
`decodeModule_eq_decodeModule` proves `decodeModule` equal to the spec's,
and `@[csimp]` makes Lean compile every later call of `Text.decodeModule` as
a call of `decodeModule`.

The spec's `Fir.parse` is compiled before this theorem, so it still calls
the spec's decoder; `FirRef.Parse` replaces it.
-/

namespace FirRef

open Fir Fir.Text

variable {d : Dialect} [DialectText d]

/-- `Text.decodeFunc`, with the loops `defineFrames` and `decodeFrames`. -/
def decodeFunc (name : String) (params : List SDef) (results : List (Attr × TextPos))
    (blocks : List SBlock) : Except ParseError (Func d) := do
  let results ← results.mapM fun (a, p) => decodeType a p
  let sc ← define ∅ params
  let sc ← defineFrames sc [.blocks blocks]
  let params ← params.mapM decodeDef
  pure ⟨name, params, results, ⟨← decodeFrames sc name [.blocks [] blocks]⟩⟩

theorem decodeFunc_eq : @decodeFunc = @Text.decodeFunc := by
  funext d _ name params results blocks
  simp only [decodeFunc, Text.decodeFunc, defineFrames_blocks, decodeFrames_blocks, define_eq]
  rfl

/-- `Text.decodeFuncItem`, with `decodeFunc`. -/
def decodeFuncItem (kindPos : TextPos) (name : String) (params : List SDef)
    (results : List (Attr × TextPos)) : List (Attr × TextPos) → SBody → Except ParseError (Item d)
  | (_, p) :: _, _ => errorAt p "a func has no attributes"
  | [], .items (_ :: _) _ => errorAt kindPos "a func's body holds blocks, not a dialect set"
  | [], .items [] (⟨_, p, _, _, _, _, _⟩ :: _) => errorAt p "a func's body holds blocks, not items"
  | [], .items [] [] => do pure (.func (← decodeFunc name params results []))
  | [], .blocks bs => do pure (.func (← decodeFunc name params results bs))

theorem decodeFuncItem_eq : @decodeFuncItem = @Text.decodeFuncItem := by
  funext d _ kindPos name params results attrs body
  simp only [decodeFuncItem, Text.decodeFuncItem, decodeFunc_eq]
  rfl

mutual
/-- `Text.decodeItem`, with `decodeFuncItem`. It takes stack per level of
nested modules. -/
def decodeItem : SItem → Except ParseError (Item d)
  | ⟨kind, kindPos, name, params, results, attrs, body⟩ =>
    if kind = "func" then decodeFuncItem kindPos name params results attrs body
    else if kind = "module" then do
      moduleHeader params results attrs
      match body with
      | .blocks [] => pure (.module name [] [])
      | .blocks (_ :: _) => errorAt kindPos "a module's body holds items, not blocks"
      | .items ds is => do pure (.module name ds (← decodeItems is))
    else errorAt kindPos ("unknown item kind " ++ kind ++ ": the kinds are func and module")

/-- `Text.decodeItems`, with `decodeItem`. -/
def decodeItems : List SItem → Except ParseError (List (Item d))
  | [] => pure []
  | i :: is => do
    let i ← decodeItem i
    pure (i :: (← decodeItems is))
end

mutual
theorem decodeItem_eq : ∀ si : SItem, decodeItem (d := d) si = Text.decodeItem si
  | ⟨kind, kindPos, name, params, results, attrs, .items ds is⟩ => by
    rw [decodeItem.eq_def, Text.decodeItem.eq_def]
    simp only [decodeFuncItem_eq, decodeItems_eq is]
  | ⟨kind, kindPos, name, params, results, attrs, .blocks bs⟩ => by
    rw [decodeItem.eq_def, Text.decodeItem.eq_def]
    simp only [decodeFuncItem_eq]
    cases bs <;> rfl

theorem decodeItems_eq : ∀ sis : List SItem, decodeItems (d := d) sis = Text.decodeItems sis
  | [] => rfl
  | si :: sis => by
    rw [decodeItems.eq_def, Text.decodeItems.eq_def]
    simp only [decodeItem_eq si, decodeItems_eq sis]
end

/-- A module decoded: `Text.decodeModule`, with no stack per level of
regions and none per block or op. -/
def decodeModule (m : SModule) : Except ParseError (Module d) := do
  pure ⟨m.dialects, ← decodeItems m.items, m.locs⟩

/-- `decodeModule` decodes as the spec's decoder does, errors included, so
`fir-ref` runs it in place of `Text.decodeModule`. -/
@[csimp] theorem decodeModule_eq_decodeModule : @Text.decodeModule = @decodeModule := by
  funext d _ m
  simp only [decodeModule, Text.decodeModule, decodeItems_eq, decodeItems_eq_mapM]

end FirRef
