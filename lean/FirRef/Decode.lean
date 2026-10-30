import FirRef.Decode.Tree

/-!
`fir-ref` decodes modules with `FirRef.decodeModule`, not with the spec's
`Text.decodeModule` (ADR-2026-10-30-1450). `decodeFunc` is the spec's
`decodeFunc` with its two passes replaced by the loops `defineFrames` and
`decodeFrames`, which take no stack per level of regions and none per block
or op, and with the copies of `decodeType`, `decodeDef` and `define`
compiled after `print_eq_printAttr`. `decodeItem` and `decodeModule` are
the spec's, calling `decodeFunc`. The theorem
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

/-- `Text.decodeItem`, with `decodeFunc`. -/
def decodeItem : SItem → Except ParseError (Item d)
  | ⟨kind, kindPos, name, params, results, attrs, body⟩ =>
    if kind ≠ "func" then errorAt kindPos ("unknown item kind " ++ kind ++ ": M0 has only func")
    else match attrs, body with
      | (_, p) :: _, _ => errorAt p "a func has no attributes"
      | [], .items (⟨_, p, _, _, _, _, _⟩ :: _) => errorAt p "a func's body holds blocks, not items"
      | [], .items [] => do pure (.func (← decodeFunc name params results []))
      | [], .blocks bs => do pure (.func (← decodeFunc name params results bs))

theorem decodeItem_eq : @decodeItem = @Text.decodeItem := by
  funext d _ i
  simp only [decodeItem, Text.decodeItem, decodeFunc_eq]
  rfl

/-- A module decoded: `Text.decodeModule`, with no stack per level of
regions and none per block or op. -/
def decodeModule (m : SModule) : Except ParseError (Module d) := do
  pure ⟨← m.items.mapM decodeItem, m.locs⟩

/-- `decodeModule` decodes as the spec's decoder does, errors included, so
`fir-ref` runs it in place of `Text.decodeModule`. -/
@[csimp] theorem decodeModule_eq_decodeModule : @Text.decodeModule = @decodeModule := by
  funext d _ m
  simp only [decodeModule, Text.decodeModule, decodeItem_eq]

end FirRef
