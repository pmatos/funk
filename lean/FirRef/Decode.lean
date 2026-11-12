import FirRef.Decode.Tree

/-!
`fir-ref` decodes modules with `FirRef.decodeModule`, not with the spec's
`Text.decodeModule` (ADR-2026-10-30-1450). `decodeFunc` is the spec's
`decodeFunc` with its two passes replaced by the loops `defineFrames` and
`decodeFrames`, which take no stack per level of regions and none per block
or op, and with the copies of `decodeType`, `decodeDef` and `define`
compiled after `print_eq_printAttr`. `decodeFuncItem` is the
spec's, calling `decodeFunc`, and `decodeDialectItem` is the spec's, with
those copies. `decodeLoop` decodes items with an explicit
stack of frames, so it takes no stack per level of nested modules, and
`decodeLoop_eq` proves that it computes what the spec's `decodeItems` does,
errors included. The theorem
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
  pure ⟨name, params, results, ⟨none, ← decodeFrames sc name [.blocks none [] blocks]⟩⟩

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

/-- `Text.decodeDialectItem`, with the copies of `decodeType` and
`decodeDef`. -/
def decodeDialectItem (kind : String) (kindPos : TextPos) (name : String) (params : List SDef)
    (results attrs : List (Attr × TextPos)) : SBody → Except ParseError (Item d)
  | .blocks [] => do
    let results ← results.mapM fun (a, p) => decodeType a p
    let params ← params.mapM decodeDef
    pure (.dialect ⟨kind, name, params, results, attrs.map (·.1)⟩)
  | _ => errorAt kindPos "an item of a dialect's kind has an empty body"

theorem decodeDialectItem_eq : @decodeDialectItem = @Text.decodeDialectItem := by
  funext d _ kind kindPos name params results attrs body
  rcases body with _ | _ | _ <;> rfl

/-- What is left to decode of items, nested modules included. -/
inductive DFrame (d : Dialect) where
  /-- Items: those decoded so far, last first, and those left. -/
  | items (done : List (Item d)) (todo : List SItem)
  /-- The nested module with this symbol and dialect set, whose items are
  those above. -/
  | module (name : Name) (dialects : List Name)

mutual
/-- A measure of an item as written that each step of `decodeLoop` lowers. -/
def sitemWeight : SItem → Nat
  | ⟨_, _, _, _, _, _, body⟩ => sbodyWeight body + 1

/-- A measure of an item's body. -/
def sbodyWeight : SBody → Nat
  | .blocks _ => 0
  | .items _ is => sitemsWeight is + 1

/-- A measure of items as written. -/
def sitemsWeight : List SItem → Nat
  | [] => 0
  | i :: is => sitemWeight i + sitemsWeight is + 1
end

/-- A measure of a frame. -/
def DFrame.weight : DFrame d → Nat
  | .items _ todo => sitemsWeight todo + 1
  | .module .. => 1

/-- A measure of a stack of frames. -/
def dWeight : List (DFrame d) → Nat
  | [] => 0
  | f :: fs => f.weight + dWeight fs

/-- `Text.decodeItems`, with an explicit stack of frames: a nested module
pushes its items, and the frame of the module below them. Every call to
itself is a tail call, so it takes no stack per level of nested modules. -/
def decodeLoop : List (DFrame d) → Except ParseError (List (Item d))
  | .items done [] :: [] => .ok done.reverse
  | .items done [] :: .module name ds :: .items done' todo :: fs =>
    decodeLoop (.items (.module name ds done.reverse :: done') todo :: fs)
  | .items done (⟨kind, kindPos, name, params, results, attrs, body⟩ :: sis) :: fs =>
    if kind = "func" then
      match decodeFuncItem kindPos name params results attrs body with
      | .ok i => decodeLoop (.items (i :: done) sis :: fs)
      | .error e => .error e
    else if kind = "module" then
      match moduleHeader params results attrs with
      | .error e => .error e
      | .ok () =>
        match body with
        | .blocks [] => decodeLoop (.items (.module name [] [] :: done) sis :: fs)
        | .blocks (_ :: _) => errorAt kindPos "a module's body holds items, not blocks"
        | .items ds is => decodeLoop (.items [] is :: .module name ds :: .items done sis :: fs)
    else if isDialectWord kind then
      match decodeDialectItem kind kindPos name params results attrs body with
      | .ok i => decodeLoop (.items (i :: done) sis :: fs)
      | .error e => .error e
    else errorAt kindPos ("unknown item kind " ++ kind ++
      ": the kinds are func, module and the words of dialects")
  | _ => .ok []
termination_by fs => dWeight fs
decreasing_by
  all_goals
    simp only [dWeight, DFrame.weight, sitemsWeight, sitemWeight, sbodyWeight]
    omega

/-- Hands the items `is`, decoded in full, to the frames `fs`, which decode
on by the spec's decoder. -/
def dFinish : List (Item d) → List (DFrame d) → Except ParseError (List (Item d))
  | is, [] => .ok is
  | is, .module name ds :: .items done todo :: fs => do
    let more ← Text.decodeItems todo
    dFinish ((.module name ds is :: done).reverse ++ more) fs
  | _, _ => .ok []

/-- What `decodeLoop` computes from the frames `fs`, by the spec's decoder. -/
def dRun : List (DFrame d) → Except ParseError (List (Item d))
  | .items done todo :: fs => do
    let is ← Text.decodeItems todo
    dFinish (done.reverse ++ is) fs
  | _ => .ok []

theorem decodeItems_nil : Text.decodeItems (d := d) [] = .ok [] := rfl

theorem decodeItems_cons (si : SItem) (sis : List SItem) :
    Text.decodeItems (d := d) (si :: sis) =
      (do let i ← Text.decodeItem si; let is ← Text.decodeItems sis; pure (i :: is)) := by
  rw [Text.decodeItems.eq_def]

theorem decodeItem_mk (kind : String) (kindPos : TextPos) (name : String) (params : List SDef)
    (results attrs : List (Attr × TextPos)) (body : SBody) :
    Text.decodeItem (d := d) ⟨kind, kindPos, name, params, results, attrs, body⟩ =
      if kind = "func" then Text.decodeFuncItem kindPos name params results attrs body
      else if kind = "module" then do
        moduleHeader params results attrs
        match body with
        | .blocks [] => pure (.module name [] [])
        | .blocks (_ :: _) => errorAt kindPos "a module's body holds items, not blocks"
        | .items ds is => do pure (.module name ds (← Text.decodeItems is))
      else if isDialectWord kind then
        Text.decodeDialectItem kind kindPos name params results attrs body
      else errorAt kindPos ("unknown item kind " ++ kind ++
        ": the kinds are func, module and the words of dialects") := by
  rw [Text.decodeItem.eq_def]
  rfl

theorem error_bind' {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (Except.error e >>= k) = Except.error e := rfl

theorem decodeLoop_eq (fs : List (DFrame d)) : decodeLoop fs = dRun fs := by
  fun_induction decodeLoop fs <;>
    simp_all [dRun, dFinish, decodeItems_nil, decodeItems_cons, decodeItem_mk, decodeFuncItem_eq,
      decodeDialectItem_eq, ok_bind, error_bind', errorAt]
  -- The stacks that `decodeLoop` does not take apart give no items on both sides.
  rename_i fs h₁ h₂ h₃
  match fs, h₁, h₂, h₃ with
  | [], _, _, _ => rfl
  | .module .. :: _, _, _, _ => rfl
  | .items _ [] :: [], h, _, _ => exact (h _ rfl).elim
  | .items _ [] :: .items .. :: _, _, _, _ => rfl
  | .items _ [] :: .module .. :: [], _, _, _ => rfl
  | .items _ [] :: .module .. :: .module .. :: _, _, _, _ => rfl
  | .items _ [] :: .module .. :: .items .. :: _, _, h, _ => exact (h _ _ _ _ _ _ rfl).elim
  | .items _ (⟨_, _, _, _, _, _, _⟩ :: _) :: _, _, _, h => exact (h _ _ _ _ _ _ _ _ _ _ rfl).elim

/-- A module decoded: `Text.decodeModule`, with no stack per level of
regions or of nested modules, and none per block or op. -/
def decodeModule (m : SModule) : Except ParseError (Module d) := do
  pure ⟨m.dialects, ← m.layout.mapM Text.decodeMemLayout, ← decodeLoop [.items [] m.items],
    m.locs⟩

/-- `decodeModule` decodes as the spec's decoder does, errors included, so
`fir-ref` runs it in place of `Text.decodeModule`. -/
@[csimp] theorem decodeModule_eq_decodeModule : @Text.decodeModule = @decodeModule := by
  funext d _ m
  simp only [decodeModule, Text.decodeModule, decodeLoop_eq, dRun, dFinish, ← decodeItems_eq_mapM]
  cases m.layout.mapM Text.decodeMemLayout <;> cases decodeItems (d := d) m.items <;> rfl

end FirRef
