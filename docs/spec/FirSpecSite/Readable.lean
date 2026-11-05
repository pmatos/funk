import VersoManual

/-!
The readable layer of the spec (ADR-2026-11-05-2012). A section that moves
to it is rendered from two sources: the Lean module in `lean/`, and a Verso
document in `docs/spec/FirSpec/` that holds one readable block per
declaration of the module: prose for a newcomer, with notation in KaTeX.
The module's own prose shows as before. Each declaration's Lean, its doc
comment, its statement and its proof, shows hidden in an HTML `<details>`
right under its readable block.

This module defines the blocks and puts a section together when the
document is rendered. `FirSpecSite.ReadableElab` checks the readable blocks
against the Lean when the document is elaborated.
-/

open Verso.Genre Manual
open Verso.Doc
open Verso.Output Html
open VersoLiterate
open Lean

namespace FirSpecSite

/-- How a declaration is named to a reader: without the `Fir.` prefix. -/
def shownName (n : Name) : String := (n.replacePrefix `Fir .anonymous).toString

/-- The styles of the readable layer. -/
def readableCss : String := "
.fir-readable {
  border-left: 3px solid #6b8fb3;
  padding: 0.1em 0 0.1em 1em;
  margin: 1.2em 0;
}
.fir-readable > p:first-child { margin-top: 0.3em; }
details.fir-lean { margin: 0.6em 0 0.3em 0; }
details.fir-lean > summary {
  cursor: pointer;
  font-family: var(--verso-structure-font-family);
  color: #4a6380;
  font-size: 0.9em;
  user-select: none;
}
details.fir-lean > summary code { font-size: 1em; }
details.fir-lean[open] > summary { margin-bottom: 0.5em; }
details.fir-lean[open] {
  border-top: 1px dashed #b8c7d6;
  padding-top: 0.3em;
}
.fir-grammar { overflow-x: auto; margin: 0.8em 0; }
"

/- A readable block: prose that explains the Lean declarations `names`. -/
block_extension Block.readable (names : Array Name) where
  data := toJson names
  traverse _ _ _ := pure none
  extraCss := [readableCss]
  toHtml := some fun _goI goB _id _data contents => do
    pure {{<div class="fir-readable">{{← contents.mapM goB}}</div>}}
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB

/- The Lean of the declarations `names`, hidden until the reader opens it. -/
block_extension Block.leanDetails (names : Array Name) where
  data := toJson names
  traverse _ _ _ := pure none
  extraCss := [readableCss]
  toHtml := some fun _goI goB _id data contents => do
    let names : Array Html := match fromJson? (α := Array Name) data with
      | .ok ns => ns.map fun n => {{<code>{{shownName n}}</code>}}
      | .error _ => #[]
    let names := names.toList.intersperse (Html.text true ", ") |>.toArray
    pure {{
      <details class="fir-lean">
        <summary>"Lean: " {{names}}</summary>
        {{← contents.mapM goB}}
      </details>
    }}
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB

/- A grammar box, whose one block is its notation as display math. -/
block_extension Block.grammar where
  traverse _ _ _ := pure none
  extraCss := [readableCss]
  toHtml := some fun _goI goB _id _data contents => do
    pure {{<div class="fir-grammar">{{← contents.mapM goB}}</div>}}
  toTeX := some fun _goI goB _id _data contents => contents.mapM goB

/-
A problem found while a readable section is put together. The checks at
elaboration should make it impossible; if one is missed, rendering the
section fails with `message`.
-/
block_extension Block.readableError (message : String) where
  data := toJson message
  traverse _ _ _ := pure none
  toHtml := some fun _goI _goB _id data _contents => do
    Verso.reportError s!"readable layer: {data.compress}"
    pure .empty
  toTeX := some fun _goI _goB _id data _contents => do
    Verso.reportError s!"readable layer: {data.compress}"
    pure .empty

/-- The names and contents of `b` when it is a readable block. -/
def readableBlock? (b : Block Manual) : Option (Array Name × Array (Block Manual)) :=
  match b with
  | .other ext contents =>
    if ext.name == (Block.readable #[]).name then
      match fromJson? (α := Array Name) ext.data with
      | .ok names => some (names, contents)
      | .error _ => none
    else none
  | _ => none

/-- `bs` with each `concat` replaced by the blocks it holds, as Verso wraps a directive's block. -/
partial def flattenConcat (bs : Array (Block Manual)) : Array (Block Manual) :=
  bs.flatMap fun
    | .concat inner => flattenConcat inner
    | b => #[b]

/-- The blocks that show one piece of a Lean module's code. -/
def codeBlocks : VersoLiterate.Code → Array (Block Manual)
  | .highlighted hl => #[loadBlock (.other (.highlighted hl) #[])]
  | .verso i declName? doc =>
    #[LoadLiterate.docstring i declName?
      (doc.text.map loadBlock ++ doc.subsections.map (LoadLiterate.part 0 ∘ loadPart))]
  | _ => #[]

/--
The section of the Lean module `mod`, titled `title`, with each declaration
shown by its readable block from `readable`, and its Lean hidden under it.

The module's own prose shows where it stands in the module. A readable
block stands where the first declaration it explains stands. Its hidden Lean
holds each declaration it explains, with the code before it that defines
nothing, such as `variable` and `namespace`, so no line of the module is
left out. The blocks of `readable` that are not readable blocks open the
section.
-/
partial def readablePage (mod : LitMod) (title : Array (Inline Manual)) (titleString : String)
    (readable : VersoDoc Manual) : VersoDoc Manual := Id.run do
  let mut entries : Array (Array Name × Array (Block Manual)) := #[]
  let mut intro : Array (Block Manual) := #[]
  for b in flattenConcat readable.toPart.content do
    match readableBlock? b with
    | some e => entries := entries.push e
    | none => intro := intro.push b
  let items := mod.contents
  let owner (item : ModuleItem') : Option Nat :=
    entries.findIdx? fun (names, _) => names.any item.defines.contains
  -- The hidden Lean of each item that defines something.
  let mut leanOf : Array (Array (Block Manual)) := Array.replicate items.size #[]
  let mut pending : Array (Block Manual) := #[]
  let mut lastDef : Option Nat := none
  for h : i in [0:items.size] do
    let item := items[i]
    let code := item.code.flatMap codeBlocks
    if item.defines.isEmpty then
      pending := pending ++ code
    else
      leanOf := leanOf.set! i (pending ++ code)
      pending := #[]
      lastDef := some i
  if let some j := lastDef then
    leanOf := leanOf.modify j (· ++ pending)
    pending := #[]
  let mut errors : Array String := #[]
  let mut stack : Array (Part Manual) := #[]
  let mut p : Part Manual := {title, titleString, metadata := none, content := intro, subParts := #[]}
  let mut emitted := Array.replicate entries.size false
  for h : i in [0:items.size] do
    let item := items[i]
    for c in item.code do
      match c with
      | .modDoc doc =>
        for b in doc.text do
          p := pushBlock p (loadBlock b)
        for (lvl, sec) in doc.sections do
          if lvl > stack.size then
            stack := stack.push p
            p := loadPart sec
          else
            while h : lvl < stack.size do
              let p' := stack.back
              stack := stack.pop
              p := pushPart p' p
            stack := stack.push p
            p := loadPart sec
      | .markdown .. | .markdownModDoc .. =>
        errors := errors.push s!"{mod.name}: Markdown docs cannot be shown in a readable section"
      | _ => pure ()
    unless item.defines.isEmpty do
      match owner item with
      | none => errors := errors.push s!"{mod.name}: no readable block explains {item.defines}"
      | some e =>
        unless emitted[e]! do
          emitted := emitted.set! e true
          let (names, contents) := entries[e]!
          let mut lean := #[]
          for h : k in [0:items.size] do
            if owner items[k] == some e then lean := lean ++ leanOf[k]!
          let details := Block.other (Block.leanDetails names) lean
          p := pushBlock p (.other (Block.readable names) (contents.push details))
  unless pending.isEmpty do
    p := pushBlock p (.other (Block.leanDetails #[]) pending)
  for h : e in [0:entries.size] do
    unless emitted[e]! do
      errors := errors.push s!"{mod.name}: the readable block for {entries[e].1} explains nothing it defines"
  while h : stack.size > 0 do
    let p' := stack.back
    stack := stack.pop
    p := pushPart p' p
  for e in errors do
    p := pushBlock p (.other (Block.readableError e) #[])
  return VersoDoc.mk (fun _ => p) "{}"

/-- `readablePage` on the module whose literate JSON is `json`. -/
def readablePage! (json : String) (title : Array (Inline Manual)) (titleString : String)
    (readable : VersoDoc Manual) : VersoDoc Manual :=
  readablePage (loadJsonString! json s!"JSON for {titleString}") title titleString readable

end FirSpecSite
