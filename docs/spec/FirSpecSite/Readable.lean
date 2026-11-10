import VersoManual

/-!
The readable layer of the spec (ADR-2026-11-05-2012). A section that moves
to it is rendered from two sources: the Lean module in `lean/`, and a Verso
document in `docs/spec/FirSpec/` that holds one readable block per
declaration of the module: prose for a newcomer, with notation in KaTeX.
The module's own prose shows as before. Each declaration's Lean, its doc
comment, its statement and its proof, shows hidden in an HTML `<details>`
right under its readable block, with the code that defines nothing placed
by `leanOwners`.

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
details.fir-lean > summary code { font-size: 1em; overflow-wrap: anywhere; }
details.fir-lean[open] > summary { margin-bottom: 0.5em; }
details.fir-lean[open] {
  border-top: 1px dashed #b8c7d6;
  padding-top: 0.3em;
}
.fir-grammar { overflow-x: auto; margin: 0.8em 0; }
.fir-readable .katex-display { overflow-x: auto; overflow-y: hidden; }
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

/--
The blocks that show one piece of a Lean module's code. A doc comment that
Lean keeps as Markdown, such as the one on a `local macro`, shows as a
docstring too; Markdown that does not load shows as a problem.
-/
def codeBlocks : VersoLiterate.Code → Array (Block Manual)
  | .highlighted hl => #[loadBlock (.other (.highlighted hl) #[])]
  | .verso i declName? doc =>
    #[LoadLiterate.docstring i declName?
      (doc.text.map loadBlock ++ doc.subsections.map (LoadLiterate.part 0 ∘ loadPart))]
  | c@(.markdown ..) =>
    -- Verso loads Markdown only through a whole module, so load a module of this one piece.
    let item : ModuleItem' := { range := none, kind := .anonymous, defines := #[], code := #[c] }
    let one : LitMod := { name := .anonymous, contents := #[item] }
    match VersoLiterate.modToPage (g := Manual) one #[] "" none with
    | .ok doc => doc.toPart.content
    | .error e => #[.other (Block.readableError s!"a Markdown doc comment does not load: {e}") #[]]
  | _ => #[]

/--
The kinds of command that define nothing and set up the code after them:
they open a scope or change what it holds, or, as a `macro`, add a tactic
for the proofs after it. Module docs count too, since they introduce what
follows them.
-/
def leadingKinds : Array SyntaxNodeKind := #[
  `Lean.Parser.Command.moduleDoc, `Lean.Parser.Command.namespace,
  `Lean.Parser.Command.section, `Lean.Parser.Command.variable,
  `Lean.Parser.Command.open, `Lean.Parser.Command.omit,
  `Lean.Parser.Command.include, `Lean.Parser.Command.set_option,
  `Lean.Parser.Command.universe, `Lean.Parser.Command.macro]

/--
For each item of a module, the item that defines something under whose
readable block its Lean is hidden: itself, when it defines something.

An item that defines nothing goes with the declaration before it, as an
anonymous `instance`, an `example`, a `#guard`, an `infix` or an `end`
belongs to what it follows (#181). It goes with the declaration after it
instead when it is of one of the `leadingKinds`, such as `variable` and
`namespace`, when module docs stand between it and the declaration before
it, or when no declaration comes before it. An item that goes back takes
the items waiting before it back too, so each block's Lean keeps the
module's order. Items still waiting after the last declaration go with
it, so no line is left out. Only when the module defines nothing is an
item's owner `none`.
-/
def leanOwners (items : Array ModuleItem') : Array (Option Nat) := Id.run do
  let mut owners := Array.replicate items.size none
  let mut pending : Array Nat := #[]
  -- The declaration before, with no module docs since.
  let mut before : Option Nat := none
  let mut last : Option Nat := none
  for h : i in [0:items.size] do
    let item := items[i]
    let owner :=
      if !item.defines.isEmpty then some i
      else if leadingKinds.contains item.kind then none
      else before
    if item.kind == `Lean.Parser.Command.moduleDoc then before := none
    match owner with
    | none => pending := pending.push i
    | some j =>
      for k in pending.push i do owners := owners.set! k (some j)
      pending := #[]
      unless item.defines.isEmpty do
        before := some i
        last := some i
  for k in pending do owners := owners.set! k last
  return owners

/--
The section of the Lean module `mod`, titled `title`, with each declaration
shown by its readable block from `readable`, and its Lean hidden under it.

The module's own prose shows where it stands in the module. A readable
block stands where the first declaration it explains stands. Its hidden Lean
holds each declaration it explains, with the code around it that defines
nothing, as `leanOwners` places it, so no line of the module is left out.
The blocks of `readable` that are not readable blocks open the section.
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
  -- The hidden Lean of each item that defines something, and of the module when none does.
  let mut leanOf : Array (Array (Block Manual)) := Array.replicate items.size #[]
  let mut unowned : Array (Block Manual) := #[]
  for (item, place) in items.zip (leanOwners items) do
    let code := item.code.flatMap codeBlocks
    match place with
    | some j => leanOf := leanOf.modify j (· ++ code)
    | none => unowned := unowned ++ code
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
      | .markdownModDoc .. =>
        errors := errors.push s!"{mod.name}: Markdown module docs cannot be shown in a readable section"
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
  unless unowned.isEmpty do
    p := pushBlock p (.other (Block.leanDetails #[]) unowned)
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
