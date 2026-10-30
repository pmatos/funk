import VersoManual
import FirSpecSite.Markdown

/-!
The appendix of ADRs. Each file in `docs/adrs/` but its `README.md` becomes
one page of the appendix, and the appendix opens with an index of them all.
The files are read when the document is rendered, so the appendix always
matches the commit it is built from.
-/

open Verso.Genre Manual

namespace FirSpecSite

/-- The tag of the appendix part in `FirSpec.lean`. -/
def appendixTag : String := "adrs"

/-- One ADR, ready to render. -/
structure Adr where
  /-- The id, such as `2026-10-29-2015`. -/
  id : String
  /-- The file, relative to the repository. -/
  file : String
  /-- The decision: the ADR's title. -/
  title : Array Inl
  /-- What follows `Status:`. -/
  status : Array Inl
  /-- The ADR's page. -/
  part : Prt

/-- The metadata of an ADR's page, whose tag is the ADR's citation. -/
def adrMetadata (id : String) : Manual.PartMetadata where
  tag := some s!"ADR-{id}"
  file := some s!"ADR-{id}"
  shortTitle := some s!"ADR-{id}"
  number := false
  htmlSplit := .never

private def stripStatus : Array Inl → Option (Array Inl)
  | xs => do
    let .text s := (← xs[0]?) | none
    guard (s.startsWith "Status:")
    let rest := (s.drop "Status:".length).trimAsciiStart.copy
    return (if rest.isEmpty then #[] else #[.text rest]) ++ xs.extract 1 xs.size

/--
The ADR in `text`, the contents of `file`. Its first block is the title, a
level-1 heading, and its second the `Status:` line. Returns the ADR and the
repository files it links to.
-/
def parseAdr (ctx : MdContext) (id file text : String) : Except String (Adr × Array String) := do
  let some doc := MD4Lean.parse text markdownFlags
    | throw "MD4Lean could not parse it"
  let some (MD4Lean.Block.header 1 titleText) := doc.blocks[0]?
    | throw "it does not start with a level-1 heading, the decision"
  let (title, _) ← (inlines titleText).run ctx |>.run #[]
  let ((content, subParts), links) ← (sections (doc.blocks.extract 1 doc.blocks.size)).run ctx |>.run #[]
  let some status := match content[0]? with
      | some (.para xs) => stripStatus xs
      | _ => none
    | throw "the line after the title is not `Status: …`"
  let titleString := String.join (titleText.map plainText).toList
  let part : Prt := {
    title := #[.text s!"ADR-{id}: "] ++ title
    titleString := s!"ADR-{id}: {titleString}"
    metadata := some (adrMetadata id)
    content
    subParts
  }
  return ({ id, file, title, status, part }, links)

/--
Reads every ADR in `docs/adrs/` of the repository at `root`, in the order of
their names, which is the order of their ids. Returns the ADRs, or one message
per problem.
-/
def loadAdrs (root : System.FilePath) : IO (Except (Array String) (Array Adr)) := do
  let entries ← (root / adrDir).readDir
  let names := entries.map (·.fileName) |>.filter (fun n => n.endsWith ".md" && n != "README.md")
  let names := names.qsort (· < ·)
  let mut errors := #[]
  let mut ids : Array (String × String) := #[]
  for name in names do
    match adrIdOfFileName? name with
    | some id =>
      if let some (other, _) := ids.find? (·.2 == id) then
        errors := errors.push s!"{adrDir}/{name}: has the id of {adrDir}/{other}"
      ids := ids.push (name, id)
    | none => errors := errors.push s!"{adrDir}/{name}: is not named like an ADR (docs/adrs/README.md)"
  let ctx : MdContext := { adrIds := ids }
  let mut adrs := #[]
  for (name, id) in ids do
    let file := s!"{adrDir}/{name}"
    match parseAdr ctx id file (← IO.FS.readFile (root / file)) with
    | .error e => errors := errors.push s!"{file}: {e}"
    | .ok (adr, links) =>
      for target in links do
        unless ← (root / target).pathExists do
          errors := errors.push s!"{file}: links to {target}, which does not exist"
      adrs := adrs.push adr
  return if errors.isEmpty then .ok adrs else .error errors

/-- The index of the appendix: one row per ADR with its id, decision and status. -/
def adrIndex (adrs : Array Adr) : Blk := Id.run do
  let cell (xs : Array Inl) : Verso.Doc.ListItem Blk := ⟨#[.para xs]⟩
  let mut items := #[cell #[.text "ADR"], cell #[.text "Decision"], cell #[.text "Status"]]
  for adr in adrs do
    items := items ++ #[cell #[.text s!"ADR-{adr.id}"], cell adr.title, cell adr.status]
  return .other (Verso.Genre.Manual.Block.table 3 true none none) #[.ul items]

/--
Fills the appendix part of `doc`, the top-level part tagged `adrs`: its index
after its prose, and one part per ADR.
-/
def addAppendix (doc : Prt) (adrs : Array Adr) : Except String Prt := do
  let isAppendix (p : Prt) := p.metadata.bind (·.tag) == some appendixTag
  let some i := doc.subParts.findIdx? isAppendix
    | throw s!"the document has no top-level part tagged {appendixTag}"
  let appendix := doc.subParts[i]!
  unless appendix.subParts.isEmpty do
    throw s!"the part tagged {appendixTag} has parts of its own; the ADRs fill it"
  let appendix := {
    appendix with
    content := appendix.content.push (adrIndex adrs)
    subParts := adrs.map (·.part)
  }
  return { doc with subParts := doc.subParts.set! i appendix }

end FirSpecSite
