import VersoManual
import FirSpecSite.Adr

/-!
Every ADR citation in the document's prose becomes a link to the ADR's page:
in `FirSpec.lean`, in the module and declaration docs that
`{includeLiterate}` renders from `lean/`, and in the ADRs. The link is a
Verso cross-reference to the tag of the ADR's page, so Verso computes its
address on every page. Code is left alone. A citation that cannot become a
link to its ADR fails the build: one in a heading, which the table of
contents shows inside a link, and one in the text of a link to anything but
that ADR.
-/

open Verso.Genre Manual

namespace FirSpecSite

/-- A linking pass collects one message per citation it cannot link. -/
abbrev LinkM := StateM (Array String)

private def refName : Lean.Name := (Verso.Genre.Manual.Inline.ref "" none none).name

/-- The text of inlines, without their code, which quotes rather than cites. -/
partial def inlineText (xs : Array Inl) : String :=
  String.join <| xs.toList.map fun
    | .text s => s
    | .emph ys | .bold ys | .concat ys | .link ys _ | .footnote _ ys | .other _ ys => inlineText ys
    | _ => ""

/-- One message per citation in `xs`, which is the text of a link to `target`, that is not `allowed`. -/
def citedInLink (place target : String) (allowed : Option String) (xs : Array Inl) : LinkM Unit :=
  for c in citations (inlineText xs) do
    unless allowed == some c.text do
      modify (·.push s!"{place}: {c.text} is the text of a link to {target}; cite the ADR as plain text outside the link")

/--
`s` with each citation of a known ADR replaced by a link to its page. `place`
says where `s` is, for the message about a citation that names no ADR.
-/
def linkText (known : String → Bool) (place : String) (s : String) : LinkM (Array Inl) :=
  (segments s).foldlM (init := #[]) fun acc seg => match seg with
    | .text t => pure (acc.push (.text t))
    | .cite c => do
      if !c.wellFormed then
        modify (·.push s!"{place}: {c.text} is not an ADR id, which ends in HHMM or HHMMSS")
      else if !known c.id then
        modify (·.push s!"{place}: {c.text} names no ADR in {adrDir}/")
      else
        return acc.push (adrRef c.id #[.text c.text])
      return acc.push (.text c.text)

mutual
  /-- Links the citations in inlines. -/
  partial def linkInlines (known : String → Bool) (place : String) (xs : Array Inl) :
      LinkM (Array Inl) :=
    (mergeText xs).foldlM (init := #[]) fun acc x => (acc ++ ·) <$> linkInline known place x

  /-- Links the citations in one inline. -/
  partial def linkInline (known : String → Bool) (place : String) : Inl → LinkM (Array Inl)
    | .text s => linkText known place s
    | .emph xs => do pure #[.emph (← linkInlines known place xs)]
    | .bold xs => do pure #[.bold (← linkInlines known place xs)]
    | .concat xs => do pure #[.concat (← linkInlines known place xs)]
    | .footnote n xs => do pure #[.footnote n (← linkInlines known place xs)]
    | .link xs url => do
      citedInLink place url none xs
      pure #[.link xs url]
    | .other c xs => do
      if c.name == refName then
        let target := (c.data.getObjValAs? String "canonicalName").toOption.getD "a section"
        citedInLink place target (some target) xs
        return #[.other c xs]
      pure #[.other c (← linkInlines known place xs)]
    | x => pure #[x]
end

/-- Links the citations in a block, and in the blocks inside it. -/
partial def linkBlock (known : String → Bool) (place : String) : Blk → LinkM Blk
  | .para xs => .para <$> linkInlines known place xs
  | .ul items => .ul <$> items.mapM fun ⟨bs⟩ => (⟨·⟩) <$> bs.mapM (linkBlock known place)
  | .ol n items => .ol n <$> items.mapM fun ⟨bs⟩ => (⟨·⟩) <$> bs.mapM (linkBlock known place)
  | .dl items => .dl <$> items.mapM fun ⟨term, desc⟩ =>
      (⟨·, ·⟩) <$> linkInlines known place term <*> desc.mapM (linkBlock known place)
  | .blockquote bs => .blockquote <$> bs.mapM (linkBlock known place)
  | .concat bs => .concat <$> bs.mapM (linkBlock known place)
  | .other c bs => .other c <$> bs.mapM (linkBlock known place)
  | b => pure b

/-- Where a part is, for messages: the ADR file it is in, if any, and the titles down to it. -/
structure Place where
  file : Option String := none
  titles : Array String := #[]

/-- The place as a message names it. -/
def Place.describe (p : Place) : String :=
  let titles := s!"in “{" › ".intercalate p.titles.toList}”"
  match p.file with
  | some f => if p.titles.isEmpty then f else s!"{f}, {titles}"
  | none => titles

/--
Links the citations in a part and its parts. `fileOf` gives the file of the
ADR whose page has a tag. An ADR's page restarts the place at its file.
-/
partial def linkPart (known : String → Bool) (fileOf : String → Option String) (outer : Place)
    (p : Prt) : LinkM Prt := do
  let tag := p.metadata.bind (·.tag)
  let here : Place := match tag.bind fileOf with
    | some f => { file := some f }
    | none => { outer with titles := outer.titles.push p.titleString }
  let place := here.describe
  for c in citations (inlineText p.title) do
    unless tag == some c.text do
      modify (·.push s!"{place}: {c.text} is in a heading, where it cannot be a link; cite it in the text below")
  return {
    p with
    content := ← p.content.mapM (linkBlock known place)
    subParts := ← p.subParts.mapM (linkPart known fileOf here)
  }

/-- `doc` with every citation linked, or one message per citation that cannot be linked. -/
def linkCitations (adrs : Array Adr) (doc : Prt) : Except (Array String) Prt :=
  let known (id : String) := adrs.any (·.id == id)
  let fileOf (tag : String) := (adrs.find? (s!"ADR-{·.id}" == tag)).map (·.file)
  let (doc, errors) := (linkPart known fileOf {} doc).run #[]
  if errors.isEmpty then .ok doc else .error errors

end FirSpecSite
