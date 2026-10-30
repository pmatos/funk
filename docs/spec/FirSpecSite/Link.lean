import VersoManual
import FirSpecSite.Markdown

/-!
Every ADR citation in the document's prose becomes a link to the ADR's page:
in `FirSpec.lean`, in the module and declaration docs that
`{includeLiterate}` renders from `lean/`, and in the ADRs. The link is a
Verso cross-reference to the tag of the ADR's page, so Verso computes its
address on every page. Code, existing links and titles are left alone.
-/

open Verso.Genre Manual

namespace FirSpecSite

/-- A linking pass collects one message per citation it cannot link. -/
abbrev LinkM := StateM (Array String)

private def refName : Lean.Name := (Verso.Genre.Manual.Inline.ref "" none none).name

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
    | .other c xs => do
      if c.name == refName then return #[.other c xs]
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

/--
Links the citations in a part and its parts. `path` holds the titles of the
parts around it, for messages.
-/
partial def linkPart (known : String → Bool) (path : Array String) (p : Prt) : LinkM Prt := do
  let path := path.push p.titleString
  let place := s!"in “{" › ".intercalate path.toList}”"
  return {
    p with
    content := ← p.content.mapM (linkBlock known place)
    subParts := ← p.subParts.mapM (linkPart known path)
  }

/-- `doc` with every citation linked, or one message per citation that names no ADR. -/
def linkCitations (ids : Array String) (doc : Prt) : Except (Array String) Prt :=
  let (doc, errors) := (linkPart (ids.contains ·) #[] doc).run #[]
  if errors.isEmpty then .ok doc else .error errors

end FirSpecSite
