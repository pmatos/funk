import VersoManual
import FirSpecSite.Citation

/-!
The Markdown of an ADR as Verso content. MD4Lean, the Markdown parser that
Verso already uses for docstrings, parses the file as GitHub does, tables and
autolinks included. Headings become parts, so a section of an ADR shows in the table
of contents and has an anchor. Markdown that the document cannot show as
GitHub does, such as raw HTML or an image, fails the build with the file's
name rather than being dropped.
-/

open Verso.Genre Manual

namespace FirSpecSite

/-- An inline of the spec document. -/
abbrev Inl := Verso.Doc.Inline Manual
/-- A block of the spec document. -/
abbrev Blk := Verso.Doc.Block Manual
/-- A part of the spec document. -/
abbrev Prt := Verso.Doc.Part Manual

/-- The repository that the rendered spec links back to. -/
def repositoryUrl : String := "https://github.com/pmatos/funk"

/-- The directory, relative to the repository, that holds the ADRs. -/
def adrDir : String := "docs/adrs"

/-- A link to the page of the ADR with id `id`. -/
def adrRef (id : String) (content : Array Inl) : Inl :=
  .other (Verso.Genre.Manual.Inline.ref ("ADR-" ++ id) (some sectionDomain) none) content

/-- Joins neighbouring text inlines, so that no citation is split across two. -/
def mergeText (xs : Array Inl) : Array Inl :=
  xs.foldl (init := #[]) fun acc x =>
    match acc.back?, x with
    | some (.text a), .text b => acc.pop.push (.text (a ++ b))
    | _, _ => acc.push x

/--
The parser flags: GitHub's dialect, so that what GitHub shows specially, such
as a task list, is either shown or rejected, never shown as plain text.
-/
def markdownFlags : UInt32 := MD4Lean.MD_DIALECT_GITHUB

/-- What a Markdown conversion knows: the ADR's ids by file name. -/
structure MdContext where
  adrIds : Array (String × String)

/-- A conversion collects the repository files that the ADR links to. -/
abbrev MdM := ReaderT MdContext (StateT (Array String) (Except String))

private def entities : List (String × String) :=
  [("&amp;", "&"), ("&lt;", "<"), ("&gt;", ">"), ("&quot;", "\""), ("&apos;", "'"),
   ("&nbsp;", "\u00a0")]

private def hexValue? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def numeric? (base : Nat) (digits : List Char) : Option Nat :=
  if digits.isEmpty then none
  else digits.foldlM (init := 0) fun n c => do
    let d ← hexValue? c
    if d < base then some (n * base + d) else none

/-- The text of an entity such as `&amp;` or `&#x2192;`. -/
def decodeEntity (e : String) : Except String String := do
  if let some (_, s) := entities.find? (·.1 == e) then return s
  let cs := e.toList
  let code? := match cs with
    | '&' :: '#' :: x :: rest => if x == 'x' || x == 'X' then numeric? 16 rest.dropLast else
        numeric? 10 (x :: rest).dropLast
    | _ => none
  match code? with
  | some n =>
    if n.isValidChar then return String.singleton (Char.ofNat n)
    else throw s!"the entity {e} is not a character"
  | none => throw s!"the entity {e} is not supported; write the character itself"

private def attrString (xs : Array MD4Lean.AttrText) : Except String String :=
  xs.foldlM (init := "") fun acc x => match x with
    | .normal s => pure (acc ++ s)
    | .entity e => (acc ++ ·) <$> decodeEntity e
    | .nullchar => throw "a link holds a null character"

/-- The plain text of Markdown inlines, for titles. -/
partial def plainText : MD4Lean.Text → String
  | .normal s | .br s | .softbr s => s
  | .entity e => (decodeEntity e).toOption.getD e
  | .em xs | .strong xs | .u xs | .del xs | .a _ _ _ xs | .wikiLink _ xs | .img _ _ xs =>
    String.join (xs.map plainText).toList
  | .code ss | .latexMath ss | .latexMathDisplay ss => String.join ss.toList
  | .nullchar => ""

private def hasScheme (url : String) : Bool :=
  match url.toList.span (· != ':') with
  | (c :: rest, _ :: _) => c.isAlpha && rest.all fun c => c.isAlphanum || c ∈ ['+', '-', '.']
  | _ => false

/-- The repository path that `path`, relative to the ADR directory, names. -/
def resolveRelative (path : String) : Except String String := do
  let mut parts : Array String := (adrDir.splitOn "/").toArray
  for p in path.splitOn "/" do
    if p == "" || p == "." then continue
    if p == ".." then
      if parts.isEmpty then throw s!"the link {path} leaves the repository"
      parts := parts.pop
    else parts := parts.push p
  return "/".intercalate parts.toList

/--
A link's target on the site. A URL with a scheme stays as it is. A relative
path to an ADR becomes a link to the ADR's page, and any other relative path a
link to the file on GitHub, which must exist.
-/
def linkTarget (url : String) (content : Array Inl) : MdM Inl := do
  if hasScheme url then return .link content url
  if url.startsWith "#" || url.startsWith "/" then
    throw s!"the link {url} is not supported; link a file by its path relative to {adrDir}/"
  let (path, fragment) := match url.splitOn "#" with
    | p :: f :: more => (p, "#" ++ "#".intercalate (f :: more))
    | _ => (url, "")
  let repoPath ← resolveRelative path
  if let some (_, id) := (← read).adrIds.find? fun (name, _) => repoPath == s!"{adrDir}/{name}" then
    unless fragment.isEmpty do
      throw s!"the link {url} points into an ADR; link the ADR as a whole"
    return adrRef id content
  modify (·.push repoPath)
  return .link content s!"{repositoryUrl}/blob/main/{repoPath}{fragment}"

mutual
  /-- Markdown inlines as Verso inlines. -/
  partial def inlines (xs : Array MD4Lean.Text) : MdM (Array Inl) :=
    mergeText <$> xs.foldlM (init := #[]) fun acc x => (acc ++ ·) <$> inline x

  /-- One Markdown inline as Verso inlines. -/
  partial def inline : MD4Lean.Text → MdM (Array Inl)
    | .normal s | .softbr s => pure #[.text s]
    | .br _ => throw "hard line breaks are not supported"
    | .entity e => do pure #[.text (← decodeEntity e)]
    | .em xs => do pure #[.emph (← inlines xs)]
    | .strong xs => do pure #[.bold (← inlines xs)]
    | .code ss => pure #[.code (String.join ss.toList)]
    | .a href _ _ xs => do
      let url ← attrString href
      pure #[← linkTarget url (← inlines xs)]
    | .del _ => throw "strikethrough is not supported"
    | .u _ => throw "underline is not supported"
    | .img .. => throw "images are not supported"
    | .latexMath _ | .latexMathDisplay _ => throw "LaTeX math is not supported"
    | .wikiLink .. => throw "wiki links are not supported"
    | .nullchar => throw "the file holds a null character"
end

/-- A table: a header row, then the body, row by row, as Manual's `table` takes them. -/
def table (head : Array (Array MD4Lean.Text)) (body : Array (Array (Array MD4Lean.Text))) :
    MdM Blk := do
  let columns := head.size
  let cell (xs : Array MD4Lean.Text) : MdM (Verso.Doc.ListItem Blk) := do
    pure ⟨#[.para (← inlines xs)]⟩
  let mut items := #[]
  for xs in head do
    items := items.push (← cell xs)
  for row in body do
    for i in [0:columns] do
      items := items.push (← cell (row[i]?.getD #[]))
  return .other (Verso.Genre.Manual.Block.table columns true none none) #[.ul items]

mutual
  /-- Markdown blocks, none of them a heading, as Verso blocks. -/
  partial def blocks (bs : Array MD4Lean.Block) : MdM (Array Blk) :=
    bs.mapM block

  /-- One Markdown block, not a heading, as a Verso block. -/
  partial def block : MD4Lean.Block → MdM Blk
    | .p xs => .para <$> inlines xs
    | .blockquote bs => .blockquote <$> blocks bs
    | .code _ _ _ ss => pure (.code (String.join ss.toList))
    | .ul _ _ items => .ul <$> items.mapM item
    | .ol _ start _ items => .ol start <$> items.mapM item
    | .table head body => table head body
    | .header .. => throw "a heading inside a list or a quote is not supported"
    | .hr => throw "horizontal rules are not supported"
    | .html _ => throw "raw HTML is not supported"

  /-- A list item. -/
  partial def item (li : MD4Lean.Li MD4Lean.Block) : MdM (Verso.Doc.ListItem Blk) := do
    if li.isTask then throw "task lists are not supported"
    return ⟨← blocks li.contents⟩
end

/-- The metadata of a section of an ADR: unnumbered, since the ADR is. -/
def sectionMetadata : Manual.PartMetadata := { number := false }

/--
The content before the first heading of `bs`, and a part for each heading at
the top: its title, and everything up to the next heading at its level or
above, with deeper headings as its parts.
-/
partial def sections (bs : Array MD4Lean.Block) : MdM (Array Blk × Array Prt) := do
  let isHeading : MD4Lean.Block → Bool := (· matches .header ..)
  let first := (bs.findIdx? isHeading).getD bs.size
  let content ← blocks (bs.extract 0 first)
  let mut parts := #[]
  let mut i := first
  while h : i < bs.size do
    let .header level title := bs[i] | throw "expected a heading"
    let mut j := i + 1
    while h' : j < bs.size do
      if let .header l _ := bs[j] then
        if l ≤ level then break
      j := j + 1
    let (inner, subParts) ← sections (bs.extract (i + 1) j)
    parts := parts.push {
      title := ← inlines title
      titleString := String.join (title.map plainText).toList
      metadata := some sectionMetadata
      content := inner
      subParts
    }
    i := j
  return (content, parts)

end FirSpecSite
