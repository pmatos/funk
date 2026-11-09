import VersoManual
import FirSpecSite.Readable
import FirSpecSite.Fingerprint
import FirSpecSite.Grammar

/-!
What keeps the readable layer from drifting from the Lean
(ADR-2026-11-05-2012). Each check fails the elaboration of the document,
and so the spec build, naming the place and what to do:

* `:::readable N₁ … Nₖ (pin := P₁) … (fingerprint := "…")` explains the
  declarations `N₁ … Nₖ` of one module of `fir`. Each must exist, and the
  fingerprint of what they say must be the one the block pins: a change to
  a statement, a definition or a constructor fails the build until the
  block is read again and its pin updated. The fingerprint covers only
  each declaration's own terms, so a block whose prose restates a
  definition that they merely refer to, from any module, adds it with
  `(pin := P)`; its body then counts too.
* A ```` ```grammar T ```` box inside a readable block shows the
  constructors of the inductive type `T`, or the fields of the structure
  `T`, which the block must explain. The boxes of a block together show
  each constructor exactly once.
* `{includeReadable "." M "Title" D (level := n)}` renders the module `M`
  as a section, with the readable blocks of the document module `D`. Every
  declaration of `M` must be explained by exactly one of them.
* `:::moduleDocs (fingerprint := "…")` in the document module `D` pins the
  fingerprint of all the declarations of `M`, for the `/-! -/` docs of `M`,
  which render on the same page (ADR-2026-11-09-1345). A change to what the
  module says fails the build until they are read again and the pin updated.
-/

open Lean Elab Term
open Verso ArgParse Doc Elab
open Verso.Doc.Concrete Verso.Parser
open Verso.Genre Manual
open Lean.Doc.Syntax
open PartElabM

namespace FirSpecSite

/--
The readable blocks of every document module: the document module, the
module of `fir` its declarations are from, and the declarations.
-/
initialize readableExt :
    SimplePersistentEnvExtension (Name × Name × Array Name) (Array (Name × Name × Array Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/--
The constructors that the grammar boxes of the readable block being
elaborated show, by type. None outside a readable block.
-/
initialize grammarExt : EnvExtension (Option (Array (Name × Array String))) ←
  registerEnvExtension (pure none)

/-- The pins of module docs, by document module. -/
initialize moduleDocsExt :
    SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

/-- The module that declares `n`, if it is imported. -/
def moduleOf? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

/-- The constructors of the inductive type `t`, or the fields of the structure `t`, by short name. -/
def alternatives (env : Environment) (t : Name) : Option (Array String) :=
  if isStructure env t then
    some <| (getStructureFields env t).map (·.toString)
  else match env.find? t with
    | some (.inductInfo v) => some <| v.ctors.toArray.map fun c => (c.replacePrefix t .anonymous).toString
    | _ => none

structure ReadableConfig where
  names : List (ArgParse.WithSyntax Name)
  pins : List (ArgParse.WithSyntax Name)
  fingerprint : ArgParse.WithSyntax String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

instance : FromArgs ReadableConfig m where
  fromArgs := ReadableConfig.mk <$> .many (.positional `name (ValDesc.name.withSyntax))
    <*> .many (.named `pin (ValDesc.name.withSyntax) false)
    <*> .named `fingerprint (ValDesc.string.withSyntax) false

structure ModuleDocsConfig where
  fingerprint : String

instance : FromArgs ModuleDocsConfig m where
  fromArgs := ModuleDocsConfig.mk <$> .named `fingerprint ValDesc.string false

structure GrammarConfig where
  type : ArgParse.WithSyntax Name

instance : FromArgs GrammarConfig m where
  fromArgs := GrammarConfig.mk <$> .positional `type (ValDesc.name.withSyntax)

end

/--
The signatures of `names`, to show in a message: for an inductive type,
also each constructor's, and for a structure, each field default.
-/
def signatures (names : Array Name) : MetaM MessageData := do
  let env ← getEnv
  let mut out := m!""
  for n in names do
    out := out ++ m!"\n  {(← PrettyPrinter.ppSignature n).fmt}"
    if let some (.inductInfo v) := env.find? n then
      for c in v.ctors do
        out := out ++ m!"\n    | {(← PrettyPrinter.ppSignature c).fmt}"
    if isStructure env n then
      for f in getStructureFields env n do
        if let some (.defnInfo d) := env.find? (n ++ f ++ `_default) then
          out := out ++ m!"\n    {f} := {← Meta.ppExpr d.value}"
  return out

/-- Checks that the grammar boxes `boxes` of a readable block for `names` show each constructor once. -/
def checkGrammars (names : Array Name) (boxes : Array (Name × Array String)) : DocElabM Unit := do
  let env ← getEnv
  let types := boxes.foldl (fun ts (t, _) => if ts.contains t then ts else ts.push t) #[]
  for t in types do
    unless names.contains t do
      throwError "a grammar box shows {t}, which this readable block does not name, so its fingerprint would not cover it"
    let some alts := alternatives env t
      | throwError "a grammar box shows {t}, which is not an inductive type or a structure"
    let shown := boxes.filter (·.1 == t) |>.flatMap (·.2)
    for tag in shown do
      unless alts.contains tag do
        throwError "a grammar box of {t} shows '{tag}', which is not one of its constructors or fields: {alts.toList}"
      if (shown.filter (· == tag)).size > 1 then
        throwError "the grammar boxes of {t} show '{tag}' more than once"
    let missing := alts.filter (!shown.contains ·)
    unless missing.isEmpty do
      throwError "the grammar boxes of {t} do not show {missing.toList}; each constructor needs an alternative"

/--
A readable block: prose for a newcomer that explains the Lean declarations
it names, pinned to their fingerprint.
-/
@[directive]
def readable : DirectiveExpanderOf ReadableConfig
  | config, contents => do
    let env ← getEnv
    let names := config.names.toArray.map (·.val)
    if names.isEmpty then
      throwError "a readable block names the Lean declarations it explains"
    let mut mod? : Option Name := none
    for n in config.names do
      unless env.contains n.val do
        throwErrorAt n.syntax "{n.val} is not a Lean declaration: it may have been renamed or removed in lean/. Read the block again against the Lean and name each declaration in full, such as Fir.HasPath.bind"
      let m := moduleOf? env n.val
      if mod?.isSome && m != mod? then
        throwErrorAt n.syntax "{n.val} is from {m}, but the block's first declaration is from {mod?}; a readable block explains declarations of one module"
      mod? := m
    let some mod := mod?
      | throwError "{names} are not from an imported module of fir"
    let pins := config.pins.toArray.map (·.val)
    for p in config.pins do
      unless env.contains p.val do
        throwErrorAt p.syntax "{p.val} is not a Lean declaration: it may have been renamed or removed in lean/. Read the block again against the Lean and pin each definition in full, such as Fir.HasPath"
      if names.contains p.val || (pins.filter (· == p.val)).size > 1 then
        throwErrorAt p.syntax "{p.val} is already covered by this block; name or pin each declaration once"
    let now := match fingerprint env (names ++ pins) with
      | .ok f => f
      | .error _ => ""
    -- Logged, not thrown, so that a grammar box that misses a new constructor is reported in the same build.
    unless config.fingerprint.val == now do
      logErrorAt config.fingerprint.syntax m!"the Lean that this readable block explains has changed: its fingerprint is now \"{now}\", and the block was checked against \"{config.fingerprint.val}\". Read the block again against the Lean, correct it, then set (fingerprint := \"{now}\").{← signatures (names ++ pins)}"
    modifyEnv (grammarExt.setState · (some #[]))
    let (blocks, boxes) ← try
        let blocks ← contents.mapM elabBlock
        pure (blocks, (grammarExt.getState (← getEnv)).getD #[])
      finally
        modifyEnv (grammarExt.setState · none)
    checkGrammars names boxes
    modifyEnv (readableExt.addEntry · (← getMainModule, mod, names))
    ``(Verso.Doc.Block.other (FirSpecSite.Block.readable $(quote names)) #[$blocks,*])

/--
The pin of the module docs of the Lean module that this document explains.
It shows nothing, and the check is made when the section is included.
-/
@[directive]
def moduleDocs : DirectiveExpanderOf ModuleDocsConfig
  | config, contents => do
    unless contents.isEmpty do
      throwError "a moduleDocs pin holds no text; the module docs are in the Lean module"
    modifyEnv (moduleDocsExt.addEntry · (← getMainModule, config.fingerprint))
    ``(Verso.Doc.Block.concat #[])

/-- A grammar box, in the notation of `FirSpecSite.Grammar`, inside a readable block. -/
@[code_block]
def grammar : CodeBlockExpanderOf GrammarConfig
  | config, str => do
    let some boxes := grammarExt.getState (← getEnv)
      | throwError "a grammar box belongs inside the readable block that explains {config.type.val}"
    let g ← match parseGrammar str.getString with
      | .ok g => pure g
      | .error e => throwErrorAt str e
    modifyEnv (grammarExt.setState · (some (boxes.push (config.type.val, g.lines.flatMap (·.tags)))))
    ``(Verso.Doc.Block.other FirSpecSite.Block.grammar
        #[Verso.Doc.Block.para #[Verso.Doc.Inline.math Lean.Doc.MathMode.display $(quote g.toLatex)]])

/--
Checks that the readable blocks of the document module `doc` explain every
declaration of the Lean module `lit`, each once.
-/
def checkCoverage (lit : VersoLiterate.LitMod) (doc : Name) : TermElabM Unit := do
  let entries := (readableExt.getState (← getEnv)).filter (·.1 == doc)
  if entries.isEmpty then
    throwError "{doc} has no readable blocks; is it imported?"
  for (_, mod, names) in entries do
    unless mod == lit.name do
      throwError "{doc} has a readable block for {names}, from {mod}, not from {lit.name}"
  let items := lit.contents.filter (!·.defines.isEmpty)
  let principal (defines : Array Name) : Name :=
    defines.foldl (fun a b => if b.toString.length < a.toString.length then b else a) defines[0]!
  let mut missing := #[]
  for item in items do
    let owners := entries.filter fun (_, _, names) => names.any item.defines.contains
    if owners.isEmpty then missing := missing.push (principal item.defines)
    if owners.size > 1 then
      throwError "{principal item.defines} is explained by more than one readable block of {doc}"
  unless missing.isEmpty do
    throwError "{lit.name}: no readable block of {doc} explains {missing.toList}. Add a readable block for each, or name it in one that explains it with its neighbours."
  for (_, _, names) in entries do
    for n in names do
      unless items.any (·.defines.contains n) do
        throwError "{doc} explains {n}, which {lit.name} does not show as a declaration"

/-- Whether the Lean module `lit` has `/-! -/` docs. -/
def hasModuleDocs (lit : VersoLiterate.LitMod) : Bool :=
  lit.contents.any fun item => item.code.any fun
    | .modDoc _ | .markdownModDoc _ => true
    | _ => false

/--
Checks the pin in the document module `doc` of the module docs of `lit`
against all the declarations that the readable blocks of `doc` explain.
Logged, not thrown, so that one build reports every stale pin.
-/
def checkModuleDocs (lit : VersoLiterate.LitMod) (doc : Name) : TermElabM Unit := do
  let env ← getEnv
  let pins := (moduleDocsExt.getState env).filter (·.1 == doc) |>.map (·.2)
  if pins.size > 1 then
    logError m!"{doc} pins the module docs of {lit.name} more than once"
    return
  unless hasModuleDocs lit do
    unless pins.isEmpty do
      logError m!"{doc} pins the module docs of {lit.name}, which has none; remove its moduleDocs directive"
    return
  let names := (readableExt.getState env).filter (·.1 == doc) |>.flatMap (·.2.2)
  let now ← match moduleFingerprint env names with
    | .ok f => pure f
    | .error n => throwError "{n} is not a Lean declaration"
  match pins[0]? with
  | none =>
    logError m!"{lit.name}: {doc} does not pin its module docs. Read the /-! -/ docs of the module against the Lean, correct them, then add to {doc} the directive :::moduleDocs (fingerprint := \"{now}\")"
  | some pin =>
    unless pin == now do
      logError m!"{lit.name}: the Lean under its module docs has changed: {doc} pins \"{pin}\", and the fingerprint is now \"{now}\". Read the /-! -/ docs of the module again against the Lean, correct them, then set (fingerprint := \"{now}\") in the moduleDocs directive of {doc}."

/-- The `VersoDoc` of the Lean module `mod` as a readable section, with the blocks of `doc`. -/
def readableModule (path : StrLit) (mod : Ident) (title : StrLit) (doc : Ident) : TermElabM Name := do
  let titleParts ← stringToInlines title
  let titleString := inlinesToString (← getEnv) titleParts
  let titleSyntax := .node .none nullKind titleParts
  let initState : PartElabM.State := .init titleSyntax titleSyntax
  let g ← elabTerm (mkIdent ``Manual) (some (.const ``Genre []))
  let (titleTerm, _) ← DocElabM.run ⟨mkIdent ``Manual, g, .always, .none⟩ {} initState <| do
    titleParts.mapM (elabInline ⟨·⟩)
  let modJson ← VersoLiterate.loadModuleJson path.getString mod.getId.toString
  let lit ← match VersoLiterate.loadJsonString modJson s!"JSON for {mod.getId}" with
    | .ok lit => pure lit
    | .error e => throwErrorAt mod e
  withRef doc <| checkCoverage lit doc.getId
  withRef doc <| checkModuleDocs lit doc.getId
  let docConst := docName doc.getId
  unless (← getEnv).contains docConst do
    throwErrorAt doc "{doc.getId} is not an imported Verso document"
  let jsonName ← mkFreshUserName (mod.getId ++ `readableJson)
  addAndCompile <| .defnDecl {
    name := jsonName, levelParams := [], type := mkConst ``String, value := mkStrLit modJson,
    hints := .regular 0, safety := .safe
  }
  let name ← mkFreshUserName (mod.getId ++ `readablePart)
  let title ← titleTerm.mapM (elabTerm · (some (.app (mkConst ``Verso.Doc.Inline) g)))
  let title ← Meta.mkArrayLit (.app (mkConst ``Verso.Doc.Inline) g) title.toList
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars <|
    mkAppN (mkConst ``readablePage!) #[mkConst jsonName, title, mkStrLit titleString, mkConst docConst]
  if value.hasMVar then
    throwError "the title of {mod.getId} did not elaborate"
  withOptions (Compiler.LCNF.compiler.extract_closed.set · false) do
    addAndCompile <| .defnDecl {
      name, levelParams := [], type := .app (mkConst ``Verso.Doc.VersoDoc) g,
      value,
      hints := .regular 0, safety := .safe
    }
  return name

structure IncludeReadableConfig where
  path : StrLit
  level : NumLit
  modName : Ident
  title : StrLit
  doc : Ident

section
variable [Monad m] [MonadError m] [MonadLiftT CoreM m]

instance : FromArgs IncludeReadableConfig m where
  fromArgs := IncludeReadableConfig.mk <$> .positional' `path <*> .named' `level false
    <*> .positional' `name <*> .positional' `title <*> .positional' `doc

end

/--
`{includeReadable "." M "Title" D (level := n)}`: the Lean module `M` as a
section at level `n`, each declaration shown by its readable block from the
document module `D` with its Lean hidden under it.
-/
@[part_command Lean.Doc.Syntax.command]
def includeReadable : PartCommand
  | `(block|command{includeReadable $args* }) => do
    let {path, level, modName, title, doc} ← parseThe IncludeReadableConfig (← parseArgs args)
    let name ← readableModule path modName title doc
    closePartsUntil level.getNat (← getRef).getHeadInfo.getPos!
    addPart <| .included (mkIdentFrom modName name)
  | _ => throwUnsupportedSyntax

end FirSpecSite
