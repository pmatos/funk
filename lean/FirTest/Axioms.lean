import Lean.Compiler.CSimpAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.LCNF.Util
import Lean.Elab.Command
import Lean.Meta.Constructions.CtorIdx
import Lean.Meta.Native
import Lean.Util.CollectAxioms

/-!
The check that every declaration of `lean/` is trusted (ADR-2026-10-30-1452).
`#check_axioms` names the root modules of the libraries to check. `FirCheck`
imports `FirTest`'s root module, which imports every module of `lean/`, and runs
it as its last command.
It fails the build when a declaration of one of their modules, or of the
module that runs it:

* depends on an axiom other than Lean's three standard ones, `propext`,
  `Classical.choice` and `Quot.sound`, and the axioms of native evaluation
  below. A `sorry` depends on `sorryAx`, so it fails the check;
* is `unsafe` or `partial`;
* is `implemented_by` other code, or `extern`, so that a program would not
  run the definition that the proofs are about.

One pair is exempt from the bans on `unsafe` and `implemented_by`: the
`T.ctorIdx` that Lean makes for an inductive type `T` with more than one
constructor, and its `T.ctorIdx._impl`. `T.ctorIdx` gives the index of a
value's constructor by `T.casesOn`, and Lean runs `T.ctorIdx._impl` in its
place, which reads the tag that the runtime keeps in the value. Lean makes the
pair for every such type, and `noConfusion` needs `T.ctorIdx`, so no inductive
type could be declared without it. The check accepts the pair only in exactly
the shape that Lean makes it, so the exemption trusts Lean's compiler and
runtime to keep a constructor's index as its tag. The human ruled this on
2026-11-26, in #511.

It also fails when a source file in `lean/` is not imported, or belongs to a
library that is not checked, so that every module of `lean/` is checked; when
a root has no declaration, so that a renamed library is not skipped in
silence; and when any text follows it, since the check would not see a
command there.

A proof by native evaluation (`native_decide`, `decide +native` or
`bv_decide`) compiles a closed term `e : Bool`, runs it, and adds an axiom
`e = true`, named after the declaration, `_native`, the tactic and `ax_…`.
The check allows such an axiom only when it compiles and runs `e` again
itself and gets `true`, so the proof trusts the compiler and nothing else
(ADR-2026-10-30-1452). The bans on `unsafe`, `partial`, `implemented_by` and
`extern` keep the compiled code equal to the definitions that the proofs are
about. A `@[csimp]` swap is allowed because it is proved, but only from the
standard axioms: the compiler applies every swap when the check runs a claim
again, so a swap proved from a native axiom could make a false claim run as
true and so confirm that axiom.

Lean does not keep an `example`, so the check cannot see one. A `sorry` in an
example gives a warning, and `lean/` builds with `lake build --wfail`, so it
fails the build (ADR-2026-10-30-1452). Native evaluation is allowed in an
example, as it is anywhere.
-/

namespace FirTest

open Lean Elab Command

/-- Lean's three standard axioms: the only ones a declaration may use. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `n` is an axiom that Lean's native evaluation added
(`Lean.Meta.nativeEqTrue`) and whose claim holds. Its name ends in `_native`,
the tactic and `ax_…`; it states `e = true` for a closed term `e : Bool`; and
`e` gives `true` when the check compiles and runs it again. -/
def isNativeAxiom (env : Environment) (n : Name) : CommandElabM Bool := do
  let some (.axiomInfo info) := env.find? n | return false
  let named := match n.components.reverse with
    | .str _ ax :: _ :: native :: _ => ax.startsWith "ax_" && native == `_native
    | _ => false
  let (``Eq, #[.const ``Bool [], e, .const ``Bool.true []]) :=
      info.type.getAppFnArgs | return false
  if info.isUnsafe || !named || e.hasLooseBVars || e.hasFVar || e.hasMVar then
    return false
  liftTermElabM <| withoutModifyingEnv do
    try return (← Meta.nativeEqTrue `check_axioms e) matches .success _
    catch _ => return false

/-- The body of `e` under its first `k` lambdas, if it has that many. -/
def underLambdas : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .lam _ _ b _ => underLambdas k b
  | _, _ => none

/-- The inductive type `T` when `n` is a safe `T.ctorIdx` as Lean makes it
for a type with more than one constructor (`Lean.mkCtorIdx`): after its
lambdas, `T.casesOn` on its last argument, whose case for each constructor is
the constructor's index. -/
def ctorIdxOf? (env : Environment) (n : Name) : Option InductiveVal := do
  let ind ← isCtorIdxCore? env n
  guard (ind.numCtors > 1 && !Compiler.LCNF.isRuntimeBuiltinType ind.name)
  let some (.defnInfo d) := env.find? n | none
  guard (d.safety == .safe)
  let body ← underLambdas (ind.numParams + ind.numIndices + 1) d.value
  let (casesOn, args) := body.getAppFnArgs
  guard (casesOn == mkCasesOnName ind.name)
  guard (args.size == ind.numParams + ind.numIndices + 2 + ind.numCtors)
  guard (args[ind.numParams + ind.numIndices + 1]! == .bvar 0)
  for c in ind.ctors, alt in args.extract (args.size - ind.numCtors) do
    let some (.ctorInfo ci) := env.find? c | none
    guard (underLambdas ci.numFields alt == some (mkRawNatLit ci.cidx))
  return ind

/-- Whether `n` is `T.ctorIdx` of `ctorIdxOf?` or its `T.ctorIdx._impl`, as
Lean makes them: `T.ctorIdx` is implemented by `T.ctorIdx._impl`, which has
its type, is neither implemented by other code nor `extern`, and after its
lambdas only reads the tag of its last argument with `getObjTagNat`. -/
def isGeneratedCtorIdx (env : Environment) (n : Name) : Bool := Id.run do
  let idx := match n with
    | .str p "_impl" => p
    | _ => n
  let some ind := ctorIdxOf? env idx | return false
  let impl := idx.str "_impl"
  unless Compiler.getImplementedBy? env idx == some impl do return false
  let some (.defnInfo d) := env.find? idx | return false
  let some (.defnInfo i) := env.find? impl | return false
  unless i.type == d.type && i.levelParams == d.levelParams do return false
  if (Compiler.getImplementedBy? env impl).isSome || isExtern env impl then return false
  let some body := underLambdas (ind.numParams + ind.numIndices + 1) i.value | return false
  return body.getAppFnArgs matches (``getObjTagNat, #[_, .bvar 0])

/-- Why the declaration `n` is not trusted, if it is not. `natives` holds the
axioms of native evaluation already found to hold. -/
def untrusted (env : Environment) (natives : IO.Ref NameSet) (n : Name)
    (info : ConstantInfo) : CommandElabM (Option String) := do
  -- Lean's own `T.ctorIdx` and its `_impl`, exempt by the ruling of
  -- 2026-11-26 (#511). Every other check still applies to them.
  let ctorIdx := isGeneratedCtorIdx env n
  if info.isUnsafe && !ctorIdx then return some "is unsafe"
  -- A `partial` definition is an opaque constant whose code is its
  -- `_unsafe_rec`. Well-founded recursion makes an `_unsafe_rec` too, for
  -- the compiler, beside a definition with a value, so the copy alone is not
  -- a sign of `partial`.
  if info matches .opaqueInfo _ && env.contains (n.str "_unsafe_rec") then
    return some "is partial"
  if let some impl := Compiler.getImplementedBy? env n then
    unless ctorIdx do return some s!"is implemented by {impl}"
  if isExtern env n then return some "is extern"
  -- A `@[csimp]` swap changes the code that the check runs to confirm a native
  -- claim, so a swap that rests on a native axiom could confirm itself.
  let csimp := Compiler.hasCSimpAttribute env n
  let mut bad := #[]
  for a in ← liftCoreM (collectAxioms n) do
    if standardAxioms.contains a then continue
    if !csimp && (← natives.get).contains a then continue
    if !csimp && (← isNativeAxiom env a) then natives.modify (·.insert a)
    else bad := bad.push a
  if bad.isEmpty then return none
  return some s!"depends on the axioms {bad.toList}"

/-- The directory that holds the sources of a library whose module `mod` is in
the file `file`: the file's directory, one level up per dot in `mod`. -/
def sourceDir (file : System.FilePath) (mod : Name) : System.FilePath :=
  mod.components.foldl (fun dir _ => dir.parent.getD ".") file

/-- The modules whose sources are in `dir`: one for each `.lean` file under it,
other than `lakefile.lean` and the files under a hidden directory, such as
Lake's `.lake`. -/
def sourceModules (dir : System.FilePath) : IO (Array Name) := do
  let hidden (p : System.FilePath) := (p.fileName.getD "").startsWith "."
  let files ← dir.walkDir fun p => pure (p == dir || !hidden p)
  let depth := dir.components.length
  let mut mods := #[]
  for file in files do
    let isSource := file.fileName != some "lakefile.lean"
    unless file.extension == some "lean" && isSource do continue
    let some stem := file.fileStem | continue
    let dirs := (file.components.drop depth).dropLast
    mods := mods.push ((dirs ++ [stem]).foldl Name.str .anonymous)
  return mods

/-- `#check_axioms R₁ R₂ …` checks every declaration of the module that runs
it and of every imported module whose name starts with one of the roots `Rᵢ`,
and fails with each one that is not trusted. It also fails when a module whose
source is in the running module's library directory is not imported or not
under a root, when a root has no declaration, and when any text follows it. -/
syntax (name := checkAxioms) "#check_axioms " ident+ : command

@[command_elab checkAxioms]
def elabCheckAxioms : CommandElab
  | `(#check_axioms $roots*) => do
    let env ← getEnv
    let main := env.mainModule
    let roots := roots.map (·.getId)
    let natives ← IO.mkRef ({} : NameSet)
    let mut problems : Array String := #[]
    let mut checked : NameSet := {}
    for h : i in [0:env.header.moduleNames.size] do
      let mod := env.header.moduleNames[i]
      unless roots.contains mod.getRoot do continue
      for n in env.header.moduleData[i]!.constNames do
        checked := checked.insert mod.getRoot
        let some info := env.find? n | continue
        if let some why ← untrusted env natives n info then
          problems := problems.push s!"{n}, in {mod}, {why}"
    for (n, info) in env.constants.map₂.toList do
      checked := checked.insert main.getRoot
      if let some why ← untrusted env natives n info then
        problems := problems.push s!"{n}, in {main}, {why}"
    for r in roots do
      unless checked.contains r do
        problems := problems.push s!"no declaration of {r} was checked"
    let dir := sourceDir ⟨← getFileName⟩ main
    for mod in ← sourceModules dir do
      if mod == main then continue
      unless env.header.moduleNames.contains mod do
        problems := problems.push s!"{mod} is not imported by {main}"
      unless roots.contains mod.getRoot do
        problems := problems.push s!"{mod} is not in a checked library"
    let src := (← getFileMap).source
    let tail := (← getRef).getTailPos?.getD 0
    let rest := String.Pos.Raw.extract src tail ⟨src.utf8ByteSize⟩
    unless rest.all Char.isWhitespace do
      problems := problems.push s!"text follows #check_axioms in {main}"
    unless problems.isEmpty do
      throwError m!"#check_axioms found {problems.size} problems:\n" ++
        "\n".intercalate problems.toList
  | _ => throwUnsupportedSyntax

end FirTest
