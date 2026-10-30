import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
The check that every declaration of `lean/` is trusted (ADR-2026-10-30-1452).
`#check_axioms` names the root modules of the libraries to check. `FirTest`'s
root module imports every module of `lean/` and runs it as its last command.
It fails the build when a declaration of one of their modules, or of the
module that runs it:

* depends on an axiom other than Lean's three standard ones, `propext`,
  `Classical.choice` and `Quot.sound`. A `sorry` depends on `sorryAx`, and
  `native_decide` on an axiom of its own, so both fail it;
* is `unsafe` or `partial`;
* is `implemented_by` other code, or `extern`, so that a program would not
  run the definition that the proofs are about.

It also fails when a source file in `lean/` is not imported, or belongs to a
library that is not checked, so that every module of `lean/` is checked; when
a root has no declaration, so that a renamed library is not skipped in
silence; and when any text follows it, since the check would not see a
command there.

Lean does not keep an `example`, so the check cannot see one.
`scripts/build-spec.sh` builds `lean/` with `--wfail`, so a `sorry` in an
`example`, which Lean warns about, fails the build too.
-/

namespace FirTest

open Lean Elab Command

/-- Lean's three standard axioms: the only ones a declaration may use. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Why the declaration `n` is not trusted, if it is not. -/
def untrusted (env : Environment) (n : Name) (info : ConstantInfo) :
    CommandElabM (Option String) := do
  if info.isUnsafe then return some "is unsafe"
  -- A `partial` definition is an opaque constant whose code is its
  -- `_unsafe_rec`. Well-founded recursion makes an `_unsafe_rec` too, for
  -- the compiler, beside a definition with a value, so the copy alone is not
  -- a sign of `partial`.
  if info matches .opaqueInfo _ && env.contains (n.str "_unsafe_rec") then
    return some "is partial"
  if let some impl := Compiler.getImplementedBy? env n then
    return some s!"is implemented by {impl}"
  if isExtern env n then return some "is extern"
  let bad := (← liftCoreM (collectAxioms n)).filter (· ∉ standardAxioms)
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
    let mut problems : Array String := #[]
    let mut checked : NameSet := {}
    for h : i in [0:env.header.moduleNames.size] do
      let mod := env.header.moduleNames[i]
      unless roots.contains mod.getRoot do continue
      for n in env.header.moduleData[i]!.constNames do
        checked := checked.insert mod.getRoot
        let some info := env.find? n | continue
        if let some why ← untrusted env n info then
          problems := problems.push s!"{n}, in {mod}, {why}"
    if roots.contains main.getRoot then
      for (n, info) in env.constants.map₂.toList do
        checked := checked.insert main.getRoot
        if let some why ← untrusted env n info then
          problems := problems.push s!"{n}, in {main}, {why}"
    for r in roots do
      unless checked.contains r do
        problems := problems.push s!"no declaration of {r} was checked"
    let dir := sourceDir ⟨← getFileName⟩ main
    for mod in ← sourceModules dir do
      unless mod == main || env.header.moduleNames.contains mod do
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
