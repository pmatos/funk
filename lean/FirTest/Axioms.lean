import Lean.Compiler.ImplementedByAttr
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
The check that every declaration of `lean/` is trusted (ADR-2026-10-30-1452).
`#check_axioms` names the root modules of the packages to check, and is run
by `FirTest`'s root module, which imports every module that Lake builds. It
fails the build when a declaration of one of their modules:

* depends on an axiom other than Lean's three standard ones, `propext`,
  `Classical.choice` and `Quot.sound`. A `sorry` depends on `sorryAx`, and
  `native_decide` on an axiom of its own, so both fail it;
* is `unsafe` or `partial`;
* is `implemented_by` other code, so that a program would not run the
  definition that the proofs are about.
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
  let bad := (← liftCoreM (collectAxioms n)).filter (· ∉ standardAxioms)
  if bad.isEmpty then return none
  return some s!"depends on the axioms {bad.toList}"

/-- `#check_axioms R₁ R₂ …` checks every declaration of every imported module
whose name starts with one of the roots `Rᵢ`, and fails with each one that is
not trusted. It also fails when a root has no declaration, so that a renamed
package is not skipped in silence. -/
syntax (name := checkAxioms) "#check_axioms " ident+ : command

@[command_elab checkAxioms]
def elabCheckAxioms : CommandElab
  | `(#check_axioms $roots*) => do
    let env ← getEnv
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
    for r in roots do
      unless checked.contains r do
        problems := problems.push s!"no declaration of {r} was checked"
    unless problems.isEmpty do
      throwError m!"{problems.size} declarations are not trusted:\n" ++
        "\n".intercalate problems.toList
  | _ => throwUnsupportedSyntax

end FirTest
