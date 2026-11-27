import FirTest.Axioms

/-!
Tests of the exemption of `#check_axioms` for Lean's `T.ctorIdx` and
`T.ctorIdx._impl` (ADR-2026-10-30-1452). Each test declares its code inside
`#untrusted_in`, which reports what the check finds and then drops the code,
so nothing here reaches the check of `FirCheck`.
-/

namespace FirTest

open Lean Elab Command

/-- `#untrusted_in (cmds) n₁ n₂ …` runs the commands, reports for each `nᵢ`
why the check does not trust it, or that it does, and then undoes the
commands. -/
syntax (name := untrustedIn) "#untrusted_in " "(" command* ")" ident+ : command

@[command_elab untrustedIn]
def elabUntrustedIn : CommandElab
  | `(#untrusted_in ( $cmds* ) $ns*) => withoutModifyingEnv do
    for c in cmds do elabCommand c
    let env ← getEnv
    let natives ← IO.mkRef ({} : NameSet)
    let mut lines := #[]
    for n in ns do
      let n := n.getId
      let some info := env.find? n | throwError "{n} is not declared"
      let why ← untrusted env natives n info
      lines := lines.push s!"{n}: {why.getD "trusted"}"
    logInfo ("\n".intercalate lines.toList)
  | _ => throwUnsupportedSyntax

end FirTest

/-- info: CtorIdxTest.T.ctorIdx: trusted
CtorIdxTest.T.ctorIdx._impl: trusted
CtorIdxTest.U.ctorIdx: trusted
CtorIdxTest.U.ctorIdx._impl: trusted -/
#guard_msgs in
#untrusted_in (
  inductive CtorIdxTest.T where
    | a
    | b (n : Nat)
  inductive CtorIdxTest.U (α : Type) : Nat → Type where
    | z : CtorIdxTest.U α 0
    | s : α → CtorIdxTest.U α n → CtorIdxTest.U α (n + 1)
) CtorIdxTest.T.ctorIdx CtorIdxTest.T.ctorIdx._impl
  CtorIdxTest.U.ctorIdx CtorIdxTest.U.ctorIdx._impl

-- A hand-written `implemented_by` is still banned.
/-- info: CtorIdxTest.f: is implemented by CtorIdxTest.g -/
#guard_msgs in
#untrusted_in (
  def CtorIdxTest.g (n : Nat) : Nat := n
  @[implemented_by CtorIdxTest.g] def CtorIdxTest.f (n : Nat) : Nat := n
) CtorIdxTest.f

-- Another implementation of a generated `T.ctorIdx` is banned, and the
-- generated `_impl` is then banned too.
/-- info: CtorIdxTest.T.ctorIdx: is implemented by CtorIdxTest.other
CtorIdxTest.T.ctorIdx._impl: is unsafe
CtorIdxTest.other: is unsafe -/
#guard_msgs in
#untrusted_in (
  inductive CtorIdxTest.T where
    | a
    | b (n : Nat)
  unsafe def CtorIdxTest.other (_ : CtorIdxTest.T) : Nat := 7
  attribute [implemented_by CtorIdxTest.other] CtorIdxTest.T.ctorIdx
) CtorIdxTest.T.ctorIdx CtorIdxTest.T.ctorIdx._impl CtorIdxTest.other

-- The pair is banned for a type with one constructor, for which Lean makes
-- no `_impl`. Lean's `mkCtorIdx` says why: reading the tag is wrong for a type
-- whose value Lean may unwrap to its field.
/-- info: CtorIdxTest.W.ctorIdx: is implemented by CtorIdxTest.W.ctorIdx._impl
CtorIdxTest.W.ctorIdx._impl: is unsafe -/
#guard_msgs in
#untrusted_in (
  structure CtorIdxTest.W where
    n : Nat
  unsafe def CtorIdxTest.W.ctorIdx._impl (w : CtorIdxTest.W) : Nat := getObjTagNat w
  attribute [implemented_by CtorIdxTest.W.ctorIdx._impl] CtorIdxTest.W.ctorIdx
) CtorIdxTest.W.ctorIdx CtorIdxTest.W.ctorIdx._impl

-- The pair is banned under a name that is not an inductive type's.
/-- info: CtorIdxTest.N.ctorIdx: is implemented by CtorIdxTest.N.ctorIdx._impl
CtorIdxTest.N.ctorIdx._impl: is unsafe -/
#guard_msgs in
#untrusted_in (
  def CtorIdxTest.N := Nat
  unsafe def CtorIdxTest.N.ctorIdx._impl (n : Nat) : Nat := getObjTagNat n
  @[implemented_by CtorIdxTest.N.ctorIdx._impl] def CtorIdxTest.N.ctorIdx (_ : Nat) : Nat := 0
) CtorIdxTest.N.ctorIdx CtorIdxTest.N.ctorIdx._impl
