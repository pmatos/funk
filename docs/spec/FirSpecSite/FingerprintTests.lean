import FirSpecSite.Fingerprint

/-!
Tests of what a declaration's fingerprint covers. Each test elaborates a
definition twice, with the same name, and compares the two fingerprints,
leaving the environment as it was. They run when the `FirSpecSite` library
builds, so `scripts/build-spec.sh` runs them.
-/

open Lean Elab Command

namespace FirSpecSite.FingerprintTests

/-- The fingerprint of the declaration `n`, in the current namespace, once the command `src` is elaborated. -/
def hashAfter (src : String) (n : Name) : CommandElabM UInt64 :=
  withoutModifyingEnv do
    let n := (← getCurrNamespace) ++ n
    let stx ← match Parser.runParserCategory (← getEnv) `command src with
      | .ok stx => pure stx
      | .error e => throwError "cannot parse {src}: {e}"
    elabCommand stx
    let some h := declHash (← getEnv) n | throwError "{src} does not declare {n}"
    return h

/-- Fails unless the two versions `old` and `new` of `n` have different fingerprints. -/
def expectChange (what : String) (n : Name) (old new : String) : CommandElabM Unit := do
  if (← hashAfter old n) == (← hashAfter new n) then
    throwError "the fingerprint of {n} misses {what}"

/-- Fails unless the two versions `old` and `new` of `n` have the same fingerprint. -/
def expectSame (what : String) (n : Name) (old new : String) : CommandElabM Unit := do
  unless (← hashAfter old n) == (← hashAfter new n) do
    throwError "the fingerprint of {n} changes with {what}"

/-! The body of a structurally recursive definition, which Lean keeps in `f._f`. -/

#eval show CommandElabM Unit from
  expectChange "a change to its structurally recursive body" `fpSum
    "def fpSum : List Nat → Nat | [] => 0 | x :: xs => x + fpSum xs"
    "def fpSum : List Nat → Nat | [] => 0 | x :: xs => x * fpSum xs"

/-! The bodies of mutually recursive definitions, whichever of them changes. -/

#eval show CommandElabM Unit from
  expectChange "a change to the body of a definition of its mutual block" `fpEven
    "mutual
     def fpEven : Nat → Bool | 0 => true | n + 1 => fpOdd n
     def fpOdd : Nat → Bool | 0 => false | n + 1 => fpEven n
     end"
    "mutual
     def fpEven : Nat → Bool | 0 => true | n + 1 => fpOdd n
     def fpOdd : Nat → Bool | 0 => true | n + 1 => fpEven n
     end"

/-! The body of a well-founded definition of several arguments, which Lean keeps in `f._unary`. -/

#eval show CommandElabM Unit from
  expectChange "a change to its well-founded body" `fpHalve
    "def fpHalve (m n : Nat) : Nat := if m ≤ 1 then n else fpHalve (m / 2) (n + 1)
     termination_by m
     decreasing_by omega"
    "def fpHalve (m n : Nat) : Nat := if m ≤ 1 then n else fpHalve (m / 2) (n + 2)
     termination_by m
     decreasing_by omega"

/-! The bodies of mutually well-founded definitions, which Lean keeps in `f._mutual`. -/

#eval show CommandElabM Unit from
  expectChange "a change to the body of a definition of its well-founded mutual block" `fpDown
    "mutual
     def fpDown (n : Nat) : Nat := if n ≤ 1 then 0 else fpUp (n / 2)
     termination_by n
     decreasing_by omega
     def fpUp (n : Nat) : Nat := if n ≤ 1 then 1 else fpDown (n / 2) + 1
     termination_by n
     decreasing_by omega
     end"
    "mutual
     def fpDown (n : Nat) : Nat := if n ≤ 1 then 0 else fpUp (n / 2)
     termination_by n
     decreasing_by omega
     def fpUp (n : Nat) : Nat := if n ≤ 1 then 1 else fpDown (n / 2) + 2
     termination_by n
     decreasing_by omega
     end"

/-! The patterns of a definition that is not recursive, which Lean keeps in `f.match_N`. -/

#eval show CommandElabM Unit from
  expectChange "a change to its patterns" `fpPick
    "def fpPick : Nat → Nat | 0 => 1 | _ => 2"
    "def fpPick : Nat → Nat | 1 => 1 | _ => 2"

/-! The names of bound variables and the layout do not count. -/

#eval show CommandElabM Unit from
  expectSame "the names of its bound variables" `fpSum
    "def fpSum : List Nat → Nat | [] => 0 | x :: xs => x + fpSum xs"
    "def fpSum : List Nat → Nat
       | [] => 0
       | y :: ys => y + fpSum ys"

/-! A definition that the declaration only refers to still counts by its name. -/

#eval show CommandElabM Unit from
  expectSame "the body of a definition it refers to" `fpTotal
    "mutual
     def fpTotal : Nat := fpCount 3
     def fpCount (n : Nat) : Nat := n + 1
     end"
    "mutual
     def fpTotal : Nat := fpCount 3
     def fpCount (n : Nat) : Nat := n + 2
     end"

end FirSpecSite.FingerprintTests
