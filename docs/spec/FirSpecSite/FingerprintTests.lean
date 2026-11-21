import FirSpecSite.Fingerprint

/-!
Tests of what a declaration's fingerprint covers. Each test elaborates a
definition twice, with the same name, and compares the two fingerprints,
leaving the environment as it was. They run when the `FirSpecSite` library
builds, so `scripts/build-spec.sh` runs them.
-/

open Lean Elab Command

namespace FirSpecSite.FingerprintTests

/-- Elaborates the commands `srcs` in order. -/
def elabAll (srcs : List String) : CommandElabM Unit :=
  for src in srcs do
    match Parser.runParserCategory (← getEnv) `command src with
    | .ok stx => elabCommand stx
    | .error e => throwError "cannot parse {src}: {e}"

/-- The fingerprint of the declaration `n`, in the current namespace, once the commands `srcs` are elaborated. -/
def hashAfterAll (srcs : List String) (n : Name) : CommandElabM UInt64 :=
  withoutModifyingEnv do
    let n := (← getCurrNamespace) ++ n
    elabAll srcs
    let some h := declHash (← getEnv) n | throwError "{srcs} do not declare {n}"
    return h

/-- The fingerprint of the declaration `n`, in the current namespace, once the command `src` is elaborated. -/
def hashAfter (src : String) (n : Name) : CommandElabM UInt64 :=
  hashAfterAll [src] n

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

/-! A change to the proof that a well-founded definition terminates does not count. -/

#eval show CommandElabM Unit from
  expectSame "the proof that it terminates" `fpHalve
    "def fpHalve (m n : Nat) : Nat := if m ≤ 1 then n else fpHalve (m / 2) (n + 1)
     termination_by m
     decreasing_by omega"
    "def fpHalve (m n : Nat) : Nat := if m ≤ 1 then n else fpHalve (m / 2) (n + 1)
     termination_by m
     decreasing_by have _h : True := trivial; omega"

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

/-!
A matcher counts by what it says, not by its name. Lean reuses the matcher
of an earlier definition of the same shape: here `fpShape` uses
`fpIsZero.match_1`. Without `fpIsZero`, `fpShape` gets a matcher of its own,
`fpShape.match_1`, with the same body, and its fingerprint must stay.
-/

#eval show CommandElabM Unit from do
  let isZero := "def fpIsZero : Nat → Bool | 0 => true | _ => false"
  let shape := "def fpShape : Nat → Nat | 0 => 1 | _ => 2"
  let ns ← getCurrNamespace
  let shared ← withoutModifyingEnv do
    elabAll [isZero, shape]
    let some (.defnInfo d) := (← getEnv).find? (ns ++ `fpShape) | throwError "no fpShape"
    return d.value.getUsedConstants.contains (ns ++ `fpIsZero.match_1)
  unless shared do
    throwError "fpShape does not reuse the matcher of fpIsZero, so this test checks nothing"
  if (← hashAfterAll [isZero, shape] `fpShape) != (← hashAfter shape `fpShape) then
    throwError "the fingerprint of fpShape changes with the name of the matcher it uses"

/-! A change to a matcher that the definition shares with another still counts. -/

#eval show CommandElabM Unit from do
  let isZero := "def fpIsZero : Nat → Bool | 0 => true | _ => false"
  if (← hashAfterAll [isZero, "def fpShape : Nat → Nat | 0 => 1 | _ => 2"] `fpShape) ==
      (← hashAfterAll [isZero, "def fpShape : Nat → Nat | 1 => 1 | _ => 2"] `fpShape) then
    throwError "the fingerprint of fpShape misses a change to the patterns of a matcher it shares"

end FirSpecSite.FingerprintTests
