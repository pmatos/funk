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

/--
Fails unless the declaration `n`, elaborated after `srcs`, uses the matcher
`m`, which an earlier declaration made, so that a test of a shared matcher
checks something.
-/
def expectShared (srcs : List String) (n m : Name) : CommandElabM Unit := do
  let ns ← getCurrNamespace
  let shared ← withoutModifyingEnv do
    elabAll srcs
    let some ci := (← getEnv).find? (ns ++ n) | throwError "{srcs} do not declare {n}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    return used.contains (ns ++ m)
  unless shared do
    throwError "{n} does not reuse {m}, so this test checks nothing"

/--
Fails unless the fingerprint of `n` is the same after `shared ++ [src]`, where
`user`, `n` or a part of it, reuses the matcher `m` that `shared` made, as
after `src` alone, where it has its own.
-/
def expectSameUnshared (what : String) (n m : Name) (shared : List String) (src : String)
    (user : Name := n) : CommandElabM Unit := do
  expectShared (shared ++ [src]) user m
  unless (← hashAfterAll (shared ++ [src]) n) == (← hashAfter src n) do
    throwError "the fingerprint of {n} changes with {what}"

/--
Fails unless the fingerprint of `n` changes from `old` to `new`, in both of
which `user`, `n` or a part of it, reuses the matcher `m`, of the same name,
that their first declarations made.
-/
def expectChangeShared (what : String) (n m : Name) (old new : List String)
    (user : Name := n) : CommandElabM Unit := do
  expectShared old user m
  expectShared new user m
  if (← hashAfterAll old n) == (← hashAfterAll new n) then
    throwError "the fingerprint of {n} misses {what}"

/-- A definition whose matcher, `fpIsZero.match_1`, the tests below share. -/
def isZero : String := "def fpIsZero : Nat → Bool | 0 => true | _ => false"
/-- `fpIsZero` with other patterns, so its matcher changes and keeps its name. -/
def isOne : String := "def fpIsZero : Nat → Bool | 1 => true | _ => false"

/-!
A matcher counts by what it says, not by its name. Lean reuses the matcher
of an earlier declaration of the same shape: here `fpShape` uses
`fpIsZero.match_1`. Without `fpIsZero`, `fpShape` gets a matcher of its own,
`fpShape.match_1`, with the same body, and its fingerprint must stay. A
change to the patterns of a shared matcher, whose name stays, must still
change it.
-/

#eval show CommandElabM Unit from
  expectSameUnshared "the name of the matcher its body uses" `fpShape `fpIsZero.match_1
    [isZero]
    "def fpShape : Nat → Nat | 0 => 1 | _ => 2"

#eval show CommandElabM Unit from
  expectChangeShared "a change to the patterns of the matcher its body shares" `fpShape
    `fpIsZero.match_1
    [isZero,
     "def fpShape : Nat → Nat | 0 => 1 | _ => 2"]
    [isOne,
     "def fpShape : Nat → Nat | 1 => 1 | _ => 2"]

/-! The same holds for a matcher in a statement. -/

#eval show CommandElabM Unit from
  expectSameUnshared "the name of the matcher its statement uses" `fpStmt `fpIsZero.match_1
    [isZero]
    "axiom fpStmt (n : Nat) : (match n with | 0 => 1 | _ => 2) = 1"

#eval show CommandElabM Unit from
  expectChangeShared "a change to the patterns of the matcher its statement shares" `fpStmt
    `fpIsZero.match_1
    [isZero,
     "axiom fpStmt (n : Nat) : (match n with | 0 => 1 | _ => 2) = 1"]
    [isOne,
     "axiom fpStmt (n : Nat) : (match n with | 1 => 1 | _ => 2) = 1"]

/-! And for a matcher in a field's default. -/

#eval show CommandElabM Unit from
  expectSameUnshared "the name of the matcher a field's default uses" `fpBox
    `fpIsZero.match_1
    [isZero]
    "structure fpBox where
       k : Nat
       x : Nat := match k with | 0 => 1 | _ => 2"
    (user := `fpBox.x._default)

#eval show CommandElabM Unit from
  expectChangeShared "a change to the patterns of the matcher a field's default shares" `fpBox
    `fpIsZero.match_1
    [isZero,
     "structure fpBox where
       k : Nat
       x : Nat := match k with | 0 => 1 | _ => 2"]
    [isOne,
     "structure fpBox where
       k : Nat
       x : Nat := match k with | 1 => 1 | _ => 2"]
    (user := `fpBox.x._default)

end FirSpecSite.FingerprintTests
