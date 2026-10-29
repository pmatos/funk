import VersoManual
import FirOwn
import FirLeanMLIR

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "fir semantics: two prototypes side by side" =>

This page shows the same definitions from both prototypes of the LeanMLIR
spike (issue 24), as the fir spec would show them: Lean definitions,
elaborated by Verso, with prose beside them.

# The `freeze` op

`freeze` turns poison into one chosen value. The choice is an effect of the
interpreter's monad, so every use of the result sees the same bits.

## fir's own calculus

The op's semantics is a function in any monad that has the choice effect.
(`FirOwn.PoisonOr` is qualified only because this page also loads
LeanMLIR, which has its own `PoisonOr`.)

```lean
namespace OwnPage
open FirOwn

def freeze [Monad m] [MonadFir m] :
    FirOwn.PoisonOr (BitVec w) → m (FirOwn.PoisonOr (BitVec w))
  | .poison => .value <$> MonadFir.choose w
  | .value x => pure (.value x)

def condBr [Monad m] [MonadFir m] :
    FirOwn.PoisonOr (BitVec 1) → m Exit
  | .poison => MonadFir.ub "branch on poison"
  | .value c => pure (if c = 1#1 then .goto 0 else .goto 1)
end OwnPage
```

## On LeanMLIR

The same op, in the dialect monad. LeanMLIR fixes one monad per dialect, so
the definition names it.

```lean
namespace MLIRPage
open FirOwn (Prog MonadFir)

def freeze (x : PoisonOr (BitVec w)) : Prog (PoisonOr (BitVec w)) :=
  match x with
  | .poison => .value <$> MonadFir.choose w
  | .value a => pure (.value a)
end MLIRPage
```

# The op signature

## fir's own calculus

```lean
namespace OwnPage
open FirOwn Core

def sig : Op → List Ty
  | .const _ _ | .br => []
  | .add w _ | .xor w => [.int w, .int w]
  | .freeze w => [.int w]
  | .condBr => [.int 1]
  | .ret ts => ts
end OwnPage
```

## On LeanMLIR

Each op also states its effect kind. Terminators return a `ctl` value,
because LeanMLIR has no successors.

```lean
namespace MLIRPage
open FirLeanMLIR

def signature : Op → Signature Ty
  | .const w _ => ⟨[], [], [.int w], .pure⟩
  | .add w _ | .xor w => ⟨[.int w, .int w], [], [.int w], .pure⟩
  | .freeze w => ⟨[.int w], [], [.int w], .impure⟩
  | .br _ ws => ⟨ints ws, [], [.ctl], .pure⟩
  | .condBr _ wt _ wf => ⟨.int 1 :: ints (wt ++ wf), [], [.ctl], .impure⟩
  | .ret ws => ⟨ints ws, [], [.ctl], .pure⟩
end MLIRPage
```

# A sample function

The tracer sample `@add3`, as the text format shows it:

```
func @add3(%x: i8) -> i8 {
entry(%x: i8):
  %c = const 3 : i8     @1
  %r = add %x, %c : i8  @1
  ret %r : i8           @2
}
```

## fir's own calculus

Names and locations are part of the term.

```lean
namespace OwnPage
open FirOwn FirOwn.Examples

def add3 : Func Core where
  name := "add3"
  results := [i 8]
  blocks := [{ label := "entry", params := [("x", i 8)], body := [
    let1 "c" 8 (.const 8 3) [] 1,
    let1 "r" 8 (.add 8 false) ["x", "c"] 1,
    { results := [], op := .ret [i 8], args := ["r"], loc := .ref 2 }] }]
end OwnPage
```

## On LeanMLIR

Variables are de Bruijn indices with a proof of their type. Names and
locations are not part of the term.

```lean
namespace MLIRPage
open FirLeanMLIR FirLeanMLIR.Examples

def add3 : Func := ⟨[{
  params := [8]
  body :=
    .var (cst 8 3) <|
    .var (add 8 false ⟨1, rfl⟩ ⟨0, rfl⟩) <|
    .var (ret 8 ⟨0, rfl⟩) done }]⟩
end MLIRPage
```

Both run the same way:

```lean
#eval FirOwn.Examples.runAll OwnPage.add3 [FirOwn.Examples.iv 8 40]
#eval FirLeanMLIR.Examples.runAll MLIRPage.add3 [FirLeanMLIR.Examples.iv 8 40]
```
