import FirTest.Modes

/-!
Tests of how `fir-ref run` looks names up (#47). It keeps the values that a
run has defined in `FirRef.Bindings`, recent ones in a list and older ones
in a map that lookups move them into
(`docs/decisions/fir-ref-fast-paths.md#the-bindings-map`), and must give
exactly what the spec's environment gives, on functions that validation
rejects too.

The runs below read block arguments bound again on each jump, values from
before a loop, values of blocks that do not dominate the read, and a
caller's name from a callee, in loops long enough that lookups move values
into the map. A text cannot define a name twice, so `renamed` writes one
name of a parsed module as another, for parameters, results and block
arguments that share a name. Each run is checked in scripted mode against
the result it must give, and against the spec's own walk of the spec's
tree of the run, which `Core.scripted`, `Core.exhaustive` and
`Core.sampled` stand for but which `fir-ref` no longer runs. `@long`,
`@after`, `@undefined` and `@flips`, which makes choices, are checked in
exhaustive and sampled modes too, against the spec's walk, and `@long` and
`@flips` in exhaustive mode against their result. The last checks look
`Bindings` up directly, to show that lookups move `young` into `old`, that
every name keeps its value, and which lookups cost nothing.
-/

namespace FirTest

open Fir FirRef

/-- Functions that read values from before a loop that runs `%n` times. -/
def lookups : String := oneFunc "func @twice() -> i32 {
^e:
  %x: i32 = const 1 @0
  %y: i32 = const 2 @0
  ret %y @0
}

func @long(%a: i32, %b: i32, %n: i32) -> i32, i32, i32 {
^e:
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  %five: i32 = const 5 @0
  br ^l(%zero, %five) @0
^l(%i: i32, %y: i32):
  %y1: i32 = add %y, %one @0
  %i1: i32 = add %i, %one @0
  %d: i1 = icmp sge %i1, %n @0
  cond_br %d, ^done(%y1), ^l(%i1, %y1) @0
^done(%r: i32):
  ret %b, %r, %i @0
}

func @two() -> i32, i32 {
^e:
  %p: i32 = const 1 @0
  %q: i32 = const 2 @0
  ret %p, %q @0
}

func @pairs(%n: i32) -> i32 {
^e:
  %r: i32, %s: i32 = call @two @0
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  br ^l(%zero) @0
^l(%i: i32):
  %i1: i32 = add %i, %one @0
  %d: i1 = icmp sge %i1, %n @0
  cond_br %d, ^done, ^l(%i1) @0
^done:
  %t: i32, %u: i32 = call @two @0
  ret %s @0
}

func @peek() -> i32 {
^e:
  br ^x @0
^never:
  %secret: i32 = const 0 @0
  br ^x @0
^x:
  ret %secret @0
}

func @caller() -> i32 {
^e:
  %secret: i32 = const 7 @0
  %r: i32 = call @peek @0
  ret %r @0
}

func @after(%n: i32, %flag: i1, %k: i32) -> i32 {
^e:
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  br ^l(%zero) @0
^l(%i: i32):
  %i1: i32 = add %i, %one @0
  %d: i1 = icmp sge %i1, %n @0
  cond_br %d, ^done, ^l(%i1) @0
^done:
  %z: i32 = add %k, %one @0
  ret %z @0
}

func @undefined(%n: i32) -> i32 {
^e:
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  br ^l(%zero) @0
^l(%i: i32):
  %i1: i32 = add %i, %one @0
  %d: i1 = icmp sge %i1, %n @0
  cond_br %d, ^done, ^l(%i1) @0
^done:
  ret %nope @0
^never:
  %nope: i32 = const 0 @0
  ret %nope @0
}

func @nodom(%c: i1) -> i32 {
^e:
  cond_br %c, ^a, ^b @0
^a:
  %v: i32 = const 1 @0
  br ^b @0
^b:
  ret %v @0
}

func @flips(%n: i32) -> i32 {
^e:
  %zero: i32 = const 0 @0
  %one: i32 = const 1 @0
  %t: i1 = const true @0
  %p: i1 = add nsw %t, %t @0
  br ^l(%zero) @0
^l(%i: i32):
  %i1: i32 = add %i, %one @0
  %d: i1 = icmp sge %i1, %n @0
  cond_br %d, ^coin, ^l(%i1) @0
^coin:
  %f1: i1 = freeze %p @0
  %f2: i1 = freeze %p @0
  %s1: i32 = select %f1, %one, %zero @0
  %s2: i32 = select %f2, %one, %zero @0
  %s: i32 = add %s1, %s2 @0
  ret %s @0
}
"

/-! # Writing one name as another -/

/-- `x`, with the name `a` written `b`. -/
def ren (a b x : Name) : Name := if x == a then b else x

/-- An op with the name `a` written `b`. -/
def renOp (a b : Name) (o : Operation CoreDialect) : Operation CoreDialect :=
  { o with
    results := o.results.map fun (x, t) => (ren a b x, t)
    operands := o.operands.map (ren a b)
    succs := o.succs.map fun s => { s with args := s.args.map (ren a b) } }

/-- A function with the name `a` written `b`. -/
def renFunc (a b : Name) (f : Func CoreDialect) : Func CoreDialect :=
  { f with
    params := f.params.map fun (x, t) => (ren a b x, t)
    body := ⟨f.body.kind, f.body.blocks.map fun blk =>
      { blk with params := blk.params.map (fun (x, t) => (ren a b x, t)),
                 body := blk.body.map (renOp a b) }⟩ }

/-- The module of `lookups`, with the name `a` written `b`. -/
def renamed (a b : Name) : Option (Module CoreDialect) :=
  match parseCore lookups with
  | .ok m => some { m with items := m.items.map fun
    | .func f => .func (renFunc a b f)
    | i => i }
  | .error _ => none

/-- The module of `lookups`. -/
def unrenamed : Option (Module CoreDialect) := renamed "" ""

/-! # Each mode, by the machine and by the spec's tree -/

/-- What `fir-ref run` reports on the function `func` of `m`, run on
`args` in the mode `mode`, by the machine (`fir-ref`'s code for the spec's
modes) when `spec` is false, and by the spec's walk of its tree when it is
true. -/
def runBy (spec : Bool) (m : Module CoreDialect) (func : String) (args : List String)
    (mode : Mode) : RunReport :=
  match m.funcs.find? (Text.printSymbol ·.name == func) with
  | none => fails 2 "no function"
  | some f =>
    let name := Text.printSymbol f.name
    match readArgs (f.params.map (·.2)) args, mode with
    | .error why, _ => fails 2 why
    | .ok vs, .scripted cs => scriptedReport name <| if spec then
        (f.memTree coreUnit (ε := Core.Op) m vs defaultFuel).script constOf cs 0
      else Core.scripted coreUnit constOf m f vs defaultFuel cs
    | .ok vs, .exhaustive b => exhaustiveReport name b <| if spec then
        (f.memTree coreUnit (ε := Core.Op) m vs defaultFuel).explore b
      else Core.exhaustive coreUnit m f vs defaultFuel b
    | .ok vs, .sampled s => sampledReport name <| if spec then
        (f.memTree coreUnit (ε := Core.Op) m vs defaultFuel).sample draw ⟨s.toUInt64⟩
      else Core.sampled coreUnit draw m f vs defaultFuel ⟨s.toUInt64⟩

/-- The machine and the spec's tree both report `r` on the function `func`
of the module, if there is one. -/
def bothGive (m : Option (Module CoreDialect)) (func : String) (args : List String)
    (r : RunReport) (mode : Mode := .scripted []) : Bool :=
  match m with
  | some m => runBy false m func args mode == r && runBy true m func args mode == r
  | none => false

/-- The machine and the spec's tree give the same report on the function
`func` of the module, if there is one. -/
def sameBy (m : Option (Module CoreDialect)) (func : String) (args : List String)
    (mode : Mode) : Bool :=
  match m with
  | some m => runBy false m func args mode == runBy true m func args mode
  | none => false

/-! # Values from before a loop, and arguments bound on each jump

`@long` loops `%n` times, reads `%one` and `%n` from before the loop on
each step, and passes `%y` to the next step; four hundred steps are enough
for lookups to move values into the map. -/

#guard bothGive unrenamed "@twice" [] (returns ["2"])
#guard bothGive unrenamed "@long" ["1", "2", "1"] (returns ["2", "6", "0"])
#guard bothGive unrenamed "@long" ["1", "2", "400"] (returns ["2", "405", "399"])
#guard bothGive unrenamed "@pairs" ["400"] (returns ["2"])
#guard bothGive unrenamed "@long" ["1", "2", "400"] (outcomes [ret ["2", "405", "399"]] 0)
  (.exhaustive 16)
#guard sameBy unrenamed "@long" ["1", "2", "400"] (.sampled 5)

/-! # Names defined twice

The latest definition wins, and of the names of one bind, the first. -/

-- `%x` and `%y` as one name: `ret` reads the latest.
#guard bothGive (renamed "y" "x") "@twice" [] (returns ["2"])
-- Two parameters `%a`: the first wins, before the loop and after it.
#guard bothGive (renamed "b" "a") "@long" ["1", "2", "1"] (returns ["1", "6", "0"])
#guard bothGive (renamed "b" "a") "@long" ["1", "2", "400"] (returns ["1", "405", "399"])
-- A block argument `%y` that the loop's body defines again.
#guard bothGive (renamed "y1" "y") "@long" ["1", "2", "400"] (returns ["2", "405", "399"])
-- Two results `%r` of one call: the first wins.
#guard bothGive (renamed "s" "r") "@pairs" ["400"] (returns ["1"])
#guard bothGive (renamed "s" "r") "@pairs" ["1"] (returns ["1"])

/-! # What a run does not see -/

-- A callee does not see its caller's names, and a block sees a value of a
-- block that does not dominate it only on a path through that block.
#guard bothGive unrenamed "@caller" [] (stuckBy "%secret is not defined")
#guard bothGive unrenamed "@nodom" ["true"] (returns ["1"])
#guard bothGive unrenamed "@nodom" ["false"] (stuckBy "%v is not defined")
-- After lookups move values into the map, a value of the wrong type, the
-- first of two parameters `%flag`, and a name that no op on the path
-- defines are stuck as before.
#guard bothGive unrenamed "@after" ["400", "true", "7"] (returns ["8"])
#guard bothGive (renamed "k" "flag") "@after" ["1", "true", "7"]
  (stuckBy "%flag does not have the operand's type")
#guard bothGive (renamed "k" "flag") "@after" ["400", "true", "7"]
  (stuckBy "%flag does not have the operand's type")
#guard bothGive unrenamed "@undefined" ["400"] (stuckBy "%nope is not defined")
#guard sameBy unrenamed "@after" ["400", "true", "7"] (.exhaustive 16)
#guard sameBy (renamed "k" "flag") "@after" ["400", "true", "7"] (.sampled 5)
#guard sameBy unrenamed "@undefined" ["400"] (.exhaustive 16)
#guard sameBy unrenamed "@undefined" ["400"] (.sampled 5)

/-! # Choices after lookups move values into the map

Each path of exhaustive mode, scripted mode and sampled mode goes on from
the bindings at the choice. -/

#guard bothGive unrenamed "@flips" ["400"] (outcomes [ret ["0"], ret ["1"], ret ["2"]] 2)
  (.exhaustive 16)
#guard bothGive unrenamed "@flips" ["400"] (returns ["1"] 2) (.scripted ["false", "true"])
#guard sameBy unrenamed "@flips" ["400"] (.sampled 5)

/-! # Lookups move `young` into `old` -/

/-- The `i8` value `i`. -/
def i8Val (i : Nat) : DVal CoreDialect :=
  ⟨.int 8, (.value (BitVec.ofNat 8 i) : PoisonOr (BitVec 8))⟩

/-- Bindings of `%v0` to `%v{n-1}`, `%v0` the latest, each `%vi` the `i8`
value `i`, and an older `%v0`, the `i8` value `-1`. -/
def bound (n : Nat) : Bindings CoreDialect :=
  Bindings.ofEnv ((List.range n).map (fun i => (s!"v{i}", i8Val i)) ++ [("v0", i8Val 255)])

/-- The bindings after `k` lookups of `x`, or the first error. -/
def lookUp (b : Bindings CoreDialect) (x : Name) : Nat → Except Stuck (Bindings CoreDialect)
  | 0 => pure b
  | k + 1 => do let (_, b) ← b.value x; lookUp b x k

/-- What the bindings give the names `%v0` to `%v{n-1}`, and a name that
they do not bind, as text. -/
def valuesOf (b : Bindings CoreDialect) (n : Nat) : List String :=
  ((List.range n).map (s!"v{·}") ++ ["w"]).map fun x => match b.get x with
    | some v => valueText v
    | none => "none"

-- Forty lookups of the oldest value pass about 8,000 entries, more than
-- `rent` times the 201 entries of `young`, so `young` moves into `old`;
-- every name keeps its value, and `%v0` its latest.
#guard match lookUp (bound 200) "v199" 40 with
  | .ok b => b.young.isEmpty && valuesOf b 200 == valuesOf (bound 200) 200 &&
      valuesOf b 3 == ["0", "1", "2", "none"]
  | .error _ => false
-- Thirty lookups do not pass enough entries to move `young`.
#guard match lookUp (bound 200) "v199" 30 with
  | .ok b => b.young.length == 201 && b.debt == 30 * 199
  | .error _ => false
-- Lookups that pass at most `deep` entries cost nothing.
#guard match lookUp (bound 200) "v128" 1000 with
  | .ok b => b.young.length == 201 && b.debt == 0
  | .error _ => false
#guard match lookUp (bound 200) "v129" 1 with
  | .ok b => b.debt == 129
  | .error _ => false

end FirTest
