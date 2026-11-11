import Fir.Core.Signature
import Fir.Text.Grammar

/-!
How each core op instance and type is written. An op is written as its name
and its attributes; its widths come from the types of its operands and
results, which are written where those values are defined.

* `const` has one attribute, its value: `%c: i32 = const -1 @1`,
  `%t: i1 = const true @1`. An `i1` constant is written `true` or `false`,
  as in LLVM and MLIR. Every other constant is written as its bits read as
  a two's-complement signed integer, in decimal, so `i8` constants run from
  `-128` to `127`. Each bit pattern has one spelling: `const 1` and
  `const -1` at `i1` are errors.
* A float constant is written as its bits read as a two's-complement
  signed integer, in decimal, as an integer constant of the same width is:
  `%one: f32 = const 1065353216 @1` is `1.0` and
  `%z: f32 = const -2147483648 @1` is `-0`. Every bit pattern has one
  spelling, each NaN's payload and sign included (ADR-2026-11-11-1138).
* `add`, `sub` and `mul` have their flags as attributes, in a fixed order,
  `nuw` before `nsw`, each at most once: `%s: i32 = add nuw nsw %a, %b @1`.
* `sdiv` and `udiv` have `exact` when it is set:
  `%q: i32 = sdiv exact %a, %b @1`.
* `icmp` has one attribute, its predicate, from `eq` to `uge`, as LLVM
  writes it: `%lt: i1 = icmp slt %a, %b @1`. No name of a core op contains
  `.`, which is kept for the names of dialects.
* `fcmp` has one attribute, its predicate, from `oeq` to `uno`, as LLVM
  writes it: `%lt: i1 = fcmp olt %a, %b @1` (ADR-2026-11-11-1139).
* `call` has one attribute, its callee's symbol: `%r: i32 = call @sum %n @1`.
* The conditional branch is written `cond_br`:
  `cond_br %c, ^then, ^else(%x) @1`.
* `poison` has no attributes and no operands, so its name comes right
  before its location: `%p: i32 = poison @1`. Its result is one integer, as
  for `const`.
* Every other op is written with the name it has in the op set, and no
  attributes: `%f: i8 = freeze %p @1`, `%w: i64 = zext %x @1`, `ret %r @1`,
  `unreachable @1`.
* The integer type of width N is written `i` and N in decimal with no
  leading zeros, such as `i32`. A width above 16,777,215, the widest the
  core dialect has, is a parse error (ADR-2026-11-03-1000).
* The pointer type of the default memory, `ptr<0>`, is written `ptr`.
  The pointer type `ptr<N>` of another memory is written `ptr(N)`, in the
  applied form of the grammar, such as `ptr(1)`. So each pointer type has
  one spelling: `ptr(0)` does not decode, since `ptr` writes that type, and
  neither does a negative number, a memory above 16,777,215 or any other
  argument list (ADR-2026-11-11-1709).
* A float type is written by its alias when it has one: `f16`, `bf16`,
  `f32`, `f64` or `f128`. Every other format `float<e,m>` is written
  `float(e, m)`, in the applied form of the grammar, such as
  `float(5, 2)`. So each format has one spelling: `float(8, 23)` does not
  decode, since `f32` writes that format, and neither does a negative
  number or a format wider than 16,777,215 bits in all
  (ADR-2026-11-11-0951). `float(1, 1)` decodes, and validation rejects it.

The values of `fir-ref`'s arguments, the values in its JSON output and the
choices that scripted mode follows (see the section "Exhaustive, scripted
and sampled modes") are spelled the same way: `true` and `false` at `i1`,
and signed decimal at every other width, a float's bits included. An
argument and a value in the output may also be `poison`, at any integer
or float type: `fir-ref run` accepts a
poison argument, since the runs of a function that the execution chapter
defines include runs on poison arguments, so differential tests cover them
too. A choice may not be `poison`, since `freeze` chooses a value of its
type.

This section gives, in order: the names of the predicates and the ops, the
attributes of an op, how an op and a type are read back, the core
dialect's text as a whole, and the samples that check it.
-/

namespace Fir.Core

/-- The name of a comparison predicate, as in `icmp slt`. -/
def Pred.name : Pred → String
  | .eq => "eq" | .ne => "ne" | .slt => "slt" | .sle => "sle" | .sgt => "sgt"
  | .sge => "sge" | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"

/-- Every comparison predicate. -/
def Pred.all : List Pred := [.eq, .ne, .slt, .sle, .sgt, .sge, .ult, .ule, .ugt, .uge]

/-- The name of a float comparison predicate, as in `fcmp olt`. -/
def FPred.name : FPred → String
  | .oeq => "oeq" | .one => "one" | .olt => "olt" | .ole => "ole" | .ogt => "ogt"
  | .oge => "oge" | .ord => "ord" | .ueq => "ueq" | .une => "une" | .ult => "ult"
  | .ule => "ule" | .ugt => "ugt" | .uge => "uge" | .uno => "uno"

/-- Every float comparison predicate. -/
def FPred.all : List FPred :=
  [.oeq, .one, .olt, .ole, .ogt, .oge, .ord, .ueq, .une, .ult, .ule, .ugt, .uge, .uno]

/-- The name of a core op instance. -/
def Op.name : Op → String
  | .const .. | .fconst .. => "const" | .add .. => "add" | .sub .. => "sub" | .mul .. => "mul"
  | .sdiv .. => "sdiv" | .udiv .. => "udiv" | .srem _ => "srem" | .urem _ => "urem"
  | .and _ => "and" | .or _ => "or" | .xor _ => "xor"
  | .shl _ => "shl" | .lshr _ => "lshr" | .ashr _ => "ashr"
  | .icmp .. => "icmp" | .fcmp .. => "fcmp" | .select _ => "select"
  | .zext .. => "zext" | .sext .. => "sext" | .trunc .. => "trunc"
  | .freeze _ => "freeze" | .poison _ => "poison" | .br => "br" | .condBr => "cond_br"
  | .ret _ => "ret" | .unreachable => "unreachable" | .call .. => "call"

/-- The flags of `add`, `sub` and `mul`, in their fixed order. -/
def WrapFlags.attrs (f : WrapFlags) : List Attr :=
  (if f.nuw then [.word "nuw"] else []) ++ (if f.nsw then [.word "nsw"] else [])

/-- The attribute of a constant: `true` or `false` at `i1`, and its bits
read as a signed integer at every other width. -/
def constAttr : (w : Nat) → BitVec w → Attr
  | 1, v => .word (if v = 1 then "true" else "false")
  | _, v => .int v.toInt

/-- The attributes of a core op instance. -/
def Op.attrs : Op → List Attr
  | .const w v => [constAttr w v]
  | .fconst _ _ v => [.int v.toInt]
  | .icmp p _ => [.word p.name]
  | .fcmp p _ _ => [.word p.name]
  | .add _ f | .sub _ f | .mul _ f => f.attrs
  | .sdiv _ e | .udiv _ e => if e then [.word "exact"] else []
  | .call f _ _ => [.sym f]
  | _ => []

/-- Reads the flags of `add`, `sub` or `mul`. -/
def decodeWrap : List Attr → Option WrapFlags
  | [] => some {}
  | [.word "nuw"] => some { nuw := true }
  | [.word "nsw"] => some { nsw := true }
  | [.word "nuw", .word "nsw"] => some { nuw := true, nsw := true }
  | _ => none

/-- Reads the flag of `sdiv` or `udiv`. -/
def decodeExact : List Attr → Option Bool
  | [] => some false
  | [.word "exact"] => some true
  | _ => none

/-- The width of an op that takes two `iN` and gives one `iN`. -/
def binWidth : List Ty → List Ty → Option Nat
  | [.int a, .int b], [.int c] => if a = b ∧ b = c then some a else none
  | _, _ => none

/-- An op without attributes. -/
def bare (as : List Attr) (op : Option Op) : Option Op := if as.isEmpty then op else none

/-- Reads a width change from `iM` to `iN`. -/
def decodeCast (mk : Nat → Nat → Op) (as : List Attr) : List Ty → List Ty → Option Op
  | [.int m], [.int n] => bare as (some (mk m n))
  | _, _ => none

/-- The ops that take two `iN`, give one `iN` and have no attributes. -/
def plainBinOps : List (String × (Nat → Op)) :=
  [("srem", .srem), ("urem", .urem), ("and", .and), ("or", .or), ("xor", .xor),
   ("shl", .shl), ("lshr", .lshr), ("ashr", .ashr)]

/-- The core op instance with this name and these attributes, at these
operand and result types. -/
def Op.decode (n : String) (as : List Attr) (ts rs : List Ty) : Option Op :=
  match n with
  | "const" => match as, ts, rs with
    | [.word "true"], [], [.int 1] => some (.const 1 1)
    | [.word "false"], [], [.int 1] => some (.const 1 0)
    | [.int v], [], [.int w] =>
      if w ≠ 1 ∧ (BitVec.ofInt w v).toInt = v then some (.const w (.ofInt w v)) else none
    | [.int v], [], [.float e m] =>
      if (BitVec.ofInt (floatWidth e m) v).toInt = v then some (.fconst e m (.ofInt _ v)) else none
    | _, _, _ => none
  | "icmp" => match as, ts, rs with
    | [.word p], [.int a, .int b], [.int 1] => do
      let pr ← Pred.all.find? (·.name == p)
      if a = b then some (.icmp pr a) else none
    | _, _, _ => none
  | "fcmp" => match as, ts, rs with
    | [.word p], [.float e m, .float e' m'], [.int 1] => do
      let pr ← FPred.all.find? (·.name == p)
      if e = e' ∧ m = m' then some (.fcmp pr e m) else none
    | _, _, _ => none
  | "add" => do pure (.add (← binWidth ts rs) (← decodeWrap as))
  | "sub" => do pure (.sub (← binWidth ts rs) (← decodeWrap as))
  | "mul" => do pure (.mul (← binWidth ts rs) (← decodeWrap as))
  | "sdiv" => do pure (.sdiv (← binWidth ts rs) (← decodeExact as))
  | "udiv" => do pure (.udiv (← binWidth ts rs) (← decodeExact as))
  | "select" => match ts, rs with
    | [.int 1, .int a, .int b], [.int c] => if a = b ∧ b = c then bare as (some (.select a)) else none
    | _, _ => none
  | "zext" => decodeCast .zext as ts rs
  | "sext" => decodeCast .sext as ts rs
  | "trunc" => decodeCast .trunc as ts rs
  | "freeze" => match ts, rs with
    | [.int a], [.int b] => if a = b then bare as (some (.freeze a)) else none
    | _, _ => none
  | "br" => if ts.isEmpty ∧ rs.isEmpty then bare as (some .br) else none
  | "cond_br" => if ts = [.int 1] ∧ rs.isEmpty then bare as (some .condBr) else none
  | "ret" => if rs.isEmpty then bare as (some (.ret ts)) else none
  | "unreachable" => if ts.isEmpty ∧ rs.isEmpty then bare as (some .unreachable) else none
  | "call" => match as with
    | [.sym f] => some (.call f ts rs)
    | _ => none
  | "poison" => match ts, rs with
    | [], [.int w] => bare as (some (.poison w))
    | _, _ => none
  | _ => if let some mk := plainBinOps.lookup n then bare as ((binWidth ts rs).map mk) else none

/-- The alias of the float format `float<e,m>`, if it has one. -/
def floatAlias : Nat → Nat → Option String
  | 5, 10 => some "f16"
  | 8, 7 => some "bf16"
  | 8, 23 => some "f32"
  | 11, 52 => some "f64"
  | 15, 112 => some "f128"
  | _, _ => none

/-- The float format that an alias names: its exponent and mantissa bits. -/
def aliasFormat : String → Option (Nat × Nat)
  | "f16" => some (5, 10)
  | "bf16" => some (8, 7)
  | "f32" => some (8, 23)
  | "f64" => some (11, 52)
  | "f128" => some (15, 112)
  | _ => none

/-- How a core type is written. -/
def Ty.attr : Ty → Attr
  | .int w => .word ("i" ++ toString w)
  | .float e m => match floatAlias e m with
    | some n => .word n
    | none => .app "float" [.int e, .int m]
  | .ptr 0 => .word "ptr"
  | .ptr (n + 1) => .app "ptr" [.int (n + 1)]

/-- Reads `float(e, m)`: a format with no alias, whose numbers are not
negative and which is no wider than `maxWidth` bits in all. -/
def decodeFloat (e m : Int) : Option Ty :=
  if 0 ≤ e ∧ 0 ≤ m ∧ e + m + 1 ≤ maxWidth ∧ floatAlias e.toNat m.toNat = none then
    some (.float e.toNat m.toNat)
  else none

/-- Reads `ptr(N)`: the pointer of a memory other than the default one, no
higher than `maxMemory`. -/
def decodePtr (n : Int) : Option Ty :=
  if 1 ≤ n ∧ n ≤ maxMemory then some (.ptr n.toNat) else none

/-- Reads a core type: `ptr` or `ptr(N)`, `i` and a width of at most
`maxWidth` with no leading zeros, a float format's alias, or
`float(e, m)`. -/
def Ty.decode : Attr → Option Ty
  | .word "ptr" => some (.ptr 0)
  | .word s => match s.toList with
    | 'i' :: ds =>
      let digits := String.ofList ds
      (digits.toNat?).bind fun w =>
        if toString w = digits ∧ w ≤ maxWidth then some (.int w) else none
    | _ => (aliasFormat s).map fun (e, m) => .float e m
  | .app "float" [.int e, .int m] => decodeFloat e m
  | .app "ptr" [.int n] => decodePtr n
  | _ => none

end Fir.Core

namespace Fir

instance : DialectText CoreDialect where
  opName := Core.Op.name
  opAttrs := Core.Op.attrs
  decodeOp := Core.Op.decode
  tyAttr := Core.Ty.attr
  decodeTy := Core.Ty.decode

end Fir

namespace Fir.Core

/-- One instance of every core op, used to check the encoding below. -/
def samples : List Op :=
  [.const 8 (-128), .const 1 1, .const 1 0, .const 7 5, .add 32 {}, .add 32 { nuw := true },
   .sub 16 { nsw := true }, .mul 64 { nuw := true, nsw := true },
   .sdiv 32 true, .udiv 32 false, .srem 8, .urem 8, .and 1, .or 33, .xor 128,
   .shl 32, .lshr 32, .ashr 32, .select 8, .zext 8 32, .sext 1 64, .trunc 64 7,
   .freeze 2, .poison 8, .br, .condBr, .ret [.int 32], .ret [], .unreachable,
   .call "f" [.int 8] [.int 1], .fconst 8 23 0x3f800000, .fconst 11 52 (-1), .fconst 2 1 0,
   .fconst 5 10 0x7e01] ++
  Pred.all.map (.icmp · 32) ++ FPred.all.map (.fcmp · 8 23) ++ [.fcmp .uno 15 112]

-- Decoding an op's encoding, at its own types, gives the op back.
#guard samples.all fun o => Op.decode o.name o.attrs o.sig o.returnTypes == some o

#guard [Ty.int 1, .int 32, .int 128, .ptr 0, .ptr 1, .ptr maxMemory].all fun t =>
  Ty.decode t.attr == some t
#guard Ty.decode (.app "ptr" [.int 0]) == none && Ty.decode (.app "ptr" [.int (-1)]) == none
#guard Ty.decode (.app "ptr" [.int (maxMemory + 1)]) == none && Ty.decode (.app "ptr" []) == none
#guard Ty.decode (.app "ptr" [.int 1, .int 2]) == none && Ty.decode (.app "ptr" [.word "x"]) == none
#guard [Ty.float 5 10, .float 8 7, .float 8 23, .float 11 52, .float 15 112, .float 2 1,
  .float 5 2, .float 2 (maxWidth - 3)].all fun t => Ty.decode t.attr == some t
#guard Ty.decode (.word "f32") == some (.float 8 23) && Ty.decode (.word "bf16") == some (.float 8 7)
#guard Ty.decode (.app "float" [.int 5, .int 2]) == some (.float 5 2)
#guard Ty.decode (.app "float" [.int 8, .int 23]) == none
#guard Ty.decode (.app "float" [.int (-1), .int 3]) == none
#guard Ty.decode (.app "float" [.int 2, .int (maxWidth - 2)]) == none
#guard Ty.decode (.app "float" [.int 5]) == none && Ty.decode (.app "f16" []) == none
#guard Ty.decode (.word "float") == none && Ty.decode (.word "f8") == none
#guard Ty.decode (.app "float" [.int 1, .int 1]) == some (.float 1 1)
#guard Ty.decode (.word "i032") == none && Ty.decode (.word "u8") == none
#guard Op.decode "const" [.int 128] [] [.int 8] == none
#guard Op.decode "add" [.word "nsw", .word "nuw"] [.int 8, .int 8] [.int 8] == none
#guard Op.decode "add" [] [.int 8, .int 16] [.int 8] == none
#guard Op.decode "const" [.word "true"] [] [.int 1] == some (.const 1 1)
#guard Op.decode "const" [.int 1] [] [.int 1] == none && Op.decode "const" [.int (-1)] [] [.int 1] == none
#guard Op.decode "const" [.word "true"] [] [.int 8] == none
#guard Op.decode "icmp" [.word "slt"] [.int 8, .int 8] [.int 1] == some (.icmp .slt 8)
#guard Op.decode "icmp.slt" [] [.int 8, .int 8] [.int 1] == none
#guard Op.decode "poison" [] [] [.int 1] == some (.poison 1)
#guard Op.decode "poison" [.int 0] [] [.int 8] == none && Op.decode "poison" [] [.int 8] [.int 8] == none
#guard Op.decode "poison" [] [] [] == none && Op.decode "poison" [] [] [.int 8, .int 8] == none
#guard Op.decode "poison" [] [] [.ptr 0] == none
#guard Ty.decode (.word "i16777215") == some (.int maxWidth) && Ty.decode (.word "i16777216") == none
-- A float constant is its bits read as a signed integer: `1.0`, `-0` and
-- the quiet NaN of `f32` with its sign set.
#guard Op.decode "const" [.int 1065353216] [] [.float 8 23] == some (.fconst 8 23 0x3f800000)
#guard Op.decode "const" [.int (-2147483648)] [] [.float 8 23] == some (.fconst 8 23 0x80000000)
#guard Op.decode "const" [.int (-4194304)] [] [.float 8 23] == some (.fconst 8 23 0xffc00000)
#guard match (Op.fconst 8 23 0xffc00000).attrs with
  | [.int v] => v == -4194304
  | _ => false
-- Each bit pattern has one spelling: the unsigned reading of `-0` does not
-- fit, and neither does `true`.
#guard Op.decode "const" [.int 2147483648] [] [.float 8 23] == none
#guard Op.decode "const" [.int 4294967295] [] [.float 8 23] == none
#guard Op.decode "const" [.word "true"] [] [.float 8 23] == none
#guard Op.decode "const" [.int 0] [.float 8 23] [.float 8 23] == none
#guard Op.decode "fcmp" [.word "olt"] [.float 11 52, .float 11 52] [.int 1] == some (.fcmp .olt 11 52)
#guard Op.decode "fcmp" [.word "olt"] [.float 11 52, .float 8 23] [.int 1] == none
#guard Op.decode "fcmp" [.word "slt"] [.float 8 23, .float 8 23] [.int 1] == none
#guard Op.decode "fcmp" [.word "olt"] [.int 32, .int 32] [.int 1] == none
#guard Op.decode "icmp" [.word "eq"] [.float 8 23, .float 8 23] [.int 1] == none

end Fir.Core
