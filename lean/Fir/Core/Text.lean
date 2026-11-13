import Fir.Core.Signature
import Fir.Core.FloatText
import Fir.Core.FloatOpText
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
* A float constant is written as a float literal, the one spelling of its
  bits that the section on float constants gives (ADR-2026-11-11-1438): a
  decimal when it reads back to the bits, such as
  `%one: f32 = const 1.0 @1` and `%z: f32 = const -0.0 @1`, and otherwise
  hexadecimal bits, such as `%n: f32 = const 0x7fc00000 @1` for a NaN.
  Every bit pattern has one spelling, each NaN's payload and sign
  included; `const 1065353216` and `const 0x3f800000` at `f32` do not
  decode.
* `add`, `sub` and `mul` have their flags as attributes, in a fixed order,
  `nuw` before `nsw`, each at most once: `%s: i32 = add nuw nsw %a, %b @1`.
* `sdiv` and `udiv` have `exact` when it is set:
  `%q: i32 = sdiv exact %a, %b @1`.
* `icmp` has one attribute, its predicate, from `eq` to `uge`, as LLVM
  writes it: `%lt: i1 = icmp slt %a, %b @1`. No name of a core op contains
  `.`, which is kept for the names of dialects.
* `fcmp` has one attribute, its predicate, from `oeq` to `uno`, as LLVM
  writes it: `%lt: i1 = fcmp olt %a, %b @1` (ADR-2026-11-09-1549).
* The float arithmetic `fadd`, `fsub`, `fmul`, `fdiv`, `sqrt` and `fma`
  has one attribute, `round(rne)`, and `frem`, `fmod`, `fneg` and `fabs`
  have none:
  `%s: f32 = fadd round(rne) %a, %b @1` (ADR-2026-11-11-1801). The
  section on how the float arithmetic is written says more.
* `bitcast` has no attributes, and its types say which way it reads the
  bits: `%b: i32 = bitcast %f @1` gives the bits of an `f32`, and
  `%f: f32 = bitcast %b @1` the `f32` of an `i32`'s bits. Its integer has
  the float's width, `1 + e + m`; an op whose widths differ does not
  decode.
* `sitofp` and `uitofp` have one attribute, `round(rne)`, and take an
  integer of any width to a float of any format:
  `%f: f64 = sitofp round(rne) %i @1`.
* `fpext` has no attributes and `fptrunc` has one, `round(rne)`, and each
  takes a float of one format to a float of another:
  `%d: f64 = fpext %f @1` and `%f: f32 = fptrunc round(rne) %d @1`. Any
  two formats decode; validation says which pairs each takes.
* `ptradd` has no attributes. It takes a pointer and an integer of any
  width, and gives a pointer of the same memory:
  `%q: ptr = ptradd %p, %k @1` (#231).
* `fptosi` and `fptoui` have no attributes, since they truncate and do not
  round, and take a float of any format to an integer of any width:
  `%i: i32 = fptosi %f @1`.
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
  core dialect has, is a parse error (ADR-2026-10-29-2007).
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
signed decimal at every other width, and a float literal at a float type,
as a float constant is written. An
argument and a value in the output may also be `poison`, at any integer
or float type: `fir-ref run` accepts a
poison argument, since the runs of a function that the execution chapter
defines include runs on poison arguments, so differential tests cover them
too. A choice may not be `poison`, since `freeze` chooses a value of its
type.

This section gives, in order: the names of the predicates and the ops, the
attributes of an op, how an op and a type are read back, the core
dialect's text as a whole. The section after it gives the samples that
check it, and the tests of misspellings are in `FirTest.CoreText`.
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
  | .fbin o .. => o.name | .funary o .. => o.name | .fma .. => "fma"
  | .zext .. => "zext" | .sext .. => "sext" | .trunc .. => "trunc"
  | .toBits .. | .ofBits .. => "bitcast" | .sitofp .. => "sitofp" | .uitofp .. => "uitofp"
  | .fpext .. => "fpext" | .fptrunc .. => "fptrunc"
  | .ptradd .. => "ptradd" | .fptosi .. => "fptosi" | .fptoui .. => "fptoui"
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
  | .fconst e m v => [.float (floatLit e m v)]
  | .icmp p _ => [.word p.name]
  | .fcmp p _ _ => [.word p.name]
  | .fma .. | .sitofp .. | .uitofp .. | .fptrunc .. => [roundAttr]
  | .fbin o .. | .funary o .. => o.attrs
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

/-- Reads `ptradd`: a pointer and an integer of any width, giving a
pointer of the same memory, without attributes. -/
def decodePtrAdd (as : List Attr) : List Ty → List Ty → Option Op
  | [.ptr n, .int w], [.ptr n'] => if n = n' then bare as (some (.ptradd n w)) else none
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
    | [.float l], [], [.float e m] => (decodeFloatLit e m l).map (.fconst e m)
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
  | "fadd" => decodeFBin .fadd as ts rs
  | "fsub" => decodeFBin .fsub as ts rs
  | "fmul" => decodeFBin .fmul as ts rs
  | "fdiv" => decodeFBin .fdiv as ts rs
  | "frem" => decodeFBin .frem as ts rs
  | "fmod" => decodeFBin .fmod as ts rs
  | "fneg" => decodeFUnary .fneg as ts rs
  | "fabs" => decodeFUnary .fabs as ts rs
  | "sqrt" => decodeFUnary .sqrt as ts rs
  | "fma" => decodeFma as ts rs
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
  | "bitcast" => decodeBitcast as ts rs
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
  | "sitofp" => decodeIntToFloat true as ts rs
  | "uitofp" => decodeIntToFloat false as ts rs
  | "fpext" => decodeFpext as ts rs
  | "fptrunc" => decodeFptrunc as ts rs
  | "ptradd" => decodePtrAdd as ts rs
  | "fptosi" => decodeFloatToInt true as ts rs
  | "fptoui" => decodeFloatToInt false as ts rs
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
