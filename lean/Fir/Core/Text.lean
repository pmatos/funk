import Fir.Core.Signature
import Fir.Text.Grammar

/-!
# The core dialect in text

How each core op instance and type is written. An op is written as its name
and its attributes; its widths come from the types of its operands and
results, which are written where those values are defined.

* `const` has one attribute, its value: `%c: i32 = const -1 @1`.
* `add`, `sub` and `mul` have their flags as attributes:
  `%s: i32 = add nuw nsw %a, %b @1`.
* `sdiv` and `udiv` have `exact` when it is set: `%q: i32 = sdiv exact %a, %b @1`.
* A comparison has its predicate in its name, from `icmp.eq` to `icmp.uge`,
  and no attributes: `%lt: i1 = icmp.slt %a, %b @1`.
* `call` has one attribute, its callee's symbol: `%r: i32 = call @sum %n @1`.
* `condBr` is written `cond_br`: `cond_br %c, ^then, ^else(%x) @1`.
* Every other op is written with the name it has in the op set, and no
  attributes: `%f: i8 = freeze %p @1`, `%w: i64 = zext %x @1`, `ret %r @1`.
* A constant is written as its bits read as a two's-complement signed
  integer, in decimal. So `i8` constants run from `-128` to `127`, and the
  `i1` constants are `0` and `-1`. Each bit pattern has one spelling.
* Flags are written in a fixed order, `nuw` before `nsw`, each at most once.
* `iN` is written `i` and `N` in decimal with no leading zeros, such as
  `i32`, and `ptr` is written `ptr`.
-/

namespace Fir.Core

/-- The name of a comparison predicate, as in `icmp.slt`. -/
def Pred.name : Pred → String
  | .eq => "eq" | .ne => "ne" | .slt => "slt" | .sle => "sle" | .sgt => "sgt"
  | .sge => "sge" | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"

/-- Every comparison predicate. -/
def Pred.all : List Pred := [.eq, .ne, .slt, .sle, .sgt, .sge, .ult, .ule, .ugt, .uge]

/-- The name of a core op instance. -/
def Op.name : Op → String
  | .const .. => "const" | .add .. => "add" | .sub .. => "sub" | .mul .. => "mul"
  | .sdiv .. => "sdiv" | .udiv .. => "udiv" | .srem _ => "srem" | .urem _ => "urem"
  | .and _ => "and" | .or _ => "or" | .xor _ => "xor"
  | .shl _ => "shl" | .lshr _ => "lshr" | .ashr _ => "ashr"
  | .icmp p _ => "icmp." ++ p.name | .select _ => "select"
  | .zext .. => "zext" | .sext .. => "sext" | .trunc .. => "trunc"
  | .freeze _ => "freeze" | .br => "br" | .condBr => "cond_br"
  | .ret _ => "ret" | .call .. => "call"

/-- The flags of `add`, `sub` and `mul`, in their fixed order. -/
def WrapFlags.attrs (f : WrapFlags) : List Attr :=
  (if f.nuw then [.word "nuw"] else []) ++ (if f.nsw then [.word "nsw"] else [])

/-- The attributes of a core op instance. -/
def Op.attrs : Op → List Attr
  | .const _ v => [.int v.toInt]
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
    | [.int v], [], [.int w] => if (BitVec.ofInt w v).toInt = v then some (.const w (.ofInt w v)) else none
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
  | "call" => match as with
    | [.sym f] => some (.call f ts rs)
    | _ => none
  | _ =>
    if let some mk := plainBinOps.lookup n then bare as ((binWidth ts rs).map mk)
    else match Pred.all.find? (fun p => "icmp." ++ p.name == n), ts, rs with
      | some p, [.int a, .int b], [.int 1] => if a = b then bare as (some (.icmp p a)) else none
      | _, _, _ => none

/-- How a core type is written. -/
def Ty.attr : Ty → Attr
  | .int w => .word ("i" ++ toString w)
  | .ptr => .word "ptr"

/-- Reads a core type: `ptr`, or `i` and a width with no leading zeros. -/
def Ty.decode : Attr → Option Ty
  | .word "ptr" => some .ptr
  | .word s => match s.toList with
    | 'i' :: ds =>
      let digits := String.ofList ds
      (digits.toNat?).bind fun w => if toString w = digits then some (.int w) else none
    | _ => none
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
  [.const 8 (-128), .const 1 1, .const 7 5, .add 32 {}, .add 32 { nuw := true },
   .sub 16 { nsw := true }, .mul 64 { nuw := true, nsw := true },
   .sdiv 32 true, .udiv 32 false, .srem 8, .urem 8, .and 1, .or 33, .xor 128,
   .shl 32, .lshr 32, .ashr 32, .select 8, .zext 8 32, .sext 1 64, .trunc 64 7,
   .freeze 2, .br, .condBr, .ret [.int 32], .ret [], .call "f" [.int 8] [.int 1]] ++
  Pred.all.map (.icmp · 32)

-- Decoding an op's encoding, at its own types, gives the op back.
#guard samples.all fun o => Op.decode o.name o.attrs o.sig o.returnTypes == some o

#guard [Ty.int 1, .int 32, .int 128, .ptr].all fun t => Ty.decode t.attr == some t
#guard Ty.decode (.word "i032") == none && Ty.decode (.word "u8") == none
#guard Op.decode "const" [.int 128] [] [.int 8] == none
#guard Op.decode "add" [.word "nsw", .word "nuw"] [.int 8, .int 8] [.int 8] == none
#guard Op.decode "add" [] [.int 8, .int 16] [.int 8] == none

end Fir.Core
