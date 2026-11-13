import Fir.Core.Text

/-!
The samples that check the core dialect's text: one instance of every core
op, which decodes from its name and attributes at its own types, and the
spellings of ops and types that read back, or do not. The text-format
chapter proves the same for every op instance and every type; these
checks run the definitions themselves, so a slip in a definition shows
at once. Later sections use the samples too, to check each op's poison
class, its rules and its effects.
-/

namespace Fir.Core

/-- One instance of every core op, used to check the encoding below and the
poison classes, rules and effects in later sections. -/
def samples : List Op :=
  [.const 8 (-128), .const 1 1, .const 1 0, .const 7 5, .add 32 {}, .add 32 { nuw := true },
   .sub 16 { nsw := true }, .mul 64 { nuw := true, nsw := true },
   .sdiv 32 true, .udiv 32 false, .srem 8, .urem 8, .and 1, .or 33, .xor 128,
   .shl 32, .lshr 32, .ashr 32, .select 8, .zext 8 32, .sext 1 64, .trunc 64 7,
   .freeze 2, .poison 8, .br, .condBr, .ret [.int 32], .ret [], .unreachable,
   .call "f" [.int 8] [.int 1], .fconst 8 23 0x3f800000, .fconst 11 52 (-1), .fconst 2 1 0,
   .fconst 5 10 0x7e01] ++
  Pred.all.map (.icmp · 32) ++ FPred.all.map (.fcmp · 8 23) ++ [.fcmp .uno 15 112] ++
  [.fbin .fadd 8 23, .fbin .fsub 11 52, .fbin .fmul 5 10, .fbin .fdiv 2 1, .funary .fneg 8 7,
   .funary .fabs 15 112, .funary .sqrt 8 23, .fma 11 52, .fbin .frem 8 23, .fbin .fmod 2 1] ++
  [.toBits 8 23, .ofBits 11 52, .toBits 2 1, .ofBits 15 112] ++
  [.sitofp 32 8 23, .uitofp 64 11 52, .sitofp 1 5 10, .uitofp 128 15 112, .sitofp 7 2 1] ++
  [.ptradd 0 64, .ptradd 1 8, .ptradd maxMemory 1]

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
-- A float constant is a float literal: `1.0`, `-0.0` and the quiet NaN of
-- `f32` with its sign set.
#guard Op.decode "const" [.float (.dec false 1 ['0'] none)] [] [.float 8 23] ==
  some (.fconst 8 23 0x3f800000)
#guard Op.decode "const" [.float (.dec true 0 ['0'] none)] [] [.float 8 23] ==
  some (.fconst 8 23 0x80000000)
#guard Op.decode "const" [.float (.hex "ffc00000".toList)] [] [.float 8 23] ==
  some (.fconst 8 23 0xffc00000)
#guard (Op.fconst 8 23 0xffc00000).attrs.map Attr.print == ["0xffc00000"]
-- Each bit pattern has one spelling: the bits read as an integer, the
-- bits of a number in hexadecimal and `true` do not decode.
#guard Op.decode "const" [.int 1065353216] [] [.float 8 23] == none
#guard Op.decode "const" [.float (.hex "3f800000".toList)] [] [.float 8 23] == none
#guard Op.decode "const" [.word "true"] [] [.float 8 23] == none
#guard Op.decode "const" [.int 0] [.float 8 23] [.float 8 23] == none
#guard Op.decode "fcmp" [.word "olt"] [.float 11 52, .float 11 52] [.int 1] == some (.fcmp .olt 11 52)
#guard Op.decode "fcmp" [.word "olt"] [.float 11 52, .float 8 23] [.int 1] == none
#guard Op.decode "fcmp" [.word "slt"] [.float 8 23, .float 8 23] [.int 1] == none
#guard Op.decode "fcmp" [.word "olt"] [.int 32, .int 32] [.int 1] == none
#guard Op.decode "icmp" [.word "eq"] [.float 8 23, .float 8 23] [.int 1] == none
-- A float op that rounds needs `round(rne)`; `fneg` and `fabs` take none.
#guard Op.decode "fadd" [roundAttr] [.float 8 23, .float 8 23] [.float 8 23] == some (.fbin .fadd 8 23)
#guard Op.decode "fadd" [] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "fdiv" [.app "round" [.word "rtz"]] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "fneg" [roundAttr] [.float 8 23] [.float 8 23] == none
#guard Op.decode "frem" [roundAttr] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "sqrt" [] [.float 8 23] [.float 8 23] == none
#guard Op.decode "fma" [roundAttr] [.float 8 23, .float 8 23, .float 8 23] [.float 8 23] ==
  some (.fma 8 23)
#guard Op.decode "fma" [roundAttr] [.float 8 23, .float 8 23] [.float 8 23] == none
#guard Op.decode "fadd" [roundAttr] [.int 32, .int 32] [.int 32] == none
-- `sitofp` and `uitofp` take an integer of any width to a float of any
-- format, with `round(rne)`.
#guard Op.decode "sitofp" [roundAttr] [.int 33] [.float 5 10] == some (.sitofp 33 5 10)
#guard Op.decode "uitofp" [roundAttr] [.int 8] [.float 11 52] == some (.uitofp 8 11 52)
#guard Op.decode "sitofp" [] [.int 32] [.float 8 23] == none
#guard Op.decode "uitofp" [roundAttr] [.float 8 23] [.float 8 23] == none
-- `ptradd` takes a pointer and an integer of any width, and gives a pointer
-- of the same memory, with no attributes.
#guard Op.decode "ptradd" [] [.ptr 0, .int 64] [.ptr 0] == some (.ptradd 0 64)
#guard Op.decode "ptradd" [] [.ptr 3, .int 1] [.ptr 3] == some (.ptradd 3 1)
#guard Op.decode "ptradd" [] [.ptr 0, .int 64] [.ptr 1] == none
#guard Op.decode "ptradd" [] [.int 64, .ptr 0] [.ptr 0] == none
#guard Op.decode "ptradd" [] [.ptr 0, .ptr 0] [.ptr 0] == none
#guard Op.decode "ptradd" [] [.ptr 0, .float 8 23] [.ptr 0] == none
#guard Op.decode "ptradd" [] [.ptr 0, .int 64] [.int 64] == none
#guard Op.decode "ptradd" [.word "nuw"] [.ptr 0, .int 64] [.ptr 0] == none

end Fir.Core
